// A faster drop-in for makefun-diff 1.0.0 (MIT, make.fun), derived from its header rule
// (vendor/makefun-diff/index.js in the kit): the same common prefix, then common suffix,
// then Myers's greedy search with make.fun's tie-break (the deletion when a deletion and
// an insertion reach the same point into the old text, no edge-diagonal pruning), and the
// same patch format. Written from scratch for speed: lines are interned to integer ids
// once, the search runs on one reused flat Int32Array with no per-cell allocation, and
// the script is recovered by backtracking the stored V rows with the same choice rule.

/** The patch's first word. */
export const FORMAT = 'makefun-diff/1';

/** The kept lines a hunk shows before and after each change run. */
export const CONTEXT = 3;

const KEEP = '=';
const DELETE = '-';
const INSERT = '+';

/** One flat scratch buffer for the V rows, reused across cases (grows as needed). Row d
 *  starts at d * (d + 1) / 2 and holds d + 1 entries, one per diagonal k = -d, -d + 2,
 *  ..., d at index (k + d) / 2. An entry holds x + 1 (x the furthest old lines consumed)
 *  or 0 when no path reaches that diagonal. */
let vbuf = new Int32Array(1 << 20);
function vbufEnsure(n) {
  if (vbuf.length < n) {
    let cap = vbuf.length;
    while (cap < n) cap *= 2;
    const nb = new Int32Array(cap);
    nb.set(vbuf);
    vbuf = nb;
  }
}

/** A text's lines, each with its "\n" (the last one without, when the text does not end in one). */
function tokenize(text) {
  const parts = text.split('\n');
  const lines = [];
  const last = parts.length - 1;
  for (let i = 0; i < last; i++) lines.push(parts[i] + '\n');
  if (parts[last] !== '') lines.push(parts[last]);
  return lines;
}

/**
 * The runs of the edit script of A into B: [{ kind, count }], in order, by the header's
 * rule. A and B are Int32Array views of interned line ids. Positions are consumed counts:
 * x old lines and y new lines consumed, y = x - k on diagonal k.
 */
function editRuns(A, B) {
  const n = A.length;
  const m = B.length;
  if (n === 0 && m === 0) return [];
  const maxD = n + m;
  // Rows 0..maxD need (maxD + 1) * (maxD + 2) / 2 entries; ensure room for the rows the
  // search may reach (it stops at dEnd, usually far below maxD, but the buffer must hold
  // whatever d the search reaches, so size for the worst case is impossible: grow on demand).
  const rowOff = (d) => (d * (d + 1)) >> 1;

  // d = 0: the snake from (0, 0) on diagonal 0.
  let x = 0;
  let y = 0;
  while (x < n && y < m && A[x] === B[y]) { x++; y++; }
  vbufEnsure(1);
  vbuf[0] = x + 1;
  if (x >= n && y >= m) return [];

  let dEnd = -1;
  let kEnd = 0;
  for (let d = 1; d <= maxD; d++) {
    const off = rowOff(d);
    const prev = rowOff(d - 1);
    vbufEnsure(off + d + 1);
    const V = vbuf;
    let done = false;
    // ki = 0 (k = -d): only the insertion predecessor exists.
    {
      const k = -d;
      const sIns = V[prev];
      if (sIns !== 0 && sIns - k <= m + 1) {
        let xx = sIns - 1;
        let yy = xx - k;
        while (xx < n && yy < m && A[xx] === B[yy]) { xx++; yy++; }
        V[off] = xx + 1;
        if (xx >= n && yy >= m) { dEnd = d; kEnd = k; done = true; }
      } else V[off] = 0;
    }
    if (!done) {
      let k = -d + 2;
      for (let ki = 1; ki < d; ki++, k += 2) {
        const sDel = V[prev + ki - 1];
        const sIns = V[prev + ki];
        const canR = sDel !== 0 && sDel <= n;
        const canA = sIns !== 0 && sIns - k <= m + 1;
        if (!canR && !canA) {
          V[off + ki] = 0;
          continue;
        }
        let xx;
        if (canR && (!canA || sDel >= sIns - 1)) xx = sDel;
        else xx = sIns - 1;
        let yy = xx - k;
        while (xx < n && yy < m && A[xx] === B[yy]) { xx++; yy++; }
        V[off + ki] = xx + 1;
        if (xx >= n && yy >= m) {
          dEnd = d;
          kEnd = k;
          done = true;
          break;
        }
      }
    }
    if (!done) {
      // ki = d (k = d): only the deletion predecessor exists.
      const k = d;
      const sDel = V[prev + d - 1];
      if (sDel !== 0 && sDel <= n) {
        let xx = sDel;
        let yy = xx - k;
        while (xx < n && yy < m && A[xx] === B[yy]) { xx++; yy++; }
        V[off + d] = xx + 1;
        if (xx >= n && yy >= m) { dEnd = d; kEnd = k; done = true; }
      } else V[off + d] = 0;
    }
    if (done) break;
  }
  if (dEnd < 0) throw new Error('makefun-diff: the search ended without reaching both ends');

  // Backtrack the first path to reach both ends, with the same choice rule at every step.
  const rev = [];
  let d = dEnd;
  let k = kEnd;
  x = vbuf[rowOff(d) + ((k + d) >> 1)] - 1;
  y = x - k;
  while (d > 0) {
    const prev = rowOff(d - 1);
    const ki = (k + d) >> 1;
    const sDel = ki > 0 ? vbuf[prev + ki - 1] : 0;
    const sIns = ki < d ? vbuf[prev + ki] : 0;
    const canR = sDel !== 0 && sDel <= n;
    const canA = sIns !== 0 && sIns - k <= m + 1;
    if (canR && (!canA || sDel >= sIns - 1)) {
      const xp = sDel - 1;
      const yp = xp - (k - 1);
      const keep = x - xp - 1;
      if (keep > 0) rev.push({ kind: KEEP, count: keep });
      rev.push({ kind: DELETE, count: 1 });
      x = xp;
      y = yp;
      k = k - 1;
    } else {
      const xp = sIns - 1;
      const yp = xp - (k + 1);
      const keep = x - xp;
      if (keep > 0) rev.push({ kind: KEEP, count: keep });
      rev.push({ kind: INSERT, count: 1 });
      x = xp;
      y = yp;
      k = k + 1;
    }
    d--;
  }
  if (x > 0) rev.push({ kind: KEEP, count: x });

  // Reverse, merging runs of one kind the reference's addToPath merges.
  const runs = [];
  for (let i = rev.length - 1; i >= 0; i--) {
    const r = rev[i];
    const last = runs[runs.length - 1];
    if (last !== undefined && last.kind === r.kind) last.count += r.count;
    else runs.push({ kind: r.kind, count: r.count });
  }
  return runs;
}

/** A line as the patch writes it: its op, the line, a newline, and "%" on a line of its own when it had none. */
function written(op, line) {
  return line.endsWith('\n') ? op + line : op + line + '\n%\n';
}

/** makefun-diff 1.0.0's answer for one case's input. */
export function run(input) {
  if (input === null || typeof input !== 'object' || typeof input.old !== 'string' || typeof input.new !== 'string') {
    throw new TypeError('makefun-diff: the input is { old, new }, two strings');
  }
  const a = tokenize(input.old);
  const b = tokenize(input.new);
  const n = a.length;
  const m = b.length;

  // Intern each distinct line to an id so the search compares integers, not strings.
  const ids = new Map();
  let nextId = 0;
  const aIds = new Int32Array(n);
  for (let i = 0; i < n; i++) {
    let id = ids.get(a[i]);
    if (id === undefined) { id = nextId++; ids.set(a[i], id); }
    aIds[i] = id;
  }
  const bIds = new Int32Array(m);
  for (let j = 0; j < m; j++) {
    let id = ids.get(b[j]);
    if (id === undefined) { id = nextId++; ids.set(b[j], id); }
    bIds[j] = id;
  }

  // The common prefix, then the common suffix of what is left.
  let prefix = 0;
  while (prefix < n && prefix < m && aIds[prefix] === bIds[prefix]) prefix++;
  let suffix = 0;
  while (suffix < n - prefix && suffix < m - prefix && aIds[n - 1 - suffix] === bIds[m - 1 - suffix]) suffix++;
  const runs = [];
  if (prefix > 0) runs.push({ kind: KEEP, count: prefix });
  runs.push(...editRuns(aIds.subarray(prefix, n - suffix), bIds.subarray(prefix, m - suffix)));
  if (suffix > 0) runs.push({ kind: KEEP, count: suffix });

  // The change runs: each a stretch of deletions and insertions between two kept lines, at old line o and new line p.
  const changes = [];
  let o = 0;
  let p = 0;
  let deleted = 0;
  let inserted = 0;
  for (const r of runs) {
    if (r.kind === KEEP) {
      o += r.count;
      p += r.count;
      continue;
    }
    let c = changes[changes.length - 1];
    if (c === undefined || c.o + c.dels !== o || c.p + c.ins !== p) {
      c = { o, p, dels: 0, ins: 0 };
      changes.push(c);
    }
    if (r.kind === DELETE) {
      c.dels += r.count;
      o += r.count;
      deleted += r.count;
    } else {
      c.ins += r.count;
      p += r.count;
      inserted += r.count;
    }
  }

  // The hunks: change runs at most 2 * CONTEXT kept lines apart share one.
  const hunks = [];
  for (const c of changes) {
    const h = hunks[hunks.length - 1];
    const prev = h !== undefined ? h[h.length - 1] : undefined;
    if (prev !== undefined && c.o - (prev.o + prev.dels) <= 2 * CONTEXT) h.push(c);
    else hunks.push([c]);
  }
  const out = [`${FORMAT} old=${n} new=${m} hunks=${hunks.length} deleted=${deleted} inserted=${inserted}\n`];
  for (const h of hunks) {
    const first = h[0];
    const last = h[h.length - 1];
    const oldStart = Math.max(0, first.o - CONTEXT);
    const newStart = first.p - (first.o - oldStart);
    const after = Math.min(CONTEXT, n - (last.o + last.dels));
    const oldEnd = last.o + last.dels + after;
    const newEnd = last.p + last.ins + after;
    out.push(`@ ${oldStart + 1} ${oldEnd - oldStart} ${newStart + 1} ${newEnd - newStart}\n`);
    let at = oldStart;
    for (const c of h) {
      for (; at < c.o; at++) out.push(written(KEEP, a[at]));
      for (let i = 0; i < c.dels; i++) out.push(written(DELETE, a[c.o + i]));
      for (let i = 0; i < c.ins; i++) out.push(written(INSERT, b[c.p + i]));
      at = c.o + c.dels;
    }
    for (; at < oldEnd; at++) out.push(written(KEEP, a[at]));
  }
  return out.join('');
}
