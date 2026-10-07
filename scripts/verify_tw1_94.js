// Board 94, front 94e7: does `Ukkonen` at L imply `t_w = 1` for the
// (L-1)-mer multigraph D of the truth?
//
// COMPUTATIONAL EVIDENCE ONLY.  The completeness of the ranges searched here is
// NOT proved, so any output is evidence and not a theorem.  This host has no
// Python interpreter, so the evaluator is JavaScript; there is no Python
// version of this file in the tree.
//
// Faithful to AssemblyP1/SourceFaithfulIs.lean:
//   cycl(i)         = S[i mod K]
//   window(e,r)     = S[(r+d) mod K] for d < e
//   Agree(e,r,t)    = window(e,r) deep-equals window(e,t)
//   Preceding(t)    = S[(t+K-1) mod K]
//   Following(e,t)  = S[(t+e) mod K]
//   IsRepeat(e,a,b) = 1<=e<K, a!=b, Agree(e,a,b),
//                     Preceding(a)!=Preceding(b), Following(e,a)!=Following(e,b)
//   IsTripleRepeat(e,a,b,c) = 1<=e<K, a,b,c pairwise distinct, the three
//                     Agrees, not all three Preceding equal, not all three
//                     Following equal
//   Interleaved(a,b,c,d) = the four points pairwise distinct and exactly one of
//                     c,d strictly inside the forward open arc (a,b)
//   Ukkonen(L)      = every maximal triple repeat has e < L-1, and every
//                     interleaved maximal-repeat pair has e1 < L-1 or e2 < L-1
//
// t_w is computed by the directed Matrix-Tree theorem: a cofactor of the
// in-arborescence Laplacian, with loop edges excluded.

'use strict';

if (process.argv[2] === '--detail') {
  const S = process.argv[3].split('').map(Number);
  detail(S, S.length, parseInt(process.argv[4], 10));
  process.exit(0);
}
const Kmax = parseInt(process.argv[2] || '9', 10);
const alph = 2;

// Self-check on hasParallelEdges, run before any sweep output is read.  The
// broken version of the predicate returned false on EVERY input, including
// inputs with an obvious parallel pair, so it is not enough to check it on
// sweep data: check it on hand-built graphs.  A witness for the failure mode
// it used to have is dEdges([0,1,0,1], 4, 3) of the refutation instance
// S = 10100 at L = 3, whose edges 1 and 4 are both 01 -> 10.
if (hasParallelEdges(dEdges([1, 0, 1, 0, 0], 5, 3)) !== true) {
  console.error('FAIL: hasParallelEdges missed the parallel pair of S=10100 at L=3');
  process.exit(1);
}
if (hasParallelEdges([['a', 'b'], ['a', 'c']]) !== false) {
  console.error('FAIL: hasParallelEdges reported a parallel pair where there is none');
  process.exit(1);
}
if (hasParallelEdges([['a', 'b'], ['c', 'b']]) !== false) {
  console.error('FAIL: hasParallelEdges conflated two different tails');
  process.exit(1);
}

function eqwin(S, K, e, r, t) {
  for (let d = 0; d < e; d++) {
    if (S[(r + d) % K] !== S[(t + d) % K]) return false;
  }
  return true;
}

function preceding(S, K, t) { return S[(t + K - 1) % K]; }
function following(S, K, e, t) { return S[(t + e) % K]; }

function isRepeat(S, K, e, a, b) {
  if (!(1 <= e && e < K)) return false;
  if (a === b) return false;
  if (!eqwin(S, K, e, a, b)) return false;
  if (preceding(S, K, a) === preceding(S, K, b)) return false;
  if (following(S, K, e, a) === following(S, K, e, b)) return false;
  return true;
}

function isTripleRepeat(S, K, e, a, b, c) {
  if (!(1 <= e && e < K)) return false;
  if (a === b || a === c || b === c) return false;
  if (!eqwin(S, K, e, a, b)) return false;
  if (!eqwin(S, K, e, a, c)) return false;
  if (!eqwin(S, K, e, b, c)) return false;
  const p = [preceding(S, K, a), preceding(S, K, b), preceding(S, K, c)];
  if (p[0] === p[1] && p[1] === p[2]) return false;
  const f = [following(S, K, e, a), following(S, K, e, b), following(S, K, e, c)];
  if (f[0] === f[1] && f[1] === f[2]) return false;
  return true;
}

function interleaved(K, a, b, c, d) {
  const s = new Set([a, b, c, d]);
  if (s.size !== 4) return false;
  const dab = ((b - a) % K + K) % K;
  if (dab === 0) return false;
  const iac = ((c - a) % K + K) % K;
  const iad = ((d - a) % K + K) % K;
  const inc = iac > 0 && iac < dab;
  const ind = iad > 0 && iad < dab;
  return inc !== ind;
}

function ukkonen(S, K, L) {
  for (let e = 1; e < K; e++) {
    for (let a = 0; a < K; a++)
      for (let b = 0; b < K; b++)
        for (let c = 0; c < K; c++) {
          if (isTripleRepeat(S, K, e, a, b, c)) {
            if (!(e < L - 1)) return false;
          }
        }
  }
  for (let e1 = 1; e1 < K; e1++) {
    for (let e2 = 1; e2 < K; e2++) {
      for (let a = 0; a < K; a++)
        for (let b = 0; b < K; b++) {
          if (!isRepeat(S, K, e1, a, b)) continue;
          for (let c = 0; c < K; c++)
            for (let d = 0; d < K; d++) {
              if (!isRepeat(S, K, e2, c, d)) continue;
              if (interleaved(K, a, b, c, d)) {
                if (!(e1 < L - 1 || e2 < L - 1)) return false;
              }
            }
        }
    }
  }
  return true;
}

function dGraph(S, K, L) {
  const e = L - 1;
  const index = new Map();
  const verts = [];
  const key = (r) => {
    let s = '';
    for (let d = 0; d < e; d++) s += S[(r + d) % K];
    return s;
  };
  for (let r = 0; r < K; r++) {
    const w = key(r);
    if (!index.has(w)) { index.set(w, verts.length); verts.push(w); }
  }
  const n = verts.length;
  const out = Array.from({ length: n }, () => []);
  for (let r = 0; r < K; r++) {
    out[index.get(key(r))].push(index.get(key((r + 1) % K)));
  }
  return { n, out, verts };
}

// exact integer determinant by Gaussian elimination over the rationals with
// BigInt numerators/denominators.  (A pivot-free fraction-free Bareiss variant
// was tried first and was wrong: it omits the division by the previous pivot,
// so the final entry is the determinant times a power of the pivots.  It
// produced root-dependent "t_w" values, which is impossible for an Eulerian D.)
// Exact integer determinant by the fraction-free Bareiss algorithm with exact
// pivot division.  (Two earlier versions were wrong: one omitted the division
// by the previous pivot, giving root-dependent `t_w` values, which is
// impossible for an Eulerian D; the second used cross-multiplied fractions and
// divided by zero on zero cells.  Both failures surfaced as `INCONSISTENT t_w
// across roots` lines, which is how they were caught.)
function det(m) {
  const n = m.length;
  if (n === 0) return 1n;
  const A = m.map((r) => r.slice());
  let prev = 1n;
  let sign = 1n;
  for (let k = 0; k < n - 1; k++) {
    if (A[k][k] === 0n) {
      let piv = -1;
      for (let i = k + 1; i < n; i++) if (A[i][k] !== 0n) { piv = i; break; }
      if (piv < 0) return 0n;
      const tmp = A[k]; A[k] = A[piv]; A[piv] = tmp;
      sign = -sign;
    }
    for (let i = k + 1; i < n; i++) {
      for (let j = k + 1; j < n; j++) {
        const num = A[i][j] * A[k][k] - A[i][k] * A[k][j];
        A[i][j] = num / prev;   // exact by the Bareiss identity
      }
      A[i][k] = 0n;
    }
    prev = A[k][k];
  }
  return sign * A[n - 1][n - 1];
}

function arborescenceCount(out, n, w) {
  if (n === 1) return 1n;
  // Out-degree Laplacian Q with Q[u][u] = outdeg(u), Q[u][v] = -m(u->v),
  // self-loops dropped entirely (a loop is never an edge of a spanning tree).
  // The number of spanning in-arborescences rooted at w is the cofactor of Q
  // obtained by deleting row w and column w.
  const Q = Array.from({ length: n }, () => new Array(n).fill(0n));
  for (let u = 0; u < n; u++) {
    for (const v of out[u]) {
      if (u === v) continue;
      Q[u][u] += 1n;
      Q[u][v] -= 1n;
    }
  }
  const rows = [];
  for (let i = 0; i < n; i++) if (i !== w) rows.push(i);
  const M = rows.map((i) => rows.map((j) => Q[i][j]));
  return det(M);
}

// Rotation-primitivity: no nontrivial rotation fixes S.  This is the
// project's PopulationReduction.IsPrimitive.
function isPrimitive(S, K) {
  for (const t of [1, 2, 3, 4, 5, 6, 7, 8]) {
    if (t >= K) continue;
    let ok = true;
    for (let i = 0; i < K; i++) if (S[i] !== S[(i + t) % K]) { ok = false; break; }
    if (ok) return false;
  }
  return true;
}

// Independent brute-force count of spanning in-arborescences rooted at w: choose
// one out-edge per vertex v != w (|V| * maxdeg choices), keep those whose
// chosen edges reach w from every vertex.  No determinant involved.  Used to
// cross-check det(); run only for small |V|.
function arborescenceCountBrute(out, n, w) {
  if (n === 1) return 1n;
  let count = 0n;
  const idx = [];
  for (let v = 0; v < n; v++) if (v !== w) idx.push(v);
  const total = idx.reduce((a, v) => a * BigInt(out[v].length), 1n);
  for (let t = 0n; t < total; t++) {
    let x = t;
    const head = new Array(n).fill(-1);
    for (const v of idx) { head[v] = out[v][Number(x % BigInt(out[v].length))]; x /= BigInt(out[v].length); }
    // every vertex must reach w following head
    let good = true;
    for (let v = 0; v < n && good; v++) {
      let c = v, steps = 0;
      while (c !== w) {
        if (head[c] === undefined || head[c] < 0) { good = false; break; }
        c = head[c];
        if (++steps > n) { good = false; break; }
      }
    }
    if (good) count++;
  }
  return count;
}

// Full report for one named instance: every maximal repeat, every maximal triple
// repeat, the multigraph D, and t_w by two independent methods.
// Number of cyclic Eulerian circuits of D up to rotation, counted DIRECTLY
// (no BEST, no matrix-tree): enumerate orderings of the K edge labels, keep
// those that traverse D, and quotient by rotation of the edge-label sequence.
// This is an independent check of what the BEST product predicts.
// Number of cyclic Eulerian circuits of D up to rotation, counted DIRECTLY
// (no BEST, no matrix-tree).  A circuit is an ordering (e_0, ..., e_{K-1}) of
// the edge labels with edges[e_i][1] = edges[e_{i+1}][0] cyclically.  Two
// orderings differing by a rotation of the list are the same circuit, so each
// orbit is recorded by its lexicographically least rotation.
// Number of edge-type Eulerian circuit orbits of D up to rotation.  Edge types
// are pairs (tail vertex word, head vertex word); copies of one type are
// INDISTINGUISHABLE, which is the convention of
// docs/exact-same-length-spectrum-fibre-count.md and of BBT Theorem 3 (which
// is about the condensed sequence graph, hence about edge types).  This is a
// strictly coarser count than eulerCircuitOrbits, which labels every edge.
function eulerCircuitTypeOrbits(edges) {
  const K = edges.length;
  const seen = new Set();
  const out = [];
  const perm = new Array(K);
  const used = new Array(K).fill(false);
  function closes() {
    for (let i = 0; i < K; i++) {
      if (edges[perm[i]][1] !== edges[perm[(i + 1) % K]][0]) return false;
    }
    return true;
  }
  function record() {
    const word = perm.map((e) => edges[e][0] + '>' + edges[e][1]);
    let best = null;
    for (let s2 = 0; s2 < K; s2++) {
      const rot = [];
      for (let j = 0; j < K; j++) rot.push(word[(j + s2) % K]);
      const key = rot.join(' | ');
      if (best === null || key < best) best = key;
    }
    if (seen.has(best)) return;
    seen.add(best);
    out.push(best);
  }
  function rec(i) {
    if (i === K) { if (closes()) record(); return; }
    for (let e = 0; e < K; e++) {
      if (used[e]) continue;
      used[e] = true; perm[i] = e; rec(i + 1); used[e] = false;
    }
  }
  rec(0);
  return out;
}

// The edge multiset of D at read length L, as a list of [tailWord, headWord].
function dEdges(S, K, L) {
  const edges = [];
  for (let r = 0; r < K; r++) {
    let tu = '', hd = '';
    for (let d = 0; d < L - 1; d++) tu += S[(r + d) % K];
    for (let d = 0; d < L - 1; d++) hd += S[(r + 1 + d) % K];
    edges.push([tu, hd]);
  }
  return edges;
}

function eulerCircuitOrbits(edges, n) {
  const K = edges.length;
  const seen = new Set();
  const out = [];
  const perm = new Array(K);
  const used = new Array(K).fill(false);
  function closes() {
    for (let i = 0; i < K; i++) {
      if (edges[perm[i]][1] !== edges[perm[(i + 1) % K]][0]) return false;
    }
    return true;
  }
  function record() {
    let best = null;
    for (let s = 0; s < K; s++) {
      const rot = [];
      for (let j = 0; j < K; j++) rot.push(perm[(j + s) % K]);
      const key = rot.join(",");
      if (best === null || key < best) best = key;
    }
    if (seen.has(best)) return;
    seen.add(best);
    out.push(best.split(",").map(Number));
  }
  function rec(i) {
    if (i === K) { if (closes()) record(); return; }
    for (let e = 0; e < K; e++) {
      if (used[e]) continue;
      used[e] = true; perm[i] = e; rec(i + 1); used[e] = false;
    }
  }
  rec(0);
  return out;
}


// BEST factor prod_v (d+(v)-1)!, with (0-1)! := 1 by convention.
function bestDegreeFactor(out, n) {
  const fact = [1n, 1n, 1n, 2n, 6n, 24n, 120n, 720n];
  let p = 1n;
  for (let v = 0; v < n; v++) {
    const d = out[v].length - 1;
    if (d >= 1) p *= (d < fact.length ? fact[d] : 0n);
  }
  return p;
}

function detail(S, K, L) {
  console.log('--- S=' + S.join('') + ' K=' + K + ' L=' + L + ' (threshold L-1=' + (L - 1) + ')');
  console.log('  primitive:', isPrimitive(S, K), ' Ukkonen:', ukkonen(S, K, L));
  for (let e = 1; e < K; e++) for (let a = 0; a < K; a++) for (let b = 0; b < K; b++)
    if (isRepeat(S, K, e, a, b)) console.log('  IsRepeat e=' + e + ' (' + a + ',' + b + ')');
  for (let e = 1; e < K; e++) for (let a = 0; a < K; a++) for (let b = 0; b < K; b++) for (let c = 0; c < K; c++)
    if (isTripleRepeat(S, K, e, a, b, c)) console.log('  IsTripleRepeat e=' + e + ' (' + a + ',' + b + ',' + c + ')');
  const g = dGraph(S, K, L);
  console.log('  verts', JSON.stringify(g.verts), 'out', JSON.stringify(g.out));
  for (let w = 0; w < g.n; w++)
    console.log('   t_w(root ' + w + ') = ' + arborescenceCount(g.out, g.n, w) +
      ' (brute ' + arborescenceCountBrute(g.out, g.n, w) + ')');
  const KK = S.length;
  const edges = [];
  for (let r = 0; r < KK; r++) {
    let tu = "", hd = "";
    for (let d = 0; d < L - 1; d++) tu += S[(r + d) % KK];
    for (let d = 0; d < L - 1; d++) hd += S[(r + 1 + d) % KK];
    edges.push([tu, hd]);
  }
  const orbits = eulerCircuitOrbits(edges, g.n);
  const tw = arborescenceCount(g.out, g.n, 0);
  const df = bestDegreeFactor(g.out, g.n);
  const typeOrbits = eulerCircuitTypeOrbits(edges);
  console.log('   edge-TYPE circuit orbits of D (unlabelled, BBT convention) = ' + typeOrbits.length);
  for (const o of typeOrbits) console.log('     type orbit: ' + o);
  console.log('   Eulerian circuit orbits of D (DIRECT count) = ' + orbits.length +
    '; BEST predicts t_w * prod(d+-1)! = ' + tw + ' * ' + df + ' = ' + (tw * df));
  for (const o of orbits)
    console.log('     orbit: ' + o.map((e) => e + ':' + edges[e][0] + '->' + edges[e][1]).join('  '));
}


// Does D have a vertex with two out-edges to the SAME head (a parallel pair)?
//
// BUG FOUND AND FIXED (board 94, front 94a10).  The previous version of this
// predicate iterated its outer loop over `edges` (an array of [tail, head]
// pairs) and its inner loop over `edges[u].length`, i.e. it treated the edge
// array as an adjacency structure.  For every input the inner loop therefore
// ran exactly twice, over the two entries `[tail, head]` in the order they
// appear, so the `seen` set was rebuilt from scratch each time and the
// predicate was IDENTICALLY FALSE.  Every instance was classified "simple",
// which is how front 94e7's report came to record 208 instances with a simple
// D and t_w > 1 at K <= 9 (548 + 208 = 756 is the true "simple" count, i.e.
// all of them).  With the predicate corrected the same sweep gives ZERO
// simple-D / t_w > 1 instances at K <= 12; see docs/edge-type-obligation-94.md.
//
// The fixed version groups the edges by tail and then by head, and reports a
// parallel pair iff some head occurs more than once under one tail.
function hasParallelEdges(edges) {
  const byTailHead = new Map();
  for (const [t, h] of edges) {
    const k = t + '>' + h;
    byTailHead.set(k, (byTailHead.get(k) || 0) + 1);
  }
  return [...byTailHead.values()].some((c) => c > 1);
}

let hits = 0;
let checked = 0;
let uniqfail = 0;
const typehist = new Map();
const parhist = new Map();
const deghist = new Map();
for (let K = 1; K <= Kmax; K++) {
  const total = Math.pow(alph, K);
  for (let n = 0; n < total; n++) {
    const S = [];
    let x = n;
    for (let i = 0; i < K; i++) { S.push(x % alph); x = Math.floor(x / alph); }
    for (let L = 2; L <= K; L++) {
      if (!ukkonen(S, K, L)) continue;
      if (!isPrimitive(S, K)) continue;
      checked++;
      const { n: nv, out } = dGraph(S, K, L);
      const ts = [];
      for (let w = 0; w < nv; w++) ts.push(arborescenceCount(out, nv, w));
      if (!ts.every((t) => t === ts[0])) {
        console.log(`INCONSISTENT t_w across roots! S=${S.join('')} K=${K} L=${L} [${ts}]`);
      }
      if (nv <= 7) {
        const t0 = arborescenceCount(out, nv, 0);
        const b0 = arborescenceCountBrute(out, nv, 0);
        if (t0 !== b0) { console.log('DET/BRUTE MISMATCH', S.join(''), K, L, t0, b0); process.exit(1); }
      }
      const maxdeg = Math.max(...out.map((x) => x.length));
      const key = `${K},${L},${nv},${maxdeg}`;
      deghist.set(key, (deghist.get(key) || 0) + 1);
      if (K <= 9) {
        const te = eulerCircuitTypeOrbits(dEdges(S, K, L));
        typehist.set(te.length, (typehist.get(te.length) || 0) + 1);
        const par = hasParallelEdges(dEdges(S, K, L));
        parhist.set((par ? 'par' : 'simple') + '/t_w=' + (ts[0] === 1n ? '1' : '>1') + '/orbits=' + te.length,
          (parhist.get((par ? 'par' : 'simple') + '/t_w=' + (ts[0] === 1n ? '1' : '>1') + '/orbits=' + te.length) || 0) + 1);
        if (te.length > 1) {
          uniqfail++;
          console.log('UNIQUENESS-FAIL S=' + S.join('') + ' K=' + K + ' L=' + L +
            ' t_w=' + ts[0] + ' edge-type-orbits=' + te.length);
          for (const o of te) console.log('     type orbit: ' + o);
        }
      }
      if (ts[0] !== 1n) {
        hits++;

      }
    }
  }
  console.log(`-- K=${K} done, checked=${checked} hits=${hits}`);
}
console.log(`checked ${checked} primitive (S,L) Ukkonen instances, ${hits} with t_w != 1, ` +
  `${uniqfail} with MORE THAN ONE edge-type circuit orbit`);
console.log('edge-type-orbit histogram:', JSON.stringify([...typehist.entries()].sort((x, y) => x[0] - y[0])));
console.log('parallel-edges / t_w / edge-type-orbits joint histogram:');
for (const [k, v] of [...parhist.entries()].sort()) console.log('  ' + k + ' : ' + v);
