// Search for violations of R1_shift_step (IssueP1/Issue94R1LongWindow.lean,
// the `def R1_shift_step` of section 4) in the range 2 <= L <= K.
// RESULT (binary, K <= 8): violations at every K >= 3 and every 2 <= L <= K-1,
// none at L = K and none at K <= 2.  The single refutation this front relies on
// is kernel-checked in Lean at K = 3, L = 2, S = 001 (theorem
// `AssemblyP1.Issue94R1LongWindow.instance3_not_shift_step`); the search is
// evidence for the *systematic* shape only, never for the refutation.
// R1_shift_step: forall x y, vtx x = vtx y -> vtx (nextPos x) = vtx (nextPos y).
// Equivalently: window_{L-1}(x) = window_{L-1}(y)  ==>  S[x+L-1] = S[y+L-1].
// Transcriptions identical to audit_dichotomy.mjs (verified against the Lean sources).
const cyc = (S, G, i) => S[((i % G) + G) % G];
const vtx = (S, G, L, r) => { const o = []; for (let d = 0; d < L - 1; d++) o.push(cyc(S, G, r + d)); return o.join(""); };
const nextpos = (G, x) => (x + 1) % G;
const agree = (S, G, e, a, b) => { for (let d = 0; d < e; d++) if (cyc(S, G, a + d) !== cyc(S, G, b + d)) return false; return true; };
const preceding = (S, G, t) => cyc(S, G, t + G - 1);
const following = (S, G, e, t) => cyc(S, G, t + e);
const isRepeat = (S, G, e, a, b) =>
  1 <= e && e < G && a !== b && agree(S, G, e, a, b) &&
  preceding(S, G, a) !== preceding(S, G, b) && following(S, G, e, a) !== following(S, G, e, b);
const isTripleRepeat = (S, G, e, a, b, c) =>
  1 <= e && e < G && a !== b && a !== c && b !== c &&
  agree(S, G, e, a, b) && agree(S, G, e, a, c) && agree(S, G, e, b, c) &&
  !(preceding(S, G, a) === preceding(S, G, b) && preceding(S, G, b) === preceding(S, G, c)) &&
  !(following(S, G, e, a) === following(S, G, e, b) && following(S, G, e, b) === following(S, G, e, c));
const inOpenArc = (G, a, b, p) => { const u = (x) => (x + G) % G; const x = u(p - a), y = u(b - a); return 0 < x && x < y; };
const fourDistinct = (a, b, c, d) => a !== b && a !== c && a !== d && b !== c && b !== d && c !== d;
const interleaved = (G, a, b, c, d) => fourDistinct(a, b, c, d) && (inOpenArc(G, a, b, c) === !inOpenArc(G, a, b, d));
const ukkonen = (S, G, L) => {
  const lim = L - 1;
  for (let e = 1; e < G; e++) for (const a of range(G)) for (const b of range(G)) for (const c of range(G))
    if (isTripleRepeat(S, G, e, a, b, c) && !(e < lim)) return false;
  for (let e1 = 1; e1 < G; e1++) for (let e2 = 1; e2 < G; e2++)
    for (const a of range(G)) for (const b of range(G)) for (const c of range(G)) for (const d of range(G))
      if (isRepeat(S, G, e1, a, b) && isRepeat(S, G, e2, c, d) && interleaved(G, a, b, c, d) && !(e1 < lim || e2 < lim)) return false;
  return true;
};
const range = n => [...Array(n).keys()];
function* words(A, n) { if (!n) { yield []; return; } for (const c of A) for (const w of words(A, n - 1)) yield [c, ...w]; }

// shiftStepFail(S,G,L): returns [x,y] witnessing failure of R1_shift_step, or null.
// Note: x = y can never fail, so the search ranges over distinct starts only.
const shiftStepFail = (S, G, L) => {
  for (let x = 0; x < G; x++) for (let y = 0; y < G; y++) {
    if (x === y) continue;
    if (vtx(S, G, L, x) === vtx(S, G, L, y) && vtx(S, G, L, nextpos(G, x)) !== vtx(S, G, L, nextpos(G, y)))
      return [x, y];
  }
  return null;
};

function run(label, alpha, maxG, maxL) {
  let tested = 0, ukk = 0, viol = 0;
  const bad = [];
  for (let G = 1; G <= maxG; G++) for (let L = 2; L <= Math.min(maxL, G); L++)
    for (const S of words(alpha, G)) {
      tested++;
      if (!ukkonen(S, G, L)) continue;
      ukk++;
      const w = shiftStepFail(S, G, L);
      if (!w) continue;
      viol++;
      if (bad.length < 12) bad.push(`G=${G} L=${L} S=${S.join("")} x=${w[0]} y=${w[1]}`);
    }
  console.log(`${label}\n  tested=${tested} Ukkonen=${ukk} shiftStepViolations=${viol}`);
  bad.forEach(b => console.log(`   VIOLATION ${b}`));
  return viol;
}
const maxG = Number(process.argv[2] ?? 7);
const al = Number(process.argv[3] ?? 2);
const v = run(`R1_shift_step, binary, G<=${maxG}`, [0, 1], maxG, maxG);
if (al >= 3) run(`R1_shift_step, ternary, G<=${maxG}`, [0, 1, 2], maxG, maxG);
console.log(`\nSUMMARY violations=${v}`);
