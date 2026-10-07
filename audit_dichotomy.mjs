// Full model of the R1 dichotomy at head 204fa19.
// EulerianCycleObstruction (BBTEulerian.lean:451) is
//   forall K hK S, Ukkonen hK L S -> forall sigma, EulerianCycle hK L S sigma ->
//     VertexCycleEq hK L S sigma refl  \/  LongObstruction hK L S
// so R1 (the range L <= K) is tested against BOTH disjuncts, with Ukkonen
// (P2.lean:91) and LongObstruction (BBTEulerian.lean:388) transcribed too.
//
// Transcriptions:
//   Genome.cycl      SourceFaithfulIs.lean:86   S.cycl i = S[i % G]
//   Genome.Agree     SourceFaithfulIs.lean:95   equal length-e substrings
//   Genome.Preceding SourceFaithfulIs.lean:100  S.cycl (t + G - 1)
//   Genome.Following SourceFaithfulIs.lean:104  S.cycl (t + e)
//   IsRepeat         SourceFaithfulIs.lean:111
//   IsTripleRepeat   SourceFaithfulIs.lean:122
//   InOpenArc        SourceFaithfulIs.lean:355
//   Interleaved      SourceFaithfulIs.lean:365
//   Ukkonen          P2.lean:91
//   LongObstruction  BBTEulerian.lean:388
const cyc = (S, G, i) => S[((i % G) + G) % G];
const vtx = (S, G, L, r) => { const o = []; for (let d = 0; d < L - 1; d++) o.push(cyc(S, G, r + d)); return o.join(""); };
const nextpos = (G, x) => (x + 1) % G;
const traverses = (S, G, L, lst) => { for (let i = 0; i < G; i++) if (vtx(S, G, L, lst[(i + 1) % G]) !== vtx(S, G, L, nextpos(G, lst[i]))) return false; return true; };
const vcEq = (S, G, L, lst) => { for (let k = 0; k < G; k++) { let ok = true; for (let i = 0; i < G; i++) if (vtx(S, G, L, lst[i]) !== vtx(S, G, L, (i + k) % G)) { ok = false; break; } if (ok) return k; } return null; };

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
  for (let e = 1; e < G; e++) {
    for (const a of range(G)) for (const b of range(G)) for (const c of range(G))
      if (isTripleRepeat(S, G, e, a, b, c) && !(e < lim)) return false;
  }
  for (let e1 = 1; e1 < G; e1++) for (let e2 = 1; e2 < G; e2++)
    for (const a of range(G)) for (const b of range(G)) for (const c of range(G)) for (const d of range(G))
      if (isRepeat(S, G, e1, a, b) && isRepeat(S, G, e2, c, d) && interleaved(G, a, b, c, d)
          && !(e1 < lim || e2 < lim)) return false;
  return true;
};
const longObstruction = (S, G, L) => {
  const lim = L - 1;
  for (let e = 1; e < G; e++) {
    if (!(lim <= e)) continue;
    for (const a of range(G)) for (const b of range(G)) for (const c of range(G))
      if (isTripleRepeat(S, G, e, a, b, c)) return true;
  }
  for (let e1 = 1; e1 < G; e1++) for (let e2 = 1; e2 < G; e2++) {
    if (!(lim <= e1 && lim <= e2)) continue;
    for (const a of range(G)) for (const b of range(G)) for (const c of range(G)) for (const d of range(G))
      if (isRepeat(S, G, e1, a, b) && isRepeat(S, G, e2, c, d) && interleaved(G, a, b, c, d)) return true;
  }
  return false;
};
const range = n => [...Array(n).keys()];
function* perms(a) { if (!a.length) { yield []; return; } for (let i = 0; i < a.length; i++) { const r = a.slice(0, i).concat(a.slice(i + 1)); for (const p of perms(r)) yield [a[i], ...p]; } }
function* words(A, n) { if (!n) { yield []; return; } for (const c of A) for (const w of words(A, n - 1)) yield [c, ...w]; }

const A2 = [0, 1];
const A3 = [0, 1, 2];

function run(label, alpha, maxG, maxL, inRange) {
  let tested = 0, ukk = 0, eucl = 0, viol = 0;
  const bad = [];
  for (let G = 1; G <= maxG; G++) {
    for (let L = 0; L <= maxL; L++) {
      if (!inRange(G, L)) continue;
      for (const S of words(alpha, G)) {
        tested++;
        if (!ukkonen(S, G, L)) continue;
        ukk++;
        for (const lst of perms(range(G))) {
          if (!traverses(S, G, L, lst)) continue;
          eucl++;
          if (vcEq(S, G, L, lst) !== null) continue;         // first disjunct holds
          if (longObstruction(S, G, L)) continue;             // second disjunct holds
          viol++;
          if (bad.length < 10) bad.push(`G=${G} L=${L} S=${S.join("")} listing=${lst.join("")}`);
        }
      }
    }
  }
  console.log(`${label}`);
  console.log(`  (K,L,S) tested=${tested}  of which Ukkonen=${ukk}  Eulerian listings=${eucl}`);
  console.log(`  listings violating BOTH disjuncts (true counterexamples to the dichotomy): ${viol}`);
  bad.forEach(b => console.log(`   DICOTOMY COUNTEREXAMPLE ${b}`));
  return viol;
}

const v1 = run("R1 dichotomy, L <= K, binary alphabet", A2, 7, 7, (G, L) => L <= G);
const v2 = run("R1 dichotomy, L <= K, ternary alphabet", A3, 6, 6, (G, L) => L <= G);
const v3 = run("R2 dichotomy, K <= L-1, binary alphabet", A2, 7, 12, (G, L) => G <= L - 1);
console.log(`\nSUMMARY R1-binary viol=${v1}  R1-ternary viol=${v2}  R2-binary viol=${v3}`);
