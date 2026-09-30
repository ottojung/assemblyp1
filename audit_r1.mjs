// R1 refinement.  See audit_hpev.mjs for the transcription of the Lean defs.
// Question: is the FIRST DISJUNCT of EulerianCycleObstruction
//   VertexCycleEq hK L S sigma (Equiv.refl (Fin K))
// true on its own in the range L <= K, even for PRIMITIVE S?
// (LongObstruction is the second disjunct; under Ukkonen it is excluded by
//  longObstruction_iff_not_Ukkonen, BBTEulerian.lean:397.)
const A2 = [0, 1];
const cyc = (S, G, i) => S[((i % G) + G) % G];
const vtx = (S, G, L, r) => { const o = []; for (let d = 0; d < L - 1; d++) o.push(cyc(S, G, r + d)); return o.join(""); };
const nextpos = (G, x) => (x + 1) % G;
const traverses = (S, G, L, lst) => { for (let i = 0; i < G; i++) if (vtx(S, G, L, lst[(i + 1) % G]) !== vtx(S, G, L, nextpos(G, lst[i]))) return false; return true; };
const vcEq = (S, G, L, lst) => { for (let k = 0; k < G; k++) { let ok = true; for (let i = 0; i < G; i++) if (vtx(S, G, L, lst[i]) !== vtx(S, G, L, (i + k) % G)) { ok = false; break; } if (ok) return k; } return null; };
function* perms(a) { if (!a.length) { yield []; return; } for (let i = 0; i < a.length; i++) { const r = a.slice(0, i).concat(a.slice(i + 1)); for (const p of perms(r)) yield [a[i], ...p]; } }
function* words(A, n) { if (!n) { yield []; return; } for (const c of A) for (const w of words(A, n - 1)) yield [c, ...w]; }
const isPrimitive = (S, G) => { for (let s = 1; s < G; s++) { let ok = true; for (let i = 0; i < 30 * G + 20; i++) if (cyc(S, G, i) !== cyc(S, G, i + s)) { ok = false; break; } if (ok) return false; } return true; };

// minimum lex counterexample (primitive only) over L <= K
let best = null, count = 0, tested = 0, primTested = 0;
for (let G = 1; G <= 8; G++) {
  for (let L = 0; L <= G; L++) {
    for (const S of words(A2, G)) {
      tested++;
      if (!isPrimitive(S, G)) continue;
      primTested++;
      for (const lst of perms([...Array(G).keys()])) {
        if (!traverses(S, G, L, lst)) continue;
        if (vcEq(S, G, L, lst) === null) { count++; if (!best) best = `G=${G} L=${L} S=${S.join("")} listing=${lst.join("")}`; }
      }
    }
  }
}
console.log(`R1 first-disjunct-only, PRIMITIVE S, L<=K, binary, G<=8:`);
console.log(`  instances (K,L,S) = ${tested}, of which primitive = ${primTested}`);
console.log(`  Eulerian listings that are NOT a rotation of the truth: ${count}`);
console.log(`  first (minimum G, then L, then lex S, then lex listing) = ${best}`);

// same, but full (all S), report minimum G and the set of L at that G
let best2 = null;
const byG = {};
for (let G = 1; G <= 7; G++) {
  for (let L = 0; L <= G; L++) {
    for (const S of words(A2, G)) {
      for (const lst of perms([...Array(G).keys()])) {
        if (!traverses(S, G, L, lst)) continue;
        if (vcEq(S, G, L, lst) === null) { (byG[G] ??= []).push([L, S.join(""), lst.join("")]); if (!best2) best2 = [G, L, S.join(""), lst.join("")]; }
      }
    }
  }
}
console.log(`\nR1 first-disjunct-only, ALL S (incl. non-primitive), L<=K, binary, G<=7:`);
console.log(`  global minimum counterexample: G=${best2[0]} L=${best2[1]} S=${best2[2]} listing=${best2[3]}`);
for (const G of Object.keys(byG).sort((a, b) => a - b)) {
  const Ls = [...new Set(byG[G].map(e => e[0]))].sort((a, b) => a - b);
  console.log(`  G=${G}: ${byG[G].length} counterexample listings, at L = ${Ls.join(",")}`);
}
