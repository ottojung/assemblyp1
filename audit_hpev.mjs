// Exhaustive check of the two hPevzner residuals R1 and R2.
// Line-by-line transcription of the Lean definitions at head 204fa19:
//   OrientedRigidity.cyc         OrientedRigidity.lean:611   cyc S i = S[i % G]
//   OrientedRigidity.nodeWindow  OrientedRigidity.lean:621   fun d => cyc S (r+d)
//   BBTCondense.vtx              BBTCondense.lean:224       window of length L-1
//   BBTChords.rotAdd             BBTChords.lean:76          (x + s) % G
//   BBTChords.nextPos            BBTChords.lean:80          (x + 1) % G
//   BBTEulerian.EulerianCycle    BBTEulerian.lean:205       traverses AND single
//   BBTEulerian.VertexCycleEq    BBTEulerian.lean:217       exists k, pointwise vtx
// The `single` clause VisitsAll (fun x => sigma(nextPos(sigma^-1 x))) (origin)
// is dropped: it is sigma o rot_1 o sigma^-1, a conjugate of a G-cycle, hence
// injective on iterates for EVERY bijection sigma. The tree already records
// this in Issue94TW5Single (cited in AssemblyP1.lean:450). So a listing is an
// Eulerian cycle iff it satisfies `traverses`.

const cyc = (S, G, i) => S[((i % G) + G) % G];
const vtx = (S, G, L, r) => {
  const out = [];
  for (let d = 0; d < L - 1; d++) out.push(cyc(S, G, r + d));
  return out.join("");
};
const nextpos = (G, x) => (x + 1) % G;

const traverses = (S, G, L, lst) => {
  for (let i = 0; i < G; i++)
    if (vtx(S, G, L, lst[(i + 1) % G]) !== vtx(S, G, L, nextpos(G, lst[i])))
      return false;
  return true;
};

const vertexCycleEqRefl = (S, G, L, lst) => {
  for (let k = 0; k < G; k++) {
    let ok = true;
    for (let i = 0; i < G; i++)
      if (vtx(S, G, L, lst[i]) !== vtx(S, G, L, (i + k) % G)) { ok = false; break; }
    if (ok) return k;
  }
  return null;
};

function* perms(a) {
  if (a.length === 0) { yield []; return; }
  for (let i = 0; i < a.length; i++) {
    const rest = a.slice(0, i).concat(a.slice(i + 1));
    for (const p of perms(rest)) yield [a[i], ...p];
  }
}
function* words(A, n) {
  if (n === 0) { yield []; return; }
  for (const c of A) for (const w of words(A, n - 1)) yield [c, ...w];
}

const isPrimitive = (S, G) => {
  for (let s = 1; s < G; s++) {
    let ok = true;
    for (let i = 0; i < 30 * G + 20; i++) if (cyc(S, G, i) !== cyc(S, G, i + s)) { ok = false; break; }
    if (ok) return false;
  }
  return true;
};

const A2 = [0, 1];

function sweep(label, inRange, maxK, maxL) {
  let tested = 0, counter = 0, nonprim = 0, listings = 0;
  const bad = [];
  for (let G = 1; G <= maxK; G++) {
    for (let L = 0; L <= maxL; L++) {
      if (!inRange(G, L)) continue;
      for (const S of words(A2, G)) {
        tested++;
        if (!isPrimitive(S, G)) nonprim++;
        for (const lst of perms([...Array(G).keys()])) {
          if (!traverses(S, G, L, lst)) continue;
          listings++;
          if (vertexCycleEqRefl(S, G, L, lst) === null) {
            counter++;
            if (bad.length < 25) bad.push(`G=${G} L=${L} S=${S.join("")} listing=${lst.join("")}`);
          }
        }
      }
    }
  }
  console.log(`${label}: ${tested} (K,L,S) instances; ${nonprim} non-primitive; ` +
              `${listings} Eulerian listings; ${counter} listings NOT a rotation of the truth`);
  bad.forEach(b => console.log(`   COUNTEREXAMPLE ${b}`));
  return counter;
}

const r2 = sweep("R2  (K <= L-1, no primitivity)", (G, L) => G <= L - 1, 7, 11);
const r1 = sweep("R1  (L <= K)", (G, L) => L <= G, 6, 6);
console.log(`\nSUMMARY  R2 counterexamples=${r2}   R1 counterexamples=${r1}`);
