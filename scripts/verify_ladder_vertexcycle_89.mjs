#!/usr/bin/env node
// Exhaustive search aimed *specifically* at `BBTLadder.LadderVertexCycle`.
//
// The Python search `scripts/verify_ladder_blocks_89.py` reported, over binary
// words of length <= 10 and ternary words of length <= 7, zero failures of
// `VertexCycleEq` among 3770 genuine traversals.  That is a strictly stronger
// statement than the falsity test for `LadderVertexCycle`, but it never
// checked the *hypothesis* of `LadderVertexCycle` and never went past
// length 10, so it cannot exclude a counterexample to the `Prop` itself.
//
// This script decides, for every genuine traversal, the pair
//
//     hypothesis  :=  every crossing pair of support chords carries the same
//                     deterministic maximal extension
//                     (`crossing_chords_coalesce`, which is literally the body
//                     of the `Prop`'s hypothesis, see
//                     AssemblyP1/BBTLadder.lean:659-666)
//
//     conclusion  :=  `BBTEulerian.VertexCycleEq hK L S sigma (Equiv.refl)`
//
// and reports the counterexample count `hypothesis AND NOT conclusion`, which
// is exactly a refutation of `BBTLadder.LadderVertexCycle` as written.
//
// It also reports, separately, how often the hypothesis is *non-vacuous*
// (there really is a crossing pair of chords) and how often the conclusion
// fails, so the reader can see which side is doing the work.
//
// NOTE: this host has no `python3`; the predicates are transcribed here from
// AssemblyP1/SourceFaithfulIs.lean (Genome.Agree / IsRepeat / IsTripleRepeat /
// InOpenArc / Interleaved) and def:P2 in AssemblyP1/P2.lean, and the search
// conventions from scripts/verify_ladder_blocks_89.py, so that the two scripts
// enumerate the same class.  The transcriptions are quoted in comments.
//
// This is EVIDENCE, NOT PROOF.  The completeness of the enumeration is not
// established in the kernel, and nothing here is kernel-checked.  The words
// are also NOT filtered by `Ukkonen`, so the class searched is *larger* than
// the class the `Prop` quantifies over: a counterexample found here would
// refute the `Prop` (its `Ukkonen` hypothesis is merely unused).
//
// Usage: node scripts/verify_ladder_vertexcycle_89.mjs [--bin G] [--tri G]

const argv = process.argv.slice(2)
function argOr(name, dflt) {
  const i = argv.indexOf('--' + name)
  return i >= 0 ? parseInt(argv[i + 1], 10) : dflt
}
const BINMAX = argOr('bin', 12)
const TRIMAX = argOr('tri', 8)

// ------------------------------------------------------------------ the source
// SourceFaithfulIs.Genome.Agree / IsRepeat / IsTripleRepeat / InOpenArc /
// Interleaved, and def:P2 of AssemblyP1/P2.lean, as in
// scripts/verify_ladder_blocks_89.py.

const cyc = (w, t) => w[((t % w.length) + w.length) % w.length]
const window = (w, r, d) => cyc(w, r + d)
const Agree = (w, e, r, t) => {
  for (let d = 0; d < e; d++) if (window(w, r, d) !== window(w, t, d)) return false
  return true
}
const Preceding = (w, t) => cyc(w, t - 1)
const Following = (w, e, t) => cyc(w, t + e)

function IsRepeat(w, e, a, b) {
  const n = w.length
  if (!(1 <= e && e < n) || a === b) return false
  if (!Agree(w, e, a, b)) return false
  if (Preceding(w, a) === Preceding(w, b)) return false
  if (Following(w, e, a) === Following(w, e, b)) return false
  return true
}

function IsTripleRepeat(w, e, a, b, c) {
  const n = w.length
  if (!(1 <= e && e < n) || a === b || a === c || b === c) return false
  if (!(Agree(w, e, a, b) && Agree(w, e, a, c) && Agree(w, e, b, c))) return false
  if (Preceding(w, a) === Preceding(w, b) && Preceding(w, a) === Preceding(w, c)) return false
  if (Following(w, e, a) === Following(w, e, b) && Following(w, e, a) === Following(w, e, c)) return false
  return true
}

const InOpenArc = (w, a, b, p) => {
  const n = w.length
  const x = ((p - a) % n + n) % n
  const y = ((b - a) % n + n) % n
  return 0 < x && x < y
}

function Interleaved(w, a, b, c, d) {
  if (new Set([a, b, c, d]).size !== 4) return false
  return InOpenArc(w, a, b, c) !== InOpenArc(w, a, b, d)
}

// def:P2 at read length L: no maximal triple repeat of length >= L-1, and no
// interleaved maximal repeat pair with both lengths >= L-2.
function P2(w, L) {
  const n = w.length
  for (let e = 1; e < n; e++)
    for (let a = 0; a < n; a++)
      for (let b = 0; b < n; b++)
        for (let c = 0; c < n; c++)
          if (IsTripleRepeat(w, e, a, b, c) && !(e < L - 1)) return false
  const R = []
  for (let e = 1; e < n; e++)
    for (let a = 0; a < n; a++)
      for (let b = 0; b < n; b++) if (IsRepeat(w, e, a, b)) R.push([e, a, b])
  for (const [e1, a1, b1] of R)
    for (const [e2, c1, d1] of R)
      if (Interleaved(w, a1, b1, c1, d1) && !(e1 <= L - 2 || e2 <= L - 2)) return false
  return true
}

// ------------------------------------------------------------------ the graph

const vtx = (w, x, L) => {
  const K = L - 1, n = w.length, out = []
  for (let i = 0; i < K; i++) out.push(w[((x + i) % n + n) % n])
  return out.join('')
}

const is_primitive = (w) => {
  const n = w.length, s = w.join('')
  for (let k = 1; k < n; k++) if (s.slice(k) + s.slice(0, k) === s) return false
  return true
}

// every involution of Fin G preserving `vtx`; under P2 + primitivity these are
// exactly the `AltF` of genuine traversals (BBTLadder.AltF_sq)
function involutions_preserving(w, L) {
  const n = w.length
  const fib = new Map()
  for (let x = 0; x < n; x++) {
    const v = vtx(w, x, L)
    if (!fib.has(v)) fib.set(v, [])
    fib.get(v).push(x)
  }
  for (const v of fib.values()) if (v.length > 2) return []
  const pairs = [...fib.values()].filter(v => v.length === 2)
  const out = []
  for (let mask = 0; mask < (1 << pairs.length); mask++) {
    const f = [...Array(n).keys()]
    for (let i = 0; i < pairs.length; i++)
      if ((mask >> i) & 1) { const [a, b] = pairs[i]; f[a] = b; f[b] = a }
    out.push(f)
  }
  return out
}

const is_G_cycle = (J) => {
  const n = J.length, seen = new Set()
  let x = 0
  while (!seen.has(x)) { seen.add(x); x = J[x] }
  return x === 0 && seen.size === n
}

// `EulerianCycle`'s `single` clause in the J = f o rho representation
const genuine = (w, f) => is_G_cycle(f.map((y, x) => f[(x + 1) % f.length]))

function listing(w, f) {
  const n = f.length
  for (let q = 0; q < n; q++) {
    const seq = [q]
    let x = q
    for (let i = 0; i < n - 1; i++) {
      x = f[(x + 1) % n]
      if (seq.includes(x)) break
      seq.push(x)
    }
    if (seq.length === n) return seq
  }
  return null
}

// `BBTEulerian.VertexCycleEq hK L S sigma (Equiv.refl)`
function vertex_cycle_is_rotation(w, L, f) {
  const n = w.length, seq = listing(w, f)
  if (seq === null) return false
  for (let k = 0; k < n; k++) {
    let ok = true
    for (let i = 0; i < n; i++)
      if (vtx(w, seq[i], L) !== vtx(w, (i + k) % n, L)) { ok = false; break }
    if (ok) return true
  }
  return false
}

// ------------------------------------------------------- the support geometry

const support = (f) => f.map((y, x) => x).filter(x => f[x] !== x)

function agree_len(w, a, b) {
  const n = w.length
  let k = 0
  while (k < n && w[(a + k) % n] === w[(b + k) % n]) k++
  return k
}

// the deterministic maximal extension of the pair (a, b): the two starts are
// the pair shifted back by the maximal backward agreement, compared as an
// unordered pair (scripts/verify_ladder_blocks_89.py `max_pair`)
function max_pair(w, a, b) {
  const n = w.length
  let back = 0
  while (back < n && w[(a - 1 - back + n * 2) % n] === w[(b - 1 - back + n * 2) % n]) back++
  let fwd = 0
  while (fwd < n - back && w[(a + fwd) % n] === w[(b + fwd) % n]) fwd++
  return [((a - back) % n + n) % n, ((b - back) % n + n) % n, back + fwd]
}

const chords = (f) => {
  const out = []
  for (const x of support(f)) {
    const c = [Math.min(x, f[x]), Math.max(x, f[x])]
    if (!out.some(e => e[0] === c[0] && e[1] === c[1])) out.push(c)
  }
  return out
}

// the body of the hypothesis of `LadderVertexCycle` (BBTLadder.lean:659-666):
// every crossing pair of transposition chords of `AltF` carries the same
// deterministic maximal extension, as unordered pairs
function hypothesis_holds(w, f) {
  const ch = chords(f)
  for (let i = 0; i < ch.length; i++)
    for (let j = i + 1; j < ch.length; j++) {
      const [a, b] = ch[i], [c, d] = ch[j]
      if (Interleaved(w, a, b, c, d)) {
        const m1 = max_pair(w, a, b), m2 = max_pair(w, c, d)
        if (!(m1[0] === m2[0] && m1[1] === m2[1]) && !(m1[0] === m2[1] && m1[1] === m2[0]))
          return false
      }
    }
  return true
}

const has_crossing_pair = (w, f) => {
  const ch = chords(f)
  for (let i = 0; i < ch.length; i++)
    for (let j = i + 1; j < ch.length; j++) {
      const [a, b] = ch[i], [c, d] = ch[j]
      if (Interleaved(w, a, b, c, d)) return true
    }
  return false
}

// ------------------------------------------------------------------ the search

function* words(alphabet, n) {
  const idx = new Array(n).fill(0)
  for (;;) {
    yield idx
    let i = n - 1
    while (i >= 0) {
      idx[i]++
      if (idx[i] < alphabet) break
      idx[i] = 0
      i--
    }
    if (i < 0) return
  }
}

function run(alphabet, gmax) {
  const st = {
    traversals: 0, hyp: 0, hyp_nonvacuous: 0,
    counterexamples: [], conclusion_failures: [], single_chord: 0,
    single_chord_genuine: 0, by_chords: {},
  }
  for (let n = 2; n <= gmax; n++) {
    for (const idx of words(alphabet, n)) {
      const w = idx
      if (!is_primitive(w)) continue
      for (let L = 2; L <= n; L++) {
        if (!P2(w, L)) continue
        for (const f of involutions_preserving(w, L)) {
          if (support(f).length === 0 || !genuine(w, f)) continue
          st.traversals++
          const nc = chords(f).length
          st.by_chords[nc] = (st.by_chords[nc] || 0) + 1
          if (nc === 1) st.single_chord_genuine++
          const H = hypothesis_holds(w, f)
          if (H) st.hyp++
          if (H && has_crossing_pair(w, f)) st.hyp_nonvacuous++
          const C = vertex_cycle_is_rotation(w, L, f)
          if (!C) {
            const tag = [w.join(''), L, f.join(''), support(f).join('')]
            st.conclusion_failures.push(tag)
            if (H) st.counterexamples.push(tag)
          }
        }
      }
    }
    process.stdout.write('  ... G=' + n + ' done, ' + st.traversals + ' genuine traversals\n')
  }
  return st
}

for (const [alphabet, gmax] of [[2, BINMAX], [3, TRIMAX]]) {
  process.stdout.write('=== alphabet ' + alphabet + ', G <= ' + gmax + ', primitive + P2 ===\n')
  const s = run(alphabet, gmax)
  process.stdout.write('  genuine traversals, nontrivial support      : ' + s.traversals + '\n')
  process.stdout.write('  hypothesis of LadderVertexCycle holds       : ' + s.hyp + '\n')
  process.stdout.write('  ... of those, non-vacuously (a crossing pair): ' + s.hyp_nonvacuous + '\n')
  process.stdout.write('  genuine traversals with a single chord      : ' + s.single_chord_genuine + '\n')
  process.stdout.write('  conclusion VertexCycleEq failures           : ' + s.conclusion_failures.length + '\n')
  for (const t of s.conclusion_failures.slice(0, 5))
    process.stdout.write('      CONCLUSION FAILS: S=' + t[0] + ' L=' + t[1] + ' f=' + t[2] + ' supp=' + t[3] + '\n')
  process.stdout.write('  COUNTEREXAMPLES to LadderVertexCycle         : ' + s.counterexamples.length + '\n')
  for (const t of s.counterexamples.slice(0, 5))
    process.stdout.write('      COUNTEREXAMPLE: S=' + t[0] + ' L=' + t[1] + ' f=' + t[2] + ' supp=' + t[3] + '\n')
  process.stdout.write('  support-chord count histogram               : ' + JSON.stringify(s.by_chords) + '\n')
}
