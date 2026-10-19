# §6.2 read-window multiset bounds physical visits (#284)

This note records the **positive** half of the physical visit-count transport
question for the corrected §6.2 spelling-preserving transitive reduction. It
complements the negative diagnostic in
`docs/section62-visit-transport-284.md`, which showed that the invariant window
multiset does **not** determine the physical visit counts.

## The object

`AssemblyP1.Section62VisitTransport` proved that a spelling-preserving detour
preserves the *full* length-`L` window multiset of the spelled word, but not the
multiset of visited read molecules. This module,
`AssemblyP1.Section62VisitWindowBridge`, proves the exact *inequality* that
survives that failure.

A `GenuineWalk L vs ovs` is a list of length-`L` reads `vs = [v₀,…,vₙ₋₁]`
chained by genuine proper overlaps `ovs = [o₀,…,oₙ₋₂]`, `oᵢ < L`, where the
`oᵢ`-suffix of `vᵢ` is the `oᵢ`-prefix of `vᵢ₊₁`. This is the walk object
of `Section62VisitTransport.spellWalk`, with the overlap compatibility made
explicit.

## The transport bound

`genuineWalk_dominates` (kernel-checked): **for every genuine walk, the multiset
of visited read words is a sub-multiset of the length-`L` window multiset of the
spelled word.**

Equivalently, writing `throughputOf vs u` for the number of walk positions whose
read word is `u` and `windowCount L u w` for the length-`L` window multiplicity of
`u` in the word `w`:

```
throughputOf vs u  ≤  windowCount L u (spellWalk vs ovs)      (visitCount_le_windowCount)
```

The proof follows the reduction step: at each genuine overlap the tail spelling
is a suffix of the full spelling (`spellWalk_cons_drop`), so the tail's windows
are windows of the full spelling (`windows_spellWalk_cons`), and the only window
added is the offset-zero window, which is the head read. No visited read is ever
lost.

## Why this is the useful direction for §6.2

* `windowCount` is a function of the spelled word alone, hence invariant under any
  reduction that preserves the spelled word (`windowCount_congr`,
  `windowCount_detour_eq`). In particular it is invariant under the merged
  spelling-preserving §6.2 reduction
  (`Section62SpellingReductionCandidate.spellPath_eq_spellDirect`).
* `throughputOf` matches the §6.2 vertex-throughput count: it is the
  word-level form of `Section62Flow.Spelling.visits` (the latter counts cyclic
  positions through the molecule-class map `rep`), which MB09 Observation 7
  identifies with the number of times the read appears as a submolecule of the
  candidate. The kernel-checked bound is stated for the linear walk; the
  cyclic-candidate correspondence is the prose identification above, not a
  separately formalized theorem.

So the invariant window multiset is a computable, reduction-invariant **upper
bound** on the §6.2 throughput vector: the set of throughput vectors realizable
by spelling-preserving walks is contained in the box
`{ d | ∀ u, d u ≤ windowCount L u W }` defined by the spelled word `W`. The
negative diagnostic shows this box is not the exact feasible-throughput image.

## The bound is not tight

`witness_bound_strict` (kernel-checked, `L = 5`): the direct `1`-overlap walk
`sx → sy` with `sx = 01234`, `sy = 41200` spells `012341200`, whose length-`5`
windows are `{01234, 12341, 23412, 34120, 41200}`. The seam window `34120` has
window multiplicity `1` but is visited by no read (`throughputOf = 0`), so

```
throughputOf [sx, sy] 34120  =  0  <  1  =  windowCount 5 34120 (spellWalk [sx,sy] [1]).
```

The residual gap is exactly the unobserved seam windows. A faithful *equality*
transport would therefore need an extra source-model hypothesis designating which
windows of the spelled word are physically observed reads — the same missing
structure recorded in `docs/section62-visit-transport-284.md`.

## Scope

* `genuineWalk_dominates` / `visitCount_le_windowCount` are genuine,
  kernel-checked, self-contained (Lean core only) consequences of the walk
  hypothesis.
* `witness_bound_strict` is a genuine kernel-checked strictness witness.
* This module does **not** redefine `isReducibleB`, `transitivelyReduced`,
  `SpelledFeasible62`, or `StepsSurviveReduction`, does not reprove any merged
  §6.2 theorem, and does not touch the #261 ML-maximality classification or the
  #263 Graver scope.
* The exact ML likelihood transport to §6.2 feasible flows remains **OPEN**; this
  module bounds it from above by a reduction-invariant quantity.

## Verification

* `lean` compile of `AssemblyP1/Section62VisitWindowBridge.lean`: exit 0.
* `lake env leanchecker AssemblyP1.Section62VisitWindowBridge`: exit 0.
* Every `#print axioms` endpoint depends only on `{}` or
  `{propext, Classical.choice, Quot.sound}`; no `sorryAx`.
* `scripts/verify_284_visit_window_bridge.py`: exit 0.
