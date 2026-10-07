import AssemblyP1.Issue94OrbitSearch

/-!
# Board 94: `IterStep4` holds outright, for every `K`

This module replaces the bounded `by decide` checks of `IterStep4 5 .. 8`
(`Issue94OrbitCheck5` .. `Issue94OrbitCheck8`) with a general proof.

## The observation

`IterStep4 K` (in `Issue94OrbitSearch`:189) is stated with the shift bound
`ti.val ≤ pairBackC hK S c.val d.val` and **no primitivity hypothesis**.
On a non-primitive circle `pairBack` is large, but that is harmless here,
because `pairBackC` is a maximum over

```lean
backSetC hK S a b = Finset.filter (backAgreeC hK S a b) (Finset.range (K + 1))
```

(`Issue94OrbitSearch`:76), so `pairBackC hK S a b ≤ K` **unconditionally** --- it is a
bound of the definition, not a theorem about primitive circles.  Hence
`ti.val ≤ pairBackC hK S c.val d.val ≤ K`, which is exactly the hypothesis
`slide_iter` (`Issue94IterSlide`:367) and its word-level form
`step4_slide_iterates_word` (`Issue94IterSlide`:440) need: `t ≤ K`.

So `IterStep4 K` is an immediate consequence of the already-proved iterated
slide, for **every** `K`, with no finite search and no kernel decision
procedure at all.

## Why the `decide` version was the wrong instrument

`decide` on `IterStep4 K` enumerates all `2^K` genomes and, for each, runs the
`pairBackC` filter, and then the compiler's export step dominates.  It reached
the host's 30.0 GiB cgroup ceiling at `K = 5` (exit 137, twice; see
`/workspace/board94-iterated-slide-c1.md`).  That cost bought nothing: the
statement was true at every `K` all along, provable by a term that is a few
lines long and elaborates in milliseconds.

This is a strengthening, not a weakening, and it should be read as such:

* the general theorem here covers **all** `K`, where the `decide` checks
  covered `K ≤ 4` and could not be pushed past `4`;
* it drops no hypothesis of `IterStep4` --- it is the very same `Prop`;
* and it still certifies `Issue89GapMap.Step4_slide_iterates` (`:443`) in the
  sense the old file claimed, because `IterStep4` was already *stronger* than
  that library `Prop` (it drops the two `vtx` hypotheses, which do not occur
  in the conclusion).

## What is still NOT established

This settles `IterStep4` only.  It does **not** produce an inhabitant of
`Issue89GapMap.Step4_slide_iterates` itself, for two reasons that remain
genuinely open and are not touched here:

1. that `Prop` is quantified over `L` and carries the two `vtx` ("still a
   chord") hypotheses, which `IterStep4` drops; and
2. its shift bound is `t ≤ pairBack hK S c.val d.val` against the library's
   `noncomputable` `pairBack`, and the unconditional `pairBack ≤ K` used
   above is available only for the computable restatement `pairBackC`.  For
   the library `pairBack` the bound `pairBack < K` does exist
   (`P2RepeatResidual.pairBack_lt_G`:654) but it is stated **under
   `IsPrimitive`**, and closing that gap under the `P2` hypotheses is real
   work that this module does not do.
-/

namespace AssemblyP1.Issue94OrbitGeneral

open AssemblyP1
open AssemblyP1.PopulationReduction
open AssemblyP1.SourceFaithfulIs
open AssemblyP1.P2RepeatResidual
open AssemblyP1.BBTChords
open AssemblyP1.Issue89GapMap
open AssemblyP1.Issue94IterSlide
open AssemblyP1.Issue94OrbitSearch

variable {K : ℕ}

/-- **`pairBackC` never exceeds the circle size.**  This is a bound of the
definition: `backSetC` is a `filter` of `Finset.range (K + 1)`, so every
element of the set whose `max'` is taken is at most `K`.  It is *unconditional*
--- no primitivity, no `P2` --- and that is precisely why `IterStep4` is
easier than `Step4_slide_iterates`. -/
theorem pairBackC_le_K (hK : 0 < K) (S : Fin K → Bin) (a b : ℕ) :
    pairBackC hK S a b ≤ K := by
  unfold pairBackC
  refine Finset.max'_le _ _ K ?_
  intro y hy
  obtain ⟨hy1, _⟩ := Finset.mem_filter.mp hy
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hy1)

/-- A guard hypothesis quantified over `Fin (K+1)` is as strong as one
quantified over `ℕ`, given the bound `t ≤ K`.  Every `j ≤ t ≤ K` lies in
`range (K+1)`, and `j % (K + 1) = j` there. -/
theorem slideGuards_of_fin (hK : 0 < K) (a b c d : Fin K) {t : ℕ} (ht : t ≤ K)
    (hg : ∀ j : Fin (K + 1), j.val ≤ t → SlideGuards hK a b c d j.val) :
    ∀ j : ℕ, j ≤ t → SlideGuards hK a b c d j := by
  intro j hj
  have hjK : j < K + 1 := by omega
  have hmod : j % (K + 1) = j := Nat.mod_eq_of_lt hjK
  have hmlt : j % (K + 1) < K + 1 := Nat.mod_lt _ (by omega)
  have hval : (⟨j % (K + 1), hmlt⟩ : Fin (K + 1)).val = j := by simp [hmod]
  have hgot : SlideGuards hK a b c d (⟨j % (K + 1), hmlt⟩ : Fin (K + 1)).val :=
    hg _ (by simpa [hval, hmod] using hj)
  simpa [hval, hmod] using hgot

/-- **The headline.  `IterStep4` holds, for every circle size `K`, with no
finite search.**  This is the statement `Issue94OrbitSearch.IterStep4`, unchanged
and unweakened; it was previously only ever `decide`-checked at `K = 3, 4`.

The proof is `step4_slide_iterates_word` instantiated at `t = ti.val`: the
shift bound `ti.val ≤ pairBackC hK S c.val d.val` combined with
`pairBackC_le_K` gives the `t ≤ K` that the proved iterated slide requires,
and `slideGuards_of_fin` bridges the two ways of quantifying the guard. -/
theorem IterStep4_all (K : ℕ) (hK : 0 < K) [NeZero K] : IterStep4 K hK := by
  intro S a b c d Li ti hab hcd hLi hL hI hti hg
  have htK : ti.val ≤ K := le_trans hti (pairBackC_le_K hK S c.val d.val)
  have hres : Interleaved (mkGenome hK S) a b
      (rotAdd hK (K - ti.val) c) (rotAdd hK (K - ti.val) d) :=
    step4_slide_iterates_word hK a b c d
      ((interleaved_iff hK a b c d).mpr hI) ti.val htK
      (slideGuards_of_fin hK a b c d htK hg)
  exact (interleaved_iff hK a b (rotAdd hK (K - ti.val) c)
    (rotAdd hK (K - ti.val) d)).mp hres

end AssemblyP1.Issue94OrbitGeneral
