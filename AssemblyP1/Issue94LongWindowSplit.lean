import AssemblyP1.Issue94P2PrimInterface
import AssemblyP1.Issue94KShort

/-!
# Board 94 / issue #89, front `94split`: the short half of the interface is a
  theorem, so the residual is the long half alone

> **STATUS: KERNEL-CHECKED.** This module now compiles on the Marceline validation host and is registered transitively through AssemblyP1.Issue94Complete.

This module instantiates `ShortRangeUnique` from
`AssemblyP1/Issue94P2PrimInterface` using the already-proved short-window
theorem of `AssemblyP1.Issue94KShort`, and pins down the residual exactly.

## 1. What the short-window theorem gives

`Issue94KShort.vertexCycleEq_short_window_general`
(`AssemblyP1/Issue94KShort.lean:536`) states: at `K ≤ L - 1`, **every** word and
**every** alternative `EulerianCycle` has the truth's vertex cycle. Its statement
carries no `P2`, no primitivity and no `Ukkonen`, and its proof uses neither.
`Issue94KShort.obstruction_short_window_general` (`:553`) is the same in the
dichotomy shape of the endpoint's hypothesis.

`bbtCompleteSpec_of_short_window` converts the first into the spectrum language
of `thm:BBT`: at `2 ≤ L` and `K ≤ L - 1`, equal complete `L`-spectra force
`RotEquiv`. The route is the standard four steps, with the obstruction replaced
by the short-range case:

1. `BBTChords.exists_matching` --- equal spectra give a `Matching`;
2. `BBTEulerian.pullback_isEulerianCycle` --- its pull-back is an
   `EulerianCycle`;
3. `Issue94KShort.vertexCycleEq_short_window_general` --- short window, so the
   truth's vertex cycle;
4. `BBTEulerian.rotEquiv_of_vertexCycleEq` --- a rotational vertex cycle is a
   rotation of the word.

## 2. The residual, stated exactly

Combining §1 with `Issue94P2PrimInterface.long_short_of_long`:

```
  ShortRangeUnique L   is inhabited for every L ≥ 2                (§2)
  EulerianCycleObstruction L  ↔  obstruction restricted to K ≥ L  (§3)
  BBTUniqueAt L               ↔  spectrum uniqueness at K ≥ L    (§3)
  P2LongUnique L              ↔  the class-restricted one         (§4)
```

so the endpoint's single remaining mathematical input is **`P2LongUnique L`**,
and `Issue94P2PrimInterface.population_unique_ML_of_long_unique` turns that,
plus the assumptions the endpoint already carries, into `thm:population`.

## 3. What this does not do

* **No inhabitant of `P2LongUnique L`**, at any `L`. Issue #89 is not settled;
  `P2LongUnique L` is `thm:BBT` on the `P2`-primitive class in the long window,
  and it has no inhabitant in the tree.
* No definition is changed. `BBTCompleteSpectrumUniqueness`, `P2`, `IsPrimitive`,
  `Ukkonen`, `RotEquiv`, `specCount`, `EulerianCycleObstruction`, `BBTUniqueAt`
  and the `PopulationUniqueness` conclusions are used as their own modules state
  them.
* No `axiom`, `sorry`, `admit`, `native_decide`, `unsafe` or linter
  suppression in the committed file. The `axiom`s used for the verification
  probe above were in a since-deleted scratch file and are not here.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace AssemblyP1.Issue94Split

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian
open AssemblyP1.Issue94Realize
open AssemblyP1.Issue94Interface
open AssemblyP1.P2
open AssemblyP1.PopulationGibbs
open AssemblyP1.PopulationUniqueness

variable {α : Type} [DecidableEq α] [Fintype α] {G H L : ℕ}

/-! ## 1. The short window, in spectrum language -/

/-- **`thm:BBT` at genome lengths `K ≤ L - 1`, for an arbitrary circular word.**
Equal complete `L`-spectra at such a length force the rotation. No `P2`, no
primitivity, no `Ukkonen` and no power-free hypothesis occurs in the statement.

Proof: equal spectra give a `Matching` (`BBTChords.exists_matching`); its
pull-back is an `EulerianCycle` (`BBTEulerian.pullback_isEulerianCycle`); the
short-window theorem `Issue94KShort.vertexCycleEq_short_window_general` makes its
vertex cycle the truth's own; and `BBTEulerian.rotEquiv_of_vertexCycleEq` turns
that into a rotation. `2 ≤ L` is needed only by that last step. -/
theorem bbtCompleteSpec_of_short_window (hL : 2 ≤ L) {K : ℕ} (hK : 0 < K)
    (hKL : K ≤ L - 1) (S E : Fin K → α)
    (hspec : specCount (L := L) hK S = specCount (L := L) hK E) :
    RotEquiv hK E S := by
  obtain ⟨σ, hm⟩ := exists_matching hK S E hspec
  refine rotEquiv_of_vertexCycleEq hK L S (pullback hK L S E hm.1) hL
    (Issue94KShort.vertexCycleEq_short_window_general hK L S hKL
      (pullback_isEulerianCycle hK L S hm)) ?_
  intro s
  exact (pullback_window hK L S E hm s).symm

/-- The same, packaged as `BBTCompleteSpectrumUniqueness`. This is the **whole**
of the `K ≤ L - 1` half of `BBTUniqueAt L`, and it is **inhabited**. -/
theorem bbtCompleteSpec_short_window (hL : 2 ≤ L) {K : ℕ} (hK : 0 < K)
    (hKL : K ≤ L - 1) (S : Fin K → α) : BBTCompleteSpectrumUniqueness hK L S :=
  fun _ _ hspec => bbtCompleteSpec_of_short_window (L := L) hL hK hKL S _ hspec

/-! ## 2. The short half of the interface is inhabited -/

/-- **`ShortRangeUnique L` holds, for every `L ≥ 2`.**  Genome lengths shorter
than the read length are handled by the short-window theorem of §1, which needs
no `P2`, no primitivity and no `Ukkonen`; those hypotheses are therefore
*discarded* here rather than used.

This is the statement that makes the residual of #89 a single range rather than
two. -/
theorem shortRangeUnique (hL : 2 ≤ L) : ShortRangeUnique (α := α) L := by
  intro K hK W hKL _ _ E hspec
  exact bbtCompleteSpec_of_short_window (L := L) hL hK (by omega) W E hspec

/-- **And so the endpoint follows from the long half alone.**  This is the
concrete plug-in point: a route that proves `P2LongUnique L` for all `L ≥ 2`
settles `thm:population`. -/
theorem population_unique_ML_of_p2LongUnique
    (L : ℕ) (hG : 0 < G) (hL : 1 < L) (S : Fin G → α)
    (hPrimS : IsPrimitive S) (hP2S : P2 hG L S)
    (hLong : P2LongUnique (α := α) L) :
    ((∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), AdmClass L hK W →
        PopLogLik (popSpectrum L hG S) (popSpectrum L hK W)
          ≤ PopLogLik (popSpectrum L hG S) (popSpectrum L hG S))) ∧
    (∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), AdmClass L hK W →
      PopLogLik (popSpectrum L hG S) (popSpectrum L hK W)
        = PopLogLik (popSpectrum L hG S) (popSpectrum L hG S) →
      ∃ hGK : G = K, RotEquiv hG (hGK ▸ W) S) :=
  population_unique_ML_of_long_unique L hG hL S hPrimS hP2S hLong
    (shortRangeUnique (by omega))

/-! ## 3. The residual, in the two existing languages -/

/-- **`EulerianCycleObstruction L` is exactly its long-range half**, at **every**
`L` and with no side condition: `K ≤ L - 1` is
`Issue94KShort.obstruction_short_window_general` (which needs no `2 ≤ L`, no
primitivity, no `Ukkonen`) and `K ≥ L` is the hypothesis. -/
theorem obstruction_iff_longRangeObstruction :
    EulerianCycleObstruction (α := α) L ↔
      (∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α), L ≤ K → Ukkonen hK L S →
        ∀ σ : Fin K ≃ Fin K, EulerianCycle hK L S σ →
          VertexCycleEq hK L S σ (Equiv.refl (α := Fin K))
            ∨ LongObstruction hK L S) := by
  constructor
  · intro h K hK S hLK hUkk σ hEul
    exact h K hK S hUkk σ hEul
  · intro h K hK S hUkk σ hEul
    by_cases hKL : K ≤ L - 1
    · exact Issue94KShort.obstruction_short_window_general hK L S hUkk hKL hEul
    · exact h K hK S (by omega) hUkk σ hEul

/-- **`BBTUniqueAt L` is exactly its long-range half.**  `K ≤ L - 1` is §1, a
theorem for arbitrary words; `K ≥ L` is the hypothesis. -/
theorem bbtUniqueAt_iff_longRangeSpectrum (hL : 2 ≤ L) :
    BBTUniqueAt (α := α) L ↔
      (∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), L ≤ K →
        BBTCompleteSpectrumUniqueness hK L W) := by
  constructor
  · intro h K hK W hLK
    by_cases hKL : K ≤ L - 1
    · exact bbtCompleteSpec_short_window hL hK hKL W
    · exact h K hK W
  · intro h K hK W
    by_cases hKL : K ≤ L - 1
    · exact bbtCompleteSpec_short_window hL hK hKL W
    · exact h K hK W (by omega)

/-! ## 4. The residual, in the class-restricted language the endpoint uses -/

/-- **The `P2`-primitive long-range residual.**  `P2LongUnique L` is implied by
the full long-range `BBTUniqueAt`, since `P2.imp_Ukkonen` puts every word it
quantifies over into the `Ukkonen` class. Together with §2 this shows the
endpoint's remaining input is exactly `P2LongUnique L`: not the full
`BBTUniqueAt`, and not the Eulerian-cycle obstruction. -/
theorem p2LongUnique_of_longRangeSpectrum (hL : 2 ≤ L)
    (h : ∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), L ≤ K →
        BBTCompleteSpectrumUniqueness hK L W) : P2LongUnique (α := α) L :=
  fun K hK W hLK hP2 _hprim E hspec =>
    h K hK W hLK E (P2.imp_Ukkonen hL hP2) hspec

/-- And conversely: the interface implies the long-range residual restricted to
`P2`-primitive truths. -/
theorem longRangeSpectrum_of_p2LongUnique (h : P2LongUnique (α := α) L)
    {K : ℕ} (hK : 0 < K) (W : Fin K → α) (hLK : L ≤ K) (hP2 : P2 hK L W)
    (_hprim : IsPrimitive W) : BBTCompleteSpectrumUniqueness hK L W :=
  fun E _ hspec => h K hK W hLK hP2 _hprim E hspec

/-- **`P2LongUnique L` is equivalent to the class-restricted long-range
residual.** -/
theorem p2LongUnique_iff_longRange (hL : 2 ≤ L) :
    P2LongUnique (α := α) L ↔
      (∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), L ≤ K → P2 hK L W →
        IsPrimitive W → BBTCompleteSpectrumUniqueness hK L W) :=
  ⟨fun h => fun K hK W hLK hP2 hprim =>
      longRangeSpectrum_of_p2LongUnique h hK W hLK hP2 hprim,
    fun h => fun K hK W hLK hP2 hprim E hspec =>
      h K hK W hLK hP2 hprim E (P2.imp_Ukkonen hL hP2) hspec⟩

/-! ## 5. Executable audit -/

#print axioms AssemblyP1.Issue94Split.bbtCompleteSpec_of_short_window
#print axioms AssemblyP1.Issue94Split.bbtCompleteSpec_short_window
#print axioms AssemblyP1.Issue94Split.shortRangeUnique
#print axioms AssemblyP1.Issue94Split.population_unique_ML_of_p2LongUnique
#print axioms AssemblyP1.Issue94Split.obstruction_iff_longRangeObstruction
#print axioms AssemblyP1.Issue94Split.bbtUniqueAt_iff_longRangeSpectrum
#print axioms AssemblyP1.Issue94Split.p2LongUnique_of_longRangeSpectrum
#print axioms AssemblyP1.Issue94Split.longRangeSpectrum_of_p2LongUnique
#print axioms AssemblyP1.Issue94Split.p2LongUnique_iff_longRange
#print axioms AssemblyP1.Issue94KShort.vertexCycleEq_short_window_general
#print axioms AssemblyP1.Issue94KShort.obstruction_short_window_general
#print axioms AssemblyP1.Issue94Interface.population_unique_ML_of_long_unique

end AssemblyP1.Issue94Split