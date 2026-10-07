import AssemblyP1.Issue94PhysicalChord
import AssemblyP1.Issue94ComponentResidual
import AssemblyP1.Issue94ComponentCoordinates
import AssemblyP1.Issue94ComponentCoboundary

/-!
# Board 94: the paired component antiderivative commutes with the residual

This module proves that the concrete interval-product antiderivative

  g = ∏_(p ∈ coordinatePairs (componentCoordinates hK S sigma c))
        intervalProd (alignedSwap hK ladderP ladderQ) p.1 (p.2 - p.1)

commutes pointwise with `componentResidual hK S sigma hEul hL hLK hprim hP2 c`:

  ∀ x, g (componentResidual ... x) = componentResidual ... (g x).

The proof is three steps:

1. **Local alignedSwap helper** (`alignedSwap_commute_componentResidual`):
   every factor `alignedSwap hK ladderP ladderQ i` swaps the aligned pair
   `rotAdd hK i ladderP`, `rotAdd hK i ladderQ`, which carries equal `(L-1)`-mers
   (`aligned_vtx_of_support_chord`).  Since `componentResidual` preserves `vtx`
   (`residual_preserves_vtx`), the doubled-fibre commutation
   `swap_commutes_of_vtx_eq` applies; when the two starts coincide the swap is
   the identity.

2. **intervalProd helper** (`intervalProd_commute_componentResidual`): a product
   of permutations each commuting with the residual commutes with the residual
   (`Commute.mul_right`).

3. **Main theorem** (`coordinatePairs_antiderivative_commute_componentResidual`):
   the ladder coordinates of a pair `p = (a, b)` are exactly the coordinates in
   `[a, b)`, all satisfying the support-chord bound
   (`componentCoordinate_mem_data`), so every factor of every interval product
   commutes with the residual; `Commute.list_prod_right` finishes.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`, and no
change to any existing definition.
-/

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace AssemblyP1.Issue94ComponentResidualCommute

open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.BBTLadder
open AssemblyP1.RepeatAdapter
open AssemblyP1.P2RepeatResidual
open AssemblyP1.Issue94Antiderivative
open AssemblyP1.Issue94IntervalCore
open AssemblyP1.Issue94AntiderivativeInterval
open AssemblyP1.Issue94LadderAligned
open AssemblyP1.Issue94P2DoubledPair
open AssemblyP1.Issue94EvenPairing
open AssemblyP1.Issue94ComponentResidual
open AssemblyP1.Issue94PhysicalChord
open AssemblyP1.Issue94ComponentCoordinates

variable {α : Type} [DecidableEq α] {K L : ℕ}

/-- **Local helper: one aligned swap commutes with the component residual.**

The aligned swap at ladder coordinate `i` exchanges the two aligned
maximal-extension starts `rotAdd hK i ladderP` and `rotAdd hK i ladderQ` of the
base chord `(c.1, AltF hK sigma c.1)`.  These two starts carry equal
`(L-1)`-mers (`aligned_vtx_of_support_chord`), and `componentResidual` preserves
`vtx` (`residual_preserves_vtx`), so the doubled-fibre commutation
`swap_commutes_of_vtx_eq` applies.  When the two starts coincide the swap is
the identity, which commutes with everything. -/
theorem alignedSwap_commute_componentResidual
    (hK : 0 < K) (hL : 2 ≤ L) (hLK : L ≤ K) (S : Fin K → α)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (sigma : Fin K ≃ Fin K) (hEul : EulerianCycle hK L S sigma)
    (c : AltFChord hK sigma) {i : ℕ}
    (hi : i + (L - 1) ≤ maxPairLen hK S c.1 (AltF hK sigma c.1)) :
    Commute (componentResidual hK S sigma hEul hL hLK hprim hP2 c)
      (alignedSwap hK (maxPairStart hK S c.1 (AltF hK sigma c.1))
        (maxPairStart hK S (AltF hK sigma c.1) c.1) i) := by
  have hvt : vtx hK L S (rotAdd hK i (maxPairStart hK S c.1 (AltF hK sigma c.1)))
      = vtx hK L S (rotAdd hK i (maxPairStart hK S (AltF hK sigma c.1) c.1)) :=
    aligned_vtx_of_support_chord hK hL hLK S hprim hP2 hEul
      (chord_ne_image hK sigma c) rfl hi
  have hres : ∀ x : Fin K,
      vtx hK L S (componentResidual hK S sigma hEul hL hLK hprim hP2 c x)
        = vtx hK L S x :=
    residual_preserves_vtx hK S sigma hEul hL hLK hprim hP2 c
  by_cases hne : rotAdd hK i (maxPairStart hK S c.1 (AltF hK sigma c.1))
      ≠ rotAdd hK i (maxPairStart hK S (AltF hK sigma c.1) c.1)
  · have ht := swap_commutes_of_vtx_eq hK S hL hLK hprim hP2 hne hvt
      (componentResidual hK S sigma hEul hL hLK hprim hP2 c) hres
    change
      componentResidual hK S sigma hEul hL hLK hprim hP2 c *
          alignedSwap hK (maxPairStart hK S c.1 (AltF hK sigma c.1))
            (maxPairStart hK S (AltF hK sigma c.1) c.1) i =
        alignedSwap hK (maxPairStart hK S c.1 (AltF hK sigma c.1))
            (maxPairStart hK S (AltF hK sigma c.1) c.1) i *
          componentResidual hK S sigma hEul hL hLK hprim hP2 c
    exact ht.symm
  · have heq : rotAdd hK i (maxPairStart hK S c.1 (AltF hK sigma c.1))
        = rotAdd hK i (maxPairStart hK S (AltF hK sigma c.1) c.1) :=
      not_ne_iff.mp hne
    have hsid : alignedSwap hK (maxPairStart hK S c.1 (AltF hK sigma c.1))
        (maxPairStart hK S (AltF hK sigma c.1) c.1) i = 1 := by
      ext x
      simp [alignedSwap, heq]
    rw [hsid]
    exact Commute.one_right _

/-- **intervalProd helper: an interval product of residual-commuting factors
commutes with the residual.** -/
theorem intervalProd_commute_componentResidual
    (hK : 0 < K) (hL : 2 ≤ L) (hLK : L ≤ K) (S : Fin K → α)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (sigma : Fin K ≃ Fin K) (hEul : EulerianCycle hK L S sigma)
    (c : AltFChord hK sigma) {a n : ℕ}
    (hcomm : ∀ i, a ≤ i → i < a + n →
      Commute (componentResidual hK S sigma hEul hL hLK hprim hP2 c)
        (alignedSwap hK (maxPairStart hK S c.1 (AltF hK sigma c.1))
          (maxPairStart hK S (AltF hK sigma c.1) c.1) i)) :
    Commute (componentResidual hK S sigma hEul hL hLK hprim hP2 c)
      (intervalProd (alignedSwap hK (maxPairStart hK S c.1 (AltF hK sigma c.1))
        (maxPairStart hK S (AltF hK sigma c.1) c.1)) a n) := by
  induction n generalizing a with
  | zero =>
      rw [intervalProd]
      exact Commute.one_right _
  | succ n ih =>
      rw [intervalProd]
      exact Commute.mul_right (hcomm a (by omega) (by omega))
        (ih (fun i hi1 hi2 => hcomm i (by omega) (by omega)))

/-- **The paired component antiderivative commutes pointwise with the residual.**

For the concrete interval-product antiderivative `g` built over
`coordinatePairs (componentCoordinates hK S sigma c)`, every factor is an
aligned swap at a ladder coordinate of the component, hence commutes with
`componentResidual` by `alignedSwap_commute_componentResidual`; therefore `g`
itself commutes with the residual, pointwise. -/
theorem coordinatePairs_antiderivative_commute_componentResidual
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : EulerianCycle hK L S sigma) (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (hUkk : Ukkonen hK L S) (c : AltFChord hK sigma) :
    ∀ x : Fin K,
      (((coordinatePairs (componentCoordinates hK S sigma c)).map
          (fun p => intervalProd (alignedSwap hK (maxPairStart hK S c.1 (AltF hK sigma c.1))
            (maxPairStart hK S (AltF hK sigma c.1) c.1)) p.1 (p.2 - p.1))).prod)
          (componentResidual hK S sigma hEul hL hLK hprim hP2 c x)
        = componentResidual hK S sigma hEul hL hLK hprim hP2 c
          (((coordinatePairs (componentCoordinates hK S sigma c)).map
              (fun p => intervalProd (alignedSwap hK (maxPairStart hK S c.1 (AltF hK sigma c.1))
                (maxPairStart hK S (AltF hK sigma c.1) c.1)) p.1 (p.2 - p.1))).prod x) := by
  intro x
  have hcomm : Commute (componentResidual hK S sigma hEul hL hLK hprim hP2 c)
      ((coordinatePairs (componentCoordinates hK S sigma c)).map
        (fun p => intervalProd (alignedSwap hK (maxPairStart hK S c.1 (AltF hK sigma c.1))
          (maxPairStart hK S (AltF hK sigma c.1) c.1)) p.1 (p.2 - p.1))).prod := by
    apply Commute.list_prod_right
    intro p hp
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    have hEven : Even (componentCoordinates hK S sigma c).card :=
      componentCoordinates_even hK hL hLK S hP2 hprim hUkk sigma hEul c
    have hq1 : q.1 ∈ componentCoordinates hK S sigma c :=
      coordinatePairs_fst_mem _ hEven hq
    have hq2 : q.2 ∈ componentCoordinates hK S sigma c :=
      coordinatePairs_snd_mem _ hEven hq
    have hle : q.1 ≤ q.2 := coordinatePairs_le _ q hq
    obtain ⟨hlen1, _⟩ :=
      componentCoordinate_mem_data hK hL hLK S hP2 hprim hUkk sigma hEul c hq1
    obtain ⟨hlen2, _⟩ :=
      componentCoordinate_mem_data hK hL hLK S hP2 hprim hUkk sigma hEul c hq2
    refine intervalProd_commute_componentResidual hK hL hLK S hprim hP2 sigma hEul c
      (a := q.1) (n := q.2 - q.1) ?_
    intro i hi1 hi2
    have hib : i + (L - 1) ≤ maxPairLen hK S c.1 (AltF hK sigma c.1) := by
      have hsum : q.1 + (q.2 - q.1) = q.2 := by omega
      omega
    exact alignedSwap_commute_componentResidual hK hL hLK S hprim hP2 sigma hEul c hib
  exact (congrArg (fun h => h x) hcomm.eq).symm

#print axioms AssemblyP1.Issue94ComponentResidualCommute.alignedSwap_commute_componentResidual
#print axioms AssemblyP1.Issue94ComponentResidualCommute.intervalProd_commute_componentResidual
#print axioms AssemblyP1.Issue94ComponentResidualCommute.coordinatePairs_antiderivative_commute_componentResidual

end AssemblyP1.Issue94ComponentResidualCommute
