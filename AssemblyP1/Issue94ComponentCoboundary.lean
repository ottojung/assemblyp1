import AssemblyP1.Issue94CommutatorProduct
import AssemblyP1.Issue94AntiderivativeInterval
import AssemblyP1.Issue94EvenPairing

/-!
# Board 94: coboundary product over the paired component intervals

This module is the concrete paired-interval wrapper over the generic
`Issue94CommutatorProduct.coboundary_prod_pairs`.  For a component coordinate
set `B` (the sorted chord coordinates of one interlace component), the
intervals are the consecutive pairs of `coordinatePairs B`.  Each pair
`p = (a, b)` carries

* the **antiderivative** `g_p = intervalProd (alignedSwap hK ladderP ladderQ) a (b - a)`
  over the interval `[a, b)`, and
* the **boundary** `c_p = alignedSwap hK ladderP ladderQ a * alignedSwap hK ladderQ b`
  (the two endpoint swaps),

where `ladderP, ladderQ` are the maximal-extension starts of the base chord
`(u, v)`.

The per-pair coboundary equation is `aligned_interval_commutator`; the
triangular boundary-vs-later-antiderivative commutation is
`alignedSwaps_commute_of_support_chord` (factors commute) composed with
`commute_intervalProd_mem` (a factor commutes with a later interval product).
The conclusion is the exact coboundary product over all paired intervals:

`coboundary (rhoEquiv hK) (∏ g_p) = ∏ c_p`.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`, and no
change to any existing definition.
-/

set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace AssemblyP1.Issue94ComponentCoboundary

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
open AssemblyP1.Issue94CommutatorProduct
open AssemblyP1.Issue94EvenPairing

variable {α : Type} [DecidableEq α] {K L : ℕ}

/-- **The coboundary product over the paired component intervals.**

For a component coordinate set `B` whose points all lie in the ladder range
of the base chord `(u, v)`, the coboundary of the product of the interval
antiderivatives `g_p = intervalProd (alignedSwap hK ladderP ladderQ) a (b - a)`
over the consecutive pairs `p = (a, b)` of `coordinatePairs B` is exactly the
product of the boundary swap pairs `c_p = alignedSwap hK ladderP ladderQ a *
alignedSwap hK ladderP ladderQ b`:

`coboundary (rhoEquiv hK) (∏_(p ∈ coordinatePairs B) g_p) = ∏_(p ∈ coordinatePairs B) c_p`.

This is `Issue94CommutatorProduct.coboundary_prod_pairs` instantiated with the
aligned-swap antiderivatives and boundaries; the per-pair coboundary equation
is `aligned_interval_commutator` and the triangular commutation is
`alignedSwaps_commute_of_support_chord` composed with `commute_intervalProd_mem`.
-/
theorem coordinatePairs_coboundary_prod
    (hK : 0 < K) (hL : 2 ≤ L) (hLK : L ≤ K) (S : Fin K → α)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (σ : Fin K ≃ Fin K) (hEul : EulerianCycle hK L S σ)
    (u v : Fin K) (huv : u ≠ v) (hfx : AltF hK σ u = v)
    (B : Finset ℕ) (hEven : Even B.card)
    (hB : ∀ x ∈ B, x + (L - 1) ≤ maxPairLen hK S u v) :
    coboundary (rhoEquiv hK)
        ((coordinatePairs B).map
          (fun p => intervalProd (alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u))
            p.1 (p.2 - p.1))).prod
      = ((coordinatePairs B).map
          (fun p => alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u) p.1
            * alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u) p.2)).prod := by
  have hcomm_factors : ∀ i j : ℕ, i + (L - 1) ≤ maxPairLen hK S u v →
      j + (L - 1) ≤ maxPairLen hK S u v →
      Commute (alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u) i)
        (alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u) j) := by
    intro i j hi hj
    exact alignedSwaps_commute_of_support_chord hK hL hLK S hprim hP2 hEul huv hfx hi hj
  have hcom : ∀ p ∈ (coordinatePairs B).map
      (fun p => (intervalProd (alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u))
          p.1 (p.2 - p.1),
        alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u) p.1
          * alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u) p.2)),
      coboundary (rhoEquiv hK) p.1 = p.2 := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    have hle : q.1 ≤ q.2 := coordinatePairs_le B q hq
    have hvalid : q.1 + (q.2 - q.1) + (L - 1) ≤ maxPairLen hK S u v :=
      coordinatePair_interval_valid B hEven hq hB
    have hcomm_q : (intervalProd (alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u))
          q.1 (q.2 - q.1))⁻¹ * rhoEquiv hK *
        intervalProd (alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u))
          q.1 (q.2 - q.1) * (rhoEquiv hK)⁻¹
        = alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u) q.1
          * alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u) q.2 := by
      have h := aligned_interval_commutator hK hL hLK S hprim hP2 hEul huv hfx hvalid
      rw [show q.1 + (q.2 - q.1) = q.2 from by omega] at h
      exact h
    unfold coboundary
    exact hcomm_q
  have hpw : List.Pairwise (fun p q => Commute p.2 q.1)
      ((coordinatePairs B).map
        (fun p => (intervalProd (alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u))
            p.1 (p.2 - p.1),
          alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u) p.1
            * alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u) p.2))) := by
    rw [List.pairwise_map]
    show (coordinatePairs B).Pairwise
      (fun x y => Commute (alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u) x.1
        * alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u) x.2)
        (intervalProd (alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u)) y.1 (y.2 - y.1)))
    rw [List.pairwise_iff_get]
    intro i j hij
    set x : ℕ × ℕ := (coordinatePairs B).get i with hx
    set y : ℕ × ℕ := (coordinatePairs B).get j with hy
    have hxi : x ∈ coordinatePairs B := by rw [hx]; exact List.get_mem _ _
    have hxj : y ∈ coordinatePairs B := by rw [hy]; exact List.get_mem _ _
    have hle : x.1 ≤ x.2 := coordinatePairs_le B x hxi
    have hle' : y.1 ≤ y.2 := coordinatePairs_le B y hxj
    have ha : x.1 ∈ B := coordinatePairs_fst_mem B hEven hxi
    have hb : x.2 ∈ B := coordinatePairs_snd_mem B hEven hxi
    have ha' : y.1 ∈ B := coordinatePairs_fst_mem B hEven hxj
    have hb' : y.2 ∈ B := coordinatePairs_snd_mem B hEven hxj
    have hca : Commute (alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u) x.1)
        (intervalProd (alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u)) y.1 (y.2 - y.1)) := by
      apply commute_intervalProd_mem (k := x.1) (a := y.1) (n := y.2 - y.1)
      intro k hk1 hk2
      apply hcomm_factors x.1 k (hB x.1 ha)
      have hkeq : y.1 + (y.2 - y.1) = y.2 := by omega
      have hb'2 := hB y.2 hb'
      omega
    have hcb : Commute (alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u) x.2)
        (intervalProd (alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u)) y.1 (y.2 - y.1)) := by
      apply commute_intervalProd_mem (k := x.2) (a := y.1) (n := y.2 - y.1)
      intro k hk1 hk2
      apply hcomm_factors x.2 k (hB x.2 hb)
      have hkeq : y.1 + (y.2 - y.1) = y.2 := by omega
      have hb'2 := hB y.2 hb'
      omega
    exact Commute.mul_left hca hcb
  have hfst : ((coordinatePairs B).map
        (fun p => (intervalProd (alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u))
            p.1 (p.2 - p.1),
          alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u) p.1
            * alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u) p.2))).map Prod.fst
      = (coordinatePairs B).map
          (fun p => intervalProd (alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u))
            p.1 (p.2 - p.1)) := by
    rw [List.map_map]
    rfl
  have hsnd : ((coordinatePairs B).map
        (fun p => (intervalProd (alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u))
            p.1 (p.2 - p.1),
          alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u) p.1
            * alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u) p.2))).map Prod.snd
      = (coordinatePairs B).map
          (fun p => alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u) p.1
            * alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u) p.2) := by
    rw [List.map_map]
    rfl
  rw [← hfst, ← hsnd]
  exact coboundary_prod_pairs (rhoEquiv hK)
    ((coordinatePairs B).map
      (fun p => (intervalProd (alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u))
          p.1 (p.2 - p.1),
        alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u) p.1
          * alignedSwap hK (maxPairStart hK S u v) (maxPairStart hK S v u) p.2))) hcom hpw

#print axioms AssemblyP1.Issue94ComponentCoboundary.coordinatePairs_coboundary_prod

end AssemblyP1.Issue94ComponentCoboundary
