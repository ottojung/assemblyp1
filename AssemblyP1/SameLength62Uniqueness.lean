import AssemblyP1.SameLength62TieUniqueness
import AssemblyP1.SameLength62Maximizer
import AssemblyP1.CycleSpellingRotation
import AssemblyP1.RepeatAdapter
import AssemblyP1.BridgingBridge

/-!
# #211: same-length §6.2 uniqueness up to rotation, closed without BBT

This module closes the uniqueness reading of the oriented same-length §6.2
maximizer statement under the source-faithful `I_s` assumptions, with **no**
external BBT / Eulerian-cycle-obstruction hypothesis. The route reuses the
existing periodic machinery (`RepeatAdapter`), the existing `I_s → no long
triple repeat` bridge (`BridgingBridge`), and the checked #243 rotation lemma
(`CycleSpellingRotation.isCyclicShift_of_isSimpleCycle_specCount`), and adds
one small glue lemma:

* **`IsPrimitive` conversion.** `PopulationReduction.IsPrimitive` (the
  power-form definition used by the #94 primitive route) and
  `RepeatAdapter.IsPrimitive` (the shift-invariance definition used by the
  periodic route) are bridged by `primitive_or_minimal_period`.

## The case split

`primitive_or_minimal_period` gives `IsPrimitive ∨ ∃ p, HasMinimalPeriod`.

* **Primitive.** `I_s → P2` (`informationFeasible_P2`) and the merged #94 route
  (`bbTP2Prim_of_94`) already give rotation
  (`unique_62_maximizer_up_to_rotation_of_primitive`, unchanged).

* **Non-primitive.** A minimal period `p` plus `¬ HasLongTripleRepeat` (from
  `BridgingBridge.informationFeasible_no_long_triple_repeat`) feeds
  `periodic_factor_distinct` and `periodic_cycle_shape`, yielding
  `IsSimpleCycle`. Combined with the spectrum equality that the §6.2 bridge
  provides (`oriented_support_eq_of_genuine62` + `Is_spectrum_eq_of_support_eq`),
  the #243 lemma `isCyclicShift_of_isSimpleCycle_specCount` gives rotation.

No hypothesis beyond `I_s` itself and the genuine §6.2 certificates is consumed.
-/

namespace AssemblyP1.SameLength62Uniqueness

open AssemblyP1.OrientedSameLengthML
open AssemblyP1.OrientedRigidity
open AssemblyP1.SourceFaithfulIs
open AssemblyP1.PopulationReduction

set_option maxHeartbeats 800000

noncomputable section

variable {α : Type} [DecidableEq α] [Fintype α]

/-! ## 1. `IsPrimitive` conversion -/

omit [DecidableEq α] [Fintype α] in
/-- **`RepeatAdapter.IsPrimitive` implies `PopulationReduction.IsPrimitive`.**
A shift-invariant word with shift `s` (`0 < s < G`) is a power-form repetition:
the minimal period divides `G` and is at most `s < G`. -/
theorem population_isPrimitive_of_repeatAdapter {G : ℕ} (hG : 0 < G)
    (S : Fin G → α) (hprim : AssemblyP1.RepeatAdapter.IsPrimitive hG S) :
    PopulationReduction.IsPrimitive S := by
  intro hcon
  obtain ⟨H, hH, U, q, hq1, hlen, hrep⟩ := hcon
  have hper : AssemblyP1.RepeatAdapter.IsPeriod hG S H := by
    intro i
    have e1 : S ⟨i % G, Nat.mod_lt _ hG⟩
        = U ⟨(i % G) % H, Nat.mod_lt _ hH⟩ := hrep ⟨i % G, Nat.mod_lt _ hG⟩
    have e2 : S ⟨(i + H) % G, Nat.mod_lt _ hG⟩
        = U ⟨((i + H) % G) % H, Nat.mod_lt _ hH⟩ :=
      hrep ⟨(i + H) % G, Nat.mod_lt _ hG⟩
    have hd : H ∣ G := ⟨q, hlen.symm⟩
    have hmod : (i + H) % G % H = i % G % H := by
      calc (i + H) % G % H = (i + H) % H := Nat.mod_mod_of_dvd _ hd
        _ = i % H := by simp
        _ = i % G % H := (Nat.mod_mod_of_dvd _ hd).symm
    have h1 : cyc hG S i = S ⟨i % G, Nat.mod_lt _ hG⟩ := rfl
    have h2 : cyc hG S (i + H) = S ⟨(i + H) % G, Nat.mod_lt _ hG⟩ := rfl
    calc cyc hG S i
        = S ⟨i % G, Nat.mod_lt _ hG⟩ := h1
      _ = U ⟨i % G % H, Nat.mod_lt _ hH⟩ := e1
      _ = U ⟨(i + H) % G % H, Nat.mod_lt _ hH⟩ := by
        apply congrArg U
        apply Fin.ext
        exact hmod.symm
      _ = S ⟨(i + H) % G, Nat.mod_lt _ hG⟩ := e2.symm
      _ = cyc hG S (i + H) := h2.symm
  have hHlt : H < G := by
    by_contra hc
    have hge : G ≤ H := by omega
    have hq2 : 2 ≤ q := by omega
    have h1 : 2 * G ≤ H * q := by nlinarith
    omega
  exact hprim H hH hHlt hper

/-! ## 2. The full uniqueness theorem -/

/-- **Same-length §6.2 uniqueness up to rotation under `I_s`.** Every genuine
same-length §6.2 candidate is a cyclic shift of the truth. The split is on
primitivity; the primitive subcase reuses the merged #94 route unchanged, and
the non-primitive subcase uses the periodic `IsSimpleCycle` route plus the
checked #243 rotation lemma. No `EulerianCycleObstruction` hypothesis.

Note: `hStruth` (the truth's genuine §6.2 certificate) is a nontrivial extra
hypothesis — it asserts the truth has complete observed support, which is not
automatic from `I_s` alone. -/
theorem unique_62_maximizer_up_to_rotation {G L n : ℕ} (hG : 0 < G)
    (hL2 : 2 ≤ L) (hLG : L ≤ G) (S : Fin G → α) (ρ : Realization G n)
    (hfeas : InformationFeasible ⟨G, hG, S⟩ L (realizedStarts ρ))
    {verts : List (Fin L → α)} {toList : (Fin L → α) → List α} {oMin : ℕ}
    (hStruth : SameLength62Maximizer.Is62Candidate62 ⟨G, hG, S⟩ verts toList
      (fun y => y) (fun y => y) oMin)
    (D : Fin G → α)
    (hD : SameLength62Maximizer.Is62Candidate62 ⟨G, hG, D⟩ verts toList
      (fun y => y) (fun y => y) oMin) :
    OrientedFinal.IsCyclicShift hG D S := by
  -- Spectrum equality from the §6.2 bridge.
  have hsup := SameLength62Maximizer.oriented_support_eq_of_genuine62 (L := L)
    (toList := toList) hStruth hD rfl
  have hspec : ∀ w : Fin L → α, OrientedRigidity.specCount (L := L) hG D w
      = OrientedRigidity.specCount (L := L) hG S w :=
    SameLength62TieUniqueness.Is_spectrum_eq_of_support_eq hG hL2 hLG S ρ hfeas D hsup
  -- Case split on primitivity.
  by_cases hprim : PopulationReduction.IsPrimitive S
  · exact SameLength62TieUniqueness.unique_62_maximizer_up_to_rotation_of_primitive
      hG hL2 hLG S hprim ρ hfeas hStruth D hD
  · -- Non-primitive: minimal period + IsSimpleCycle + #243 rotation.
    have hno : ¬ AssemblyP1.RepeatAdapter.HasLongTripleRepeat hG S L :=
      BridgingBridge.informationFeasible_no_long_triple_repeat hL2 hfeas
    have hprimRA : ¬ AssemblyP1.RepeatAdapter.IsPrimitive hG S := by
      intro hcon
      exact hprim (population_isPrimitive_of_repeatAdapter hG S hcon)
    rcases AssemblyP1.RepeatAdapter.primitive_or_minimal_period hG S with
      hprim' | ⟨p, hp⟩
    · exact absurd hprim' hprimRA
    · have hNwin : ∀ i j : ℕ, i < p → j < p →
          (∀ d : ℕ, d < L - 1 → OrientedRigidity.cyc hG S (i + d)
            = OrientedRigidity.cyc hG S (j + d)) → i = j :=
        AssemblyP1.RepeatAdapter.periodic_factor_distinct hG S p hL2 hp hno
      obtain ⟨hp0, hpG, hGp, hper, hsmall⟩ := hp
      have hcyc := AssemblyP1.RepeatAdapter.periodic_cycle_shape hG S p hp0
        (le_of_lt hpG) hper hNwin
      exact AssemblyP1.CycleSpellingRotation.isCyclicShift_of_isSimpleCycle_specCount
        hG hL2 S D hspec hcyc

end

#print axioms unique_62_maximizer_up_to_rotation

end AssemblyP1.SameLength62Uniqueness
