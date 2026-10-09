import AssemblyP1.SameLength62TieUniqueness
import AssemblyP1.SameLength62Maximizer
import AssemblyP1.SameLength62Nonprimitive
import AssemblyP1.RepeatAdapter
import AssemblyP1.BridgingBridge
import AssemblyP1.CycleSpellingRotation

/-!
# #211: same-length §6.2 uniqueness up to rotation, closed without BBT

This module closes the uniqueness reading of the oriented same-length §6.2
maximizer statement under the source-faithful `I_s` assumptions, with **no**
external BBT / Eulerian-cycle-obstruction hypothesis. The route reuses the
existing periodic machinery (`RepeatAdapter`) and the existing `I_s → no long
triple repeat` bridge (`BridgingBridge`), and consumes the #243 lemma
(`CycleSpellingRotation.isCyclicShift_of_isSimpleCycle_specCount`) for the
deterministic-continuation step.

## The case split

`primitive_or_minimal_period` gives `IsPrimitive ∨ ∃ p, HasMinimalPeriod`.

* **Primitive.** `I_s → P2` (`informationFeasible_P2`) and the merged #94 route
  (`bbTP2Prim_of_94`) already give rotation
  (`unique_62_maximizer_up_to_rotation_of_primitive`, unchanged).

* **Non-primitive.** A minimal period `p` plus `¬ HasLongTripleRepeat` (from
  `BridgingBridge.informationFeasible_no_long_triple_repeat`) feeds
  `periodic_factor_distinct` and `periodic_cycle_shape`, yielding
  `IsSimpleCycle`. The #243 lemma `isCyclicShift_of_isSimpleCycle_specCount`
  then converts `IsSimpleCycle` + spectrum equality directly into
  `IsCyclicShift`, with no separate NoBranching formalization.

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

/-- **`PopulationReduction.IsPrimitive` implies `RepeatAdapter.IsPrimitive`.**
A power-form non-repetition leaves no shift below `G` preserving the word:
the minimal period of a shift-invariant word divides `G` and is below `G`,
giving a power-form repetition. -/
theorem repeatAdapter_isPrimitive_of_population {G : ℕ} (hG : 0 < G)
    (S : Fin G → α) (hprim : PopulationReduction.IsPrimitive S) :
    AssemblyP1.RepeatAdapter.IsPrimitive hG S := by
  intro s hs0 hsG hshift
  -- `s` is a period below `G`; the minimal period is at most `s`, hence below
  -- `G`, and divides `G`, yielding a power-form repetition.
  have hper : AssemblyP1.RepeatAdapter.IsPeriod hG S s := hshift
  cases AssemblyP1.RepeatAdapter.primitive_or_minimal_period hG S with
  | inl hprim' => exact hprim' s hs0 hsG hshift
  | inr hmin =>
      obtain ⟨p, hp⟩ := hmin
      obtain ⟨hp0, hpG, hGp, hper_p, _⟩ := hp
      -- Build the power-form witness: `U` of length `p`, `q = G / p ≥ 2`.
      have hq : 2 ≤ G / p := by
        by_contra hc
        have hlt : G / p < 2 := by omega
        have hdecomp : G = p * (G / p) + G % p := (Nat.div_add_mod G p).symm
        rw [hGp] at hdecomp
        have key : ∀ k : ℕ, G = p * k → 2 ≤ k := by
          intro k hk
          by_contra hc
          have hkt : k < 2 := by omega
          interval_cases k
          · rw [Nat.mul_zero] at hk; omega
          · rw [Nat.mul_one] at hk; omega
        exact absurd (key (G / p) (by omega)) hc
      have hdvdp : p ∣ G := Nat.dvd_of_mod_eq_zero hGp
      obtain ⟨q, hq_eq⟩ := hdvdp
      have hq2 : 1 < q := by
        have htmp : G = p * (G / p) + G % p := (Nat.div_add_mod G p).symm
        rw [hGp] at htmp
        have hG0 : G = p * (G / p) := by omega
        have hpq : p * q = p * (G / p) := by
          rw [← hG0]
          exact hq_eq.symm
        have hmul : G / p * p = q * p := by
          rw [Nat.mul_comm (G / p) p, Nat.mul_comm q p]
          exact hpq.symm
        have hdiv : G / p = q := Nat.mul_right_cancel hp0 hmul
        omega
      -- `S` is `p`-periodic, so it is the `q`-th power of its length-`p` prefix.
      have hrep : ∀ i : Fin G,
          S i = (fun j : Fin p => S ⟨j.val, lt_trans j.isLt hpG⟩)
            ⟨i.val % p, Nat.mod_lt _ hp0⟩ := by
        intro i
        have hdecomp : i.val = i.val % p + p * (i.val / p) :=
          (Nat.mod_add_div i.val p).symm
        have key : ∀ q : ℕ, cyc hG S (i.val % p + p * q)
            = cyc hG S (i.val % p) := by
          intro q
          induction q with
          | zero => simp
          | succ n ih =>
            have h1 := hper_p (i.val % p + p * n)
            rw [Nat.mul_succ]
            have heq : i.val % p + (p * n + p) = (i.val % p + p * n) + p := by omega
            rw [heq]
            exact h1.symm.trans ih
        have hcyc : cyc hG S i.val = cyc hG S (i.val % p) :=
          (congrArg (cyc hG S) hdecomp).trans (key (i.val / p))
        have e : S i = cyc hG S i.val :=
          congrArg S (Fin.ext (Nat.mod_eq_of_lt i.isLt).symm)
        rw [e, hcyc]
        show S ⟨(i.val % p) % G, Nat.mod_lt _ hG⟩
            = S ⟨i.val % p, lt_trans (Nat.mod_lt _ hp0) hpG⟩
        have hmod : (i.val % p) % G = i.val % p :=
          Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ hp0) hpG)
        exact congrArg S (Fin.ext hmod)
      exact hprim ⟨p, hp0, (fun j : Fin p => S ⟨j.val, lt_trans j.isLt hpG⟩), q,
        hq2, hq_eq.symm, hrep⟩

/-- **`RepeatAdapter.IsPrimitive` implies `PopulationReduction.IsPrimitive`.**
A shift-invariant word with shift `s` (`0 < s < G`) is a power-form repetition:
the minimal period divides `G` and is at most `s < G`. -/
theorem population_isPrimitive_of_repeatAdapter {G : ℕ} (hG : 0 < G)
    (S : Fin G → α) (hprim : AssemblyP1.RepeatAdapter.IsPrimitive hG S) :
    PopulationReduction.IsPrimitive S := by
  intro hcon
  obtain ⟨H, hH, U, q, hq1, hlen, hrep⟩ := hcon
  -- `H` is a period below `G`, so shift-invariance holds.
  have hper : AssemblyP1.RepeatAdapter.IsPeriod hG S H := by
    intro i
    have e1 : S ⟨i % G, Nat.mod_lt _ hG⟩
        = U ⟨(i % G) % H, Nat.mod_lt _ hH⟩ := hrep ⟨i % G, Nat.mod_lt _ hG⟩
    have e2 : S ⟨(i + H) % G, Nat.mod_lt _ hG⟩
        = U ⟨((i + H) % G) % H, Nat.mod_lt _ hH⟩ :=
      hrep ⟨(i + H) % G, Nat.mod_lt _ hG⟩
    have hmod : (i + H) % G % H = i % G % H := by
      have hHG : H ∣ G := ⟨q, hlen.symm⟩
      have e1 : (i + H) % G % H = (i + H) % H := Nat.mod_mod_of_dvd _ hHG
      have e2 : (i + H) % H = i % H := by
        rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
      have e3 : i % G % H = i % H := Nat.mod_mod_of_dvd _ hHG
      rw [e1, e2, e3]
    show S ⟨i % G, Nat.mod_lt _ hG⟩ = S ⟨(i + H) % G, Nat.mod_lt _ hG⟩
    rw [e1, e2]
    exact congrArg U (Fin.ext hmod.symm)
  have hHlt : H < G := by
    by_contra hc
    have hge : G ≤ H := by omega
    have hq2 : 2 ≤ q := by omega
    have h1 : 2 * G ≤ H * q := by nlinarith
    omega
  exact hprim H hH hHlt hper

/-! ## 2. Rotation from `IsSimpleCycle` and spectrum equality

The deterministic-continuation argument is provided by the #243 lemma
`CycleSpellingRotation.isCyclicShift_of_isSimpleCycle_specCount`, which is
kernel-checked and imported here. No separate NoBranching formalization
is needed. -/

/-! ## 3. The full uniqueness theorem -/

/-- **Same-length §6.2 uniqueness up to rotation under `I_s`.** Every genuine
same-length §6.2 candidate is a cyclic shift of the truth. The split is on
primitivity; the primitive subcase reuses the merged #94 route unchanged, and
the non-primitive subcase uses the periodic `IsSimpleCycle` route plus
deterministic continuation. No `EulerianCycleObstruction` hypothesis. -/
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
  · -- Non-primitive: minimal period + IsSimpleCycle + rotation.
    have hno : ¬ AssemblyP1.RepeatAdapter.HasLongTripleRepeat hG S L :=
      BridgingBridge.informationFeasible_no_long_triple_repeat hL2 hfeas
    have hprimRA : ¬ AssemblyP1.RepeatAdapter.IsPrimitive hG S := by
      intro hcon
      exact hprim (population_isPrimitive_of_repeatAdapter hG S hcon)
    cases AssemblyP1.RepeatAdapter.primitive_or_minimal_period hG S with
    | inl hprim' => exact absurd hprim' hprimRA
    | inr hmin =>
        obtain ⟨p, hp⟩ := hmin
        obtain ⟨hp0, hpG, hGp, hper, hsmall⟩ := hp
        have hL2' : 2 ≤ L := hL2
        have hNwin : ∀ i j : ℕ, i < p → j < p →
            (∀ d : ℕ, d < L - 1 → OrientedRigidity.cyc hG S (i + d)
              = OrientedRigidity.cyc hG S (j + d)) → i = j :=
          AssemblyP1.RepeatAdapter.periodic_factor_distinct hG S p hL2' ⟨hp0, hpG, hGp, hper, hsmall⟩ hno
        have hcyc := AssemblyP1.RepeatAdapter.periodic_cycle_shape hG S p hp0
          (le_of_lt hpG) hper hNwin
        exact AssemblyP1.CycleSpellingRotation.isCyclicShift_of_isSimpleCycle_specCount
          hG hL2 S D hspec hcyc

end

end AssemblyP1.SameLength62Uniqueness
