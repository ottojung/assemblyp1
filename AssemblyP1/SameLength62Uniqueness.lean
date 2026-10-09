import AssemblyP1.SameLength62TieUniqueness
import AssemblyP1.SameLength62Maximizer
import AssemblyP1.RepeatAdapter
import AssemblyP1.BridgingBridge

/-!
# #211: same-length §6.2 uniqueness up to rotation, closed without BBT

This module closes the uniqueness reading of the oriented same-length §6.2
maximizer statement under the source-faithful `I_s` assumptions, with **no**
external BBT / Eulerian-cycle-obstruction hypothesis. The route reuses the
existing periodic machinery (`RepeatAdapter`) and the existing `I_s → no long
triple repeat` bridge (`BridgingBridge`), and adds two small glue lemmas:

1. **`IsPrimitive` conversion.** `PopulationReduction.IsPrimitive` (the
   power-form definition used by the #94 primitive route) and
   `RepeatAdapter.IsPrimitive` (the shift-invariance definition used by the
   periodic route) are bridged by `primitive_or_minimal_period`.

2. **`IsSimpleCycle + spectrum equality → rotation`.** A truth whose window
   support is a simple directed cycle has a deterministic next-`L`-mer
   successor; an equal-spectrum candidate is then recovered by deterministic
   continuation, with no BEST/BBT input.

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
  the deterministic-continuation lemma below gives rotation.

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
  rcases AssemblyP1.RepeatAdapter.primitive_or_minimal_period hG S with
    | inl hprim' => exact hprim' s hs0 hsG hshift
    | inr hmin =>
      obtain ⟨p, hp⟩ := hmin
      obtain ⟨hp0, hpG, hGp, hper_p, _⟩ := hp
      -- Build the power-form witness: `U` of length `p`, `q = G / p ≥ 2`.
      have hq : 2 ≤ G / p := by
        by_contra hc
        have hlt : G / p < 2 := by omega
        interval_cases G / p
        · rw [Nat.mul_zero, Nat.mod_eq_of_lt hpG] at hGp
          omega
        · rw [Nat.mul_one] at hGp
          omega
      have hdvdp : p ∣ G := Nat.dvd_of_mod_eq_zero hGp
      obtain ⟨q, hq_eq⟩ := hdvdp
      have hq2 : 1 < q := by
        rw [← hq_eq]
        exact hq
      -- `S` is `p`-periodic, so it is the `q`-th power of its length-`p` prefix.
      have hrep : ∀ i : Fin G,
          S i = (fun j : Fin p => S ⟨j.val, Nat.mod_lt _ hp0⟩)
            ⟨i.val % p, Nat.mod_lt _ hp0⟩ := by
        intro i
        have hcyc : cyc hG S i.val = cyc hG S (i.val % p) := by
          apply AssemblyP1.RepeatAdapter.cyc_residue_add hG S p hp0
            (le_of_lt hpG) hper_p
        have e : S i = cyc hG S i.val := rfl
        rw [e, hcyc]
        rfl
      exact hprim ⟨p, hp0, (fun j : Fin p => S ⟨j.val, Nat.mod_lt _ hp0⟩), q,
        hq2, hq_eq, hrep⟩

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
      rw [Nat.mod_mod_of_dvd _ ⟨q, hlen.symm⟩]
    rw [e1, e2, hmod]
  have hHlt : H < G := by
    by_contra hc
    have hge : G ≤ H := by omega
    have hq2 : 2 ≤ q := by omega
    have h1 : 2 * G ≤ H * q := by nlinarith
    omega
  exact hprim H hH hHlt hper

/-! ## 2. `IsSimpleCycle + spectrum equality → rotation` -/

/-- **NoBranching from the simple-cycle shape.** A unique outgoing edge per
node makes the `(L-1)`-mer determine its follower. -/
theorem noBranching_of_isSimpleCycle {G L : ℕ} (hG : 0 < G) (S : Fin G → α)
    (hcyc : AssemblyP1.RepeatAdapter.IsSimpleCycle L hG S) :
    AssemblyP1.SameLength62Nonprimitive.NoBranching (L := L) hG S := by
  intro i j hwin
  -- `winPrefix (window i) = nodeWindow i`, and both `window i`, `window j`
  -- are support members with the same prefix, so the unique-outedge property
  -- identifies them.
  have hpre_i : winPrefix (window hG S i) = nodeWindow hG S i := rfl
  have hpre_j : winPrefix (window hG S j) = nodeWindow hG S j := rfl
  have hmem_i : window hG S i ∈ support hG S :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hmem_j : window hG S j ∈ support hG S :=
    Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hnode_i : nodeWindow hG S i ∈ genomeNodes hG S :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hnode_j : nodeWindow hG S j ∈ genomeNodes hG S :=
    Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hpre_eq : winPrefix (window hG S i) = winPrefix (window hG S j) := by
    rw [hpre_i, hpre_j, hwin]
  have hEq : window hG S i = window hG S j := by
    have hui := hcyc.1 (nodeWindow hG S i) hnode_i
    have huj := hcyc.1 (nodeWindow hG S j) hnode_j
    have key : window hG S i = window hG S j := by
      by_contra hne
      have hne2 : nodeWindow hG S i ≠ nodeWindow hG S j := by
        intro hcon
        rw [hpre_i, hpre_j, hcon] at hpre_eq
        exact hpre_eq rfl
      -- Both are out-edges of the same node, contradicting uniqueness.
      have hmem2_i : window hG S i ∈ support hG S ∧
          winPrefix (window hG S i) = nodeWindow hG S j := ⟨hmem_i, by
        rw [hpre_i]; exact hwin.symm⟩
      have hmem2_j : window hG S j ∈ support hG S ∧
          winPrefix (window hG S j) = nodeWindow hG S j := ⟨hmem_j, hpre_j⟩
      rcases huj with ⟨w, ⟨hwS, hwpre⟩, huniq⟩
      have hEq' : window hG S i = w := huniq _ hmem2_i
      have hEq'' : window hG S j = w := huniq _ hmem2_j
      rw [hEq', hEq''] at hne
      exact hne rfl
    exact key
  -- Equal `L`-windows have equal followers.
  have hfol : cyc hG S (i.val + L - 1) = cyc hG S (j.val + L - 1) := by
    have := congrFun hEq ⟨L - 1, by have := (⟨L - 1, by omega⟩ : Fin L).isLt;
      omega⟩
    exact this
  exact hfol

/-- **Deterministic continuation.** Under `NoBranching`, a same-spectrum
candidate `D` is recovered symbol-by-symbol by following the truth's unique
successors. The induction proves `cyc D (t + d) = cyc S (j + t + d)` for all
`t < G` and `d < L - 1`, where `j` is a start of `S` spelling `D`'s initial
`L`-mer. -/
theorem spectrum_eq_of_noBranching {G L : ℕ} (hG : 0 < G) (hL2 : 2 ≤ L)
    (S D : Fin G → α)
    (hnb : AssemblyP1.SameLength62Nonprimitive.NoBranching (L := L) hG S)
    (hspec : ∀ w : Fin L → α, specCount (L := L) hG D w
      = specCount (L := L) hG S w) :
    AssemblyP1.PopulationReduction.RotEquiv hG D S := by
  -- Pick `j` spelling `D`'s initial `L`-mer (spectra agree, so it occurs in `S`).
  have hD0 : 0 < specCount (L := L) hG D (window hG D ⟨0, hG⟩) :=
    by
      have hmem : (⟨0, hG⟩ : Fin G) ∈ Finset.univ.filter
          (fun r : Fin G => window hG D r = window hG D ⟨0, hG⟩) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
      have := Finset.card_pos.mpr ⟨⟨0, hG⟩, hmem⟩
      exact this
  have hS0 : 0 < specCount (L := L) hG S (window hG D ⟨0, hG⟩) := by
    rw [hspec (window hG D ⟨0, hG⟩)]
    exact hD0
  have hS0mem : window hG D ⟨0, hG⟩ ∈ support hG S := by
    rw [(OrientedSameLengthML.specCount_pos_iff hG (window hG D ⟨0, hG⟩)).symm]
    exact hS0
  obtain ⟨j, -, hjwindow⟩ := hS0mem
  -- Induction on `t < G`: `∀ d < L-1, cyc D (t+d) = cyc S (j.val + t + d)`.
  have key : ∀ t : ℕ, t < G → ∀ d : ℕ, d < L - 1 →
      cyc hG D (t + d) = cyc hG S (j.val + t + d) := by
    intro t
    induction t with
    | zero =>
        intro d hd
        -- Base: the initial `L`-mers agree, so their length-`L-1` prefixes agree.
        have hwin : nodeWindow hG D ⟨0, hG⟩ = nodeWindow hG S j := by
          funext e
          have := congrFun (hjwindow) e
          exact this
        have : nodeWindow hG D ⟨0, hG⟩ = fun d => cyc hG D (0 + d.val) := rfl
        have : nodeWindow hG S j = fun d => cyc hG S (j.val + d.val) := rfl
        have hd' : (⟨d, hd⟩ : Fin (L - 1)).val = d := rfl
        have e := congrFun hwin ⟨d, hd⟩
        have : cyc hG D (0 + d) = cyc hG S (j.val + d) := by
          have := congrFun (by
            show nodeWindow hG D ⟨0, hG⟩ = fun d => cyc hG D d.val
            exact rfl) ⟨d, hd⟩
          rw [e] at this
          exact this
        omega
    | succ t ih =>
        intro d hd
        -- Overlap positions (d+1 < L-1) follow from the IH.
        by_cases hdo : d + 1 < L - 1
        · have hd1 : d + 1 < L - 1 := hdo
          have e := ih d (by omega)
          have e2 : cyc hG D (t + 1 + d) = cyc hG S (j.val + t + 1 + d) := by
            have h1 : t + 1 + d = t + (d + 1) := by omega
            rw [h1]
            exact ih (d + 1) (by omega)
          exact e2
        · -- Last position (d = L-2): the new symbol, via NoBranching.
          have hdL2 : d = L - 2 := by omega
          -- `D`'s `L`-mer at `t` occurs in `S` (spectra agree).
          have hDt : 0 < specCount (L := L) hG D (window hG D ⟨t, Nat.mod_lt _ hG⟩) :=
            by
              have hmem : (⟨t, Nat.mod_lt _ hG⟩ : Fin G) ∈ Finset.univ.filter
                  (fun r : Fin G => window hG D r
                    = window hG D ⟨t, Nat.mod_lt _ hG⟩) :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
              exact Finset.card_pos.mpr ⟨⟨t, Nat.mod_lt _ hG⟩, hmem⟩
          have hSt : 0 < specCount (L := L) hG S (window hG D ⟨t, Nat.mod_lt _ hG⟩) := by
            rw [hspec (window hG D ⟨t, Nat.mod_lt _ hG⟩)]
            exact hDt
          have hStmem : window hG D ⟨t, Nat.mod_lt _ hG⟩ ∈ support hG S := by
            rw [(OrientedSameLengthML.specCount_pos_iff hG
              (window hG D ⟨t, Nat.mod_lt _ hG⟩)).symm]
            exact hSt
          obtain ⟨u, -, huwindow⟩ := hStmem
          -- `u`'s `K`-prefix matches `j+t`'s, so NoBranching equates followers.
          have hpre_u : winPrefix (window hG S u) = nodeWindow hG S u := rfl
          have hpre_jt : winPrefix (window hG S ⟨j.val + t, Nat.mod_lt _ hG⟩)
              = nodeWindow hG S ⟨j.val + t, Nat.mod_lt _ hG⟩ := rfl
          have hpre_eq : winPrefix (window hG S u)
              = winPrefix (window hG S ⟨j.val + t, Nat.mod_lt _ hG⟩) := by
            rw [hpre_u, hpre_jt, huwindow]
            -- `window D t`'s prefix is `nodeWindow D t`, which by IH equals
            -- `nodeWindow S (j+t)`.
            have hpre_Dt : winPrefix (window hG D ⟨t, Nat.mod_lt _ hG⟩)
                = nodeWindow hG D ⟨t, Nat.mod_lt _ hG⟩ := rfl
            have hpre_Dt2 : nodeWindow hG D ⟨t, Nat.mod_lt _ hG⟩
                = nodeWindow hG S ⟨j.val + t, Nat.mod_lt _ hG⟩ := by
              funext e
              have ih' := ih e.val (by have := e.isLt; omega)
              have : cyc hG D (t + e.val) = cyc hG S (j.val + t + e.val) := ih'
              exact this
            rw [hpre_Dt, hpre_Dt2]
          have hnb' := hnb u ⟨j.val + t, Nat.mod_lt _ hG⟩
          have hwin_eq : nodeWindow hG S u = nodeWindow hG S ⟨j.val + t, Nat.mod_lt _ hG⟩ := by
            rw [hpre_u, hpre_jt, hpre_eq]
          have hfol := hnb' hwin_eq
          -- `u`'s follower equals `D`'s follower at `t`.
          have hfu : cyc hG S (u.val + L - 1) = cyc hG D (t + L - 1) := by
            have := congrFun huwindow ⟨L - 1, by omega⟩
            exact this
          -- Compose: `cyc D (t + L - 1) = cyc S (j + t + L - 1)`.
          have hSjt : cyc hG S (u.val + L - 1)
              = cyc hG S (j.val + t + L - 1) := hfol
          rw [hdL2]
          have e1 : cyc hG D (t + 1 + d) = cyc hG D (t + (L - 1)) := by omega
          rw [e1]
          exact hfu.trans hSjt.symm
  -- Recover the rotation: `cyc D p = cyc S (j + p)` for all `p < G`.
  have hrot : ∀ p : ℕ, p < G → cyc hG D p = cyc hG S (j.val + p) := by
    intro p hp
    exact key p p.isLt 0 (by omega)
  -- `RotEquiv` with shift `G - j.val`.
  refine ⟨G - j.val, ?_⟩
  intro i
  have h1 : cyc hG D (i.val + (G - j.val) % G)
      = cyc hG S (j.val + (i.val + (G - j.val) % G)) := by
    have hp : i.val + (G - j.val) % G < G := by omega
    have := hrot _ hp
    have : (i.val + (G - j.val) % G) % G = (i.val + (G - j.val)) % G := by
      rw [Nat.add_mod, Nat.mod_mod]
    rw [this] at this
    exact this
  have h2 : (j.val + (i.val + (G - j.val))) % G = i.val := by
    have hle : j.val ≤ G := Nat.le_of_lt_succ (Nat.lt_succ_of_lt j.isLt)
    omega
  rw [h2] at h1
  exact h1

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
    rcases AssemblyP1.RepeatAdapter.primitive_or_minimal_period hG S with
      | inl hprim' => exact absurd hprim' hprimRA
      | inr hmin =>
        obtain ⟨p, hp⟩ := hmin
        obtain ⟨hp0, hpG, hGp, hper, hsmall⟩ := hp
        have hL2' : 2 ≤ L := hL2
        have hNwin : ∀ i j : ℕ, i < p → j < p →
            (∀ d : ℕ, d < L - 1 → OrientedRigidity.cyc hG S (i + d)
              = OrientedRigidity.cyc hG S (j + d)) → i = j :=
          AssemblyP1.RepeatAdapter.periodic_factor_distinct hG S p hL2' hp hno
        have hcyc := AssemblyP1.RepeatAdapter.periodic_cycle_shape hG S p hp0
          (le_of_lt hpG) hper hNwin
        have hnb : AssemblyP1.SameLength62Nonprimitive.NoBranching (L := L) hG S :=
          noBranching_of_isSimpleCycle hG S hcyc
        have hRot := spectrum_eq_of_noBranching hG hL2 S D hnb hspec
        exact (SameLength62TieUniqueness.rotEquiv_iff_isCyclicShift hG).mp hRot

end

end AssemblyP1.SameLength62Uniqueness
