import AssemblyP1.Issue94PhysicalChord
import AssemblyP1.Issue94IterSlide
import AssemblyP1.Issue94CLEDeletion
import Mathlib.Data.ZMod.Basic

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace AssemblyP1.Issue94InterlaceKernel

open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.Issue94PhysicalChord
open AssemblyP1.Issue94CLEDeletion

variable {α : Type} [DecidableEq α] {K L : ℕ}

/-- Pure arithmetic form of the boundary of a half-open interval [a,b) on
the linearly represented circle. -/
theorem intervalBit_boundary_nat
    {K a b y : ℕ}
    (hK : 0 < K) (haK : a < K) (hab : a < b)
    (hbK : b < K) (hyK : y < K) :
    (if a ≤ (if y = 0 then K - 1 else y - 1) ∧
          (if y = 0 then K - 1 else y - 1) < b
      then (1 : ZMod 2) else 0) +
      (if a ≤ y ∧ y < b then 1 else 0)
      =
      (if y = a ∨ y = b then 1 else 0) := by
  by_cases hy0 : y = 0
  · subst y
    simp only [ite_eq_left_iff]
    by_cases ha0 : a = 0
    · subst a
      have hbpos : 0 < b := by omega
      have hK1 : ¬ K - 1 < b := by omega
      simp [hK1, hbpos]
    · have hK1 : ¬ K - 1 < b := by omega
      have h0a : ¬ (0 : ℕ) = a := by omega
      have h0b : ¬ (0 : ℕ) = b := by omega
      simp [ha0, hK1, h0a, h0b]
  · rw [ite_eq_right hy0]
    by_cases hya : y = a
    · subst y
      have hprev : ¬ a ≤ a - 1 := by omega
      simp [hprev, hab]
    · by_cases hyb : y = b
      · subst y
        have h1 : a ≤ b - 1 := by omega
        have h2 : b - 1 < b := by omega
        simp [hya, h1, h2]
      · by_cases hylt : y < a
        · have hnot1 : ¬ a ≤ y - 1 := by omega
          have hnot2 : ¬ a ≤ y := by omega
          simp [hya, hyb, hnot1, hnot2]
        · by_cases hyin : y < b
          · have hay : a ≤ y := by omega
            have hp_ge : a ≤ y - 1 := by omega
            have hp_lt : y - 1 < b := by omega
            simp [hya, hyb, hay, hyin, hp_ge, hp_lt]
            have htwo : (1 : ZMod 2) + 1 = 0 := by decide
            exact htwo
          · have hcur : ¬ (a ≤ y ∧ y < b) := by omega
            have hpre : ¬ (a ≤ y - 1 ∧ y - 1 < b) := by omega
            simp [hya, hyb, hcur, hpre]

/-- Indicator of the canonical half-open interval [lower,upper) of a physical
AltF chord. -/
def arcBit (hK : 0 < K) (sigma : Fin K ≃ Fin K)
    (c : AltFChord hK sigma) (x : Fin K) : ZMod 2 :=
  if c.1.val ≤ x.val ∧ x.val < (AltF hK sigma c.1).val then 1 else 0

theorem prev_val
    (hK : 0 < K) (y : Fin K) :
    (prevPos hK y).val =
      if y.val = 0 then K - 1 else y.val - 1 := by
  unfold prevPos
  simp only [Fin.val_mk]
  by_cases hy : y.val = 0
  · rw [ite_eq_left hy, hy]
    have hlt : K - 1 < K := by omega
    have heq0 : 0 + K - 1 = K - 1 := by omega
    rw [heq0, Nat.mod_eq_of_lt hlt]
  · rw [ite_eq_right hy]
    have heq : y.val + K - 1 = (y.val - 1) + K := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt]
    omega

/-- The one-step truth boundary of one physical chord indicator is exactly its
two endpoints. -/
theorem arcBit_boundary_val
    (hK : 0 < K) (sigma : Fin K ≃ Fin K)
    (c : AltFChord hK sigma) (y : Fin K) :
    arcBit hK sigma c (prevPos hK y) + arcBit hK sigma c y =
      if y.val = c.1.val ∨ y.val = (AltF hK sigma c.1).val then 1 else 0 := by
  have hp := prev_val hK y
  have hnat := intervalBit_boundary_nat
    (K := K) (a := c.1.val) (b := (AltF hK sigma c.1).val) (y := y.val)
    hK c.1.isLt (chord_lower hK sigma c) (AltF hK sigma c.1).isLt y.isLt
  unfold arcBit
  rw [hp]
  exact hnat


theorem inArc_physical_iff
    (hK : 0 < K) (sigma : Fin K ≃ Fin K)
    (c : AltFChord hK sigma) (x : Fin K) :
    InArc hK c.1 (AltF hK sigma c.1) x ↔
      c.1.val < x.val ∧ x.val < (AltF hK sigma c.1).val := by
  rw [AssemblyP1.Issue94IterSlide.inArc_val hK]
  have hlt := chord_lower hK sigma c
  constructor
  · rintro (h | h)
    · exact ⟨h.2.1, h.2.2⟩
    · omega
  · intro h
    exact Or.inl ⟨hlt, h.1, h.2⟩

noncomputable def inArcBit
    (hK : 0 < K) (sigma : Fin K ≃ Fin K)
    (c : AltFChord hK sigma) (x : Fin K) : ZMod 2 := by
  classical
  exact if InArc hK c.1 (AltF hK sigma c.1) x then 1 else 0

theorem arcBit_eq_inArcBit
    (hK : 0 < K) (sigma : Fin K ≃ Fin K)
    (c : AltFChord hK sigma) (x : Fin K)
    (hx : x ≠ c.1) :
    arcBit hK sigma c x = inArcBit hK sigma c x := by
  classical
  unfold arcBit inArcBit
  by_cases hIn : InArc hK c.1 (AltF hK sigma c.1) x
  · have hv := (inArc_physical_iff hK sigma c x).mp hIn
    have hcond : c.1.val ≤ x.val ∧
        x.val < (AltF hK sigma c.1).val :=
      ⟨Nat.le_of_lt hv.1, hv.2⟩
    rw [ite_eq_left hcond, ite_eq_left hIn]
  · have hval : x.val ≠ c.1.val := by
      intro h
      apply hx
      apply Fin.ext
      exact h
    have hnot : ¬ (c.1.val ≤ x.val ∧
        x.val < (AltF hK sigma c.1).val) := by
      intro h
      apply hIn
      apply (inArc_physical_iff hK sigma c x).mpr
      exact ⟨lt_of_le_of_ne h.1 (Ne.symm hval), h.2⟩
    rw [ite_eq_right hnot, ite_eq_right hIn]

theorem physical_four_distinct
    {L : ℕ}
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : AssemblyP1.BBTEulerian.EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    {c d : AltFChord hK sigma} (hcd : c ≠ d) :
    FourDistinctStarts
      c.1 (AltF hK sigma c.1)
      d.1 (AltF hK sigma d.1) := by
  have hll : c.1 ≠ d.1 := by
    intro h
    apply hcd
    apply Subtype.ext
    exact h
  have hinj := (AltF_bijective hK sigma).1
  have huu : AltF hK sigma c.1 ≠ AltF hK sigma d.1 := by
    intro h
    exact hll (hinj h)
  have hcc := chord_ne_image hK sigma c
  have hdd := chord_ne_image hK sigma d
  have hsqc := AssemblyP1.BBTLadder.AltF_sq hK S hEul hL hLK hprim hP2 c.1
  have hsqd := AssemblyP1.BBTLadder.AltF_sq hK S hEul hL hLK hprim hP2 d.1
  have hlu : c.1 ≠ AltF hK sigma d.1 := by
    intro h
    have h2 := congrArg (AltF hK sigma) h
    have heq : AltF hK sigma c.1 = d.1 := by
      simpa [hsqd] using h2
    have hc := chord_lower hK sigma c
    have hd := chord_lower hK sigma d
    have hv1 := congrArg Fin.val h
    have hv2 := congrArg Fin.val heq
    omega
  have hul : AltF hK sigma c.1 ≠ d.1 := by
    intro h
    have h2 := congrArg (AltF hK sigma) h
    have heq : c.1 = AltF hK sigma d.1 := by
      simpa [hsqc] using h2
    exact hlu heq
  exact ⟨hcc, hll, hlu, hul, huu, hdd⟩

theorem arcBit_pair_eq_interlace
    {L : ℕ}
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : AssemblyP1.BBTEulerian.EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    {c d : AltFChord hK sigma} (hcd : c ≠ d) :
    arcBit hK sigma d c.1 +
        arcBit hK sigma d (AltF hK sigma c.1) =
      AssemblyP1.Issue94CLEDeletion.interlaceMatrix
        (altFInterlaceGraph hK S sigma) d c := by
  classical
  have hfour := physical_four_distinct hK S sigma hEul hL hLK hprim hP2 hcd
  have h1 : c.1 ≠ d.1 := hfour.2.1
  have h2 : AltF hK sigma c.1 ≠ d.1 := hfour.2.2.2.1
  rw [arcBit_eq_inArcBit hK sigma d c.1 h1]
  rw [arcBit_eq_inArcBit hK sigma d (AltF hK sigma c.1) h2]
  have hfour' : FourDistinctStarts
      d.1 (AltF hK sigma d.1) c.1 (AltF hK sigma c.1) :=
    ⟨hfour.2.2.2.2.2, hfour.2.1.symm, hfour.2.2.2.1.symm,
      hfour.2.2.1.symm, hfour.2.2.2.2.1.symm, hfour.1⟩
  have hadj :
      (altFInterlaceGraph hK S sigma).Adj d c ↔
        (InArc hK d.1 (AltF hK sigma d.1) c.1 ↔
          ¬ InArc hK d.1 (AltF hK sigma d.1) (AltF hK sigma c.1)) := by
    constructor
    · intro h
      have hraw := (altFInterlaceGraph_adj hK S sigma d c).mp h
      have hs := (AssemblyP1.Issue94IterSlide.interleaved_iff
        hK (S := S) d.1 (AltF hK sigma d.1)
          c.1 (AltF hK sigma c.1)).mp hraw
      exact hs.2
    · intro h
      apply (altFInterlaceGraph_adj hK S sigma d c).mpr
      apply (AssemblyP1.Issue94IterSlide.interleaved_iff
        hK (S := S) d.1 (AltF hK sigma d.1)
          c.1 (AltF hK sigma c.1)).mpr
      exact ⟨hfour', h⟩
  unfold inArcBit
  simp only [AssemblyP1.Issue94CLEDeletion.interlaceMatrix]
  rw [hadj]
  by_cases hc1 : InArc hK d.1 (AltF hK sigma d.1) c.1 <;>
    by_cases hc2 : InArc hK d.1 (AltF hK sigma d.1) (AltF hK sigma c.1) <;>
    simp [hc1, hc2] <;> decide

noncomputable def color
    (hK : 0 < K) (sigma : Fin K ≃ Fin K)
    (z : AltFChord hK sigma → ZMod 2) (x : Fin K) : ZMod 2 :=
  ∑ d : AltFChord hK sigma, z d * arcBit hK sigma d x

theorem arcBit_own_pair
    (hK : 0 < K) (sigma : Fin K ≃ Fin K)
    (c : AltFChord hK sigma) :
    arcBit hK sigma c c.1 +
        arcBit hK sigma c (AltF hK sigma c.1) = 1 := by
  have hlt := chord_lower hK sigma c
  unfold arcBit
  have hle : c.1.val ≤ c.1.val := le_rfl
  have hle2 : c.1.val ≤ (AltF hK sigma c.1).val := Nat.le_of_lt hlt
  have hirr : ¬ (AltF hK sigma c.1).val < (AltF hK sigma c.1).val :=
    lt_irrefl _
  simp [hlt, hle, hle2, hirr]

theorem color_pair_eq
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : AssemblyP1.BBTEulerian.EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (z : AltFChord hK sigma → ZMod 2)
    (c : AltFChord hK sigma) :
    color hK sigma z c.1 +
        color hK sigma z (AltF hK sigma c.1) =
      z c + (interlaceMatrix (altFInterlaceGraph hK S sigma)).mulVec z c := by
  classical
  calc
    color hK sigma z c.1 +
          color hK sigma z (AltF hK sigma c.1)
        = ∑ d : AltFChord hK sigma,
            z d * (arcBit hK sigma d c.1 +
              arcBit hK sigma d (AltF hK sigma c.1)) := by
            simp [color, mul_add, Finset.sum_add_distrib]
    _ = ∑ d : AltFChord hK sigma,
          (z d * interlaceMatrix (altFInterlaceGraph hK S sigma) d c +
            if d = c then z c else 0) := by
        apply Finset.sum_congr rfl
        intro d hd
        by_cases hdc : d = c
        · subst d
          rw [arcBit_own_pair]
          simp [interlaceMatrix_hollow]
        · have hs := arcBit_pair_eq_interlace
            hK S sigma hEul hL hLK hprim hP2 (Ne.symm hdc)
          rw [hs]
          simp [hdc]
    _ = (∑ d : AltFChord hK sigma,
          z d * interlaceMatrix (altFInterlaceGraph hK S sigma) d c) +
          z c := by
        calc
          (∑ d : AltFChord hK sigma,
            (z d * interlaceMatrix (altFInterlaceGraph hK S sigma) d c +
              if d = c then z c else 0))
              =
            (∑ d : AltFChord hK sigma,
              z d * interlaceMatrix (altFInterlaceGraph hK S sigma) d c) +
            (∑ d : AltFChord hK sigma,
              if d = c then z c else 0) := Finset.sum_add_distrib
          _ = _ := by simp
    _ = z c + (interlaceMatrix (altFInterlaceGraph hK S sigma)).mulVec z c := by
        rw [add_comm]
        congr 1
        unfold Matrix.mulVec dotProduct
        apply Finset.sum_congr rfl
        intro d hd
        rw [interlaceMatrix_symm (altFInterlaceGraph hK S sigma) d c]
        exact mul_comm _ _

#print axioms AssemblyP1.Issue94InterlaceKernel.color_pair_eq

theorem color_boundary_of_endpoint
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : AssemblyP1.BBTEulerian.EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (z : AltFChord hK sigma → ZMod 2)
    (c : AltFChord hK sigma) (y : Fin K)
    (hy : y = c.1 ∨ y = AltF hK sigma c.1) :
    color hK sigma z (AssemblyP1.BBTChords.prevPos hK y) +
        color hK sigma z y = z c := by
  classical
  calc
    color hK sigma z (AssemblyP1.BBTChords.prevPos hK y) +
          color hK sigma z y
        = ∑ d : AltFChord hK sigma,
            z d * (arcBit hK sigma d (AssemblyP1.BBTChords.prevPos hK y) +
              arcBit hK sigma d y) := by
            simp [color, mul_add, Finset.sum_add_distrib]
    _ = ∑ d : AltFChord hK sigma,
          (if d = c then z c else 0) := by
        apply Finset.sum_congr rfl
        intro d hd
        by_cases hdc : d = c
        · subst d
          have hby : y.val = c.1.val ∨
              y.val = (AltF hK sigma c.1).val := by
            rcases hy with h | h
            · left; exact congrArg Fin.val h
            · right; exact congrArg Fin.val h
          rw [arcBit_boundary_val hK sigma c y]
          rw [ite_eq_left hby]
          simp
        · have hfour := physical_four_distinct hK S sigma hEul hL hLK hprim hP2
            (Ne.symm hdc)
          have hylo : y ≠ d.1 := by
            rcases hy with h | h
            · rw [h]
              exact hfour.2.1
            · rw [h]
              exact hfour.2.2.2.1
          have hyup : y ≠ AltF hK sigma d.1 := by
            rcases hy with h | h
            · rw [h]
              exact hfour.2.2.1
            · rw [h]
              exact hfour.2.2.2.2.1
          have hvlo : y.val ≠ d.1.val := by
            intro h
            exact hylo (Fin.ext h)
          have hvup : y.val ≠ (AltF hK sigma d.1).val := by
            intro h
            exact hyup (Fin.ext h)
          rw [arcBit_boundary_val hK sigma d y]
          rw [ite_eq_right (by exact fun h => h.elim hvlo hvup)]
          simp [hdc]
    _ = z c := by simp

#print axioms AssemblyP1.Issue94InterlaceKernel.color_boundary_of_endpoint

theorem zmod2_add_self (q : ZMod 2) : q + q = 0 := by
  calc
    q + q = (2 : ZMod 2) * q := (two_mul q).symm
    _ = 0 := by
      have h2 : (2 : ZMod 2) = 0 := by decide
      rw [h2, zero_mul]

theorem color_boundary_of_fixed
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : AssemblyP1.BBTEulerian.EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (z : AltFChord hK sigma → ZMod 2)
    (y : Fin K) (hfix : AltF hK sigma y = y) :
    color hK sigma z (AssemblyP1.BBTChords.prevPos hK y) +
        color hK sigma z y = 0 := by
  classical
  calc
    color hK sigma z (AssemblyP1.BBTChords.prevPos hK y) +
          color hK sigma z y
        = ∑ d : AltFChord hK sigma,
            z d * (arcBit hK sigma d (AssemblyP1.BBTChords.prevPos hK y) +
              arcBit hK sigma d y) := by
            simp [color, mul_add, Finset.sum_add_distrib]
    _ = ∑ d : AltFChord hK sigma, 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        have hylo : y ≠ d.1 := by
          intro h
          subst y
          exact (chord_ne_image hK sigma d) hfix.symm
        have hsq := AssemblyP1.BBTLadder.AltF_sq
          hK S hEul hL hLK hprim hP2 d.1
        have hyup : y ≠ AltF hK sigma d.1 := by
          intro h
          rw [h] at hfix
          have heq : d.1 = AltF hK sigma d.1 := hsq.symm.trans hfix
          exact (chord_ne_image hK sigma d) heq
        have hvlo : y.val ≠ d.1.val := by
          intro h
          exact hylo (Fin.ext h)
        have hvup : y.val ≠ (AltF hK sigma d.1).val := by
          intro h
          exact hyup (Fin.ext h)
        rw [arcBit_boundary_val hK sigma d y]
        rw [ite_eq_right (by exact fun h => h.elim hvlo hvup)]
        simp
    _ = 0 := by simp

theorem color_jump_of_endpoint
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : AssemblyP1.BBTEulerian.EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (z : AltFChord hK sigma → ZMod 2)
    (c : AltFChord hK sigma) (y : Fin K)
    (hy : y = c.1 ∨ y = AltF hK sigma c.1) :
    color hK sigma z (AltF hK sigma y) +
        color hK sigma z y =
      z c + (interlaceMatrix (altFInterlaceGraph hK S sigma)).mulVec z c := by
  rcases hy with h | h
  · subst y
    simpa [add_comm] using
      (color_pair_eq hK S sigma hEul hL hLK hprim hP2 z c)
  · subst y
    have hsq := AssemblyP1.BBTLadder.AltF_sq
      hK S hEul hL hLK hprim hP2 c.1
    simpa [hsq] using
      (color_pair_eq hK S sigma hEul hL hLK hprim hP2 z c)

theorem color_succ_eq_of_kernel
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : AssemblyP1.BBTEulerian.EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (z : AltFChord hK sigma → ZMod 2)
    (hker :
      (interlaceMatrix (altFInterlaceGraph hK S sigma)).mulVec z = 0)
    (x : Fin K) :
    color hK sigma z (Succ hK sigma x) = color hK sigma z x := by
  let y := AssemblyP1.BBTChords.nextPos hK x
  have hprev : AssemblyP1.BBTChords.prevPos hK y = x := by
    dsimp [y]
    exact AssemblyP1.BBTSequenceGraph.prevNext hK x
  have hsucc : AltF hK sigma y = Succ hK sigma x := by
    dsimp [y]
    exact AltF_succ hK sigma x
  by_cases hfix : AltF hK sigma y = y
  · have hb := color_boundary_of_fixed
      hK S sigma hEul hL hLK hprim hP2 z y hfix
    have hj : color hK sigma z (AltF hK sigma y) +
        color hK sigma z y = 0 := by
      rw [hfix]
      exact zmod2_add_self _
    have hc :
        color hK sigma z (AltF hK sigma y) =
          color hK sigma z (AssemblyP1.BBTChords.prevPos hK y) :=
      add_right_cancel (hj.trans hb.symm)
    simpa [hsucc, hprev] using hc
  · obtain ⟨c, hpair⟩ :=
      exists_physical_chord_of_support
        hK S sigma hEul hL hLK hprim hP2 hfix
    have hymem :
        y ∈ ({c.1, AltF hK sigma c.1} : Finset (Fin K)) := by
      rw [hpair]
      simp
    have hy : y = c.1 ∨ y = AltF hK sigma c.1 := by
      simpa using hymem
    have hb := color_boundary_of_endpoint
      hK S sigma hEul hL hLK hprim hP2 z c y hy
    have hj := color_jump_of_endpoint
      hK S sigma hEul hL hLK hprim hP2 z c y hy
    have hm :
        (interlaceMatrix (altFInterlaceGraph hK S sigma)).mulVec z c = 0 := by
      simpa using congrFun hker c
    have hj0 :
        color hK sigma z (AltF hK sigma y) + color hK sigma z y = z c := by
      calc
        color hK sigma z (AltF hK sigma y) + color hK sigma z y
            = z c +
              (interlaceMatrix (altFInterlaceGraph hK S sigma)).mulVec z c := hj
        _ = z c := by rw [hm]; simp
    have hc :
        color hK sigma z (AltF hK sigma y) =
          color hK sigma z (AssemblyP1.BBTChords.prevPos hK y) :=
      add_right_cancel (hj0.trans hb.symm)
    simpa [hsucc, hprev] using hc

#print axioms AssemblyP1.Issue94InterlaceKernel.color_succ_eq_of_kernel

theorem color_iterate_eq_of_kernel
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : AssemblyP1.BBTEulerian.EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (z : AltFChord hK sigma → ZMod 2)
    (hker :
      (interlaceMatrix (altFInterlaceGraph hK S sigma)).mulVec z = 0)
    (n : ℕ) (x : Fin K) :
    color hK sigma z ((Succ hK sigma)^[n] x) = color hK sigma z x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      calc
        color hK sigma z ((Succ hK sigma)^[n] (Succ hK sigma x))
            = color hK sigma z (Succ hK sigma x) := ih _
        _ = color hK sigma z x :=
          color_succ_eq_of_kernel hK S sigma hEul hL hLK hprim hP2 z hker x

theorem color_constant_of_kernel
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : AssemblyP1.BBTEulerian.EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (z : AltFChord hK sigma → ZMod 2)
    (hker :
      (interlaceMatrix (altFInterlaceGraph hK S sigma)).mulVec z = 0) :
    ∀ x : Fin K,
      color hK sigma z x =
        color hK sigma z (AssemblyP1.BBTEulerian.origin hK) := by
  let orbit : Fin K → Fin K :=
    fun n => (Succ hK sigma)^[n.val] (AssemblyP1.BBTEulerian.origin hK)
  have hinj : Function.Injective orbit := by
    exact hEul.2
  have hsurj : Function.Surjective orbit :=
    Finite.injective_iff_surjective.mp hinj
  intro x
  obtain ⟨n, hn⟩ := hsurj x
  rw [← hn]
  exact color_iterate_eq_of_kernel
    hK S sigma hEul hL hLK hprim hP2 z hker n.val
      (AssemblyP1.BBTEulerian.origin hK)

theorem physicalInterlace_kerZero
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : AssemblyP1.BBTEulerian.EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S) :
    kerZero (interlaceMatrix (altFInterlaceGraph hK S sigma)) := by
  intro z hker
  funext c
  by_contra hzc
  have hconst :=
    color_constant_of_kernel hK S sigma hEul hL hLK hprim hP2 z hker
  have hb := color_boundary_of_endpoint
    hK S sigma hEul hL hLK hprim hP2 z c c.1 (Or.inl rfl)
  have hp := hconst (AssemblyP1.BBTChords.prevPos hK c.1)
  have hc := hconst c.1
  rw [hp, hc] at hb
  have hz :
      color hK sigma z (AssemblyP1.BBTEulerian.origin hK) +
        color hK sigma z (AssemblyP1.BBTEulerian.origin hK) = 0 :=
    zmod2_add_self _
  have hzc0 : z c = 0 := by
    rw [← hb]
    exact hz
  exact hzc hzc0

#print axioms AssemblyP1.Issue94InterlaceKernel.color_constant_of_kernel
#print axioms AssemblyP1.Issue94InterlaceKernel.physicalInterlace_kerZero


theorem physicalInterlace_component_even_card
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : AssemblyP1.BBTEulerian.EulerianCycle hK L S sigma)
    (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (c : AltFChord hK sigma) :
    Even
      (componentFinset (altFInterlaceGraph hK S sigma) c).card := by
  exact AssemblyP1.Issue94InterlaceParity.interlaceComponent_even_card
    (altFInterlaceGraph hK S sigma) c
    (physicalInterlace_kerZero hK S sigma hEul hL hLK hprim hP2)

#print axioms AssemblyP1.Issue94InterlaceKernel.physicalInterlace_component_even_card


#print axioms AssemblyP1.Issue94InterlaceKernel.physical_four_distinct
#print axioms AssemblyP1.Issue94InterlaceKernel.arcBit_pair_eq_interlace

#print axioms AssemblyP1.Issue94InterlaceKernel.intervalBit_boundary_nat
#print axioms AssemblyP1.Issue94InterlaceKernel.arcBit_boundary_val

end AssemblyP1.Issue94InterlaceKernel
