import AssemblyP1.Issue94InterlaceKernelBoundary

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace AssemblyP1.Issue94InterlaceKernel

open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.Issue94PhysicalChord
open AssemblyP1.Issue94CLEDeletion

variable {α : Type} [DecidableEq α] {K L : ℕ}

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

end AssemblyP1.Issue94InterlaceKernel
