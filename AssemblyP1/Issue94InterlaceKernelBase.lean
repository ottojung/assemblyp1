import AssemblyP1.Issue94InterlaceKernelArc

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace AssemblyP1.Issue94InterlaceKernel

open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.Issue94PhysicalChord
open AssemblyP1.Issue94CLEDeletion

variable {α : Type} [DecidableEq α] {K L : ℕ}

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
