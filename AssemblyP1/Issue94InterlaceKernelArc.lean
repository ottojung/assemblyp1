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

end AssemblyP1.Issue94InterlaceKernel
