import AssemblyP1.Issue94IterSlide

namespace AssemblyP1.Issue94InterleavedPairSwap

open AssemblyP1
open AssemblyP1.SourceFaithfulIs
open AssemblyP1.BBTChords
open AssemblyP1.Issue94IterSlide

variable {K : ℕ}

theorem interleavedStarts_pair_swap (hK : 0 < K) {a b c d : Fin K}
    (hI : InterleavedStarts hK a b c d) : InterleavedStarts hK c d a b := by
  have hne : FourDistinctStarts a b c d := hI.1
  have h : InArc hK a b c ↔ ¬ InArc hK a b d := hI.2
  rcases hne with ⟨h1, h2, h3, h4, h5, h6⟩
  refine ⟨⟨h6, h2.symm, h4.symm, h3.symm, h5.symm, h1⟩, ?_⟩
  have key : ∀ (u v w : Fin K),
      InArc hK u v w ↔
        (u.val < v.val ∧ u.val < w.val ∧ w.val < v.val) ∨
          (v.val < u.val ∧ (u.val < w.val ∨ w.val < v.val)) := by
    intro u v w
    exact inArc_val hK
  rw [key a b c, key a b d] at h
  rw [key c d a, key c d b]
  by_cases hab : a.val < b.val <;> by_cases hcd : c.val < d.val <;> omega

theorem interleaved_pair_swap (hK : 0 < K) {α : Type} {S : Fin K → α}
    (a b c d : Fin K) (hI : Interleaved (mkGenome hK S) a b c d) :
    Interleaved (mkGenome hK S) c d a b :=
  (interleaved_iff hK c d a b).mpr
    (interleavedStarts_pair_swap hK ((interleaved_iff hK a b c d).mp hI))

end AssemblyP1.Issue94InterleavedPairSwap
