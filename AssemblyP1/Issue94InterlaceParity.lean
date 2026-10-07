import AssemblyP1.Issue94CLEDeletion
import AssemblyP1.Issue94Parity

set_option linter.unusedSectionVars false

set_option autoImplicit false

namespace AssemblyP1.Issue94InterlaceParity

open Matrix
open AssemblyP1.Issue94CLEDeletion
open AssemblyP1.Issue94Parity

variable {C : Type*} [Fintype C] [DecidableEq C]

def principalMatrix (M : Matrix C C (ZMod 2)) (S : Finset C) :
    Matrix S S (ZMod 2) :=
  M.submatrix Subtype.val Subtype.val

@[simp] theorem principalMatrix_apply
    (M : Matrix C C (ZMod 2)) (S : Finset C) (i j : S) :
    principalMatrix M S i j = M i j := rfl

theorem principalInterlace_kerZero
    {X : SimpleGraph C} {S : Finset C}
    (hS : IsUnionOfComponents X S)
    (hone : kerZero (interlaceMatrix X)) :
    ∀ z : S → ZMod 2,
      (principalMatrix (interlaceMatrix X) S).mulVec z = 0 → z = 0 := by
  classical
  intro z hz
  let zext : C → ZMod 2 := fun c =>
    if hc : c ∈ S then z ⟨c, hc⟩ else 0
  have hfull : (interlaceMatrix X).mulVec zext = 0 := by
    funext c
    by_cases hc : c ∈ S
    · have hrow := congrFun hz ⟨c, hc⟩
      change (∑ d : C, interlaceMatrix X c d * zext d) = 0
      calc
        (∑ d : C, interlaceMatrix X c d * zext d)
            = Finset.sum S (fun d => interlaceMatrix X c d * zext d) := by
                symm
                apply Finset.sum_subset (by simp)
                intro d _ hd
                simp [zext, hd]
        _ = ∑ d : S, interlaceMatrix X c d * zext d := by
              exact Finset.sum_subtype S (fun _ => Iff.rfl)
                (fun d => interlaceMatrix X c d * zext d)
        _ = ∑ d : S, principalMatrix (interlaceMatrix X) S ⟨c, hc⟩ d * z d := by
              apply Finset.sum_congr rfl
              intro d _
              simp [principalMatrix, zext, d.property]
        _ = 0 := by
              simpa [Matrix.mulVec, dotProduct] using hrow
    · change (∑ d : C, interlaceMatrix X c d * zext d) = 0
      apply Finset.sum_eq_zero
      intro d _
      by_cases hd : d ∈ S
      · rw [interlaceMatrix_blockDiag' hS hc hd]
        simp
      · simp [zext, hd]
  have hzext : zext = 0 := hone zext hfull
  funext i
  have hi := congrFun hzext i.1
  simpa [zext, i.property] using hi

theorem interlaceUnion_even_card
    {X : SimpleGraph C} {S : Finset C}
    (hS : IsUnionOfComponents X S)
    (hone : kerZero (interlaceMatrix X)) :
    Even S.card := by
  classical
  have hker := principalInterlace_kerZero hS hone
  have heven :=
    even_card_of_hollow_symm_kerZero
      (principalMatrix (interlaceMatrix X) S)
      (fun i => by simp [principalMatrix, interlaceMatrix_hollow])
      (fun i j => by
        simp only [principalMatrix_apply]
        exact interlaceMatrix_symm X i j)
      hker
  simpa using heven

theorem interlaceComponent_even_card
    (X : SimpleGraph C) (c : C)
    (hone : kerZero (interlaceMatrix X)) :
    Even (componentFinset X c).card := by
  apply interlaceUnion_even_card
  · exact component_connectedComponentMk X c
  · exact hone

#print axioms AssemblyP1.Issue94InterlaceParity.principalInterlace_kerZero
#print axioms AssemblyP1.Issue94InterlaceParity.interlaceUnion_even_card
#print axioms AssemblyP1.Issue94InterlaceParity.interlaceComponent_even_card

end AssemblyP1.Issue94InterlaceParity
