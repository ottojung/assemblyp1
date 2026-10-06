import AssemblyP1.Issue94AlignedPairs
import AssemblyP1.Issue94ComponentAlgebra
import AssemblyP1.Issue94TransposePreserve

/-!
# Board 94: discrete antiderivative for aligned ladder swaps

This module packages the local permutation algebra used by the component-deletion
route.  The first step is the exact shift identity for one aligned swap.
-/

namespace AssemblyP1.Issue94Antiderivative

open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTUniqueEulerian

variable {G : ℕ}

/-- The one-step truth rotation as an actual permutation. -/
def rhoEquiv (hG : 0 < G) : Equiv.Perm (Fin G) where
  toFun := nextPos hG
  invFun := prevPos hG
  left_inv := prevNext hG
  right_inv := nextPrev hG

@[simp] theorem rhoEquiv_apply (hG : 0 < G) (x : Fin G) :
    rhoEquiv hG x = nextPos hG x := rfl

@[simp] theorem rhoEquiv_symm_apply (hG : 0 < G) (x : Fin G) :
    (rhoEquiv hG).symm x = prevPos hG x := rfl

/-- The aligned transposition at ladder shift coordinate `t`. -/
def alignedSwap (hG : 0 < G) (p q : Fin G) (t : ℕ) : Equiv.Perm (Fin G) :=
  Equiv.swap (rotAdd hG t p) (rotAdd hG t q)

/-- Conjugating one aligned swap by one truth step increments its ladder
coordinate. -/
theorem rho_conj_alignedSwap (hG : 0 < G) (p q : Fin G) (t : ℕ) :
    ((rhoEquiv hG).symm.trans (alignedSwap hG p q t)).trans (rhoEquiv hG) =
      alignedSwap hG p q (t + 1) := by
  unfold alignedSwap
  rw [Equiv.symm_trans_swap_trans]
  simp only [rhoEquiv_apply, nextPos_rotAdd]

#print axioms AssemblyP1.Issue94Antiderivative.rho_conj_alignedSwap

end AssemblyP1.Issue94Antiderivative
