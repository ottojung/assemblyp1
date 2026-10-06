import AssemblyP1.Issue94LadderInterval
import AssemblyP1.Issue94ComponentAlgebra

/-!
# Board 94: one-rung ladder coboundary

An aligned swap at ladder rung `i` has coboundary equal to the product of the
rung-`i` and rung-`i+1` swaps.  This is the pure circle algebra behind
sliding one AltF support chord along a maximal-repeat ladder.
-/

set_option autoImplicit false

namespace AssemblyP1.Issue94LadderSlide

open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTUniqueEulerian

variable {G : ℕ}

/-- The one-step rotation as a bundled permutation. -/
def rhoEquiv (hG : 0 < G) : Equiv.Perm (Fin G) where
  toFun := nextPos hG
  invFun := prevPos hG
  left_inv := BBTSequenceGraph.prevNext hG
  right_inv := BBTSequenceGraph.nextPrev hG

@[simp] theorem rhoEquiv_apply (hG : 0 < G) (x : Fin G) :
    rhoEquiv hG x = nextPos hG x := rfl

@[simp] theorem rhoEquiv_symm_apply (hG : 0 < G) (x : Fin G) :
    (rhoEquiv hG).symm x = prevPos hG x := rfl

/-- The aligned transposition at rung `i` of copies rooted at `p,q`. -/
def rungSwap (hG : 0 < G) (p q : Fin G) (i : ℕ) : Equiv.Perm (Fin G) :=
  Equiv.swap (rotAdd hG i p) (rotAdd hG i q)

@[simp] theorem rungSwap_symm (hG : 0 < G) (p q : Fin G) (i : ℕ) :
    (rungSwap hG p q i).symm = rungSwap hG p q i := by
  simp [rungSwap]

/-- Rotating an aligned swap one step conjugates it to the next rung. -/
theorem rungSwap_succ_eq_conj (hG : 0 < G) (p q : Fin G) (i : ℕ) :
    rungSwap hG p q (i + 1) =
      rhoEquiv hG * rungSwap hG p q i * (rhoEquiv hG)⁻¹ := by
  simpa [rungSwap, rhoEquiv, BBTUniqueEulerian.nextPos_rotAdd] using
    (Equiv.swap_apply_apply (rhoEquiv hG) (rotAdd hG i p) (rotAdd hG i q))

/-- The coboundary of one aligned swap is exactly the two adjacent rung swaps. -/
theorem rungSwap_coboundary (hG : 0 < G) (p q : Fin G) (i : ℕ) :
    (rungSwap hG p q i)⁻¹ * rhoEquiv hG * rungSwap hG p q i * (rhoEquiv hG)⁻¹ =
      rungSwap hG p q i * rungSwap hG p q (i + 1) := by
  rw [show (rungSwap hG p q i)⁻¹ = rungSwap hG p q i by
    exact rungSwap_symm hG p q i]
  calc
    rungSwap hG p q i * rhoEquiv hG * rungSwap hG p q i * (rhoEquiv hG)⁻¹
        = rungSwap hG p q i *
            (rhoEquiv hG * rungSwap hG p q i * (rhoEquiv hG)⁻¹) := by
              simp only [mul_assoc]
    _ = rungSwap hG p q i * rungSwap hG p q (i + 1) := by
          rw [← rungSwap_succ_eq_conj hG p q i]

/-- Pointwise form matching `Issue94ComponentAlgebra.delete_component`. -/
theorem rungSwap_coboundary_apply (hG : 0 < G) (p q : Fin G) (i : ℕ) (x : Fin G) :
    (rungSwap hG p q i).symm
        (nextPos hG (rungSwap hG p q i (prevPos hG x))) =
      (rungSwap hG p q i * rungSwap hG p q (i + 1)) x := by
  have h := congrArg (fun e : Equiv.Perm (Fin G) => e x)
    (rungSwap_coboundary hG p q i)
  simpa [Equiv.Perm.mul_apply, rhoEquiv] using h

end AssemblyP1.Issue94LadderSlide

