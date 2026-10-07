import Mathlib

/-!
# Board 94: products of coboundaries

A small group-algebra adapter for the component-antiderivative construction.
If each factor has a boundary factor, and each earlier boundary factor commutes
with all later antiderivative factors, the coboundary of the product is the
product of the boundary factors.
-/

namespace AssemblyP1.Issue94CommutatorProduct

variable {Γ : Type} [Group Γ]

/-- The multiplicative coboundary of g with respect to rho. -/
def coboundary (rho g : Γ) : Γ :=
  g⁻¹ * rho * g * rho⁻¹

/-- Two-factor coboundaries multiply when the first boundary term commutes
with the second antiderivative factor. -/
theorem coboundary_mul {rho a b ca cb : Γ}
    (ha : coboundary rho a = ca)
    (hb : coboundary rho b = cb)
    (hcomm : Commute ca b) :
    coboundary rho (a * b) = ca * cb := by
  unfold coboundary at *
  calc
    (a * b)⁻¹ * rho * (a * b) * rho⁻¹
        = b⁻¹ * (a⁻¹ * rho * a * rho⁻¹) * rho * b * rho⁻¹ := by group
    _ = b⁻¹ * ca * rho * b * rho⁻¹ := by rw [ha]
    _ = ca * (b⁻¹ * rho * b * rho⁻¹) := by
      rw [← hcomm.inv_right.eq]
      group
    _ = ca * cb := by rw [hb]

/-- List form of coboundary_mul.

The list stores (antiderivative factor, boundary factor) pairs. The Pairwise
hypothesis is triangular: the boundary of every earlier factor commutes with
every later antiderivative factor. -/
theorem coboundary_prod_pairs (rho : Γ) :
    ∀ xs : List (Γ × Γ),
      (∀ p ∈ xs, coboundary rho p.1 = p.2) →
      List.Pairwise (fun p q : Γ × Γ => Commute p.2 q.1) xs →
      coboundary rho ((xs.map Prod.fst).prod) = (xs.map Prod.snd).prod
  | [], _, _ => by simp [coboundary]
  | p :: xs, hall, hpw => by
      have hp := hall p (by simp)
      have htail_all : ∀ q ∈ xs, coboundary rho q.1 = q.2 := by
        intro q hq
        exact hall q (by simp [hq])
      have hpw' := List.pairwise_cons.mp hpw
      have htail := coboundary_prod_pairs rho xs htail_all hpw'.2
      have hcomm : Commute p.2 ((xs.map Prod.fst).prod) := by
        apply Commute.list_prod_right
        intro x hx
        rcases List.mem_map.mp hx with ⟨q, hq, rfl⟩
        exact hpw'.1 q hq
      simpa using coboundary_mul hp htail hcomm

#print axioms AssemblyP1.Issue94CommutatorProduct.coboundary_mul
#print axioms AssemblyP1.Issue94CommutatorProduct.coboundary_prod_pairs

end AssemblyP1.Issue94CommutatorProduct
