import AssemblyP1.BBTLadder

/-!
# Board 94: doubled-fibre swaps commute with label-preserving permutations

Once `{a,b}` is a `DoubledPair`, it is the complete fibre of its `(L-1)`-mer.
Hence any bijection preserving `vtx` maps `{a,b}` to itself. On a two-point
set it either fixes both points or exchanges them, so it commutes with
`Equiv.swap a b`.

This is the local commutation fact needed by the component-antiderivative route.
No `P2`, primitivity, interlacement, or cyclic-order hypothesis is needed here.
-/

namespace AssemblyP1.Issue94FibreCommute

open AssemblyP1
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTLadder

variable {α : Type} [DecidableEq α] {K L : ℕ}
  (hK : 0 < K) (S : Fin K → α)

theorem image_left_or_right {a b : Fin K} (g : Fin K ≃ Fin K)
    (hd : DoubledPair (L := L) hK S a b)
    (hg : ∀ x : Fin K, vtx hK L S (g x) = vtx hK L S x) :
    g a = a ∨ g a = b := by
  apply hd.2.1 (g a)
  change vtx hK L S (g a) = vtx hK L S a
  exact hg a

theorem image_right_or_left {a b : Fin K} (g : Fin K ≃ Fin K)
    (hd : DoubledPair (L := L) hK S a b)
    (hg : ∀ x : Fin K, vtx hK L S (g x) = vtx hK L S x) :
    g b = a ∨ g b = b := by
  apply hd.2.1 (g b)
  change vtx hK L S (g b) = vtx hK L S a
  exact (hg b).trans hd.2.2

theorem doubledPair_action {a b : Fin K} (hab : a ≠ b) (g : Fin K ≃ Fin K)
    (hd : DoubledPair (L := L) hK S a b)
    (hg : ∀ x : Fin K, vtx hK L S (g x) = vtx hK L S x) :
    (g a = a ∧ g b = b) ∨ (g a = b ∧ g b = a) := by
  rcases image_left_or_right hK S g hd hg with ha | ha <;>
    rcases image_right_or_left hK S g hd hg with hb | hb
  · exfalso
    apply hab
    apply g.injective
    exact ha.trans hb.symm
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hb⟩
  · exfalso
    apply hab
    apply g.injective
    exact ha.trans hb.symm

theorem swap_commutes_vtxPreserving {a b : Fin K} (hab : a ≠ b)
    (g : Fin K ≃ Fin K) (hd : DoubledPair (L := L) hK S a b)
    (hg : ∀ x : Fin K, vtx hK L S (g x) = vtx hK L S x) :
    g.trans (Equiv.swap a b) = (Equiv.swap a b).trans g := by
  rcases doubledPair_action hK S hab g hd hg with hfix | hswap
  · rcases hfix with ⟨hga, hgb⟩
    ext x
    simp only [Equiv.trans_apply]
    by_cases hxa : x = a
    · subst x
      simp [hga, hgb]
    by_cases hxb : x = b
    · subst x
      simp [hga, hgb]
    have hgxa : g x ≠ a := by
      intro hx
      apply hxa
      apply g.injective
      exact hx.trans hga.symm
    have hgxb : g x ≠ b := by
      intro hx
      apply hxb
      apply g.injective
      exact hx.trans hgb.symm
    rw [Equiv.swap_apply_of_ne_of_ne hgxa hgxb,
      Equiv.swap_apply_of_ne_of_ne hxa hxb]
  · rcases hswap with ⟨hga, hgb⟩
    ext x
    simp only [Equiv.trans_apply]
    by_cases hxa : x = a
    · subst x
      simp [hga, hgb]
    by_cases hxb : x = b
    · subst x
      simp [hga, hgb]
    have hgxa : g x ≠ a := by
      intro hx
      apply hxb
      apply g.injective
      exact hx.trans hgb.symm
    have hgxb : g x ≠ b := by
      intro hx
      apply hxa
      apply g.injective
      exact hx.trans hga.symm
    rw [Equiv.swap_apply_of_ne_of_ne hgxa hgxb,
      Equiv.swap_apply_of_ne_of_ne hxa hxb]

#print axioms AssemblyP1.Issue94FibreCommute.image_left_or_right
#print axioms AssemblyP1.Issue94FibreCommute.image_right_or_left
#print axioms AssemblyP1.Issue94FibreCommute.doubledPair_action
#print axioms AssemblyP1.Issue94FibreCommute.swap_commutes_vtxPreserving

end AssemblyP1.Issue94FibreCommute
