import AssemblyP1.BBTCrossingCoalesce

/-!
# Board 94: doubled-fibre swaps commute with label-preserving equivalences

Under primitive P2, every (L-1)-mer fibre has cardinality at most two.
Consequently, once two distinct starts a,b have the same vertex label, any
label-preserving equivalence must permute exactly the pair {a,b}. Mathlib's
naturality law for swaps under injective maps then says swap a b commutes
with that equivalence.

This is the local commutation fact needed by the ladder-antiderivative
component-deletion route. It deliberately assumes no involution property of
the residual equivalence.
-/

namespace AssemblyP1.Issue94FibreCommute

open AssemblyP1
open AssemblyP1.OrientedRigidity
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.P2RepeatResidual
open AssemblyP1.BBTCrossingCoalesce

variable {α : Type} [DecidableEq α] {G L : ℕ} (hG : 0 < G) (S : Fin G → α)

theorem swap_comm_of_vtxPreserving_equiv
    {a b : Fin G} (hL : 2 ≤ L) (hLG : L ≤ G)
    (hprim : RepeatAdapter.IsPrimitive hG S) (hP2 : P2 hG L S)
    (hab : a ≠ b) (hvab : vtx hG L S a = vtx hG L S b)
    (f : Fin G ≃ Fin G)
    (hf : ∀ x : Fin G, vtx hG L S (f x) = vtx hG L S x) :
    (Equiv.swap a b : Fin G → Fin G) ∘ f = f ∘ Equiv.swap a b := by
  by_cases hfa : f a = a
  · have hfba : f b ≠ a := by
      intro h
      apply hab
      apply f.injective
      exact hfa.trans h.symm
    have hvafb : vtx hG L S a = vtx hG L S (f b) :=
      hvab.trans (hf b).symm
    have hfb : f b = b := by
      exact (three_starts_ne (a := a) (b := b) (c := f b)
        hG S hL hLG hprim hP2 hvab hvafb hab (Ne.symm hfba)).symm
    have hnat := f.injective.swap_comp a b
    rw [hfa, hfb] at hnat
    exact hnat
  · have hfab : f a = b := by
      exact (three_starts_ne (a := a) (b := b) (c := f a)
        hG S hL hLG hprim hP2 hvab (hf a).symm hab (Ne.symm hfa)).symm
    have hfbb : f b ≠ b := by
      intro h
      apply hab
      apply f.injective
      exact hfab.trans h.symm
    have hfb : f b = a := by
      exact (three_starts_ne (a := b) (b := a) (c := f b)
        hG S hL hLG hprim hP2 hvab.symm (hf b).symm hab.symm (Ne.symm hfbb)).symm
    have hnat := f.injective.swap_comp a b
    rw [hfab, hfb, Equiv.swap_comm b a] at hnat
    exact hnat

end AssemblyP1.Issue94FibreCommute
