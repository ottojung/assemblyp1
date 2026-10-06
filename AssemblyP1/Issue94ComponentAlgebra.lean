import AssemblyP1.BBTUniqueEulerian

/-!
# Board 94: pure algebra for deleting an AltF component

Write `rho = nextPos hG` and `f = AltF hG sigma`.  If a listing is
postcomposed on its values by an equivalence `g`, i.e. `sigma' = g ∘ sigma`,
then

  AltF sigma' = g ∘ f ∘ rho ∘ g^{-1} ∘ rho^{-1}.

Suppose `f = c ∘ h`, the component `c` commutes with the residual `h`, `g`
commutes with `h`, and

  c = g^{-1} ∘ rho ∘ g ∘ rho^{-1}.

Then the new AltF is exactly `h`.  This module is pure permutation algebra:
no word, P2, repeat, or interlacement assumptions occur.
-/

namespace AssemblyP1.Issue94ComponentAlgebra

open AssemblyP1
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTChords
open AssemblyP1.BBTUniqueEulerian

variable {G : ℕ} (hG : 0 < G)

/-- Postcomposing the values of a listing by `g` conjugates its successor,
which gives this exact update formula for `AltF`. -/
theorem altF_postcompose (sigma g : Fin G ≃ Fin G) (q : Fin G) :
    AltF hG (sigma.trans g) q =
      g (AltF hG sigma (nextPos hG (g.symm (prevPos hG q)))) := by
  unfold AltF Succ
  simp only [Equiv.trans_apply]
  have hsymm : (sigma.trans g).symm (prevPos hG q) =
      sigma.symm (g.symm (prevPos hG q)) := rfl
  rw [hsymm]
  congr 1
  congr 1
  rw [prevNext hG]

/-- Pure component-deletion algebra.  `c` is the component being removed,
`h` the residual switch permutation, and `g` its discrete antiderivative. -/
theorem delete_component
    (sigma g c h : Fin G ≃ Fin G)
    (hAlt : ∀ x : Fin G, AltF hG sigma x = c (h x))
    (hch : ∀ x : Fin G, c (h x) = h (c x))
    (hgh : ∀ x : Fin G, g (h x) = h (g x))
    (hcob : ∀ x : Fin G,
      c x = g.symm (nextPos hG (g (prevPos hG x)))) :
    ∀ q : Fin G, AltF hG (sigma.trans g) q = h q := by
  intro q
  rw [altF_postcompose hG sigma g q]
  let y : Fin G := nextPos hG (g.symm (prevPos hG q))
  change g (AltF hG sigma y) = h q
  rw [hAlt y, hch y, hgh (c y), hcob y]
  have hy : prevPos hG y = g.symm (prevPos hG q) := by
    dsimp [y]
    rw [prevNext hG]
  rw [hy, Equiv.apply_symm_apply g (prevPos hG q)]
  rw [Equiv.apply_symm_apply g (nextPos hG (prevPos hG q))]
  exact congrArg h (nextPrev hG q)

#print axioms AssemblyP1.Issue94ComponentAlgebra.altF_postcompose
#print axioms AssemblyP1.Issue94ComponentAlgebra.delete_component

end AssemblyP1.Issue94ComponentAlgebra
