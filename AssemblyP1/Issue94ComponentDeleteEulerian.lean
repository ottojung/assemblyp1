import AssemblyP1.Issue94ComponentAlgebra
import AssemblyP1.Issue94TW5Single

namespace AssemblyP1.Issue94ComponentDeleteEulerian

open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.Issue94ComponentAlgebra
open AssemblyP1.Issue94TW5Single

variable {α : Type} [DecidableEq α] {G : ℕ}

theorem delete_component_eulerian
    (hG : 0 < G) (L : ℕ) (S : Fin G → α)
    (sigma g c h : Fin G ≃ Fin G)
    (hAlt : ∀ x : Fin G, AltF hG sigma x = c (h x))
    (hch : ∀ x : Fin G, c (h x) = h (c x))
    (hgh : ∀ x : Fin G, g (h x) = h (g x))
    (hcob : ∀ x : Fin G,
      c x = g.symm (nextPos hG (g (prevPos hG x))))
    (hgVtx : ∀ x : Fin G, vtx hG L S (g x) = vtx hG L S x)
    (hhVtx : ∀ x : Fin G, vtx hG L S (h x) = vtx hG L S x) :
    let tau := sigma.trans g
    (∀ q : Fin G, AltF hG tau q = h q) ∧
      (∀ i : Fin G, vtx hG L S (tau i) = vtx hG L S (sigma i)) ∧
      EulerianCycle hG L S tau := by
  let tau := sigma.trans g
  have hAltTau : ∀ q : Fin G, AltF hG tau q = h q := by
    simpa [tau] using
      (delete_component hG sigma g c h hAlt hch hgh hcob)
  have hVtxTau :
      ∀ i : Fin G, vtx hG L S (tau i) = vtx hG L S (sigma i) := by
    intro i
    change vtx hG L S (g (sigma i)) = vtx hG L S (sigma i)
    exact hgVtx (sigma i)
  have hTrav :
      ∀ i : Fin G,
        vtx hG L S (tau (nextPos hG i)) =
          vtx hG L S (nextPos hG (tau i)) := by
    intro i
    let q : Fin G := tau i
    have hSucc : Succ hG tau q = tau (nextPos hG i) := by
      simp [Succ, q]
    calc
      vtx hG L S (tau (nextPos hG i))
          = vtx hG L S (Succ hG tau q) := by rw [hSucc]
      _ = vtx hG L S (AltF hG tau (nextPos hG q)) := by
        rw [AltF_succ hG tau q]
      _ = vtx hG L S (h (nextPos hG q)) := by rw [hAltTau]
      _ = vtx hG L S (nextPos hG q) := hhVtx _
      _ = vtx hG L S (nextPos hG (tau i)) := rfl
  have hEul : EulerianCycle hG L S tau :=
    (eulerianCycle_iff_traverses hG L S tau).2 hTrav
  exact ⟨hAltTau, hVtxTau, hEul⟩

#print axioms AssemblyP1.Issue94ComponentDeleteEulerian.delete_component_eulerian

end AssemblyP1.Issue94ComponentDeleteEulerian
