import AssemblyP1.BBTUniqueEulerian

/-! Probe: does the `traverses` clause alone imply `VertexCycleEq σ refl`? -/

namespace Probe94

open SourceFaithfulIs
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTUniqueEulerian

set_option maxRecDepth 10000

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)

theorem vtx_rotAdd_shift {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)
    (n : ℕ) (x : Fin G) (d : Fin (L - 1)) :
    vtx hG L S (rotAdd hG n x) d = cyc hG S (x.val + n + d.val) := by
  simp only [vtx, nodeWindow]
  show cyc hG S ((rotAdd hG n x).val + d.val) = cyc hG S (x.val + n + d.val)
  have h1 : ((rotAdd hG n x).val + d.val) % G = (x.val + n + d.val) % G := by
    show (((x.val + n) % G) + d.val) % G = (x.val + n + d.val) % G
    rw [← mod_add_shl (x.val + n) d.val, Nat.add_assoc]
  rw [cyc_congr hG S _ _ h1]

theorem probe_traverses_gives_vertexCycleEq {σ : Fin G ≃ Fin G}
    (htr : ∀ i : Fin G, vtx hG L S (σ (nextPos hG i)) = vtx hG L S (nextPos hG (σ i))) :
    VertexCycleEq hG L S σ (Equiv.refl (α := Fin G)) :=
  ⟨σ (origin hG), fun i => by
    have key : ∀ n : ℕ, ∀ j : Fin G,
        vtx hG L S (σ (rotAdd hG n j)) = vtx hG L S (rotAdd hG n (σ j)) := by
      intro n
      induction n with
      | zero => intro j; rw [rotAdd_zero]
      | succ m ih =>
          intro j
          have h := htr (rotAdd hG m j)
          rw [nextPos_rotAdd hG j m, ← ih (rotAdd hG m j), nextPos_rotAdd] at h
          exact h
    have h1 := key i.val (origin hG)
    have h2 : rotAdd hG i.val (origin hG) = i := Fin.ext (by simp [rotAdd, origin])
    rw [h2] at h1
    show vtx hG L S (σ i) = vtx hG L S (rotAdd hG (σ (origin hG)).val i)
    exact h1.symm
  ⟩

theorem probe_eulerianCycle_gives_vertexCycleEq {σ : Fin G ≃ Fin G}
    (hEul : EulerianCycle hG L S σ) :
    VertexCycleEq hG L S σ (Equiv.refl (α := Fin G)) :=
  probe_traverses_gives_vertexCycleEq hG L S hEul.1

#print axioms AssemblyP1.Probe94.probe_eulerianCycle_gives_vertexCycleEq
end Probe94
