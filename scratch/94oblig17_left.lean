import AssemblyP1.BBTCandidateTransfer

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace AssemblyP1.BBTEulerian

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1
open AssemblyP1.BBTEulerianSearch

variable {α : Type} [DecidableEq α]

theorem rotEquiv_shift_flip {G : ℕ} (hG : 0 < G) {D S : Fin G → α} (k : ℕ)
    (hk : ∀ i : Fin G, D ⟨(i.val + k) % G, Nat.mod_lt _ hG⟩ = S i) :
    ∀ i : Fin G, D i = S ⟨(i.val + (G - k % G)) % G, Nat.mod_lt _ hG⟩ := by
  intro i
  have hk' : ∀ r : Fin G, D ⟨(r.val + k) % G, Nat.mod_lt _ hG⟩ = S r := by
    intro r
    have h := hk ⟨r.val, r.isLt⟩
    simpa only [Nat.mod_eq_of_lt r.isLt] using h
  have hr : ((i.val + (G - k % G)) % G + k % G) % G = i.val :=
    rotAdd_neg_cancel hG (k % G) i.val i.isLt (Nat.mod_lt _ hG)
  have hDi : i = ⟨((i.val + (G - k % G)) % G + k % G) % G, Nat.mod_lt _ hG⟩ :=
    Fin.ext hr.symm
  have := hk' ⟨(i.val + (G - k % G)) % G, Nat.mod_lt _ hG⟩
  rw [hDi] at this
  exact this

theorem rotEquiv_flip {G : ℕ} (hG : 0 < G) {D S : Fin G → α} (hR : RotEquiv hG D S) :
    ∃ k : ℕ, ∀ i : Fin G, D i = S ⟨(i.val + (G - k % G)) % G, Nat.mod_lt _ hG⟩ := by
  obtain ⟨k, hk⟩ := hR
  exact ⟨k, rotEquiv_shift_flip hG k hk⟩

theorem vtx_pullback {G : ℕ} (hG : 0 < G) {L : ℕ} (hL : 1 ≤ L)
    {S E : Fin G → α} {σ : Fin G → Fin G} (hm : Matching (L := L) hG S E σ)
    (s : Fin G) : vtx hG L S (pullback hG L S E hm.1 s) = vtx hG L E s := by
  have hwin := pullback_window hG L S E hm s
  unfold vtx nodeWindow
  funext d
  have hd : d.val < L := by
    have h := d.isLt
    omega
  have he := congrArg (fun f : Fin L → α => f ⟨d.val, hd⟩) hwin
  unfold window cyc at he
  exact he

theorem vertexCycleEq_pullback_of_RotEquiv {G : ℕ} (hG : 0 < G) {L : ℕ} (hL : 2 ≤ L)
    {S E : Fin G → α} {σ : Fin G → Fin G} (hm : Matching (L := L) hG S E σ)
    (hR : RotEquiv hG E S) :
    VertexCycleEq hG L S (pullback hG L S E hm.1) (Equiv.refl (α := Fin G)) := by
  obtain ⟨k, hk⟩ := rotEquiv_flip hG hR
  refine ⟨⟨(G - k % G) % G, Nat.mod_lt _ hG⟩, ?_⟩
  intro i
  have hrot : rotAdd hG ((G - k % G) % G) (Equiv.refl (α := Fin G) i)
      = rotAdd hG (G - k % G) i := by
    simp only [Equiv.refl_apply]
    exact (rotAdd_mod hG (G - k % G) i).symm
  rw [hrot]
  unfold vtx nodeWindow
  funext d
  have hd : d.val < L := by
    have h := d.isLt
    omega
  have hwin := pullback_window hG L S E hm i
  have h1 := congrArg (fun f : Fin L → α => f ⟨d.val, hd⟩) hwin
  unfold window cyc at h1
  rw [hk ⟨(i.val + d.val) % G, Nat.mod_lt _ hG⟩] at h1
  have hEq : ((i.val + d.val) % G + (G - k % G)) % G
      = (rotAdd hG (G - k % G) i).val + d.val := by
    have hFin := Fin.mk.inj h1
    unfold rotAdd at hFin
    rw [Fin.mk.injEq] at hFin
    exact hFin.symm
  have hEq' : ((i.val + d.val) % G + (G - k % G)) % G
      = ((i.val + (G - k % G)) % G + d.val) % G := by
    rw [Nat.mod_add_mod, Nat.mod_add_mod (m := i.val + (G - k % G)) (n := G) (k := d.val),
      Nat.add_comm (G - k % G) d.val]
  unfold cyc rotAdd Equiv.refl_apply
  rw [hEq', ← hEq]
  rfl

end AssemblyP1.BBTEulerian
