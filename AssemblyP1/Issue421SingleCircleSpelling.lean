import AssemblyP1.OrientedRigidity
import AssemblyP1.PopulationReduction
import AssemblyP1.ScalarPrimitiveSpellings
import AssemblyP1.RepeatAdapter

/-!
# Issue #421: exact spelling criterion for balanced flows and circular genomes

Forward: every nonzero finite integral balanced flow on a directed de Bruijn
graph with connected positive-edge support has a single circular Eulerian
spelling whose exact L-window count vector equals the flow (including total
edges fewer than read length). Converse: every circular spectrum is
balanced/connected.
-/

namespace AssemblyP1.Issue421

open OrientedRigidity
open PopulationReduction
open ScalarPrimitive

variable {α : Type} [DecidableEq α] [Fintype α]
variable {L : ℕ}

/-- Forward direction: nonzero finite integral balanced flow on a directed de
Bruijn graph (winPrefix/winSuffix on L-windows) with connected positive-edge
support has a single circular Eulerian spelling with exact L-window count
vector equal to the flow (total mass may be < L). -/
theorem single_circular_eulerian_spelling_of_balanced_flow
    (hL : 1 < L)
    (q : (Fin L → α) → ℕ)
    (hqpos : ∃ e, 0 < q e)
    (hbal : CircBalanced (V := Fin (L - 1) → α) (E := Fin L → α)
      winPrefix winSuffix q)
    (hsupp_conn : WeakConn (V := Fin (L - 1) → α) (E := Fin L → α)
      winPrefix winSuffix {e : Fin L → α | 0 < q e}) :
    ∃ (G : ℕ) (hG : 0 < G) (W : Fin G → α),
      specCount (L := L) hG W = q := by
  let supp := ({e : Fin L → α | 0 < q e} : Finset (Fin L → α))
  have hsupp : ∀ e, e ∈ supp ↔ 0 < q e := by intro e; simp [supp]
  have hne : supp.Nonempty := by
    obtain ⟨e, hepos⟩ := hqpos
    exact ⟨e, (hsupp e).mpr hepos⟩
  have hG : 0 < ∑ w : Fin L → α, q w := by
    obtain ⟨e, hepos⟩ := hqpos
    have hmem : e ∈ Finset.univ := Finset.mem_univ e
    have hle := Finset.single_le_sum (f := q) (fun _ _ => Nat.zero_le _) hmem
    omega
  obtain ⟨m, hm, W, hspec, _hlen⟩ :=
    ScalarPrimitive.spell_exists_circulation (α := α) (L := L) hG
      (fun _ : Fin (∑ w, q w) => Classical.arbitrary α) hL q hbal supp hsupp hne hsupp_conn
      (by simp)
  exact ⟨m, hm, W, hspec⟩

/-- Exact spelling criterion (issue #421). -/
theorem exact_spelling_criterion_issue421
    (hL : 1 < L)
    (q : (Fin L → α) → ℕ) :
    ((∃ e, 0 < q e) ∧
     CircBalanced (V := Fin (L - 1) → α) (E := Fin L → α) winPrefix winSuffix q ∧
     WeakConn (V := Fin (L - 1) → α) (E := Fin L → α) winPrefix winSuffix {e | 0 < q e})
    ↔
    (∃ (G : ℕ) (hG : 0 < G) (W : Fin G → α), specCount (L := L) hG W = q) := by
  constructor
  · intro ⟨hqpos, hbal, hconn⟩
    exact single_circular_eulerian_spelling_of_balanced_flow hL q hqpos hbal hconn
  · intro ⟨G, hG, W, hspec⟩
    have hbal := truth_balanced (α := α) (G := G) (L := L) hG W
    have hstrong := truth_strongly_connected (α := α) (G := G) (L := L) hG W
    have hconn := StronglyConnected.weaklyConnected
      (V := Fin (L - 1) → α) (E := Fin L → α)
      winPrefix winSuffix (genomeNodes hG W) (support hG W) hstrong
    have hqpos : ∃ e, 0 < q e := by
      rw [← hspec]
      have hne := support_nonempty (α := α) (G := G) (L := L) hG W
      obtain ⟨e, he⟩ := hne
      have hpos := truth_pos_on_support (L := L) hG W e he
      omega
    exact ⟨hqpos, hbal, hconn⟩

/-- Naming matching issue text more directly. -/
theorem balanced_oriented_flow_connected_support_spells_one_circular_genome
    (hL : 1 < L)
    (q : (Fin L → α) → ℕ)
    (hqnonzero : ∃ e, 0 < q e)
    (hbal : CircBalanced (V := Fin (L - 1) → α) (E := Fin L → α) winPrefix winSuffix q)
    (hconn : WeakConn (V := Fin (L - 1) → α) (E := Fin L → α) winPrefix winSuffix {e | 0 < q e}) :
    ∃ (G : ℕ) (hG : 0 < G) (W : Fin G → α),
      specCount (L := L) hG W = q := by
  exact single_circular_eulerian_spelling_of_balanced_flow hL q hqnonzero hbal hconn

end AssemblyP1.Issue421
