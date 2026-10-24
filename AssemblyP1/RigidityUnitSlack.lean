import AssemblyP1.GraverRigidity

set_option linter.unusedSectionVars false

/-!
# Unit-slack rigidity lemma (issue #257)

Small general fact used by per-support exact criteria (e.g. the `AATATT`/`AATT`
support analysis): when the total mass `G` equals the number of support edges,
positivity alone forces every feasible circulation to be the all-ones vector,
hence any feasible circulation of that total is rigid.

This is the "forward direction" (`G = |E|` forces uniqueness) of exact
per-support characterizations such as `aatatt_rigid_iff` (slack branch). It is
stated here in full generality over `AssemblyP1.GraverRigidity` definitions,
with no repeat bound, throughput cap, or connectivity hypothesis. It does not
claim any repeat restriction is iff: the `ATATAT` rigid directed cycle already
refutes the necessity of "no triple repeat".
-/

namespace AssemblyP1.RigidityUnitSlack

open Finset BigOperators
open AssemblyP1.GraverRigidity

variable {V E : Type} [DecidableEq V] [DecidableEq E] [Fintype E]

/-- Every feasible circulation of total `G = |E|` is the all-ones vector. -/
theorem feasible_eq_one_of_total_eq_card (tail head : E → V) (nodes : Finset V)
    (B : E → ℤ) (G : ℕ) (hG : G = Fintype.card E)
    (hB : Feasible tail head nodes G B) :
    B = fun _ => 1 := by
  obtain ⟨hpos, _, hsum⟩ := hB
  have h1 : (∑ _e ∈ (Finset.univ : Finset E), (1 : ℤ))
      = ((Fintype.card E : ℕ) : ℤ) := by simp
  have hsub : ∑ e ∈ (Finset.univ : Finset E), (B e - 1) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, h1, hG, sub_self]
  have hnn : ∀ i ∈ (Finset.univ : Finset E), (0 : ℤ) ≤ B i - 1 := by
    intro i _
    have := hpos i
    omega
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsub
  funext e
  have he := hall e (Finset.mem_univ e)
  have := hpos e
  omega

/-- **Unit-slack rigidity.** Any feasible circulation whose total equals the
support size is rigid. -/
theorem rigid_of_total_eq_card (tail head : E → V) (nodes : Finset V)
    (A : E → ℤ) (G : ℕ) (hG : G = Fintype.card E)
    (hA : Feasible tail head nodes G A) :
    Rigid tail head nodes A G := by
  have hA1 : A = fun _ => 1 :=
    feasible_eq_one_of_total_eq_card tail head nodes A G hG hA
  intro B hBpos hBbal hBsum
  rw [hA1, feasible_eq_one_of_total_eq_card tail head nodes B G hG ⟨hBpos, hBbal, hBsum⟩]

end AssemblyP1.RigidityUnitSlack
