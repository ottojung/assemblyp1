import AssemblyP1.PrimitiveP2FiniteClass

/-!
# Independent kernel axiom audit for the finite primitive-P2 class, and a
  non-vacuity witness (issue #281)

`AssemblyP1.PrimitiveP2FiniteClass` proves that the class of all primitive
P2-admissible circular genomes, over all positive genome lengths, is finite,
and uses that to drop the finite-candidate-family premise of
`AssemblyP1.FiniteReadRecoveryP2Complete.finite_primitiveP2_ML_confidence`.

This module only:

* re-checks the axiom dependencies of the endpoints independently;
* exhibits a concrete admissible genome, so the finite class is nonempty and
  the length bound `G ≤ 2 * q ^ (L - 1)` is attained at `q = 2`, `L = 2`.

Nothing here adds a hypothesis or restates a result.
-/

/-! ## Axioms used -/

#print axioms AssemblyP1.PrimitiveP2FiniteClass.nodeWindow_injective_of_short
#print axioms AssemblyP1.PrimitiveP2FiniteClass.primitive_P2_len_le
#print axioms AssemblyP1.PrimitiveP2FiniteClass.mem_shortGenomes
#print axioms AssemblyP1.PrimitiveP2FiniteClass.mem_primitiveP2Candidates
#print axioms AssemblyP1.PrimitiveP2FiniteClass.mem_nonRotationalCandidates_iff
#print axioms AssemblyP1.PrimitiveP2FiniteClass.primitiveP2Class_finite
#print axioms AssemblyP1.PrimitiveP2FiniteClass.all_primitiveP2_ML_confidence

/-! ## Non-vacuity: the binary word `1100` at read length `L = 2` -/

namespace AssemblyP1.PrimitiveP2FiniteClassAudit

open AssemblyP1.PopulationReduction
open AssemblyP1.SourceFaithfulIs

/-- The circular binary word `1100`, as a `Fin 4 → Bool` word. -/
def w1100 : Fin 4 → Bool := fun i => i == 0 || i == 1

/-- `1100` as a genome: the non-vacuity witness for the finite candidate
class at `L = 2` over the binary alphabet. -/
def D1100 : Genome Bool := ⟨4, by omega, w1100⟩

theorem D1100_len : D1100.len = 4 := rfl
theorem D1100_sym : D1100.sym = w1100 := rfl

/-- `1100` is primitive. `H * q = 4` with `q > 1` forces `H ∈ {1, 2}`, hence
`0 % H = 2 % H`, so the repetition would have to identify the two distinct
symbols of the word. -/
theorem w1100_primitive : IsPrimitive w1100 := by
  intro h
  obtain ⟨H, hH, U, q, hq, hlen, hrep⟩ := h
  have hq2 : 2 ≤ q := by omega
  have hHle : H ≤ 2 := by
    have h2 : 2 * H ≤ q * H := Nat.mul_le_mul_right H hq2
    have h3 : q * H = 4 := by rw [Nat.mul_comm, hlen]
    have h4 : H * 2 ≤ 4 := by
      calc H * 2 = 2 * H := by rw [Nat.mul_comm]
        _ ≤ q * H := h2
        _ = 4 := h3
    omega
  have hH1 : H = 1 ∨ H = 2 := by omega
  have hdvd : H ∣ 2 := by
    rcases hH1 with h | h <;> subst h <;> decide
  have hkey : w1100 0 = w1100 2 := by
    have h1 : w1100 0 = U ⟨(0 : ℕ) % H, Nat.mod_lt _ hH⟩ := hrep 0
    have h2 : w1100 2 = U ⟨(2 : ℕ) % H, Nat.mod_lt _ hH⟩ := hrep 2
    rw [h1, h2]
    congr 1
    simp [Nat.mod_eq_zero_of_dvd hdvd]
  simp [w1100] at hkey

/-- `1100` has no maximal triple repeat of any length, so it satisfies P2 at
every read length `L ≥ 2`; the exhibited case is `L = 2`, where P2 forbids
maximal triple repeats of length `≥ 1`. -/
theorem w1100_P2 : AssemblyP1.P2 (by omega : 0 < 4) 2 w1100 := by
  unfold AssemblyP1.P2 AssemblyP1.mkGenome
  decide

/-- `1100` is primitive-P2 admissible at read length `2`. -/
theorem w1100_adm :
    AssemblyP1.PopulationUniqueness.AdmClass 2 (by omega : 0 < 4) w1100 :=
  ⟨w1100_primitive, w1100_P2⟩

/-- **Non-vacuity of the finite candidate class at `L = 2`.** The admissible
circular genome `1100` of length `4` exists, so the finite family constructed
from the length bound is not the empty set. -/
theorem candidateClass_nonempty_binary_L2 :
    ∃ D : Genome Bool,
      AssemblyP1.PopulationUniqueness.AdmClass 2 D.len_pos D.sym ∧ D.len = 4 :=
  ⟨D1100, by exact w1100_adm, D1100_len⟩

/-- The length bound `G ≤ 2 * q ^ (L - 1)` is attained: at `L = 2` over the
binary alphabet it gives `4`, and `1100` is an admissible genome of length
`4`. The bound is therefore tight, not merely an upper estimate. -/
theorem lenBound_tight_binary_L2 :
    (AssemblyP1.PrimitiveP2FiniteClass.maxLen (α := Bool) 2) = 4 ∧
      ∃ D : Genome Bool,
        AssemblyP1.PopulationUniqueness.AdmClass 2 D.len_pos D.sym ∧ D.len = 4 :=
  ⟨(by decide), candidateClass_nonempty_binary_L2⟩

/-- The nonempty class really reaches the finite family: `1100` is a member of
`primitiveP2Candidates`, so the family the ML theorem ranges over is inhabited
whenever the admissible class is. -/
theorem witness_in_candidates :
    D1100 ∈ AssemblyP1.PrimitiveP2FiniteClass.primitiveP2Candidates 2 :=
  AssemblyP1.PrimitiveP2FiniteClass.mem_primitiveP2Candidates
    (hL := (by omega : 2 ≤ 2)) (D := D1100) (by exact w1100_adm)

end AssemblyP1.PrimitiveP2FiniteClassAudit
