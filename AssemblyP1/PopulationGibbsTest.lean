import AssemblyP1.PopulationGibbs

/-!
# Kernel checks for the population log-likelihood support-inclusion
semantics (issue #274)

The published convention of `def:population` is
`ℓpop_S(D) = -∞` **iff some word with `p_S(w) > 0` has `p_D(w) = 0`**,
i.e. iff `supp pS ⊄ supp pD`. A candidate with extra positive read
support has a finite log-likelihood. These checks pin that semantics on
concrete two-type instances:

* `pS = (1, 0)`, `pD = (1/2, 1/2)` over types `A, B`: the candidate has
  extra support, so the likelihood is finite and equals `log(1/2)` —
  the counterexample to the old equal-support (`SuppEq`) gate;
* equal support: the likelihood is finite and equals the self-likelihood;
* missing support `pS = (1/2, 1/2)`, `pD = (1, 0)`: the likelihood is `⊥`;
* the Gibbs inequality and the tie characterization hold on these
  concrete instances, and an extra-support candidate strictly loses.
-/

namespace AssemblyP1.PopulationGibbs

open BigOperators

variable {W : Type} [Fintype W]

/-- The truth distribution `(1, 0)` on two read types: only type `A` is
read. -/
noncomputable def pS2 : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0

/-- The candidate distribution `(1/2, 1/2)` on two read types: both types
are read, so the candidate has **extra** positive support. -/
noncomputable def pD2 : Fin 2 → ℝ := fun _ => (1 / 2 : ℝ)

/-- Both are genuine read distributions. -/
theorem pS2_isProb : IsProb pS2 := by
  refine ⟨fun w => ?_, ?_⟩
  · fin_cases w <;> simp [pS2]
  · rw [Fin.sum_univ_two]
    simp [pS2]

theorem pD2_isProb : IsProb pD2 := by
  refine ⟨fun _ => by norm_num [pD2], ?_⟩
  rw [Fin.sum_univ_two]
  simp [pD2]
  ring

/-- The truth's support is included in the candidate's: every word read
by `pS2` is read by `pD2`. -/
theorem pD2_suppSub : SuppSub pS2 pD2 := by
  intro w hw
  fin_cases w
  · simp [pS2] at hw
    simp [pD2]
  · simp [pS2] at hw

/-- The candidate's support is NOT included in the truth's: type `B` is
read by `pD2` but not by `pS2`. -/
theorem pS2_not_suppSub : ¬ SuppSub pD2 pS2 := by
  intro h
  have h1 := h 1 (by norm_num [pD2])
  simp [pS2] at h1

/-! ## The two-type counterexample, kernel-checked -/

/-- **The counterexample of issue #274.** With `pS = (1, 0)` and
`pD = (1/2, 1/2)` the candidate has extra positive support, so the
population log-likelihood is finite and equals `log(1/2)` — not `⊥`. -/
theorem popLogLik_counterexample :
    PopLogLik pS2 pD2 = (Real.log (1 / 2) : WithBot ℝ) := by
  rw [popLogLik_of pD2_suppSub]
  unfold PopLogLikValue
  rw [Fin.sum_univ_two]
  simp [pS2, pD2]

/-- The counterexample value is finite (not `-∞`). -/
theorem popLogLik_counterexample_ne_bot :
    PopLogLik pS2 pD2 ≠ (⊥ : WithBot ℝ) := by
  rw [popLogLik_counterexample]
  exact WithBot.coe_ne_bot

/-- The self-likelihood of the truth is `0` (`log 1 = 0`). -/
theorem popLogLik_self_two :
    PopLogLik pS2 pS2 = (0 : WithBot ℝ) := by
  rw [popLogLik_self]
  unfold PopLogLikValue
  rw [Fin.sum_univ_two]
  simp [pS2, Real.log_zero]

/-- An extra-support candidate **strictly loses**: `log(1/2) < 0`. -/
theorem popLogLik_counterexample_lt_self :
    PopLogLik pS2 pD2 < PopLogLik pS2 pS2 := by
  rw [popLogLik_counterexample, popLogLik_self_two]
  refine WithBot.coe_lt_coe.mpr ?_
  have hlt := Real.log_lt_log (by norm_num : (0:ℝ) < 1 / 2) (by norm_num : (1/2:ℝ) < 1)
  simpa [Real.log_one] using hlt

/-! ## Equal support -/

/-- Equal supports: the likelihood is finite and equals the
self-likelihood. -/
theorem popLogLik_equal_support :
    PopLogLik pD2 pD2 = PopLogLik pD2 pD2 ∧
      PopLogLik pD2 pD2 = (Real.log (1 / 2) : WithBot ℝ) := by
  refine ⟨rfl, ?_⟩
  rw [popLogLik_self]
  have hval : PopLogLikValue pD2 pD2 = Real.log (1 / 2) := by
    unfold PopLogLikValue
    rw [Fin.sum_univ_two]
    simp [pD2]
    ring
  rw [hval]

/-! ## Missing support -/

/-- **Missing support gives `-∞`.** With `pS = (1/2, 1/2)` and
`pD = (1, 0)` a word read by the truth is not read by the candidate, so
the population log-likelihood is `⊥`. -/
theorem popLogLik_missing_support :
    PopLogLik pD2 pS2 = (⊥ : WithBot ℝ) :=
  popLogLik_bot_of pS2_not_suppSub

/-- The missing-support likelihood is genuinely `-∞`, not finite. -/
theorem popLogLik_missing_support_eq_bot :
    PopLogLik pD2 pS2 = (⊥ : WithBot ℝ) ↔ ¬ SuppSub pD2 pS2 :=
  popLogLik_eq_bot

/-! ## Gibbs and ties on the concrete instances -/

/-- Gibbs holds on the counterexample instance: the extra-support
candidate still loses (weakly). -/
theorem popLogLik_le_self_counterexample :
    PopLogLik pS2 pD2 ≤ PopLogLik pS2 pS2 :=
  popLogLik_le_self pS2_isProb pD2_isProb pD2_suppSub

/-- Gibbs holds with no support hypothesis at all. -/
theorem popLogLik_le_self'_counterexample :
    PopLogLik pS2 pD2 ≤ PopLogLik pS2 pS2 :=
  popLogLik_le_self' pS2_isProb pD2_isProb

/-- The tie characterization on the counterexample: no tie, because the
distributions differ. -/
theorem popTie_counterexample :
    (PopLogLik pS2 pD2 = PopLogLik pS2 pS2) ↔ pD2 = pS2 :=
  popTie_iff pS2_isProb pD2_isProb

/-- A tie with an equal-support candidate holds exactly when the
distributions are equal. -/
theorem popTie_equal_support :
    (PopLogLik pD2 pD2 = PopLogLik pD2 pD2) ↔ pD2 = pD2 :=
  popTie_iff pD2_isProb pD2_isProb

/-! ## Axiom boundary of the repaired layer -/

#print axioms AssemblyP1.PopulationGibbs.PopLogLik
#print axioms AssemblyP1.PopulationGibbs.popLogLik_le_self
#print axioms AssemblyP1.PopulationGibbs.popLogLik_le_self'
#print axioms AssemblyP1.PopulationGibbs.popTie_iff
#print axioms AssemblyP1.PopulationGibbs.popLogLik_counterexample
#print axioms AssemblyP1.PopulationGibbs.popLogLik_missing_support

end AssemblyP1.PopulationGibbs
