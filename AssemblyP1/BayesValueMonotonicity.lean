import Mathlib
import AssemblyP1.FiniteBayesDecision
import AssemblyP1.IidMapMonotonicity

/-!
# Explicit Bayes value `V_n` and its `n → n+1` monotonicity (Antonina #269, target C)

This module states the exact target-C object of Antonina #269,

    V_n := ∑_{x : Fin n → R} max_{θ} (π θ * ∏_{i : Fin n} p θ (x i)),

as a first-class definition `bayesValue`, and proves directly that

    V_{n+1} ≥ V_n

for every `n` (including `n = 0`) under the only hypothesis actually needed:
each per-candidate read score is normalized, `∑_r p θ r = 1`.

It does **not** reprove the finite-sum lemmas of PR #174
(`AssemblyP1.FiniteBayesDecision`) or the merged iid bridge of PR #193
(`AssemblyP1.IidMapMonotonicity`).  Instead it is a pure bridge:

* `sum_sup'_eq_success` — the explicit `∑ max` form equals the merged
  `success`/`chooseMAP` form (the `chooseMAP` witness attains the `sup'`).
* `bayesValue_eq_mapSuccess` — hence `bayesValue` is exactly the merged
  `IidMapMonotonicity.mapSuccess`.
* `bayesValue_succ_eq_pairValue` / `pairValue_eq_mapSuccessSucc` — the literal
  `Fin (n+1) → R` sample is reindexed (via `Fin.snoc`) onto the pair form used
  by `IidMapMonotonicity.mapSuccessSucc`.

The monotonicity then follows by chaining the merged theorem
`IidMapMonotonicity.iid_map_success_monotone`.  Scope is unchanged and explicit:
prior-**averaged** success, fixed iid observation model, no per-true-genome
claim (see `AssemblyP1.GenomeOrbitAdapter.PerTruthDrop`), no conditioning on
coverage (Antonina #266), no MB09 product-binomial surrogate.  Ties are handled
by the constructive `chooseMAP` maximizer; no uniqueness is claimed.
-/

namespace AssemblyP1.BayesValueMonotonicity

open Finset BigOperators

/-- The `(Fin n → R) × R ≃ Fin (n+1) → R` reindexing `(x, r) ↦ Fin.snoc x r`
that separates the last read from the first `n`. -/
def snocEquiv (R : Type*) (n : ℕ) : ((Fin n → R) × R) ≃ (Fin (n + 1) → R) where
  toFun p := Fin.snoc p.1 p.2
  invFun y := (Fin.init y, y (Fin.last n))
  left_inv := by
    rintro ⟨x, r⟩
    simp [Fin.init_snoc, Fin.snoc_last]
  right_inv := by
    intro y
    simp [Fin.snoc_init_self]

/-- The last-read separation `Fin.snoc` commutes with the iid joint mass: the
`(n+1)`-read joint mass at `Fin.snoc x r` is the pair joint mass at `(x, r)`. -/
theorem iidJoint_snoc {Θ R : Type*} [Fintype R] (π : Θ → ℝ) (p : Θ → R → ℝ)
    (n : ℕ) (θ : Θ) (x : Fin n → R) (r : R) :
    IidMapMonotonicity.iidJoint π p (n + 1) θ (Fin.snoc x r)
      = IidMapMonotonicity.iidJointSucc π p n θ x r := by
  simp only [IidMapMonotonicity.iidJoint, IidMapMonotonicity.iidJointSucc,
    Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  ring

/-- The explicit `∑_x max_θ J θ x` Bayes value equals the merged
`success`/`chooseMAP` form: the constructive `chooseMAP` witness attains the
finite `sup'`. -/
theorem sum_sup'_eq_success {Θ X : Type*} [Fintype Θ] [DecidableEq Θ] [Nonempty Θ]
    [Fintype X] (J : Θ → X → ℝ) :
    (∑ x : X, Finset.sup' Finset.univ
        (Finset.univ_nonempty : (Finset.univ : Finset Θ).Nonempty) (fun θ => J θ x))
      = FiniteBayesDecision.success J (FiniteBayesDecision.chooseMAP J) := by
  rw [FiniteBayesDecision.success_eq_observation_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply le_antisymm
  · exact Finset.sup'_le Finset.univ_nonempty (fun θ => J θ x)
      (fun θ _ => FiniteBayesDecision.chooseMAP_maximizes J x θ)
  · exact Finset.le_sup' (fun θ => J θ x)
      (Finset.mem_univ (FiniteBayesDecision.chooseMAP J x))

/-- **Exact Bayes-optimal zero-one value at sample size `n`.**
`V_n = ∑_{x : Fin n → R} max_θ (π θ * ∏ i, p θ (x i))`. -/
noncomputable def bayesValue {Θ R : Type*} [Fintype Θ] [Nonempty Θ] [Fintype R]
    (π : Θ → ℝ) (p : Θ → R → ℝ) (n : ℕ) : ℝ :=
  ∑ x : Fin n → R,
    Finset.sup' Finset.univ
      (Finset.univ_nonempty : (Finset.univ : Finset Θ).Nonempty)
      (fun θ => IidMapMonotonicity.iidJoint π p n θ x)

/-- Pair-indexed Bayes value, matching `IidMapMonotonicity.mapSuccessSucc`'s
`(x, r)` sample representation. -/
noncomputable def pairValue {Θ R : Type*} [Fintype Θ] [Nonempty Θ] [Fintype R]
    (π : Θ → ℝ) (p : Θ → R → ℝ) (n : ℕ) : ℝ :=
  ∑ xr : (Fin n → R) × R,
    Finset.sup' Finset.univ
      (Finset.univ_nonempty : (Finset.univ : Finset Θ).Nonempty)
      (fun θ => IidMapMonotonicity.iidJointSucc π p n θ xr.1 xr.2)

/-- The literal `V_n` equals the merged `IidMapMonotonicity.mapSuccess`. -/
theorem bayesValue_eq_mapSuccess {Θ R : Type*} [Fintype Θ] [DecidableEq Θ]
    [Nonempty Θ] [Fintype R] (π : Θ → ℝ) (p : Θ → R → ℝ) (n : ℕ) :
    bayesValue π p n = IidMapMonotonicity.mapSuccess π p n := by
  unfold bayesValue IidMapMonotonicity.mapSuccess
  exact sum_sup'_eq_success (IidMapMonotonicity.iidJoint π p n)

/-- The pair-indexed Bayes value equals the merged `mapSuccessSucc`. -/
theorem pairValue_eq_mapSuccessSucc {Θ R : Type*} [Fintype Θ] [DecidableEq Θ]
    [Nonempty Θ] [Fintype R] (π : Θ → ℝ) (p : Θ → R → ℝ) (n : ℕ) :
    pairValue π p n = IidMapMonotonicity.mapSuccessSucc π p n := by
  have h := sum_sup'_eq_success
    (fun θ (xr : (Fin n → R) × R) =>
      IidMapMonotonicity.iidJointSucc π p n θ xr.1 xr.2)
  unfold pairValue IidMapMonotonicity.mapSuccessSucc
  rw [h, FiniteBayesDecision.success_eq_observation_sum, Fintype.sum_prod_type]

/-- The literal `Fin (n+1)` Bayes value equals the pair-indexed Bayes value,
via the `Fin.snoc` reindexing and the last-read separation of the iid mass. -/
theorem bayesValue_succ_eq_pairValue {Θ R : Type*} [Fintype Θ] [Nonempty Θ]
    [Fintype R] (π : Θ → ℝ) (p : Θ → R → ℝ) (n : ℕ) :
    bayesValue π p (n + 1) = pairValue π p n := by
  unfold bayesValue pairValue
  trans ∑ xr : (Fin n → R) × R,
      Finset.sup' Finset.univ
        (Finset.univ_nonempty : (Finset.univ : Finset Θ).Nonempty)
        (fun θ => IidMapMonotonicity.iidJoint π p (n + 1) θ (snocEquiv R n xr))
  · exact (Fintype.sum_equiv (snocEquiv R n)
      (fun xr : (Fin n → R) × R =>
        Finset.sup' Finset.univ
          (Finset.univ_nonempty : (Finset.univ : Finset Θ).Nonempty)
          (fun θ => IidMapMonotonicity.iidJoint π p (n + 1) θ (snocEquiv R n xr)))
      (fun y : Fin (n + 1) → R =>
        Finset.sup' Finset.univ
          (Finset.univ_nonempty : (Finset.univ : Finset Θ).Nonempty)
          (fun θ => IidMapMonotonicity.iidJoint π p (n + 1) θ y))
      (fun _ => rfl)).symm
  · apply Finset.sum_congr rfl
    intro xr _
    apply Finset.sup'_congr (Finset.univ_nonempty)
    · rfl
    · intro θ _
      exact iidJoint_snoc π p n θ xr.1 xr.2

/-- **Antonina #269 target C (exact statement).**  The Bayes-optimal
prior-averaged zero-one value `V_n = ∑_x max_θ (π θ * ∏_i p θ (x_i))` is
nondecreasing in the number of iid reads, for every `n` including `0`.  The only
hypothesis is per-candidate normalization `∑_r p θ r = 1`.  This is
prior-averaged only; per-true-genome success may decrease
(`GenomeOrbitAdapter.PerTruthDrop.perTruth_true_drops`). -/
theorem bayesValue_succ_ge {Θ R : Type*} [Fintype Θ] [DecidableEq Θ] [Nonempty Θ]
    [Fintype R] (π : Θ → ℝ) (p : Θ → R → ℝ) (n : ℕ)
    (hnorm : ∀ θ, ∑ r : R, p θ r = 1) :
    bayesValue π p n ≤ bayesValue π p (n + 1) := by
  calc bayesValue π p n
      = IidMapMonotonicity.mapSuccess π p n := bayesValue_eq_mapSuccess π p n
    _ ≤ IidMapMonotonicity.mapSuccessSucc π p n :=
        IidMapMonotonicity.iid_map_success_monotone π p n hnorm
    _ = pairValue π p n := (pairValue_eq_mapSuccessSucc π p n).symm
    _ = bayesValue π p (n + 1) := (bayesValue_succ_eq_pairValue π p n).symm

/-- Iterated form: `V_n` is nondecreasing along `≤` on sample sizes. -/
theorem bayesValue_mono {Θ R : Type*} [Fintype Θ] [DecidableEq Θ] [Nonempty Θ]
    [Fintype R] (π : Θ → ℝ) (p : Θ → R → ℝ)
    (hnorm : ∀ θ, ∑ r : R, p θ r = 1) {n m : ℕ} (hnm : n ≤ m) :
    bayesValue π p n ≤ bayesValue π p m := by
  induction hnm with
  | refl => exact le_rfl
  | step _ ih => exact le_trans ih (bayesValue_succ_ge π p _ hnorm)

#print axioms iidJoint_snoc
#print axioms sum_sup'_eq_success
#print axioms bayesValue_eq_mapSuccess
#print axioms pairValue_eq_mapSuccessSucc
#print axioms bayesValue_succ_eq_pairValue
#print axioms bayesValue_succ_ge
#print axioms bayesValue_mono

end AssemblyP1.BayesValueMonotonicity
