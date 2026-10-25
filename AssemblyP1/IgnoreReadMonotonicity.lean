import Mathlib
import AssemblyP1.FiniteBayesDecision
import AssemblyP1.IidMapMonotonicity
import AssemblyP1.BayesValueMonotonicity
import AssemblyP1.GenomeOrbitAdapter

/-!
# Prior-averaged MAP success is nondecreasing in the read count, by ignoring the last read (Antonina #269, target C)

Antonina #269 target C asks for a kernel-checked proof that the optimal
prior-averaged zero-one success of the finite iid read model

    V_n = ∑_{x : Fin n → R} max_{θ} (π θ * ∏_{i : Fin n} p θ (x i))

is **nondecreasing** in the number of reads `n`, by the proof route the target
names explicitly: construct, from a policy at `n` reads, the policy at `n + 1`
reads that *ignores the last read*, and invoke the finite optimality theorem
(`AssemblyP1.FiniteBayesDecision.chooseMAP_optimal`).  Because the ignored
read contributes only the factor `p θ r`, which sums to `1` over the read
alphabet under per-candidate normalization, the constructed policy's success at
`n + 1` reads equals the `n`-read success of the original policy; optimality
then lower-bounds `V_{n + 1}` by `V_n`.  Ties need no uniqueness: the
constructive `chooseMAP` witness handles them, exactly as in the merged
certificate `AssemblyP1.BayesOptimalityCertificate` (target B, not restated
here).

The second half of target C is the scope boundary, kernel-checked: the
monotonicity theorem makes **no** per-truth claim.  In the binary counterexample
model of the merged `AssemblyP1.GenomeOrbitAdapter.PerTruthDrop` (read alphabet
`{A, C}`, true candidate `p_true(A) = 4/5`, competitor `p_comp(A) = 1/2`,
uniform prior, deterministic ML policies with `≥` tie-breaking), the
prior-averaged MAP success increases from `13/20` (1 read) to `139/200`
(2 reads) while the success probability of the fixed true candidate strictly
drops from `4/5` to `16/25`.  The exact rational values `13/20` and `139/200`
are evaluated here in Lean by pinning the `chooseMAP` choices via the
unique-maximizer lemma `chooseMAP_unique_max`.

Explicit scope (no silent identifications):

* PRIOR-AVERAGED success under the fixed finite iid observation model, for
  every sample size `n` including `0`.  It is not a claim about each fixed
  true candidate, and not a global "ML is the best algorithm" claim.
* The only model hypothesis is per-candidate read normalization
  `∑ r, p θ r = 1`; positivity of `π` and `p` is needed only to read the
  numbers as probabilities, not for the inequalities.
* This is the finite Bayesian decision theorem, not the MB09 fixed-`N`
  product-binomial pseudo-likelihood and not the §6.2 feasible-flow objective.
  It preserves a clean separation from the event-conditional inference of
  #266: nothing here conditions on a truth-dependent event.
* The per-truth drop endpoints (`perTruth_true_one` / `perTruth_true_two` /
  `perTruth_true_drops`) are the merged `GenomeOrbitAdapter.PerTruthDrop`
  declarations (PR #200), reused, not reproven; this module adds only their
  exact prior-averaged values and the scope-boundary theorem that combines
  them with the monotonicity theorem.

No `sorry`, `admit`, `axiom`, or `native_decide`.
-/

set_option linter.unusedSectionVars false

namespace AssemblyP1.IgnoreReadMonotonicity

open Finset BigOperators

variable {Θ R : Type*} [Fintype R]

/-! ## 1. The ignore-last-read construction -/

/-- The policy on `n + 1` reads that **ignores the last read**: it applies the
`n`-read policy `d` to the first `n` reads. -/
def ignoreLast {Θ : Type*} {n : ℕ} (d : (Fin n → R) → Θ) : (Fin (n + 1) → R) → Θ :=
  fun x => d (Fin.init x)

/-! ## 2. The ignore-read bridge: success at `n + 1` equals success at `n` -/

/-- The success of the ignore-last-read policy at `n + 1` reads equals the
success of the original policy at `n` reads, because the read pmf is
normalized: the factor contributed by the ignored read, `p θ r`, sums to `1`
over the read alphabet. -/
theorem success_ignoreLast [Fintype Θ] [DecidableEq Θ] (π : Θ → ℝ) (p : Θ → R → ℝ)
    (n : ℕ) (d : (Fin n → R) → Θ) (hnorm : ∀ θ, ∑ r : R, p θ r = 1) :
    FiniteBayesDecision.success (IidMapMonotonicity.iidJoint π p (n + 1))
        (ignoreLast d)
      = FiniteBayesDecision.success (IidMapMonotonicity.iidJoint π p n) d := by
  rw [FiniteBayesDecision.success_eq_observation_sum,
    FiniteBayesDecision.success_eq_observation_sum]
  have hterm : ∀ (x : Fin n → R) (r : R),
      IidMapMonotonicity.iidJoint π p (n + 1)
          (ignoreLast d (Fin.snoc x r)) (Fin.snoc x r)
        = IidMapMonotonicity.iidJoint π p n (d x) x * p (d x) r := by
    intro x r
    simp only [ignoreLast, Fin.init_snoc]
    exact BayesValueMonotonicity.iidJoint_snoc π p n (d x) x r
  have hreindex :
      (∑ x : Fin (n + 1) → R, IidMapMonotonicity.iidJoint π p (n + 1)
          (ignoreLast d x) x)
        = ∑ xr : (Fin n → R) × R, IidMapMonotonicity.iidJoint π p n (d xr.1) xr.1
            * p (d xr.1) xr.2 := by
    have hre := (Fintype.sum_equiv (BayesValueMonotonicity.snocEquiv R n)
      (fun xr => IidMapMonotonicity.iidJoint π p (n + 1)
        (ignoreLast d (Fin.snoc xr.1 xr.2)) (Fin.snoc xr.1 xr.2))
      (fun y => IidMapMonotonicity.iidJoint π p (n + 1) (ignoreLast d y) y)
      (fun _ => rfl)).symm
    rw [hre]
    exact Finset.sum_congr rfl (fun xr _ => hterm xr.1 xr.2)
  rw [hreindex, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  simp only
  rw [← Finset.mul_sum, hnorm (d x), mul_one]

/-! ## 3. Target C: the monotonicity theorem, via optimality -/

/-- A unique maximizer is the value of the constructive `chooseMAP` witness. -/
theorem chooseMAP_unique_max [Fintype Θ] [Nonempty Θ] {X : Type*} [Fintype X]
    {J : Θ → X → ℝ} {x : X} {θ : Θ}
    (_hmax : ∀ θ', J θ' x ≤ J θ x) (hstrict : ∀ θ', θ' ≠ θ → J θ' x < J θ x) :
    FiniteBayesDecision.chooseMAP J x = θ := by
  by_contra hne
  have h1 := FiniteBayesDecision.chooseMAP_maximizes J x θ
  have h2 := hstrict _ hne
  linarith

/-- **Antonina #269 target C, exact statement.**  For the finite iid read model
with per-candidate normalized read scores, the prior-averaged zero-one success
of the MAP policy at `n + 1` reads is at least that at `n` reads, for every
`n` (including `0`).  Proof route (as the target requires): lift the
constructed `n`-read MAP policy to the `(n + 1)`-read policy that ignores the
last read; by the bridge `success_ignoreLast` its success is unchanged, and by
the finite optimality theorem (`chooseMAP_optimal`) no policy exceeds the
`(n + 1)`-read MAP value.  Ties are handled by the constructive `chooseMAP`
witness.  This is a prior-averaged statement only; per-truth success may
strictly drop (see `perTruthDrop_scope_separation` below). -/
theorem mapSuccess_ignoreRead_monotone [Fintype Θ] [DecidableEq Θ] [Nonempty Θ]
    (π : Θ → ℝ) (p : Θ → R → ℝ) (n : ℕ) (hnorm : ∀ θ, ∑ r : R, p θ r = 1) :
    IidMapMonotonicity.mapSuccess π p n ≤ IidMapMonotonicity.mapSuccess π p (n + 1) := by
  have hbridge := success_ignoreLast π p n
    (FiniteBayesDecision.chooseMAP (IidMapMonotonicity.iidJoint π p n)) hnorm
  have hopt := FiniteBayesDecision.chooseMAP_optimal
    (IidMapMonotonicity.iidJoint π p (n + 1))
    (ignoreLast (FiniteBayesDecision.chooseMAP
      (IidMapMonotonicity.iidJoint π p n)))
  unfold IidMapMonotonicity.mapSuccess
  rw [← hbridge]
  exact hopt

/-- Iterated form: the MAP value is nondecreasing along `≤` on sample sizes. -/
theorem mapSuccess_ignoreRead_mono [Fintype Θ] [DecidableEq Θ] [Nonempty Θ]
    (π : Θ → ℝ) (p : Θ → R → ℝ) (hnorm : ∀ θ, ∑ r : R, p θ r = 1)
    {n m : ℕ} (hnm : n ≤ m) :
    IidMapMonotonicity.mapSuccess π p n ≤ IidMapMonotonicity.mapSuccess π p m := by
  induction hnm with
  | refl => exact le_rfl
  | step _ ih => exact le_trans ih (mapSuccess_ignoreRead_monotone π p _ hnorm)

/-! ## 4. The per-truth drop counterexample (target C scope boundary) -/

/-- The uniform prior `1/2` of the counterexample model, as a real-valued
prior. -/
def halfℝ : GenomeOrbitAdapter.PerTruthDrop.Read → ℝ := fun _ => (1 / 2 : ℚ)

/-- The counterexample read scores `p_true(A) = 4/5`, `p_comp(A) = 1/2`,
coerced to the reals. -/
def readPℝ (θ w : GenomeOrbitAdapter.PerTruthDrop.Read) : ℝ :=
  (GenomeOrbitAdapter.PerTruthDrop.readP θ w : ℚ)

/-- The reindexing `(Fin 1 → Read) ≃ Read`, `x ↦ x 0`, used to enumerate the
one-read sample space. -/
def oneArrowRead : (Fin 1 → GenomeOrbitAdapter.PerTruthDrop.Read) ≃
    GenomeOrbitAdapter.PerTruthDrop.Read where
  toFun x := x 0
  invFun r := fun _ => r
  left_inv x := by
    rw [funext_iff]
    intro i
    cases i with
    | mk i hi =>
      have hi0 : i = 0 := by omega
      simp [hi0]
  right_inv r := rfl

/-- The counterexample read scores are normalized: each candidate's pmf sums to
`1`, so the monotonicity theorem applies to this model. -/
theorem perTruthDrop_normalized :
    ∀ θ : GenomeOrbitAdapter.PerTruthDrop.Read, ∑ r : GenomeOrbitAdapter.PerTruthDrop.Read,
      GenomeOrbitAdapter.PerTruthDrop.readP θ r = 1 := by
  intro θ
  fin_cases θ <;> simp only [Fin.sum_univ_two] <;>
    norm_num [GenomeOrbitAdapter.PerTruthDrop.readP]

/-- The real-valued normalization of the counterexample read scores, the exact
hypothesis of `mapSuccess_ignoreRead_monotone` instantiated to this model. -/
theorem perTruthDrop_normalized_real :
    ∀ θ : GenomeOrbitAdapter.PerTruthDrop.Read, ∑ r : GenomeOrbitAdapter.PerTruthDrop.Read,
      readPℝ θ r = 1 := by
  intro θ
  fin_cases θ <;> simp only [Fin.sum_univ_two, readPℝ] <;>
    norm_num [GenomeOrbitAdapter.PerTruthDrop.readP]

/-- At the one-read sample `A` the unique joint-mass maximizer is the true
candidate `0` (`(1/2)(4/5) = 2/5 > 1/4 = (1/2)(1/2)`), so the constructed MAP
policy returns `0`. -/
theorem chooseMAP_one_A :
    FiniteBayesDecision.chooseMAP (IidMapMonotonicity.iidJoint halfℝ readPℝ 1)
      (fun _ => (0 : GenomeOrbitAdapter.PerTruthDrop.Read))
      = (0 : GenomeOrbitAdapter.PerTruthDrop.Read) := by
  refine chooseMAP_unique_max ?_ ?_
  · intro θ'
    fin_cases θ' <;> norm_num [IidMapMonotonicity.iidJoint, readPℝ, halfℝ,
      GenomeOrbitAdapter.PerTruthDrop.readP, Fin.prod_univ_one]
  · intro θ' hne
    fin_cases θ' <;> norm_num [IidMapMonotonicity.iidJoint, readPℝ, halfℝ,
      GenomeOrbitAdapter.PerTruthDrop.readP, Fin.prod_univ_one] at *

/-- At the one-read sample `C` the unique maximizer is the competitor `1`
(`1/4 > 1/10`), so the constructed MAP policy returns `1`. -/
theorem chooseMAP_one_C :
    FiniteBayesDecision.chooseMAP (IidMapMonotonicity.iidJoint halfℝ readPℝ 1)
      (fun _ => (1 : GenomeOrbitAdapter.PerTruthDrop.Read))
      = (1 : GenomeOrbitAdapter.PerTruthDrop.Read) := by
  refine chooseMAP_unique_max ?_ ?_
  · intro θ'
    fin_cases θ' <;> norm_num [IidMapMonotonicity.iidJoint, readPℝ, halfℝ,
      GenomeOrbitAdapter.PerTruthDrop.readP, Fin.prod_univ_one]
  · intro θ' hne
    fin_cases θ' <;> norm_num [IidMapMonotonicity.iidJoint, readPℝ, halfℝ,
      GenomeOrbitAdapter.PerTruthDrop.readP, Fin.prod_univ_one] at *

/-- At the two-read sample `(A,A)` the unique maximizer is the true candidate `0`
(`8/25 > 1/8`), so the constructed MAP policy returns `0`. -/
theorem chooseMAP_two_aa :
    FiniteBayesDecision.chooseMAP (IidMapMonotonicity.iidJoint halfℝ readPℝ 2)
      (fun i => if i = 0 then (0 : GenomeOrbitAdapter.PerTruthDrop.Read)
        else (0 : GenomeOrbitAdapter.PerTruthDrop.Read))
      = (0 : GenomeOrbitAdapter.PerTruthDrop.Read) := by
  refine chooseMAP_unique_max ?_ ?_
  · intro θ'
    fin_cases θ' <;> norm_num [IidMapMonotonicity.iidJoint, readPℝ, halfℝ,
      GenomeOrbitAdapter.PerTruthDrop.readP, Fin.prod_univ_two]
  · intro θ' hne
    fin_cases θ' <;> norm_num [IidMapMonotonicity.iidJoint, readPℝ, halfℝ,
      GenomeOrbitAdapter.PerTruthDrop.readP, Fin.prod_univ_two] at *

/-- At the two-read sample `(A,C)` the unique maximizer is the competitor `1`
(`1/8 > 2/25`), so the constructed MAP policy returns `1`. -/
theorem chooseMAP_two_ac :
    FiniteBayesDecision.chooseMAP (IidMapMonotonicity.iidJoint halfℝ readPℝ 2)
      (fun i => if i = 0 then (0 : GenomeOrbitAdapter.PerTruthDrop.Read)
        else (1 : GenomeOrbitAdapter.PerTruthDrop.Read))
      = (1 : GenomeOrbitAdapter.PerTruthDrop.Read) := by
  refine chooseMAP_unique_max ?_ ?_
  · intro θ'
    fin_cases θ' <;> norm_num [IidMapMonotonicity.iidJoint, readPℝ, halfℝ,
      GenomeOrbitAdapter.PerTruthDrop.readP, Fin.prod_univ_two]
  · intro θ' hne
    fin_cases θ' <;> norm_num [IidMapMonotonicity.iidJoint, readPℝ, halfℝ,
      GenomeOrbitAdapter.PerTruthDrop.readP, Fin.prod_univ_two] at *

/-- At the two-read sample `(C,A)` the unique maximizer is the competitor `1`
(`1/8 > 2/25`), so the constructed MAP policy returns `1`. -/
theorem chooseMAP_two_ca :
    FiniteBayesDecision.chooseMAP (IidMapMonotonicity.iidJoint halfℝ readPℝ 2)
      (fun i => if i = 0 then (1 : GenomeOrbitAdapter.PerTruthDrop.Read)
        else (0 : GenomeOrbitAdapter.PerTruthDrop.Read))
      = (1 : GenomeOrbitAdapter.PerTruthDrop.Read) := by
  refine chooseMAP_unique_max ?_ ?_
  · intro θ'
    fin_cases θ' <;> norm_num [IidMapMonotonicity.iidJoint, readPℝ, halfℝ,
      GenomeOrbitAdapter.PerTruthDrop.readP, Fin.prod_univ_two]
  · intro θ' hne
    fin_cases θ' <;> norm_num [IidMapMonotonicity.iidJoint, readPℝ, halfℝ,
      GenomeOrbitAdapter.PerTruthDrop.readP, Fin.prod_univ_two] at *

/-- At the two-read sample `(C,C)` the unique maximizer is the competitor `1`
(`1/8 > 1/50`), so the constructed MAP policy returns `1`. -/
theorem chooseMAP_two_cc :
    FiniteBayesDecision.chooseMAP (IidMapMonotonicity.iidJoint halfℝ readPℝ 2)
      (fun i => if i = 0 then (1 : GenomeOrbitAdapter.PerTruthDrop.Read)
        else (1 : GenomeOrbitAdapter.PerTruthDrop.Read))
      = (1 : GenomeOrbitAdapter.PerTruthDrop.Read) := by
  refine chooseMAP_unique_max ?_ ?_
  · intro θ'
    fin_cases θ' <;> norm_num [IidMapMonotonicity.iidJoint, readPℝ, halfℝ,
      GenomeOrbitAdapter.PerTruthDrop.readP, Fin.prod_univ_two]
  · intro θ' hne
    fin_cases θ' <;> norm_num [IidMapMonotonicity.iidJoint, readPℝ, halfℝ,
      GenomeOrbitAdapter.PerTruthDrop.readP, Fin.prod_univ_two] at *

/-- In the binary counterexample model with uniform prior, the one-read
prior-averaged MAP success is exactly `13/20`. -/
theorem mapSuccess_binary_one :
    IidMapMonotonicity.mapSuccess halfℝ readPℝ 1 = 13 / 20 := by
  have hreindex : (∑ x : Fin 1 → GenomeOrbitAdapter.PerTruthDrop.Read,
      IidMapMonotonicity.iidJoint halfℝ readPℝ 1
          (FiniteBayesDecision.chooseMAP (IidMapMonotonicity.iidJoint halfℝ readPℝ 1) x) x)
      = ∑ r : GenomeOrbitAdapter.PerTruthDrop.Read,
          IidMapMonotonicity.iidJoint halfℝ readPℝ 1
              (FiniteBayesDecision.chooseMAP (IidMapMonotonicity.iidJoint halfℝ readPℝ 1)
                (fun _ => r)) (fun _ => r) := by
    have key : ∀ x, x = (oneArrowRead).invFun ((oneArrowRead) x) := by
      intro x
      rw [funext_iff]
      intro i
      cases i with
      | mk i hi =>
        have hi0 : i = 0 := by omega
        simp [hi0]
    exact (Fintype.sum_equiv (oneArrowRead)
      (fun x => IidMapMonotonicity.iidJoint halfℝ readPℝ 1
          (FiniteBayesDecision.chooseMAP (IidMapMonotonicity.iidJoint halfℝ readPℝ 1) x) x)
      (fun r => IidMapMonotonicity.iidJoint halfℝ readPℝ 1
          (FiniteBayesDecision.chooseMAP (IidMapMonotonicity.iidJoint halfℝ readPℝ 1)
            (fun _ => r)) (fun _ => r))
      (fun x => congrArg (fun y => IidMapMonotonicity.iidJoint halfℝ readPℝ 1
          (FiniteBayesDecision.chooseMAP (IidMapMonotonicity.iidJoint halfℝ readPℝ 1) y) y)
        (key x))).symm
  unfold IidMapMonotonicity.mapSuccess
  rw [FiniteBayesDecision.success_eq_observation_sum, hreindex, Fin.sum_univ_two,
    chooseMAP_one_A, chooseMAP_one_C]
  norm_num [IidMapMonotonicity.iidJoint, readPℝ, halfℝ,
    GenomeOrbitAdapter.PerTruthDrop.readP, Fin.prod_univ_one]

/-- The reindexing `(Fin 2 → Read) ≃ Read × Read`, `x ↦ (x 0, x 1)`, used to
enumerate the two-read sample space.  Stated at top level (like `oneArrowRead`)
so definitional unfolding is available to the unifier in `mapSuccess_binary_two`. -/
def twoArrowRead : (Fin 2 → GenomeOrbitAdapter.PerTruthDrop.Read) ≃
    (GenomeOrbitAdapter.PerTruthDrop.Read × GenomeOrbitAdapter.PerTruthDrop.Read) where
  toFun x := (x 0, x 1)
  invFun p := fun i => if i = 0 then p.1 else p.2
  left_inv x := by
    rw [funext_iff]
    intro i
    fin_cases i <;> simp
  right_inv := by rintro ⟨a, b⟩; rfl

/-- In the binary counterexample model with uniform prior, the two-read
prior-averaged MAP success is exactly `139/200`. -/
theorem mapSuccess_binary_two :
    IidMapMonotonicity.mapSuccess halfℝ readPℝ 2 = 139 / 200 := by
  have key : ∀ x : Fin 2 → GenomeOrbitAdapter.PerTruthDrop.Read,
      x = (fun i => if i = 0 then x 0 else x 1) := by
    intro x
    rw [funext_iff]
    intro i
    fin_cases i <;> simp
  have hreindex : (∑ x : Fin 2 → GenomeOrbitAdapter.PerTruthDrop.Read,
      IidMapMonotonicity.iidJoint halfℝ readPℝ 2
          (FiniteBayesDecision.chooseMAP (IidMapMonotonicity.iidJoint halfℝ readPℝ 2) x) x)
      = ∑ p : GenomeOrbitAdapter.PerTruthDrop.Read × GenomeOrbitAdapter.PerTruthDrop.Read,
          IidMapMonotonicity.iidJoint halfℝ readPℝ 2
              (FiniteBayesDecision.chooseMAP (IidMapMonotonicity.iidJoint halfℝ readPℝ 2)
                (fun i => if i = 0 then p.1 else p.2))
              (fun i => if i = 0 then p.1 else p.2) := by
    refine Finset.sum_bij (fun x _ => twoArrowRead x)
      (fun x _ => Finset.mem_univ _) ?_ ?_ (fun x _ => ?_)
    · intro a _ b _ hab
      exact twoArrowRead.injective hab
    · intro p _
      exact ⟨twoArrowRead.symm p, Finset.mem_univ _,
        twoArrowRead.apply_symm_apply p⟩
    · exact congrArg (fun y => IidMapMonotonicity.iidJoint halfℝ readPℝ 2
        (FiniteBayesDecision.chooseMAP (IidMapMonotonicity.iidJoint halfℝ readPℝ 2) y) y)
        (key x)
  -- Each summand is a closed joint-mass value, proved separately so no single
  -- tactic call exceeds the heartbeat limit.
  have hAA : IidMapMonotonicity.iidJoint halfℝ readPℝ 2
      (0 : GenomeOrbitAdapter.PerTruthDrop.Read)
      (fun i => if i = 0 then (0 : GenomeOrbitAdapter.PerTruthDrop.Read)
        else (0 : GenomeOrbitAdapter.PerTruthDrop.Read)) = 8 / 25 := by
    norm_num [IidMapMonotonicity.iidJoint, readPℝ, halfℝ,
      GenomeOrbitAdapter.PerTruthDrop.readP, Fin.prod_univ_two]
  have hAC : IidMapMonotonicity.iidJoint halfℝ readPℝ 2
      (1 : GenomeOrbitAdapter.PerTruthDrop.Read)
      (fun i => if i = 0 then (0 : GenomeOrbitAdapter.PerTruthDrop.Read)
        else (1 : GenomeOrbitAdapter.PerTruthDrop.Read)) = 1 / 8 := by
    norm_num [IidMapMonotonicity.iidJoint, readPℝ, halfℝ,
      GenomeOrbitAdapter.PerTruthDrop.readP, Fin.prod_univ_two]
  have hCA : IidMapMonotonicity.iidJoint halfℝ readPℝ 2
      (1 : GenomeOrbitAdapter.PerTruthDrop.Read)
      (fun i => if i = 0 then (1 : GenomeOrbitAdapter.PerTruthDrop.Read)
        else (0 : GenomeOrbitAdapter.PerTruthDrop.Read)) = 1 / 8 := by
    norm_num [IidMapMonotonicity.iidJoint, readPℝ, halfℝ,
      GenomeOrbitAdapter.PerTruthDrop.readP, Fin.prod_univ_two]
  have hCC : IidMapMonotonicity.iidJoint halfℝ readPℝ 2
      (1 : GenomeOrbitAdapter.PerTruthDrop.Read)
      (fun i => if i = 0 then (1 : GenomeOrbitAdapter.PerTruthDrop.Read)
        else (1 : GenomeOrbitAdapter.PerTruthDrop.Read)) = 1 / 8 := by
    norm_num [IidMapMonotonicity.iidJoint, readPℝ, halfℝ,
      GenomeOrbitAdapter.PerTruthDrop.readP, Fin.prod_univ_two]
  unfold IidMapMonotonicity.mapSuccess
  rw [FiniteBayesDecision.success_eq_observation_sum, hreindex, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, chooseMAP_two_aa, chooseMAP_two_ac,
    chooseMAP_two_ca, chooseMAP_two_cc, hAA, hAC, hCA, hCC]
  norm_num

/-- **Target C scope boundary, kernel-checked.**  In the binary counterexample
model (`p_true(A) = 4/5`, `p_comp(A) = 1/2`, uniform prior, deterministic ML
policies with `≥` tie-breaking), the prior-averaged MAP success is
nondecreasing from 1 read to 2 reads (`13/20 ≤ 139/200`, by the monotonicity
theorem `mapSuccess_ignoreRead_monotone`) while the success probability of the
fixed true candidate strictly drops from `4/5` to `16/25`.  The monotonicity
theorem therefore makes no claim about each fixed true genome. -/
theorem perTruthDrop_scope_separation :
    IidMapMonotonicity.mapSuccess halfℝ readPℝ 1
      ≤ IidMapMonotonicity.mapSuccess halfℝ readPℝ 2 ∧
      GenomeOrbitAdapter.PerTruthDrop.perTruth2 0
        < GenomeOrbitAdapter.PerTruthDrop.perTruth1 0 :=
  ⟨mapSuccess_ignoreRead_monotone halfℝ readPℝ 1 perTruthDrop_normalized_real,
    GenomeOrbitAdapter.PerTruthDrop.perTruth_true_drops⟩

/-- The exact prior-averaged values of the counterexample model at one and two
reads: `13/20` and `139/200`, so the prior average strictly increases while the
per-truth success drops. -/
theorem perTruthDrop_priorAverage_values :
    IidMapMonotonicity.mapSuccess halfℝ readPℝ 1 = 13 / 20 ∧
      IidMapMonotonicity.mapSuccess halfℝ readPℝ 2 = 139 / 200 :=
  ⟨mapSuccess_binary_one, mapSuccess_binary_two⟩

/-! ## 5. Axiom audit -/

#print axioms ignoreLast
#print axioms success_ignoreLast
#print axioms chooseMAP_unique_max
#print axioms mapSuccess_ignoreRead_monotone
#print axioms mapSuccess_ignoreRead_mono
#print axioms perTruthDrop_normalized
#print axioms perTruthDrop_normalized_real
#print axioms chooseMAP_one_A
#print axioms chooseMAP_one_C
#print axioms chooseMAP_two_aa
#print axioms chooseMAP_two_ac
#print axioms chooseMAP_two_ca
#print axioms chooseMAP_two_cc
#print axioms mapSuccess_binary_one
#print axioms mapSuccess_binary_two
#print axioms perTruthDrop_scope_separation
#print axioms perTruthDrop_priorAverage_values

end AssemblyP1.IgnoreReadMonotonicity
