import AssemblyP1.SameLengthSection62Counterexample
import AssemblyP1.PerOccurrenceSameLengthCounterexample
import Mathlib

/-!
# W1/W2 separation under ONE shared observable model (issue #271, goal (b))

**Status: Lean kernel-checked. This is a concrete adapter on the historical
W1/W2 witnesses, not a claim that the §6.1 product-of-binomials objective is a
pmf over count vectors.**

The merged `AssemblyP1/W1W2SeparationCompatibility.lean` instantiated the
(B)-side of the #271 comparison on the W1/W2 witnesses — ordinary ML strictly
prefers the wrong candidate — but recorded that the (A)-side (conditional Bayes
recovery) has **no** W1/W2 instance, because the historical witness model
carries no prior over candidates, no normalized observation pmf, and no side
event `E`.  This module closes that gap by supplying exactly the missing
minimal structure and kernel-checking the **full two-sided separation on one
shared observable model** for each witness.

## The single shared observable model

For each witness (W1, W2) the SAME four objects serve both sides of the
comparison:

* **candidate universe** — the two witness spectra, truth `dS` and competitor
  `dD` (`W1Cand`, resp. `W2Cand`);
* **prior** — the uniform prior `1/2` over the two candidates (`w1prior`,
  resp. `w2prior`);
* **observation representation** — the two-point collapse `{obs, other}` of
  the read-count-vector space (`W1Obs`, resp. `W2Obs`): the observation is
  either the actual realized count vector `obs` or "something else";
* **likelihood** — the **exact multinomial pmf** of the observed count vector
  under the iid read-sampling model: with `n` reads each uniform over the `G`
  cyclic starts, `p_d(obs) = (n! / ∏_c obs c!) · ∏_c (d c / G)^{obs c}`.  This
  is the genuine normalized observation model (unlike the §6.1 product of
  binomials, which is not a pmf, and unlike the unnormalized `exactLik`
  kernel).  Crucially, the multinomial coefficient `n! / ∏ obs c!` and the
  `G^n` normalization are **candidate-independent** (same `obs`, same `G`),
  so they cancel between the two candidates and the multinomial likelihood
  ratio equals the already-kernel-checked `exactLik` ratio — the (B)-failure
  is inherited exactly, not re-proved.

The joint distribution is made explicit as

  `J(g, r) = π g · p_g(r) · 1_E(g, r)`

(`jointE` below).  Conditioning on `(r, E)` forms
`P(g | r, E) = J(g, r) / ∑_h J(h, r)`, so **conditioning touches both the
prior and the likelihood**: both `π` and `p` appear in the joint.  Under the
truth-dependent promise `E` (below) the non-truth candidate's joint mass
vanishes, the prior and likelihood cancel in the ratio, and the posterior on
the truth is `1`; without `E` they do not cancel and the posterior is `< 1`.

## The truth-dependent promise `E`

`E g r := (g = truth)` — the externally supplied promise "the candidate is the
true genome".  This is the minimal truth-dependent `E`: it is a function of the
candidate and the read (constant in the read), it is *not* a function of the
read alone, and it is *not* ML-sound (it holds on the truth at a read where the
truth is not an ML maximizer — see
`AssemblyP1.ConditionalBayesEImpliesB271.not_MLsound_of_witness`).  This is
exactly the "externally supplied truth-dependent `E`" of #271 goal 2; it is
deliberately NOT the same as running ordinary ML over `E`-qualified
candidates, and it is NOT a theorem for unrestricted likelihood.

## What is kernel-checked

For each witness, on the one shared model:

* **(A)** `postE … = 1` — conditional recovery is certain under `E`
  (`w1_A`, `w2_A`);
* **(B)** `¬ mlMax …` — ordinary R-only ML strictly prefers the wrong
  candidate (`w1_B`, `w2_B`), inherited from the witness `exactLik` ratio;
* **E-ablation** — the no-`E` posterior on the truth is `< 1` (`w1_noE_post`
  `= 1/4`, `w2_noE_post = 2/5`), so `E` is doing the work for (A);
* **prior-ablation** — the no-`E` posterior depends on the prior (`1/4` vs
  `1/10` under a skewed prior), while the ML ranking (B) is prior-free;
* the packaged premise-sensitivity conjunction (`w1_premise_sensitivity`,
  `w2_premise_sensitivity`).

No `sorry`/`admit`/`axiom`/`native_decide`; the axiom audit is in
`AxiomAudit271.lean`.
-/

namespace AssemblyP1.W1W2SharedObservableSeparation

/-! ## General shared observable model over a finite candidate type -/

section General

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {C O : Type*} [Fintype C] [DecidableEq C] [DecidableEq O]

/-- The truth-dependent promise: "candidate `g` is the true genome".  Constant
in the read; a function of the candidate and the read, not of the read alone. -/
def truthE (truth : C) (g : C) (_ : O) : Prop := g = truth

instance {truth : C} : DecidableRel (truthE truth) := fun g _ =>
  inferInstanceAs (Decidable (g = truth))

/-- The joint distribution with the `E` indicator made explicit:
`J(g, r) = π g · p_g(r) · 1_E(g, r)`.  Both the prior and the likelihood
enter. -/
def jointE (π : C → 𝕜) (p : C → O → 𝕜) (truth : C) (g : C) (r : O) : 𝕜 :=
  π g * p g r * (if truthE truth g r then 1 else 0)

/-- Predictive mass under `E`: `∑_g π g · p_g(r) · 1_E(g, r)`. -/
def predE (π : C → 𝕜) (p : C → O → 𝕜) (truth : C) (r : O) : 𝕜 :=
  ∑ g, jointE π p truth g r

/-- Conditional posterior on the truth under `E`:
`P(g = truth | r, E) = J(truth, r) / ∑_g J(g, r)`. -/
def postE (π : C → 𝕜) (p : C → O → 𝕜) (truth : C) (r : O) : 𝕜 :=
  jointE π p truth truth r / predE π p truth r

/-- Ordinary maximum-likelihood maximizer (ties allowed).  The prior and the
side information do not enter. -/
def mlMax (p : C → O → 𝕜) (g : C) (r : O) : Prop := ∀ g', p g' r ≤ p g r

/-- The ordinary (no-`E`) posterior on the truth:
`π truth · p truth r / ∑_g π g · p_g(r)`.  Both the prior and the likelihood
enter and do NOT cancel. -/
def postNoE (π : C → 𝕜) (p : C → O → 𝕜) (truth : C) (r : O) : 𝕜 :=
  π truth * p truth r / ∑ g, π g * p g r

/-- A non-truth candidate has zero conditional joint mass: the `E` indicator
vanishes. -/
theorem jointE_eq_zero_of_ne (π : C → 𝕜) (p : C → O → 𝕜) (truth : C) {g : C} {r : O}
    (h : g ≠ truth) : jointE π p truth g r = 0 := by
  unfold jointE
  simp only [truthE, if_neg h, mul_zero]

/-- **(A) Conditional recovery is certain under the truth-dependent `E`.**  The
only candidate of positive joint mass satisfying `E` at `r` is the truth, so
the conditional posterior on the truth is `1`.  The prior and likelihood enter
the joint but cancel in the ratio. -/
theorem postE_truth_eq_one (π : C → 𝕜) (p : C → O → 𝕜) (truth : C) (r : O)
    (hπ : 0 < π truth) (hp : 0 < p truth r) : postE π p truth r truth = 1 := by
  have hj : jointE π p truth truth r = π truth * p truth r := by
    unfold jointE
    simp only [truthE, if_pos rfl]
    ring
  have hsum : predE π p truth r = π truth * p truth r := by
    unfold predE
    rw [Finset.sum_eq_single truth]
    · exact hj
    · intro g _ hne
      exact jointE_eq_zero_of_ne π p truth g r hne
    · intro h
      exact absurd (Finset.mem_univ truth) h
  rw [postE, hsum, hj, div_self (ne_of_gt (by exact mul_pos hπ hp))]

/-- **(B) Ordinary ML strictly prefers a wrong candidate.**  If the competitor
scores strictly higher than the truth at `r`, the truth is not an ML
maximizer.  The prior and `E` do not enter. -/
theorem truth_not_ml_of_comp_strict (p : C → O → 𝕜) {truth competitor : C} (r : O)
    (h : p truth r < p competitor r) : ¬ mlMax p truth r := by
  intro hmax
  exact absurd (hmax competitor) (not_le.mpr h)

/-- The `E`-indicator joint mass is nonnegative under a nonnegative prior and
nonnegative likelihood. -/
theorem jointE_nonneg (π : C → 𝕜) (p : C → O → 𝕜) (truth : C)
    (hπ : ∀ g, 0 ≤ π g) (hp : ∀ g r, 0 ≤ p g r) (g : C) (r : O) :
    0 ≤ jointE π p truth g r := by
  unfold jointE
  split
  · exact mul_nonneg (mul_nonneg (hπ g) (hp g r)) (le_of_lt (by norm_num))
  · exact le_refl 0

/-- **E-ablation (general).**  The no-`E` posterior on the truth is `< 1`
whenever some competitor has positive prior and positive likelihood: the
competitor adds positive mass to the denominator that is absent from the
numerator. -/
theorem noE_post_lt_one (π : C → 𝕜) (p : C → O → 𝕜) (truth : C) (r : O)
    (hπ : ∀ g, 0 ≤ π g) (hp : ∀ g r, 0 ≤ p g r)
    (hπt : 0 < π truth) (hpt : 0 < p truth r)
    (hc : ∃ c, c ≠ truth ∧ 0 < π c ∧ 0 < p c r) :
    postNoE π p truth r < 1 := by
  obtain ⟨c, hne, hπc, hpc⟩ := hc
  have hnum : 0 < π truth * p truth r := mul_pos hπt hpt
  have hden_pos : 0 < ∑ g, π g * p g r := by
    have hle : π truth * p truth r ≤ ∑ g, π g * p g r :=
      Finset.single_le_sum (f := fun g => π g * p g r)
        (fun g _ => mul_nonneg (hπ g) (hp g r)) (Finset.mem_univ truth)
    have hterm : 0 < π c * p c r := mul_pos hπc hpc
    linarith
  have hstrict : π truth * p truth r < ∑ g, π g * p g r := by
    have hcC : π c * p c r ≤ ∑ g ∈ Finset.univ.erase truth, π g * p g r :=
      Finset.single_le_sum (f := fun g => π g * p g r)
        (fun g _ => mul_nonneg (hπ g) (hp g r))
        (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ c⟩)
    have hdecomp : ∑ g, π g * p g r
        = π truth * p truth r + ∑ g ∈ Finset.univ.erase truth, π g * p g r := by
      have := Finset.sum_erase_add (s := Finset.univ)
        (f := fun g => π g * p g r) (Finset.mem_univ truth)
      simpa using this
    linarith
  unfold postNoE
  rw [div_lt_iff hden_pos, one_mul]
  exact hstrict

end General

/-! ## W1 instantiation: `AAATAT` (truth) vs `AAAAAT` (competitor) -/

/-- The W1 candidate universe: the truth spectrum `dS` and the competitor
spectrum `dD`. -/
inductive W1Cand where
  | truth
  | competitor
  deriving DecidableEq, Inhabited, Repr

instance : Fintype W1Cand where
  elems := {W1Cand.truth, W1Cand.competitor}
  complete := by intro x; cases x <;> simp

/-- Map a W1 candidate to its molecule spectrum. -/
def w1spec : W1Cand → (Fin 8 → Nat)
  | .truth => SameLengthSection62Counterexample.dS
  | .competitor => SameLengthSection62Counterexample.dD

/-- The W1 observation space: the two-point collapse `{obs, other}` of the
read-count-vector space. -/
inductive W1Obs where
  | obs
  | other
  deriving DecidableEq, Inhabited, Repr

instance : Fintype W1Obs where
  elems := {W1Obs.obs, W1Obs.other}
  complete := by intro x; cases x <;> simp

/-- The exact multinomial pmf of the W1 observed count vector under a
candidate spectrum `d`.  With `n = 5` iid reads each uniform over the `G = 6`
cyclic starts, `p_d(obs) = (5! / ∏_c obs c!) · ∏_c (d c / 6)^{obs c}`.  The
four relevant classes are `0,1,2,4` with `obs = 2,1,1,1`, so the coefficient
is `5!/(2!1!1!1!) = 60`. -/
def w1pmf (d : Fin 8 → Nat) : ℝ :=
  60 * ((d 0 : ℝ) / 6) ^ (SameLengthSection62Counterexample.obs 0) *
    ((d 1 : ℝ) / 6) ^ (SameLengthSection62Counterexample.obs 1) *
    ((d 2 : ℝ) / 6) ^ (SameLengthSection62Counterexample.obs 2) *
    ((d 4 : ℝ) / 6) ^ (SameLengthSection62Counterexample.obs 4)

/-- The W1 observation model on the two-point space: the exact multinomial
probability at `obs`, and the remaining mass at `other`. -/
def w1p (g : W1Cand) (r : W1Obs) : ℝ :=
  match r with
  | .obs => w1pmf (w1spec g)
  | .other => 1 - w1pmf (w1spec g)

/-- The uniform prior over the two W1 candidates. -/
def w1prior (_ : W1Cand) : ℝ := 1 / 2

/-- A skewed prior over the two W1 candidates (for the prior-ablation). -/
def w1prior' : W1Cand → ℝ
  | .truth => 1 / 4
  | .competitor => 3 / 4

/-- The W1 multinomial coefficient, computed from the observed counts, is
`60 = 5!/(2!1!1!1!)`. -/
theorem w1coeff_from_obs :
    (Nat.factorial 5 / (Nat.factorial (SameLengthSection62Counterexample.obs 0) *
      Nat.factorial (SameLengthSection62Counterexample.obs 1) *
      Nat.factorial (SameLengthSection62Counterexample.obs 2) *
      Nat.factorial (SameLengthSection62Counterexample.obs 4)) : ℝ) = 60 := by
  rw [SameLengthSection62Counterexample.obs_0, SameLengthSection62Counterexample.obs_1,
    SameLengthSection62Counterexample.obs_2, SameLengthSection62Counterexample.obs_4]
  norm_num

/-- The exact multinomial probability of the W1 observation under the truth
spectrum is `5/216`. -/
theorem w1pmf_truth : w1pmf SameLengthSection62Counterexample.dS = 5 / 216 := by
  unfold w1pmf
  rw [SameLengthSection62Counterexample.obs_0, SameLengthSection62Counterexample.obs_1,
    SameLengthSection62Counterexample.obs_2, SameLengthSection62Counterexample.obs_4,
    SameLengthSection62Counterexample.dS_0, SameLengthSection62Counterexample.dS_1,
    SameLengthSection62Counterexample.dS_2, SameLengthSection62Counterexample.dS_4]
  norm_num

/-- The exact multinomial probability of the W1 observation under the
competitor spectrum is `5/72`. -/
theorem w1pmf_comp : w1pmf SameLengthSection62Counterexample.dD = 5 / 72 := by
  unfold w1pmf
  rw [SameLengthSection62Counterexample.obs_0, SameLengthSection62Counterexample.obs_1,
    SameLengthSection62Counterexample.obs_2, SameLengthSection62Counterexample.obs_4,
    SameLengthSection62Counterexample.dD_0, SameLengthSection62Counterexample.dD_1,
    SameLengthSection62Counterexample.dD_2, SameLengthSection62Counterexample.dD_4]
  norm_num

theorem w1pmf_truth_pos : 0 < w1pmf SameLengthSection62Counterexample.dS := by
  rw [w1pmf_truth]; norm_num

theorem w1pmf_comp_pos : 0 < w1pmf SameLengthSection62Counterexample.dD := by
  rw [w1pmf_comp]; norm_num

/-- The exact multinomial likelihood strictly prefers the competitor at the
W1 observation: `5/216 < 5/72`.  This is the (B)-failure, inherited from the
witness `exactLik` ratio `3` (the candidate-independent multinomial coefficient
and `6^5` normalization cancel). -/
theorem w1pmf_truth_lt_comp : w1pmf SameLengthSection62Counterexample.dS
    < w1pmf SameLengthSection62Counterexample.dD := by
  rw [w1pmf_truth, w1pmf_comp]; norm_num

/-- The W1 observation model is nonnegative. -/
theorem w1p_nonneg (g : W1Cand) (r : W1Obs) : 0 ≤ w1p g r := by
  cases r
  · unfold w1p w1spec; cases g
    · exact le_of_lt w1pmf_truth_pos
    · exact le_of_lt w1pmf_comp_pos
  · unfold w1p w1spec; cases g
    · rw [w1pmf_truth]; norm_num
    · rw [w1pmf_comp]; norm_num

/-- The W1 observation model is normalized on the two-point space. -/
theorem w1p_sum_one (g : W1Cand) : w1p g W1Obs.obs + w1p g W1Obs.other = 1 := by
  unfold w1p; ring

theorem w1prior_pos (g : W1Cand) : 0 < w1prior g := by
  unfold w1prior; norm_num

theorem w1prior_nonneg (g : W1Cand) : 0 ≤ w1prior g := le_of_lt (w1prior_pos g)

theorem w1prior_sum_one : ∑ g : W1Cand, w1prior g = 1 := by
  unfold w1prior; simp

theorem w1prior'_pos (g : W1Cand) : 0 < w1prior' g := by
  cases g <;> unfold w1prior' <;> norm_num

theorem w1prior'_nonneg (g : W1Cand) : 0 ≤ w1prior' g := le_of_lt (w1prior'_pos g)

theorem w1prior'_sum_one : ∑ g : W1Cand, w1prior' g = 1 := by
  unfold w1prior'; simp

/-- The likelihood of the W1 observation under the truth, as a positive real. -/
theorem w1_p_truth_obs_pos : 0 < w1p W1Cand.truth W1Obs.obs := by
  unfold w1p w1spec; exact w1pmf_truth_pos

/-- The likelihood of the W1 observation under the competitor, as a positive
real. -/
theorem w1_p_comp_obs_pos : 0 < w1p W1Cand.competitor W1Obs.obs := by
  unfold w1p w1spec; exact w1pmf_comp_pos

/-- The likelihood of the W1 observation under the truth is strictly below the
competitor's. -/
theorem w1_p_truth_lt_comp_obs : w1p W1Cand.truth W1Obs.obs
    < w1p W1Cand.competitor W1Obs.obs := by
  unfold w1p w1spec; exact w1pmf_truth_lt_comp

/-- Sum over the two-element W1 candidate universe. -/
theorem w1_sum (f : W1Cand → ℝ) :
    ∑ x : W1Cand, f x = f W1Cand.truth + f W1Cand.competitor := by
  have h1 : Finset.univ = {W1Cand.truth, W1Cand.competitor} := by
    ext x
    constructor
    · intro _
      cases x
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · intro hx
      rcases Finset.mem_insert.mp hx with h | h
      · exact Finset.mem_univ _
      · exact Finset.mem_univ _
  rw [h1, Finset.sum_insert (by simp), Finset.sum_singleton]
  ring

/-! ### W1 separation on the shared model -/

/-- **(A) W1: conditional recovery is certain under the truth-dependent `E`.**
On the one shared model, conditioning on `(obs, E)` gives posterior `1` on the
true spectrum. -/
theorem w1_A : postE w1prior w1p W1Cand.truth W1Obs.obs W1Cand.truth = 1 :=
  postE_truth_eq_one w1prior w1p W1Cand.truth W1Obs.obs
    (w1prior_pos W1Cand.truth) w1_p_truth_obs_pos

/-- **(B) W1: ordinary R-only ML strictly prefers the wrong candidate.**  The
true spectrum is not an ML maximizer at `obs`. -/
theorem w1_B : ¬ mlMax (fun g r => w1p g r) W1Cand.truth W1Obs.obs :=
  truth_not_ml_of_comp_strict (fun g r => w1p g r) W1Cand.truth W1Cand.competitor
    W1Obs.obs w1_p_truth_lt_comp_obs

/-- **W1 E-ablation.**  Without `E`, the ordinary posterior on the truth is
`1/4 ≠ 1`: the competitor retains positive prior and positive likelihood. -/
theorem w1_noE_post : postNoE w1prior w1p W1Cand.truth W1Obs.obs = 1 / 4 := by
  unfold postNoE
  have h1 : w1prior W1Cand.truth * w1p W1Cand.truth W1Obs.obs = 5 / 432 := by
    unfold w1prior w1p w1spec; rw [w1pmf_truth]; norm_num
  have hsum : ∑ g : W1Cand, w1prior g * w1p g W1Obs.obs = 5 / 108 := by
    rw [w1_sum]
    unfold w1prior w1p w1spec; rw [w1pmf_truth, w1pmf_comp]; norm_num
  rw [h1, hsum]; norm_num

/-- **W1 E-ablation (general bound).**  The no-`E` posterior on the truth is
`< 1`, via the general `noE_post_lt_one`. -/
theorem w1_noE_lt_one : postNoE w1prior w1p W1Cand.truth W1Obs.obs < 1 :=
  noE_post_lt_one w1prior w1p W1Cand.truth W1Obs.obs
    (fun g => w1prior_nonneg g) (fun g r => w1p_nonneg g r)
    (w1prior_pos W1Cand.truth) w1_p_truth_obs_pos
    ⟨W1Cand.competitor, by simp, w1prior_pos W1Cand.competitor, w1_p_comp_obs_pos⟩

/-- **W1 prior-ablation.**  Under the skewed prior `w1prior'`, the no-`E`
posterior on the truth is `1/10 ≠ 1/4`: the no-`E` posterior depends on the
prior. -/
theorem w1_noE_post' : postNoE w1prior' w1p W1Cand.truth W1Obs.obs = 1 / 10 := by
  unfold postNoE
  have h1 : w1prior' W1Cand.truth * w1p W1Cand.truth W1Obs.obs = 5 / 864 := by
    unfold w1prior' w1p w1spec; rw [w1pmf_truth]; norm_num
  have hsum : ∑ g : W1Cand, w1prior' g * w1p g W1Obs.obs = 25 / 432 := by
    rw [w1_sum]
    unfold w1prior' w1p w1spec; rw [w1pmf_truth, w1pmf_comp]; norm_num
  rw [h1, hsum]; norm_num

/-- **W1 premise sensitivity, packaged.**  On the one shared observable model:
(A) holds with the truth-dependent `E`; (B) fails; removing `E` drops (A)
(no-`E` posterior `1/4 ≠ 1`) but leaves (B) unchanged; the no-`E` posterior
depends on the prior (`1/4` vs `1/10`) while the ML ranking (B) is
prior-free. -/
theorem w1_premise_sensitivity :
    postE w1prior w1p W1Cand.truth W1Obs.obs W1Cand.truth = 1 ∧
      ¬ mlMax (fun g r => w1p g r) W1Cand.truth W1Obs.obs ∧
      postNoE w1prior w1p W1Cand.truth W1Obs.obs = 1 / 4 ∧
      postNoE w1prior w1p W1Cand.truth W1Obs.obs ≠ 1 ∧
      postNoE w1prior' w1p W1Cand.truth W1Obs.obs = 1 / 10 ∧
      postNoE w1prior' w1p W1Cand.truth W1Obs.obs ≠
        postNoE w1prior w1p W1Cand.truth W1Obs.obs :=
  ⟨w1_A, w1_B, w1_noE_post, by rw [w1_noE_post]; norm_num, w1_noE_post',
    by rw [w1_noE_post, w1_noE_post']; norm_num⟩

/-! ## W2 instantiation: per-occurrence strengthening -/

/-- The W2 candidate universe: the truth spectrum `dS` and the competitor
spectrum `dD`. -/
inductive W2Cand where
  | truth
  | competitor
  deriving DecidableEq, Inhabited, Repr

instance : Fintype W2Cand where
  elems := {W2Cand.truth, W2Cand.competitor}
  complete := by intro x; cases x <;> simp

/-- Map a W2 candidate to its molecule spectrum. -/
def w2spec : W2Cand → (Fin 64 → Nat)
  | .truth => PerOccurrenceSameLengthCounterexample.dS
  | .competitor => PerOccurrenceSameLengthCounterexample.dD

/-- The W2 observation space: the two-point collapse `{obs, other}`. -/
inductive W2Obs where
  | obs
  | other
  deriving DecidableEq, Inhabited, Repr

instance : Fintype W2Obs where
  elems := {W2Obs.obs, W2Obs.other}
  complete := by intro x; cases x <;> simp

/-- The exact multinomial pmf of the W2 observed count vector under a
candidate spectrum `d`.  With `n = 6` iid reads each uniform over the `G = 8`
cyclic starts, `p_d(obs) = (6! / ∏_c obs c!) · ∏_c (d c / 8)^{obs c}`.  The
five relevant classes are `4,12,14,17,44` with `obs = 2,1,1,1,1`, so the
coefficient is `6!/(2!1!1!1!1!) = 360`. -/
def w2pmf (d : Fin 64 → Nat) : ℝ :=
  360 * ((d 4 : ℝ) / 8) ^ (PerOccurrenceSameLengthCounterexample.obs 4) *
    ((d 12 : ℝ) / 8) ^ (PerOccurrenceSameLengthCounterexample.obs 12) *
    ((d 14 : ℝ) / 8) ^ (PerOccurrenceSameLengthCounterexample.obs 14) *
    ((d 17 : ℝ) / 8) ^ (PerOccurrenceSameLengthCounterexample.obs 17) *
    ((d 44 : ℝ) / 8) ^ (PerOccurrenceSameLengthCounterexample.obs 44)

/-- The W2 observation model on the two-point space. -/
def w2p (g : W2Cand) (r : W2Obs) : ℝ :=
  match r with
  | .obs => w2pmf (w2spec g)
  | .other => 1 - w2pmf (w2spec g)

/-- The uniform prior over the two W2 candidates. -/
def w2prior (_ : W2Cand) : ℝ := 1 / 2

/-- The W2 multinomial coefficient, computed from the observed counts, is
`360 = 6!/(2!1!1!1!1!)`. -/
theorem w2coeff_from_obs :
    (Nat.factorial 6 / (Nat.factorial (PerOccurrenceSameLengthCounterexample.obs 4) *
      Nat.factorial (PerOccurrenceSameLengthCounterexample.obs 12) *
      Nat.factorial (PerOccurrenceSameLengthCounterexample.obs 14) *
      Nat.factorial (PerOccurrenceSameLengthCounterexample.obs 17) *
      Nat.factorial (PerOccurrenceSameLengthCounterexample.obs 44)) : ℝ) = 360 := by
  rw [PerOccurrenceSameLengthCounterexample.obs_values.1,
    PerOccurrenceSameLengthCounterexample.obs_values.2.1,
    PerOccurrenceSameLengthCounterexample.obs_values.2.2.1,
    PerOccurrenceSameLengthCounterexample.obs_values.2.2.2.1,
    PerOccurrenceSameLengthCounterexample.obs_values.2.2.2.2]
  norm_num

/-- The exact multinomial probability of the W2 observation under the truth
spectrum is `135/8192`. -/
theorem w2pmf_truth : w2pmf PerOccurrenceSameLengthCounterexample.dS = 135 / 8192 := by
  unfold w2pmf
  rw [PerOccurrenceSameLengthCounterexample.obs_values.1,
    PerOccurrenceSameLengthCounterexample.obs_values.2.1,
    PerOccurrenceSameLengthCounterexample.obs_values.2.2.1,
    PerOccurrenceSameLengthCounterexample.obs_values.2.2.2.1,
    PerOccurrenceSameLengthCounterexample.obs_values.2.2.2.2,
    PerOccurrenceSameLengthCounterexample.dS_values.1,
    PerOccurrenceSameLengthCounterexample.dS_values.2.1,
    PerOccurrenceSameLengthCounterexample.dS_values.2.2.1,
    PerOccurrenceSameLengthCounterexample.dS_values.2.2.2.1,
    PerOccurrenceSameLengthCounterexample.dS_values.2.2.2.2]
  norm_num

/-- The exact multinomial probability of the W2 observation under the
competitor spectrum is `405/16384`. -/
theorem w2pmf_comp : w2pmf PerOccurrenceSameLengthCounterexample.dD = 405 / 16384 := by
  unfold w2pmf
  rw [PerOccurrenceSameLengthCounterexample.obs_values.1,
    PerOccurrenceSameLengthCounterexample.obs_values.2.1,
    PerOccurrenceSameLengthCounterexample.obs_values.2.2.1,
    PerOccurrenceSameLengthCounterexample.obs_values.2.2.2.1,
    PerOccurrenceSameLengthCounterexample.obs_values.2.2.2.2,
    PerOccurrenceSameLengthCounterexample.dD_values.1,
    PerOccurrenceSameLengthCounterexample.dD_values.2.1,
    PerOccurrenceSameLengthCounterexample.dD_values.2.2.1,
    PerOccurrenceSameLengthCounterexample.dD_values.2.2.2.1,
    PerOccurrenceSameLengthCounterexample.dD_values.2.2.2.2]
  norm_num

theorem w2pmf_truth_pos : 0 < w2pmf PerOccurrenceSameLengthCounterexample.dS := by
  rw [w2pmf_truth]; norm_num

theorem w2pmf_comp_pos : 0 < w2pmf PerOccurrenceSameLengthCounterexample.dD := by
  rw [w2pmf_comp]; norm_num

/-- The exact multinomial likelihood strictly prefers the competitor at the
W2 observation: `135/8192 < 405/16384`.  Inherited from the witness `exactLik`
ratio `3/2`. -/
theorem w2pmf_truth_lt_comp : w2pmf PerOccurrenceSameLengthCounterexample.dS
    < w2pmf PerOccurrenceSameLengthCounterexample.dD := by
  rw [w2pmf_truth, w2pmf_comp]; norm_num

/-- The W2 observation model is nonnegative. -/
theorem w2p_nonneg (g : W2Cand) (r : W2Obs) : 0 ≤ w2p g r := by
  cases r
  · unfold w2p w2spec; cases g
    · exact le_of_lt w2pmf_truth_pos
    · exact le_of_lt w2pmf_comp_pos
  · unfold w2p w2spec; cases g
    · rw [w2pmf_truth]; norm_num
    · rw [w2pmf_comp]; norm_num

/-- The W2 observation model is normalized on the two-point space. -/
theorem w2p_sum_one (g : W2Cand) : w2p g W2Obs.obs + w2p g W2Obs.other = 1 := by
  unfold w2p; ring

theorem w2prior_pos (g : W2Cand) : 0 < w2prior g := by
  unfold w2prior; norm_num

theorem w2prior_nonneg (g : W2Cand) : 0 ≤ w2prior g := le_of_lt (w2prior_pos g)

/-- The likelihood of the W2 observation under the truth, as a positive real. -/
theorem w2_p_truth_obs_pos : 0 < w2p W2Cand.truth W2Obs.obs := by
  unfold w2p w2spec; exact w2pmf_truth_pos

/-- The likelihood of the W2 observation under the competitor, as a positive
real. -/
theorem w2_p_comp_obs_pos : 0 < w2p W2Cand.competitor W2Obs.obs := by
  unfold w2p w2spec; exact w2pmf_comp_pos

/-- The likelihood of the W2 observation under the truth is strictly below the
competitor's. -/
theorem w2_p_truth_lt_comp_obs : w2p W2Cand.truth W2Obs.obs
    < w2p W2Cand.competitor W2Obs.obs := by
  unfold w2p w2spec; exact w2pmf_truth_lt_comp

/-- Sum over the two-element W2 candidate universe. -/
theorem w2_sum (f : W2Cand → ℝ) :
    ∑ x : W2Cand, f x = f W2Cand.truth + f W2Cand.competitor := by
  have h1 : Finset.univ = {W2Cand.truth, W2Cand.competitor} := by
    ext x
    constructor
    · intro _
      cases x
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · intro hx
      rcases Finset.mem_insert.mp hx with h | h
      · exact Finset.mem_univ _
      · exact Finset.mem_univ _
  rw [h1, Finset.sum_insert (by simp), Finset.sum_singleton]
  ring

/-! ### W2 separation on the shared model -/

/-- **(A) W2: conditional recovery is certain under the truth-dependent `E`.** -/
theorem w2_A : postE w2prior w2p W2Cand.truth W2Obs.obs W2Cand.truth = 1 :=
  postE_truth_eq_one w2prior w2p W2Cand.truth W2Obs.obs
    (w2prior_pos W2Cand.truth) w2_p_truth_obs_pos

/-- **(B) W2: ordinary R-only ML strictly prefers the wrong candidate.** -/
theorem w2_B : ¬ mlMax (fun g r => w2p g r) W2Cand.truth W2Obs.obs :=
  truth_not_ml_of_comp_strict (fun g r => w2p g r) W2Cand.truth W2Cand.competitor
    W2Obs.obs w2_p_truth_lt_comp_obs

/-- **W2 E-ablation.**  Without `E`, the ordinary posterior on the truth is
`2/5 ≠ 1`. -/
theorem w2_noE_post : postNoE w2prior w2p W2Cand.truth W2Obs.obs = 2 / 5 := by
  unfold postNoE
  have h1 : w2prior W2Cand.truth * w2p W2Cand.truth W2Obs.obs = 135 / 16384 := by
    unfold w2prior w2p w2spec; rw [w2pmf_truth]; norm_num
  have hsum : ∑ g : W2Cand, w2prior g * w2p g W2Obs.obs = 675 / 32768 := by
    rw [w2_sum]
    unfold w2prior w2p w2spec; rw [w2pmf_truth, w2pmf_comp]; norm_num
  rw [h1, hsum]; norm_num

/-- **W2 E-ablation (general bound).** -/
theorem w2_noE_lt_one : postNoE w2prior w2p W2Cand.truth W2Obs.obs < 1 :=
  noE_post_lt_one w2prior w2p W2Cand.truth W2Obs.obs
    (fun g => w2prior_nonneg g) (fun g r => w2p_nonneg g r)
    (w2prior_pos W2Cand.truth) w2_p_truth_obs_pos
    ⟨W2Cand.competitor, by simp, w2prior_pos W2Cand.competitor, w2_p_comp_obs_pos⟩

/-- **W2 premise sensitivity, packaged.** -/
theorem w2_premise_sensitivity :
    postE w2prior w2p W2Cand.truth W2Obs.obs W2Cand.truth = 1 ∧
      ¬ mlMax (fun g r => w2p g r) W2Cand.truth W2Obs.obs ∧
      postNoE w2prior w2p W2Cand.truth W2Obs.obs = 2 / 5 ∧
      postNoE w2prior w2p W2Cand.truth W2Obs.obs ≠ 1 :=
  ⟨w2_A, w2_B, w2_noE_post, by rw [w2_noE_post]; norm_num⟩

end AssemblyP1.W1W2SharedObservableSeparation
