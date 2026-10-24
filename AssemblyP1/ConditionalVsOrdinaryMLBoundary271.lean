import AssemblyP1.ConditionalVsOrdinaryMLSeparation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Tiny-table sanity regressions for the conditional-Bayes vs ordinary-ML boundary (#271)

Companion to `AssemblyP1/ConditionalVsOrdinaryMLSeparation.lean`.  The main
module exhibits the two-way separation of the two finite-recovery guarantees on
a single two-candidate table.  This module adds the three degenerate tables
that the #271 comparison must distinguish, all with exact rational arithmetic
and kernel-checked:

* **ties** — at the truth, ordinary ML holds only as a *tied* (non-unique)
  maximizer, and the unconditional posterior is still not certain; this
  separates "maximizer" from "unique maximizer" and shows neither form of (B)
  gives (A);
* **zero-likelihood competitors** — a candidate with zero read likelihood is
  excluded from the posterior automatically, with no side information needed.
  This is an *overlap*: posterior certainty and unique ordinary-ML recovery
  hold simultaneously, and no prior can rescue the excluded candidate.  This is
  the concrete shadow of the general excluded-orbit result
  `AssemblyP1.FiniteBayesianSideInformation.posteriorMass_eq_one_iff_excluded`
  (#272);
* **uniform vs nonuniform priors (MAP vs ML)** — a nonuniform prior flips the
   posterior maximizer (MAP) away from the likelihood maximizer (ML), while ML
   is unchanged.  The general posterior/MAP equivalence is owned by #269
   (`AssemblyP1.GenomeOrbitAdapter.PosteriorMAP.posterior_argmax_iff`); this
   module only instantiates it on a concrete tiny table and is not generic MAP
   infrastructure.
* **unique ML maximizer without posterior certainty** — a strictly separated
   likelihood table where the truth is the *unique* ordinary-ML maximizer while
   the unconditional posterior on the truth is strictly below `1`.  This is the
   abstract tiny-table shadow of the genome-adapter converse
   (`conv_ml_unique` + `conv_ordinary_not_certain`): unique (B) still does not
   give (A).

Everything here is an abstract finite pmf regression, not a source-faithful
genome witness.
-/

namespace AssemblyP1.ConditionalVsOrdinaryMLBoundary271

open AssemblyP1.ConditionalVsOrdinaryMLSeparation

/-- Ordinary ML maximizer for an arbitrary score table: `h` is a maximizer at
`r` when no candidate scores strictly higher (ties allowed).  Same shape as the
merged `ConditionalVsOrdinaryMLSeparation.isMLMaximizer`, generalized over the
score table. -/
def IsMLMaximizerOf (score : Hypothesis → Obs → ℚ) (h : Hypothesis) (r : Obs) : Prop :=
  ∀ h' : Hypothesis, score h' r ≤ score h r

/-- Posterior of `h` at `r` for a two-candidate prior `π` and likelihood `p`,
`π h · p h r / (π A · p A r + π B · p B r)`.  A tiny concrete helper, not the
general `#272` posterior. -/
def post2 (π : Hypothesis → ℚ) (p : Hypothesis → Obs → ℚ) (h : Hypothesis) (r : Obs) : ℚ :=
  π h * p h r / (π Hypothesis.A * p Hypothesis.A r + π Hypothesis.B * p Hypothesis.B r)

/-- The uniform prior `π = (1/2, 1/2)`. -/
def priorUnif (_ : Hypothesis) : ℚ := 1 / 2

/-- A nonuniform prior `π = (9/10, 1/10)`, putting most mass on the truth `A`. -/
def priorSkew (h : Hypothesis) : ℚ := if h = Hypothesis.A then 9 / 10 else 1 / 10

theorem priorSkew_A : priorSkew Hypothesis.A = 9 / 10 := by simp [priorSkew]

theorem priorSkew_B : priorSkew Hypothesis.B = 1 / 10 := by
  unfold priorSkew
  rw [ite_eq_right (by decide)]

/-! ## Table 1: tied ordinary-ML maximizer (non-unique) -/

/-- All four likelihood entries equal: a maximally degenerate tie table. -/
def likTie (_ : Hypothesis) (_ : Obs) : ℚ := 1 / 2

/-- At `r = r0` the truth `A` is an ordinary-ML maximizer. -/
theorem ml_tie_A_r0 : IsMLMaximizerOf likTie Hypothesis.A Obs.r0 := by
  intro h'
  cases h' <;> norm_num [likTie]

/-- But the tie is non-unique: `B` is also a maximizer, so `A` is not the
unique maximizer.  This is the "maximizer vs unique maximizer" distinction of
the (B)-boundary. -/
theorem ml_tie_not_unique_r0 :
    ¬ (∀ h, IsMLMaximizerOf likTie h Obs.r0 → h = Hypothesis.A) := by
  intro huniq
  have hB : IsMLMaximizerOf likTie Hypothesis.B Obs.r0 := by
    intro h'
    cases h' <;> norm_num [likTie]
  exact absurd (huniq Hypothesis.B hB) (by decide)

/-- Even when ordinary ML holds (as a tie), the unconditional posterior on the
truth is `1/2`, not certainty: (B) does not give (A). -/
theorem post_tie_A_r0 : post2 priorUnif likTie Hypothesis.A Obs.r0 = 1 / 2 := by
  norm_num [post2, priorUnif, likTie]

theorem post_tie_A_r0_not_certain : post2 priorUnif likTie Hypothesis.A Obs.r0 ≠ 1 := by
  rw [post_tie_A_r0]; norm_num

/-- A tied (non-unique) ML maximizer still does not certify the truth: the
posterior is not one. -/
theorem tie_maximizer_posterior_not_certain :
    IsMLMaximizerOf likTie Hypothesis.A Obs.r0 ∧
      ¬ (∀ h, IsMLMaximizerOf likTie h Obs.r0 → h = Hypothesis.A) ∧
      post2 priorUnif likTie Hypothesis.A Obs.r0 ≠ 1 :=
  ⟨ml_tie_A_r0, ml_tie_not_unique_r0, post_tie_A_r0_not_certain⟩

/-! ## Table 2: zero-likelihood competitor (overlap, automatic exclusion) -/

/-- Likelihood table with a *zero* at the observed read: `A` emits `r0` with
probability one and `r1` never; `B` the reverse. -/
def likZero : Hypothesis → Obs → ℚ
  | Hypothesis.A, Obs.r0 => 1
  | Hypothesis.A, Obs.r1 => 0
  | Hypothesis.B, Obs.r0 => 0
  | Hypothesis.B, Obs.r1 => 1

theorem likZero_A_r0 : likZero Hypothesis.A Obs.r0 = 1 := rfl

theorem likZero_B_r0 : likZero Hypothesis.B Obs.r0 = 0 := rfl

/-- At `r = r0`, `B` has zero likelihood, so `A` is the unique ordinary-ML
maximizer. -/
theorem ml_zero_A_unique_r0 :
    IsMLMaximizerOf likZero Hypothesis.A Obs.r0 ∧
      ∀ h, IsMLMaximizerOf likZero h Obs.r0 → h = Hypothesis.A := by
  constructor
  · intro h'
    cases h' <;> norm_num [likZero]
  · intro h hmax
    cases h with
    | A => rfl
    | B => exact absurd (hmax Hypothesis.A) (by norm_num [likZero])

/-- At `r = r0` the zero-likelihood competitor `B` is automatically excluded:
its posterior is `0` and the truth `A` has posterior `1` — with no side
information and any positive prior. -/
theorem post_zero_A_r0 : post2 priorUnif likZero Hypothesis.A Obs.r0 = 1 := by
  norm_num [post2, priorUnif, likZero]

theorem post_zero_B_r0 : post2 priorUnif likZero Hypothesis.B Obs.r0 = 0 := by
  norm_num [post2, priorUnif, likZero]

/-- No prior can rescue the zero-likelihood competitor: even with a skewed prior
`π B = 1/10`, `B`'s posterior at `r = r0` is still `0` and the truth's is `1`. -/
theorem post_zero_A_r0_skew : post2 priorSkew likZero Hypothesis.A Obs.r0 = 1 := by
  norm_num [post2, priorSkew, likZero]

theorem post_zero_B_r0_skew : post2 priorSkew likZero Hypothesis.B Obs.r0 = 0 := by
  norm_num [post2, priorSkew, likZero]

/-- **Overlap table.** At `r = r0` the two guarantees hold *simultaneously*:
the truth `A` is the unique ordinary-ML maximizer *and* the posterior on `A` is
`1` (the zero-likelihood competitor `B` is automatically excluded).  This is
the opposite of the separation tables: zero-likelihood competitors collapse the
support for free. -/
theorem zero_likelihood_overlap :
    (IsMLMaximizerOf likZero Hypothesis.A Obs.r0 ∧
        ∀ h, IsMLMaximizerOf likZero h Obs.r0 → h = Hypothesis.A) ∧
      post2 priorUnif likZero Hypothesis.A Obs.r0 = 1 ∧
      post2 priorUnif likZero Hypothesis.B Obs.r0 = 0 :=
  ⟨ml_zero_A_unique_r0, post_zero_A_r0, post_zero_B_r0⟩

/-! ## Table 3: uniform vs nonuniform prior — MAP vs ML -/

/-- The likelihood table of the main #271 witness: `p_A = (1/4, 3/4)`,
`p_B = (3/4, 1/4)` (this is exactly the merged
`ConditionalVsOrdinaryMLSeparation.lik`). -/
abbrev likMap : Hypothesis → Obs → ℚ := lik

/-- At `r = r0` ordinary ML strictly prefers `B` (`3/4 > 1/4`): the likelihood
maximizer is `B`, independently of the prior. -/
theorem ml_map_B_r0 : IsMLMaximizerOf likMap Hypothesis.B Obs.r0 := by
  intro h'
  cases h' <;> norm_num [likMap, lik]

theorem ml_map_B_strict_r0 : likMap Hypothesis.A Obs.r0 < likMap Hypothesis.B Obs.r0 := by
  norm_num [likMap, lik]

/-- With the *uniform* prior the posterior maximizer agrees with ML: `B` has the
larger posterior (`3/4` vs `1/4`). -/
theorem map_uniform_B_r0 : post2 priorUnif likMap Hypothesis.B Obs.r0 = 3 / 4 := by
  norm_num [post2, priorUnif, likMap, lik]

theorem map_uniform_A_r0 : post2 priorUnif likMap Hypothesis.A Obs.r0 = 1 / 4 := by
  norm_num [post2, priorUnif, likMap, lik]

/-- With the *nonuniform* prior `π = (9/10, 1/10)` the posterior maximizer flips
to `A` (`3/4` vs `1/4`), while the likelihood maximizer is still `B`. -/
theorem map_skew_A_r0 : post2 priorSkew likMap Hypothesis.A Obs.r0 = 3 / 4 := by
  norm_num [post2, priorSkew, likMap, lik]

theorem map_skew_B_r0 : post2 priorSkew likMap Hypothesis.B Obs.r0 = 1 / 4 := by
  norm_num [post2, priorSkew, likMap, lik]

/-- **MAP ≠ ML under a nonuniform prior.** At the same observation `r = r0` and
the same likelihood table, the ordinary ML maximizer is `B` (`3/4 > 1/4`) while
the MAP/posterior maximizer is `A` (`3/4 > 1/4`), because the prior mass on `A`
is large enough to outweigh the likelihood deficit.  This is the uniform vs
nonuniform (MAP vs ML) distinction; the general equivalence of posterior
maximizer and joint-mass maximizer is #269
(`GenomeOrbitAdapter.PosteriorMAP.posterior_argmax_iff`). -/
theorem map_ne_ml_nonuniform :
    likMap Hypothesis.B Obs.r0 > likMap Hypothesis.A Obs.r0 ∧
      post2 priorSkew likMap Hypothesis.A Obs.r0 >
        post2 priorSkew likMap Hypothesis.B Obs.r0 := by
  refine ⟨?_, ?_⟩
  · exact ml_map_B_strict_r0
  · rw [map_skew_A_r0, map_skew_B_r0]; norm_num

/-- The prior changes the MAP decision but not the ML decision: with the uniform
prior the posterior maximizer is `B` (as in ML); with the skewed prior it is
`A`.  Ordinary ML is prior-free. -/
theorem prior_flips_MAP_not_ML :
    post2 priorUnif likMap Hypothesis.B Obs.r0 >
        post2 priorUnif likMap Hypothesis.A Obs.r0 ∧
      post2 priorSkew likMap Hypothesis.A Obs.r0 >
        post2 priorSkew likMap Hypothesis.B Obs.r0 ∧
      likMap Hypothesis.B Obs.r0 > likMap Hypothesis.A Obs.r0 := by
  refine ⟨?_, ?_, ml_map_B_strict_r0⟩
  · rw [map_uniform_B_r0, map_uniform_A_r0]; norm_num
  · rw [map_skew_A_r0, map_skew_B_r0]; norm_num

/-! ## Table 4: unique ordinary-ML maximizer without posterior certainty -/

/-- Strictly separated likelihood table: `A` emits `r0` with probability `2/3`
and `r1` with `1/3`; `B` the reverse.  Both rows are pmfs. -/
def likHi : Hypothesis → Obs → ℚ
  | Hypothesis.A, Obs.r0 => 2 / 3
  | Hypothesis.A, Obs.r1 => 1 / 3
  | Hypothesis.B, Obs.r0 => 1 / 3
  | Hypothesis.B, Obs.r1 => 2 / 3

/-- At `r = r0` the truth `A` is the *unique* ordinary-ML maximizer
(`2/3 > 1/3`). -/
theorem ml_hi_A_unique_r0 :
    IsMLMaximizerOf likHi Hypothesis.A Obs.r0 ∧
      ∀ h, IsMLMaximizerOf likHi h Obs.r0 → h = Hypothesis.A := by
  constructor
  · intro h'
    cases h' <;> norm_num [likHi]
  · intro h hmax
    cases h with
    | A => rfl
    | B => exact absurd (hmax Hypothesis.A) (by norm_num [likHi])

/-- With the uniform prior the posterior on the truth at `r = r0` is `2/3`:
ML is decisive while the posterior still spreads mass over `B`. -/
theorem post_hi_A_r0 : post2 priorUnif likHi Hypothesis.A Obs.r0 = 2 / 3 := by
  norm_num [post2, priorUnif, likHi]

theorem post_hi_B_r0 : post2 priorUnif likHi Hypothesis.B Obs.r0 = 1 / 3 := by
  norm_num [post2, priorUnif, likHi]

theorem post_hi_A_r0_not_certain : post2 priorUnif likHi Hypothesis.A Obs.r0 ≠ 1 := by
  rw [post_hi_A_r0]; norm_num

/-- **Unique (B) does not give (A).** At `r = r0` the truth `A` is the unique
ordinary-ML maximizer, yet the unconditional posterior on `A` is `2/3 ≠ 1`.
This completes the tiny-table boundary alongside the tied Table 1
(non-unique maximizer, posterior `1/2`) and the zero-likelihood Table 2
(unique maximizer with posterior `1`): uniqueness of the ML maximizer is
orthogonal to posterior certainty. -/
theorem unique_ml_posterior_not_certain :
    (IsMLMaximizerOf likHi Hypothesis.A Obs.r0 ∧
        ∀ h, IsMLMaximizerOf likHi h Obs.r0 → h = Hypothesis.A) ∧
      post2 priorUnif likHi Hypothesis.A Obs.r0 ≠ 1 :=
  ⟨ml_hi_A_unique_r0, post_hi_A_r0_not_certain⟩

end AssemblyP1.ConditionalVsOrdinaryMLBoundary271
