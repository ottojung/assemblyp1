import AssemblyP1.SameLengthSection62Counterexample
import AssemblyP1.PerOccurrenceSameLengthCounterexample

/-!
# Can the historical witnesses W1/W2 instantiate the #271 separation?

**Verdict (kernel-checked where positive).** Under the EXACT shared observable
data model of the historical same-length witnesses —

* candidates: genomes given through their read-type spectra
  (W1: `AAATAT` vs `AAAAAT`, spectra `Fin 8 → ℕ`;
  W2 per-occurrence strengthening: `ATATACAC` vs `ATACACAC`, spectra
  `Fin 64 → ℕ`),
* observation: the fixed realized read-type count vector `obs`,
* objectives: the literal §6.1 product of binomial marginals `lik` and the
  exact same-length multinomial score `exactLik`,

the witnesses DO instantiate the (B)-side failure of the #271 comparison: at
the fixed observation `obs`, ordinary ML — under either objective — strictly
prefers the wrong candidate. This is the "ordinary R-only ML rule strictly
prefers a wrong candidate" half of the separation, kernel-checked by reuse of
the existing witness theorems (no re-proof).

They do NOT instantiate the (A)-side, and hence not the full two-sided
separation, under this shared observable data model:

* the model carries **no prior over candidates** and **no normalized
  observation pmf** — `exactLik` is by definition the unnormalized score
  `∏ c, (d c)^(x c)` (`SameLengthSection62Counterexample.exactFactor`), with
  neither the per-class probability `d c / G` nor the multinomial coefficient,
  and `lik` is a product of per-class binomials at fixed external `N`, `n`,
  which is not a pmf over count vectors either; so the conditional posterior
  `P(g | obs, E) ∝ π g · P(obs | g) · 1_E(g, obs)` of #271(A) is **not
  defined** in the W1/W2 model — there is no `π`, no `P(obs | g)`, and no side
  event `E` in it;
* instantiating (A) would require a NEW concrete adapter (a normalized
  per-candidate observation model, a candidate prior, and a promise `E`),
  which is exactly the "explicit concrete adapter and Lean proof" that the
  #271 kernel standard demands before any genome-level conditional-recovery
  claim is made. No such adapter is claimed here.

Representation warnings (per `docs/bridging-source-semantics.md` and the
#266/#267 corrections): W1/W2 are **oriented read-string** witnesses — the
observable is built from the oriented windows `SourceFaithfulIs.window` — and
must NOT be coerced into the reverse-complement-collapsed molecule
representation of #260, which is a different observable representation with a
different likelihood. Likewise the historical coverage predicates come in two
variants that must not be silently identified: `HistoricalCovers` (matched
observed read strings, #247) versus `SourceFaithfulIs.InformationFeasible`
(latent sampled starts); the W1/W2 likelihood statements are independent of
that distinction, since they concern the count vector `obs`, not coverage.

Connection to the abstract comparison: the (B)-boundary predicate
`AssemblyP1.ConditionalVsOrdinaryMLSeparation.isMLMaximizer` is a statement
about the objective alone; the W1/W2 theorems below instantiate the same
prior-free, `E`-free boundary on the witness model with the truth spectrum
`dS` and the competitor `dD`, and refute it. The (A)-boundary
(`AssemblyP1.ConditionalVsOrdinaryMLSeparation.condRecoveryCertain_iff`,
general #272 `posteriorMass_eq_one_iff`) has no W1/W2 instance for the
structural reasons above.
-/

namespace AssemblyP1.W1W2SeparationCompatibility

/-- Ordinary ML truth-maximizer boundary at the fixed observation `obs`, for a
fixed-observation score `score : candidate ↦ ℚ`: the truth spectrum `dS` is a
maximizer iff no candidate spectrum scores higher. The prior and any side
observation do not enter. -/
def MLTruthMaximizer {ι : Type} (score : (ι → ℕ) → ℚ) (dS : ι → ℕ) : Prop :=
  ∀ h : ι → ℕ, score h ≤ score dS

/-! ## W1: `AAATAT` (truth) versus `AAAAAT` (competitor), spectra `Fin 8 → ℕ` -/

/-- **W1 instantiates the (B)-side failure under the literal §6.1 product of
binomial marginals**: the competitor `dD` (`AAAAAT`) strictly beats the truth
`dS` (`AAATAT`) at the fixed observation, by reuse of the existing
kernel-checked ratio theorem. -/
theorem w1_truth_not_maximizer_binomial :
    ¬ MLTruthMaximizer
        (fun h => SameLengthSection62Counterexample.lik
          SameLengthSection62Counterexample.obs h)
        SameLengthSection62Counterexample.dS := by
  intro h
  exact absurd (h SameLengthSection62Counterexample.dD)
    (by linarith [SameLengthSection62Counterexample.competitor_strictly_better])

/-- **W1 instantiates the (B)-side failure under the exact same-length
multinomial objective** as well: `exactLik dD obs = 9 > 3 = exactLik dS obs`. -/
theorem w1_truth_not_maximizer_exact :
    ¬ MLTruthMaximizer
        (fun h => SameLengthSection62Counterexample.exactLik
          h SameLengthSection62Counterexample.obs)
        SameLengthSection62Counterexample.dS := by
  intro h
  have hle := h SameLengthSection62Counterexample.dD
  simp only at hle
  rw [SameLengthSection62Counterexample.exactLik_competitor,
      SameLengthSection62Counterexample.exactLik_truth] at hle
  norm_num at hle

/-- The exact multinomial score of the W1 truth at the observed sample is `3`,
not a probability: the per-class normalization `d c / G` and the multinomial
coefficient are absent from `exactFactor` by definition. -/
theorem w1_exactLik_dS_obs :
    SameLengthSection62Counterexample.exactLik
      SameLengthSection62Counterexample.dS
      SameLengthSection62Counterexample.obs = 3 :=
  SameLengthSection62Counterexample.exactLik_truth

/-- The §6.1 product-of-binomial-marginals score of the W1 truth at the
observed sample is positive; being a product of per-class binomials at fixed
external `N`, `n`, it is not a pmf over count vectors. -/
theorem w1_lik_dS_obs_pos :
    0 < SameLengthSection62Counterexample.lik
      SameLengthSection62Counterexample.obs
      SameLengthSection62Counterexample.dS :=
  SameLengthSection62Counterexample.lik_truth_pos

/-! ## W2: per-occurrence strengthening, spectra `Fin 64 → ℕ` -/

/-- **W2 (per-occurrence strengthening) instantiates the same (B)-side failure
under the §6.1 product-of-binomial-marginals objective**, reusing the existing
W2 theorem. -/
theorem w2_truth_not_maximizer_binomial :
    ¬ MLTruthMaximizer
        (fun h => PerOccurrenceSameLengthCounterexample.lik
          PerOccurrenceSameLengthCounterexample.obs h)
        PerOccurrenceSameLengthCounterexample.dS := by
  intro h
  exact absurd (h PerOccurrenceSameLengthCounterexample.dD)
    (by linarith [PerOccurrenceSameLengthCounterexample.competitor_strictly_better])

/-- **W2 instantiates the same (B)-side failure under the exact same-length
multinomial objective** (`exactLik dD obs = 18 > 12 = exactLik dS obs`),
reusing the existing W2 theorem. -/
theorem w2_truth_not_maximizer_exact :
    ¬ MLTruthMaximizer
        (fun h => PerOccurrenceSameLengthCounterexample.exactLik
          h PerOccurrenceSameLengthCounterexample.obs)
        PerOccurrenceSameLengthCounterexample.dS := by
  intro h
  exact absurd (h PerOccurrenceSameLengthCounterexample.dD)
    (by linarith [PerOccurrenceSameLengthCounterexample.exact_competitor_strictly_better])

/-- The exact multinomial score of the W2 truth at the observed sample is `12`,
not a probability, for the same structural reason as W1. -/
theorem w2_exactLik_dS_obs :
    PerOccurrenceSameLengthCounterexample.exactLik
      PerOccurrenceSameLengthCounterexample.dS
      PerOccurrenceSameLengthCounterexample.obs = 12 :=
  PerOccurrenceSameLengthCounterexample.exactLik_truth_value

end AssemblyP1.W1W2SeparationCompatibility
