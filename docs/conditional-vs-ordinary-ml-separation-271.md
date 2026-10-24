# Conditional Bayes vs ordinary finite ML: exact comparison boundaries (issue #271)

_Status: research comparison note. The abstract witness and boundary
characterizations are Lean kernel-checked in
`AssemblyP1/ConditionalVsOrdinaryMLSeparation.lean`; the historical W1/W2
(B)-side compatibility is Lean kernel-checked by reuse in
`AssemblyP1/W1W2SeparationCompatibility.lean`. The abstract toy is **not** a
source-faithful genome witness. Genome-level statements are either
kernel-checked by reuse of existing witness theorems or explicitly marked
open/external. Axiom audit: `AxiomAudit271.lean` (only `propext`,
`Classical.choice`, `Quot.sound`)._

## 1. The joint comparison diagram (axes fixed)

```
                       (A) conditional Bayes recovery     (B) ordinary finite ML recovery
                       P([G]=g | R,E) = 1                 g_true ∈ argmax_h P_h(R)  (and uniquely)
                       ---------------------------------   ---------------------------------
candidate universe     fixed finite Θ (toy: {A,B};         same fixed Θ; genome-level universes
                       genome-level: #255/#258/#259/#261)  are NOT re-classified here (no forking)
prior                  π > 0 on candidates (toy: uniform   prior does NOT enter (B); MAP = ML
                       1/2); uniform-orbit vs              under uniform positive prior
                       uniform-spelling priors differ
                       when orbit sizes differ (#269)
observation repr.      one oriented read draw r from the   same observable R; RC-collapsed molecule
                       candidate pmf (RC representation    representation (#260) is a DIFFERENT
                       is a different observable, not       observable and is not mixed here
                       mixed here)
likelihood objective   exact iid product p_g(r) (toy);      same objective; MB09 product-binomial
                       §6.1 binomial and §6.2 flow         surrogate and §6.2 flow feasibility are
                       feasibility are separate            separate objectives (#259/#261)
                       objectives, not conflated
genome-length          no constraint at toy level;         fixed-x universes: #258; arbitrary §6.2
                       fixed-x universes: #258             models: #255/#261
rotation equivalence   orbit classes of the rotation       rotation acts on candidates; ML is
                       action; orbit-size-1 vs orbit-      invariant under relabeling within an
                       size-2 toy instantiates the prior   orbit (likelihood depends on the
                       support difference                    candidate, not its spelling)
```

## 2. The exact decision boundary

* **(A)-boundary (kernel-checked).** Conditional recovery at `r` under side
  observation `E` holds iff the posterior support fibre
  `{g : π g > 0 ∧ p_g(r) > 0 ∧ E g r}` is a singleton:
  `ConditionalVsOrdinaryMLSeparation.condRecoveryCertain_iff` (toy level, with
  `condPosterior_one_imp` / `condPosterior_of_fibre`); the general orbit-class
  statement is `AssemblyP1.FiniteBayesianSideInformation.posteriorMass_eq_one_iff`
  (#272). Necessary ingredients: positive prior mass, positive likelihood, and
  `E` excluding every other orbit that `R` alone leaves possible. A data-only
  `E` (a function of `R` alone) cannot change the per-sample posterior
  (`condPosterior_dataOnly`): the indicator is constant across hypotheses at
  fixed `r` and cancels.
* **(B)-boundary (definitional, kernel-checked).** Ordinary ML
  truth-maximality at `r` holds iff `p_{g_true}(r) ≥ p_h(r)` for every
  candidate `h` (ties allowed) — `isMLMaximizer`. The unique-maximizer form
  additionally requires strict inequality off the truth
  (`ml_unique_maximizer_r1`). Neither the prior nor `E` enters (B):
  `isMLMaximizer` is a statement about the likelihood alone
  (`ml_ignores_prior_r0`).

The two boundaries are **logically independent**: neither implies the other.

## 3. The separation, both directions (kernel-checked, same generative model)

Witness (`Hypothesis = {A, B}`, `Obs = {r0, r1}`, uniform prior `1/2`,
`p_A = (1/4, 3/4)`, `p_B = (3/4, 1/4)`) with side observation
`E = sideInfo = {(A, r0), (B, r1)}` (truth-dependent, externally supplied):

* **(A ∧ ¬B)** at `r = r0` with truth `A`: conditional recovery is certain —
  `P(A | r0, E) = 1` (`condPosterior_A_r0`) — while ordinary R-only ML
  strictly prefers the wrong hypothesis `B` (`3/4 > 1/4`,
  `ml_unique_maximizer_r0`); the truth `A` is not even a maximizer
  (`truth_not_ml_maximizer_r0`) and the ordinary posterior on the truth is
  `1/4`, not certainty. Packaged as `separation_A_not_B`.
* **(B ∧ ¬A)** at `r = r1` with truth `A`: ordinary ML uniquely selects the
  truth (`3/4 > 1/4`, `ml_unique_maximizer_r1`), yet the ordinary posterior on
  the truth is `3/4`, not certainty (`posterior_A_r1_not_certain`). Packaged
  as `separation_B_not_A`. Unique-maximizer ML recovery does not give
  posterior certainty without side information.
* **Certainty is not correctness.** With the same `E`, conditioning at
  `r = r1` collapses the posterior onto the WRONG candidate `B`
  (`condPosterior_E_certifies_wrong_r1`). (A) is a statement about the
  support-collapse mechanism; whether the collapsed candidate is the truth
  depends on `E` being the right promise (cf. #272 proper-promise discussion).

## 4. Prior support: uniform sequences vs uniform rotation/RC orbits

Toy instantiation (kernel-checked): orbit sizes 1 (`A`, periodic) vs 2 (`B`).
The uniform-sequence prior `(1/3, 2/3)` and the uniform-orbit prior
`(1/2, 1/2)` differ (`priorOrbit_ne_priorSeq_A`); the posterior on `A` at
`r = r0` differs with them — `1/7` vs `1/4`
(`posteriorSeq_A_r0_ne_posterior_A_r0`) — while ordinary ML is unchanged
(`ml_ignores_prior_r0`). General treatment: `AssemblyP1.GenomeOrbitAdapter`
(#269) — the pushforward of the uniform spelling prior is uniform on orbits
iff all orbits have equal size.

## 5. W1/W2 compatibility verdict (shared observable data model)

Under the EXACT shared observable data model of the historical same-length
witnesses (candidates = genomes via spectra `dS`, `dD`; observation = the
fixed count vector `obs`; objectives = the literal §6.1 product of binomial
marginals `lik` and the exact same-length multinomial score `exactLik`):

* **(B)-side failure: YES, instantiated (kernel-checked by reuse).** At the
  fixed observation `obs`, ordinary ML strictly prefers the wrong candidate
  under both objectives — W1: `w1_truth_not_maximizer_binomial` (ratio `5`) and
  `w1_truth_not_maximizer_exact` (`exactLik dD obs = 9 > 3`); W2:
  `w2_truth_not_maximizer_binomial` and `w2_truth_not_maximizer_exact`
  (`18 > 12`). The truth is not even a maximizer. This reuses, without
  re-proving, the merged witness theorems
  (`SameLengthSection62Counterexample.competitor_strictly_better`,
  `exactLik_truth`, `exactLik_competitor`;
  `PerOccurrenceSameLengthCounterexample.competitor_strictly_better`,
  `exact_competitor_strictly_better`).
* **(A)-side: NOT instantiated (structural obstruction).** The W1/W2 model
  carries no prior over candidates, no normalized observation pmf, and no side
  event: `exactLik` is by definition the unnormalized score
  `∏ c, (d c)^(x c)` (no `d c / G` normalization, no multinomial
  coefficient), and `lik` is a product of per-class binomials at fixed
  external `N`, `n` — not a pmf over count vectors. The conditional posterior
  `P(g | obs, E)` of (A) is therefore not defined in this model. Instantiating
  (A) requires a NEW concrete adapter (normalized per-candidate observation
  model + candidate prior + promise `E`), which the #271 kernel standard
  demands be explicit and Lean-checked before any genome-level
  conditional-recovery claim; none is claimed here.
* **Full two-sided separation: NOT instantiated** by existing W1/W2 under this
  shared model — only the (B)-failure half is.
* **Representation warnings.** The historical W1/W2 witnesses are
  **reverse-complement molecule** witnesses: their observable is the
  molecule-class count `obs` (oriented windows collapsed through the molecule
  class `cls`), not the oriented read-string representation
  (`SourceFaithfulIs.window`) that the Not-So-Greedy model uses. `cls` is
  non-injective, so the molecule observable is a strict quotient of the oriented
  one; the two must not be identified (kernel-checked in
  `AssemblyP1/W1W2RcOrientedRepresentation271.lean`). The historical matched
  read-string coverage (`HistoricalCovers`, #247) versus latent-start
  (`InformationFeasible`) variants do not affect the likelihood comparison,
  which concerns the count vector `obs`, not coverage.
* **Necessary conditions do not guarantee (B).** The weaker
  information-theoretic necessary conditions (coverage, repeat bridging) do
  not guarantee ordinary ML recovery: W1/W2 satisfy their source certificates
  while ordinary ML fails (kernel-checked above). Companion analysis:
  `docs/audit-267-finite-ml-vs-conditional-bayes.md` — for most witnesses the
  competitor fails `I_s` so conditional-on-`I_s` MAP excludes it, but for
  W3 (`AABB`/`ABAB`) and W6 (`AABBC`/`AABC`) the competitor satisfies `I_s`
  as well, so even the conditional rule fails there.

## 6. Fixed-sample (R = x): tautological vs structural

In fixed-sample comparisons, "the truth's complete likelihood score is
maximal" is a tautological complete score comparison unless the candidate
universe, objective, and tie semantics are fixed; the meaningful structural
content is the classification of WHEN the score comparison holds (#255
umbrella; #258 fixed-x exact ML; #259 binomial approximation; #261 general
bidirected flow; #256/#260 restricted sample-uniform iff). This note does not
re-open those classifications; it only records that the (B)-boundary is
prior-free and `E`-free, so no fixed-x classification result can transfer to
(A) without adding the conditional layer (prior + promise + normalized
observation model).

## 7. Which refinements would establish E → B, refute it, or guarantee A

* **E → B (ordinary ML recovery from side information):** would require `E` to
  carry information about `R` beyond the truth-dependent promise — e.g., a
  promise that also constrains the observation (coverage/bridging-style
  conditions on the sampled starts). A truth-dependent promise alone cannot
  imply (B): `separation_A_not_B` exhibits `E` with (A) certain and (B)
  failing. **Open conjecture (refuted in general):** no truth-dependent `E`
  implies (B) without an observation-side component; a sufficient refinement
  is `E = F(G,R) ∧ C(R)` with `C` an observation-side necessary condition
  that is also sufficient for (B) on the fixed candidate universe (the
  #255/#258 classifications are candidates for `C`, universe-restricted).
* **Guaranteeing A:** (A) is guaranteed whenever the promise `E` excludes
  every orbit that `R` alone leaves possible while retaining the true orbit
  with positive prior and positive likelihood
  (`condRecoveryCertain_iff`; #272 `posteriorMass_eq_one_iff_excluded`).
  "Knowing the truth satisfies `F`" as side information is NOT the same as
  running ordinary ML over `F`-qualified candidates (the former is a
  conditional experiment, the latter a restricted unconditional one), and NOT
  the same as a theorem for unrestricted likelihood.
* **Maximizer vs unique maximizer:** the (B)-boundary has both forms;
  `separation_B_not_A` shows the unique form still does not give (A).
  **Open:** whether unique-maximizer (B) plus a uniform-orbit prior and a
  proper promise gives (A) — this is exactly the #272 proper-promise question
  and is not settled here.
* **Prior support:** with equal orbit sizes the uniform-spelling and
  uniform-orbit priors coincide (#269); with differing orbit sizes they do
  not, and (A)/(MAP) is prior-sensitive while (B)/ML is not (Section 4).

## 8. Manuscript-safe wording (for #265/#268, non-competing)

> For a fixed finite candidate universe, conditional Bayes recovery with
> side information `E` and unconditional ordinary maximum-likelihood recovery
> are logically independent guarantees. Conditional recovery at an
> observation holds exactly when the posterior support fibre — candidates of
> positive prior and positive likelihood not excluded by `E` — is a single
> rotation orbit; ordinary ML truth-maximality holds exactly when the true
> candidate's likelihood dominates every candidate's, independently of the
> prior and of `E`. A truth-dependent side observation can therefore yield
> posterior certainty while ordinary ML strictly prefers a wrong candidate,
> and conversely ordinary ML can uniquely select the truth while the
> unconditional posterior remains uncertain. The historical same-length
> witnesses W1/W2 instantiate the second guarantee's failure under the exact
> §6.1-binomial and exact-multinomial objectives at their fixed observed
> count vectors; they do not instantiate the conditional guarantee, which
> requires a prior, a normalized observation model, and a promise that the
> witness model does not contain.

## 9. Tiny-table sanity regressions: ties, zero-likelihood competitors, MAP vs ML

_Added by the follow-up to PR #232; Lean kernel-checked in
`AssemblyP1/ConditionalVsOrdinaryMLBoundary271.lean` (audited in
`AxiomAudit271.lean`). Abstract finite pmf regressions, not genome witnesses._

The single separation table of Section 3 is not the whole boundary. The
degenerate cases the #271 comparison must distinguish are pinned by three tiny
exact-rational tables:

* **Ties (maximizer vs unique maximizer).** With `p_A = p_B = (1/2, 1/2)` at
  `r = r0`, the truth `A` is an ordinary-ML maximizer but **not** the unique
  maximizer (`ml_tie_A_r0`, `ml_tie_not_unique_r0`), and the unconditional
  posterior on `A` is `1/2`, not certainty (`post_tie_A_r0`). Packaged as
  `tie_maximizer_posterior_not_certain`: neither the maximizer nor the
  unique-maximizer form of (B) gives (A).
* **Zero-likelihood competitors (overlap).** With `p_A = (1, 0)`,
  `p_B = (0, 1)`, the candidate `B` has zero likelihood at `r = r0`, so it is
  excluded from the posterior automatically: `post2 A r0 = 1`,
  `post2 B r0 = 0` (`zero_likelihood_overlap`), and `A` is the unique ordinary
  ML maximizer. This is an **overlap** of the two guarantees and the concrete
  shadow of the general excluded-orbit result
  `AssemblyP1.FiniteBayesianSideInformation.posteriorMass_eq_one_iff_excluded`
  (#272). No prior rescues the excluded candidate: with the skewed prior
  `π = (9/10, 1/10)` the posteriors are unchanged (`post_zero_A_r0_skew`,
  `post_zero_B_r0_skew`).
* **Uniform vs nonuniform prior (MAP vs ML).** On the Section-3 likelihood
  table `p_A = (1/4, 3/4)`, `p_B = (3/4, 1/4)`, ordinary ML at `r = r0`
  prefers `B` (`3/4 > 1/4`). Under the uniform prior the posterior maximizer
  is also `B`; under the skewed prior `π = (9/10, 1/10)` the posterior
  maximizer flips to `A` (`map_ne_ml_nonuniform`, `prior_flips_MAP_not_ML`).
  The prior moves MAP but not ML. The general equivalence of posterior
  maximizer and joint-mass maximizer is #269
  (`AssemblyP1.GenomeOrbitAdapter.PosteriorMAP.posterior_argmax_iff`); this is
  only its concrete two-candidate instantiation, not new generic MAP
  infrastructure.

Summary of the boundary, case by case (truth `A` at the shown observation):

| table | likelihood order | ordinary ML (B) | posterior (A) | overlap/separate |
|---|---|---|---|---|
| Section 3, `r = r0` | `B` strictly higher | `B` unique | `1/4` | separate (A∧¬B via `E`) |
| Section 3, `r = r1` | `A` strictly higher | `A` unique | `3/4` | separate (B∧¬A) |
| tie | equal | `A` non-unique | `1/2` | separate (B non-unique ∧ ¬A) |
| zero-likelihood | `A` strictly higher | `A` unique | `1` | **overlap** |
| MAP vs ML, skew prior | `B` strictly higher | `B` unique | `3/4` (posterior argmax `A`) | MAP ≠ ML |
| strict-separation `likHi` | `A` strictly higher (`2/3 > 1/3`) | `A` unique | `2/3` | separate (unique B ∧ ¬A) |

* **Unique ML maximizer without posterior certainty.** On the strictly
  separated table `likHi` (`p_A = (2/3, 1/3)`, `p_B = (1/3, 2/3)`) at
  `r = r0`, the truth `A` is the *unique* ordinary-ML maximizer while the
  unconditional posterior on `A` is `2/3 ≠ 1`
  (`unique_ml_posterior_not_certain`, with `ml_hi_A_unique_r0`,
  `post_hi_A_r0`). Uniqueness of the ML maximizer is therefore orthogonal to
  posterior certainty: Table 2 (zero-likelihood) has unique ML *with*
  certainty, this table has unique ML *without* certainty. This is the
  abstract tiny-table shadow of the genome-adapter converse
  (`conv_ml_unique` + `conv_ordinary_not_certain`).
