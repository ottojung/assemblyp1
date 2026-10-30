# White-paper verification index

## Reader entry points: shared read models and headline contracts

- [Headlines.lean](../AssemblyP1/Headlines.lean) provides a kernel-checked
  navigational index of the principal finite counterexamples, MAP optimality,
  primitive-P2 population uniqueness, restricted same-length uniqueness, and
  finite-read recovery results. Its aliases preserve all hypotheses of the
  existing proof endpoints. Inspect the inferred full types with the Lean
  #check command. Historical source interpretations and computational-only
  claims are NOT turned into Lean theorems.
- [ExactReadLikelihood.lean](../AssemblyP1/ExactReadLikelihood.lean) defines
  uniform-start oriented circular read probabilities, an exact multinomial
  score, and a SEPARATE fixed-reference-length binomial surrogate.
- [ExactReadLikelihoodAdapters.lean](../AssemblyP1/ExactReadLikelihoodAdapters.lean)
  proves pointwise equality of the old exact and binomial witness scores to
  their matching shared objectives for every candidate. It also proves
  correspondences for the Issue209EAudit score and both oriented rigidity
  and variable-length witness windows.
- [Legacy/reachability audit](likelihood-model-and-archive-audit.md) records
  the observational model boundary and intentionally preserved historical
  root-level artifacts excluded from the Lean library glob.

Neither the exact nor the binomial definition asserts equivalence to the
reverse-complement molecule law or the historical bidirected physical flow
domain, whose admissible candidates and objectives are distinct.



This is the **claim → exact formal endpoint → independent check** index for
[*The Most Likely Genome*](../paper/main.tex). Its role is to keep the research
paper readable while preserving verifiable proof provenance in the repository.
This index names source files and declarations that exist in this repository;
where a claim has no dedicated script, we do not invent one.

## How to reproduce

Use the pinned Lean/Mathlib toolchain at the repository root:

~~~sh
lake build
lake env lean AssemblyP1/Issue94Complete.lean
lake env lean AssemblyP1/PrimitiveP2FiniteClassAudit.lean
python3 scripts/verify_247c_historical_witnesses.py
python3 scripts/verify_nonmonotonicity_witness_281.py
sh paper/build.sh
~~~

The Lean commands compile/check the imported proofs, with axiom audits in the
named sources. The Python verifiers independently recompute selected finite
certificates and are **not** replacements for Lean proofs. The paper build uses
the pinned Guix/TeX environment described in
[paper/README.md](../paper/README.md). Historical-source correspondence,
and an external reconstruction premise, are not established by running these
commands.

Module-relative identifiers below must be read in the linked Lean file's
namespace. In the conditional-posterior row, **eventJoint** belongs to the
**ConditionalIdentifiability** namespace, while **ReadModel.conditional_posterior_eq_one**
and **ReadModel.constrained_MAP_mem_orbit** are theorem names inside it.
The complete population theorem is fully qualified below.
Click the source to inspect the exact hypotheses.

## Primary claims and evidence

| Claim | Exact Lean endpoint or source | Independent check / caveat |
| --- | --- | --- |
| MAP maximizes prior-average exact reconstruction success, deterministic and randomized | [FiniteBayesDecision.lean](../AssemblyP1/FiniteBayesDecision.lean): **chooseMAP_optimal**, **chooseMAP_optimal_randomized**, **finite_iid_MAP_optimal** | Standard finite-model Bayes theorem, not per-truth ML optimality |
| Tiny explicit iid Bayes/MAP check at n=0 and n=1 | [FiniteBayesTwoHypothesisWitness.lean](../AssemblyP1/FiniteBayesTwoHypothesisWitness.lean): **prior_normalized**, **readPmf_normalized**, **empty_policy_optimal**, **one_read_policy_optimal**, **empty_success_eq_half**, **one_read_success_eq_half** | Uniform prior on two candidates and a fair binary read law identical under both candidates; explicit tie policy; didactic finite instance, not a replacement for the general theorem |
| Finite Bayes/MAP optimality certificate (necessary and sufficient), tie witness, posterior-one boundary | [BayesOptimalityCertificate.lean](../AssemblyP1/BayesOptimalityCertificate.lean): **pointwiseMAP_iff_bayesOptimal**, **bayesOptimal_imp_pointwiseMAP**, **not_pointwiseMAP_imp_strict_loss**, **TieWitness.both_optimal**, **pointwiseMAP_forces_strictMax**, **posterior_eq_one_iff_singleton_support**, **orbit_posterior_eq_one_iff_singleton_support** | [BayesOptimalityCertificateAudit.lean](../AssemblyP1/BayesOptimalityCertificateAudit.lean); [exact verifier](../scripts/verify_269_bayes_optimality_certificate.py). Deterministic policies over arbitrary real joint mass; the tie witness shows optimality does not force a unique rule; posterior-one boundary needs nonnegative mass and positive predictive mass; not per-truth optimality |
| Standalone model-level Bayes/MAP evaluator, with concrete witnesses | [FiniteMapOptimality.lean](../AssemblyP1/FiniteMapOptimality.lean): **bayes_optimality**, **map_beats_infallible_on_E**, **map_ne_ml_nonuniform** | Explicit **Finset.exists_max_image**; exact `ℚ`; endpoint axioms `{propext, Classical.choice, Quot.sound}`; `leanchecker` clean |
| Optimal prior-average success is nondecreasing in sample size (`V_n ≤ V_{n+1}`), general and genome-rotation-class instances | [IidMapMonotonicity.lean](../AssemblyP1/IidMapMonotonicity.lean): **iid_map_success_monotone**; [BayesValueMonotonicity.lean](../AssemblyP1/BayesValueMonotonicity.lean): **bayesValue_succ_ge** (iterated **bayesValue_mono**); [GenomeOrbitAdapter.lean](../AssemblyP1/GenomeOrbitAdapter.lean): **orbit_map_success_monotone** | Kernel-checked; the `ignore extra observation` argument. Prior-averaged only: per-truth success can drop (see non-monotonicity row below) |
| Conditional event-restricted posterior and MAP (Question A) | [ConditionalIdentifiability.lean](../AssemblyP1/ConditionalIdentifiability.lean): **eventJoint**, **ReadModel.conditional_posterior_eq_one**, **ReadModel.constrained_MAP_mem_orbit** | Uses weights π(g)P_g(r)1_{F(g,r)} and **assumes** the external decoder-correctness/reconstruction interface. Not ordinary ML |
| Positive same-length oriented complete-spectrum circulation rigidity | [OrientedFinalRigidity.lean](../AssemblyP1/OrientedFinalRigidity.lean): **oriented_same_length_spectrum_rigidity**; [OrientedRigidity.lean](../AssemblyP1/OrientedRigidity.lean): **rigidity_same_spectrum** | [Oriented support script](../scripts/verify_oriented_se62_rigidity.py). Same total length and full-overlap support |
| No strict same-length counterexample: spectrum-factored objectives tie | [OrientedFinalRigidity.lean](../AssemblyP1/OrientedFinalRigidity.lean): **spectrum_objective_tie** | Kernel-checked; equal spectra give equal objective values for every spectrum-factored objective (cor:same-length-zero), **not** maximizer uniqueness |
| Variable-length primitive identifiability iff nonbranching | [ScalarPrimitiveSpellings.lean](../AssemblyP1/ScalarPrimitiveSpellings.lean): **identifiable_iff_nonbranching** | Kernel-checked; primitive truth, no external complete-spectrum uniqueness premise |
| Same-length complete-spectrum fibre count and singleton criterion | [FibreCountArithmetic.lean](../AssemblyP1/FibreCountArithmetic.lean): **fibre_mobius_inversion**, **fibre_totient** | Divisor-sum core kernel-checked; full count is a mathematical proof ([exact-fibre-count-theorem-219.md](../docs/exact-fibre-count-theorem-219.md)); BEST theorem and branching construction are external |
| Exact robust same-length oriented ML iff | [RobustSameLengthIff.lean](../AssemblyP1/RobustSameLengthIff.lean): **robust_iff_unique_spectrum** | Kernel-checked; paper states only the beatability direction (prop:beatability) |
| Source-faithful full-overlap molecule ML maximality iff | [FullOverlapMoleculeML.lean](../AssemblyP1/FullOverlapMoleculeML.lean): **robust_maximality_iff_unique** | Kernel-checked; paper states only negative molecule witnesses (thm:cex-molecule) |
| Same-length genuine §6.2 maximizer and rotation uniqueness | [SameLength62Maximizer.lean](../AssemblyP1/SameLength62Maximizer.lean): **informationFeasible_62_maximizer_of_exact_R**; [SameLength62Uniqueness.lean](../AssemblyP1/SameLength62Uniqueness.lean): **unique_62_maximizer_up_to_rotation** | Requires actual realized placements, **truth and competitor candidacy**, oriented reads and equal length |
| Exact multinomial witness AAABB → AAAAB | [FixedLengthExactCounterexample.lean](../AssemblyP1/FixedLengthExactCounterexample.lean): **fixed_length_exact_counterexample**, **likelihood_ratio** | Kernel-checked strict ratio 2, placement-based feasibility |
| Fixed-N binomial witness AAACC → AAAAC | [FixedLengthBinomialCounterexample.lean](../AssemblyP1/FixedLengthBinomialCounterexample.lean): **fixed_length_binomial_counterexample** | Kernel-checked ratio 1125/512, zero-count factors included |
| Same-length truth-candidacy boundary AABB → ABAB | [SameLengthExactMLCounterexample.lean](../AssemblyP1/SameLengthExactMLCounterexample.lean): **same_length_exact_ML_refutation_62**, **truth_likelihood**, **competitor_likelihood** | Truth is **not** §6.2-admissible; competitor is. Exact multinomial values 1/8 and 1/2 |
| Oriented variable-length boundary AAATT → AAAATT | [OrientedVariableLengthSe62.lean](../AssemblyP1/OrientedVariableLengthSe62.lean): **oriented_variable_length_se62_counterexample** | [Direct witness](../scripts/verify_oriented_variable_length_se62.py), [multiplicity amplification](../scripts/verify_oriented_variable_length_se62_amplification.py). General family has a separate paper/notes proof |
| Reverse-complement molecule variable-length counterexample | [Section62BridgingCounterexample.lean](../AssemblyP1/Section62BridgingCounterexample.lean): **se62_bridging_bidirected_flow_counterexample** | [Independent verifier](../scripts/verify_se62_bridging_flow_counterexample.py); molecule types differ from oriented types |
| Historical matched-string W1: AAATAT → AAAAAT | [HistoricalCoverageSameLengthWitnesses.lean](../AssemblyP1/HistoricalCoverageSameLengthWitnesses.lean): **W1.w1_historical_literal_se62_flow_counterexample** | [247c verifier](../scripts/verify_247c_historical_witnesses.py), full historical triple-repeat clause, genuine bidirected flows, exact/binomial ratios 3 and 5 |
| Historical matched-string W2: ATATACAC → ATACACAC | Same file: **W2.w2_historical_literal_se62_flow_counterexample** | Same script; truth and competitor per-occurrence feasible, ratios 3/2 and 9/5 |
| Historical matching differs from placements | [HistoricalCovers.lean](../AssemblyP1/HistoricalCovers.lean), [HistoricalCoverageSameLengthWitnesses.lean](../AssemblyP1/HistoricalCoverageSameLengthWitnesses.lean): **regA_historicalCovers**, **regB_not_historicalCovers** | [Historical predicate audit](../scripts/verify_historical_coverage_audit.py); model predicates are incomparable |
| Finite sampling witness AABBC → AABC | [FiniteSamplingCounterexample.lean](../AssemblyP1/FiniteSamplingCounterexample.lean): **finite_sampling_counterexample**, **likelihood_ratio** | **Kernel-checked**, ratio 25/16; not merely an exact computation |
| Non-spellable §6.2 flow optimum | [Section62NonSpelledFlow.lean](../AssemblyP1/Section62NonSpelledFlow.lean): **nonspelled_se62_flow_domain_countermodel** | [Flow script](../scripts/verify_se62_nonspelled_flow_domain.py); a feasible optimum need not be a genome |
| Disconnected full-overlap optimum | [Section62FullOverlapDisconnected.lean](../AssemblyP1/Section62FullOverlapDisconnected.lean): **full_overlap_disconnected_optimum** | [Flow script](../scripts/verify_se62_full_overlap_disconnected_optimum.py); disconnected does **not** imply non-spellable |
| Graver-basis criterion for integral-flow rigidity | [GraverRigidity.lean](../AssemblyP1/GraverRigidity.lean): **GraverBasis.rigid_iff_forall_graver_not_inbox** | [GraverRigidityAudit.lean](../AssemblyP1/GraverRigidityAudit.lean), for the specified finite positive circulation domain |
| Unconstrained-KKT counterexample at a discrete exact-multinomial optimum | [SeparableConvexKKTRefutation263.lean](../AssemblyP1/SeparableConvexKKTRefutation263.lean): **mlCost_slope_neg**, **mlCost_slope_ne_zero**, **mlCost_slope_at_truth**, **truth_gradient_ne_zero** | [Axiom audit](../AssemblyP1/SeparableConvexKKTRefutation263Audit.lean). In the four-class `AAABBB` case all positive truth-count slopes are `-1`, not zero; this refutes *unconstrained* stationarity, while the constrained fixed-total multiplier remains valid. Does not settle arbitrary RC §6.2 flow optimization. |
| Fixed-N binomial effective-weight criterion | [FixedNBinomialEffectiveWeights.lean](../AssemblyP1/FixedNBinomialEffectiveWeights.lean): **effectiveProduct_eq_binomialNumerator**, **every_observation_effectiveProduct_le_iff** | [Effective-weights script](../scripts/verify_fixedn_effective_weights_259.py). This is a surrogate objective, not exact iid ML |
| Gibbs/KL maximality and equality of read laws | [PopulationGibbs.lean](../AssemblyP1/PopulationGibbs.lean): **truth_is_population_maximizer**; [PopulationMaximizerUnrestricted.lean](../AssemblyP1/PopulationMaximizerUnrestricted.lean): **population_maximizer_unrestricted** | Maximality alone does **not** establish uniqueness |
| **Unconditional primitive-P2 population uniqueness** | **[Issue94Complete.lean](../AssemblyP1/Issue94Complete.lean): population_unique_ML** | Fully qualified: **AssemblyP1.Issue94Complete.population_unique_ML**. **No EulerianCycleObstruction hypothesis**. Internally proved long-window step; see its **#print axioms** |
| Primitive-P2 intrinsic length bound and class finiteness | [PrimitiveP2FiniteClass.lean](../AssemblyP1/PrimitiveP2FiniteClass.lean): **primitive_P2_len_le**, **primitiveP2Class_finite** | [PrimitiveP2FiniteClassAudit.lean](../AssemblyP1/PrimitiveP2FiniteClassAudit.lean); bound 2q^(L−1), no arbitrary genome-length cutoff |
| Tightness of the length bound at K = 1 | [PrimitiveP2FiniteClassTight.lean](../AssemblyP1/PrimitiveP2FiniteClassTight.lean): **exists_primitive_P2_at_bound_K1**, **maxLen_two**, **no_triple**, **repeat_consec**, **not_interleaved** | [PrimitiveP2FiniteClassTightAudit.lean](../AssemblyP1/PrimitiveP2FiniteClassTightAudit.lean); the doubled-alphabet word `0 0 1 1 … (q−1)(q−1)` attains `G = 2q = maxLen 2` for **every** `q ≥ 2`, using the source-faithful maximal-repeat definitions |
| Finite-family Hellinger union bound | [FiniteReadRecovery.lean](../AssemblyP1/FiniteReadRecovery.lean): **eventProb_pairwise**, **eventProb_wrong_le_sum**, **eventProb_wrong_tendsto_zero** | [FiniteReadRecoveryAudit.lean](../AssemblyP1/FiniteReadRecoveryAudit.lean); iid read laws, finite distinguishable family |
| Complete primitive-P2 finite-read confidence | [PrimitiveP2FiniteClass.lean](../AssemblyP1/PrimitiveP2FiniteClass.lean): **all_primitiveP2_ML_confidence** | [FiniteReadRecoveryP2Complete.lean](../AssemblyP1/FiniteReadRecoveryP2Complete.lean): **finite_primitiveP2_ML_confidence**; no finite-family input for the **entire** class |
| Explicit uniform exponential exact-ML error rate | [PrimitiveP2UniformSeparation.lean](../AssemblyP1/PrimitiveP2UniformSeparation.lean): **readLaw_separation**, **one_sub_hellinger_ge_of_gap**, **primitiveP2_exponential_error_bound**, **primitiveP2_ML_confidence_explicit**, **readLawFamily_card_le** | [PrimitiveP2UniformSeparationAudit.lean](../AssemblyP1/PrimitiveP2UniformSeparationAudit.lean); bound `N_C exp(-n/(8 B^4))`, `B = 2 q^(L-1)`, threshold `n >= 8 B^4 log(N_C/delta)`. Constants deliberately loose (exponential in `L`); exact oriented iid only; not universal ML and not the MB09 product-binomial surrogate |
| No uniform exponential exact-ML rate over the length-unrestricted universe; kernel-checked `1/(8 B^4)` exponent is valid but loose (extremal one-symbol insertions suggest sharp `Θ(1/B)`) | Research note [restricted-vs-unrestricted-exponent-265.md](restricted-vs-unrestricted-exponent-265.md) | **Paper-level exact computation, NOT kernel-checked**: `AB` vs `ABAB` read-law collision gives error probability 1 for every `n`; exact check [verify_exponent_265.py](../scripts/verify_exponent_265.py). The sharp-exponent `c_1/B` lower bound is a named missing lemma, not proved |
| Bridging-conditioned ML error bound | [Section 3 corollary](../paper/sections/03-open-question.tex) and **eventProb_wrong_le_sum** above | **Paper-level corollary**: P(error given B) ≤ P(error)/P(B), P(B)>0. No dedicated Lean formalization claimed |
| Per-truth finite-sample ML non-monotonicity | [NonmonotonicityWitness281.lean](../AssemblyP1/NonmonotonicityWitness281.lean): **succ_one**, **succ_two**, **success_not_monotone** | [Exact enumeration script](../scripts/verify_nonmonotonicity_witness_281.py). The n=1,2 result is kernel-checked; later tabulated values are independently computed |
| Strong consistency on a finite identifiable family (eventual a.s. exact-ML selection; P(correct at n) -> 1; no finite n supplied) | [Section 5.6 proposition](../paper/sections/05-population.tex): **prop:strong-consistency** (Section **sec:strong-consistency**) | **Paper-level, classical (EXTERNAL)**: strong law + KL nonnegativity, Durrett 2019; Cover & Thomas 2006; NOT kernel-checked. Exact mechanism check: [verify_strong_consistency_265.py](../scripts/verify_strong_consistency_265.py) |
| One-sided likelihood-ratio exponent for finite identifiable families: E_+(p,q)=-ln inf_{t>0} E_p[(q/p)^t], with errors counted on L_q >= L_p, and asymptotic family rate E_* = min_D E_+ | [Section 3 proposition](../paper/sections/03-open-question.tex): **prop:chernoff-refinement**, **rem:chernoff-sharp** | **Paper-level, classical (EXTERNAL), NOT kernel-checked**: the symmetric Chernoff information with t in [0,1] is not always sharp for this one-sided event. The AAB/AABB genome example (L=2) has zero error at all positive sample sizes, E_+=infinity, but symmetric Chernoff ln(4/3). The Hellinger rho_* result remains kernel-checked in [FiniteReadRecovery.lean](../AssemblyP1/FiniteReadRecovery.lean). [Revised note](chernoff-exponent-finite-recovery-265.md); [independent verifier](../scripts/verify_chernoff_finite_recovery_265.py) |
| Exact finite-n minimax/optimal recovery for one explicit read family (`A=(1/2,1/2)`, `B=(3/4,1/4)`, `C=(1/4,3/4)`): prior-averaged `n*=85` and minimax-over-truths `n*=87` for 99%; least-favourable prior + optimally tie-split certificate; kernel-checked Hellinger union bound is conservative (`n=153`) | [Section 3 remark](../paper/sections/03-open-question.tex): **rem:minimax-sample-size** | **Paper-level, classical (EXTERNAL)**: finite Bayes risk, minimax = maximum Bayes risk over priors, Berger 1985; Lehmann & Casella 1998; NOT kernel-checked. Abstract Bayes optimality is kernel-checked ([FiniteBayesDecision.lean](../AssemblyP1/FiniteBayesDecision.lean), [FiniteMapOptimality.lean](../AssemblyP1/FiniteMapOptimality.lean)). Note [minimax-finite-recovery-265.md](minimax-finite-recovery-265.md); exact check [verify_minimax_finite_recovery_265.py](../scripts/verify_minimax_finite_recovery_265.py) |
| Spelling preservation and unsafe overlap deletion | [Section62GlobalSpellingPreservation.lean](../AssemblyP1/Section62GlobalSpellingPreservation.lean): **global_walk_signed_expansion**; [Section62ReductionMismatch.lean](../AssemblyP1/Section62ReductionMismatch.lean): **longer_is_not_spelling_preserving** | Distinguishes graph connectivity from correctly spelled genome sequences |

The AAABCBC → AAAAABC ratio 27 is an independently verified finite
computation, **not** claimed as a Lean theorem here:
[verify_readtiled_exact_counterexample.py](../scripts/verify_readtiled_exact_counterexample.py).

## Population theorem: do not confuse these two endpoints

[PopulationUniqueness.lean](../AssemblyP1/PopulationUniqueness.lean)
contains **population_unique_ML_up_to_rotation**, but its declaration has
an explicit hypothesis **hPevzner : EulerianCycleObstruction**.
It is a useful conditional interface, **not the proof** of the unconditional
result asserted in the paper.

The correct published-paper endpoint is
**AssemblyP1.Issue94Complete.population_unique_ML** in
[Issue94Complete.lean](../AssemblyP1/Issue94Complete.lean).
It assumes a positive genome length, read length at least two,
primitivity and P2 of the truth. It concludes (i) population
maximality and (ii) rotation uniqueness of every population tie against
all positive-length P2-admissible candidates. It has no separate
Eulerian-obstruction input; its long-window obligation is discharged
internally. The two propositions are **not interchangeable**.

## Evidence and modeling boundaries

- **External reconstruction:** The original Not-So-Greedy and historical
  matched-string predicates come from Shomorony et al. (2016).
  The conditional-Bayes derivation assumes their reconstruction guarantee
  through a decoder-correctness interface.
- **Model distinction:** Placement-based feasibility, historical
  matched-string bridging, oriented reads, and reverse-complement molecule
  types represent different experiments and cannot be swapped silently.
- **Scripts versus proofs:** A script establishes only its finite
  arithmetic or enumerative scope. An axiom audit applies to the *exact*
  named theorem, not every theorem in a similarly named module.
- **Error-exponent caveat:** Primitive-P2 finiteness ensures a strict
  exponential rate, and `PrimitiveP2UniformSeparation` now supplies an explicit
  one (`N_C exp(-n/(8 B^4))`, `B = 2 q^(L-1)`). The constants are deliberately
  loose --- `B` is exponential in the read length `L` and `N_C` is enormous ---
  so this is a positive rate, not a practical sample-depth estimate. The bound
  is on the probability of exact-ML error, not on the likelihood, and it does
  not make per-truth finite-sample success monotone.
- **Historical filenames:** Some files retain issue-numbered names for
  repository traceability. The paper instead uses theorem names and this
  index preserves the exact paths needed to reproduce them.


## Oriented AAATT historical witness and unrestricted finite-sample bound

The revised paper's introductory example and
\`thm:aaatt-unrestricted\` use the exact oriented, uniform-start
read law. On \`S=AAATT\` at \`L=3\` all five truth read types
appear in the example; the historical matched-string coverage and
triple-bridging conditions are proved directly in the paper.
The exact likelihood ratio against \`D=AAAATT\` is
\`15625/11664\`.

The unconditional finite-sample statement is a **paper-level theorem**,
not a new Lean declaration. Its elementary proof optimizes along
explicit genome spellings
\`D(j,k)=A^(j+2)TT(AATT)^(k-1)\`, whose normalized
3-spectra have counts \`(j,k,k,k,k)/(j+4k)\`.
It proves only the necessary event \`5*x_AAA=n\` for unrestricted ML,
not a general \`E-V\`-codimension theorem. Independent exact rational
regressions, source-model window checks and the numerical
binomial probabilities are in
\`scripts/verify_aaatt_historical_kkt.py\` and run in CI.
The source-correspondence and KKT generalization boundaries
remain explicit.


## Fixed-truth unrestricted ML obstruction on branching read-support graphs

\`thm:unrestricted-branching-rate\` is a **paper-level** theorem.
It uses the integer circulation realization lemma (positive rational
balanced de Bruijn flows on the truth support are realized by genuine
circular spellings), first-order stationarity of the exact
log-likelihood, and an elementary multivariate lattice
anti-concentration bound proved using Fourier inversion.
For fixed truth and read length, if the support graph has
\`d = |E|-|V| > 0\`, then
\`P(truth is unrestricted exact-ML maximizer)=O(n^(-d/2))\`.

The theorem is **not** a new Lean endpoint and does not imply a
uniform bound when genome length or read length varies with sample
size. It does not extend to the primitive-P2-restricted maximum
likelihood candidate class or non-spellable physical flow
optimizers. This is the rigorous fixed-truth version of the
reviewer's stationarity/codimension proposal, not a resolution
of the growing-genome threshold question.


## paper-v1.2.0: Unattained ML, one-sided length bounds, MAP priors

Theorem \`thm:unattained-ML\` is a **paper-level proof**, not a Lean
endpoint. For primitive P2 truth \`AAACAC\` at \`L=3\` and a
seven-read sample with an extra \`AAC\`, an irrational law
with coefficients in \`Q(sqrt(73))\` uniquely maximizes the
likelihood on the **complete four-letter de Bruijn flow
polytope**. Every finite circular genome has a rational
read law, but positive rational Eulerian circulations
converge to that unique optimum, so the maximum is not
attained. \`scripts/verify_irrational_ml_nonattainment.py\`
certifies exact KKT equalities on the five observed edges,
strict dual inequalities on all 59 unobserved edges,
rational balance, and explicit circular Eulerian
approximations. This test does not formalize the
concavity/Eulerian/density proof in Lean.

Theorem \`thm:one-sided-length-window\` derives from
the primitive-P2 gcd-one theorem and complete-spectrum
uniqueness. If the truth has length G, no non-rotation
genome of length less than 2G can have the same oriented
read law, even without competitor P2 or primitivity.
The finite-family Hellinger bound gives a paper-level
corollary of exponential exact-ML recovery over any
supplied length ceiling B with G <= B < 2G.
\`scripts/verify_one_sided_length_window.py\` exhaustively
compares AAATT and AAACAC against 40,956 candidate
binary circular genomes of lengths through 2G+2.
The double-length boundary is sharp because S squared
is a read-law twin.

Proposition \`prop:length-prior-map\` is also a
**paper-level** result: the proper rotation-class prior
pi([D]) proportional to beta^|D|, 0 < beta < 1/|Sigma|,
ensures that every nonzero-marginal sample has an
attained posterior mode, and eventually selects
the true rotation class almost surely for each fixed
primitive P2 truth. Its proof uses countable-mixture
posterior concentration on the observational-equivalence
fibre; a summable prior without a favourable preference
within that fibre does not guarantee truth recovery.

None of these three general statements is claimed as
a kernel-checked Lean theorem. In particular, the
fixed-genome and bounded-length rates are not uniform
over a growing-genome bridging threshold.


## Balanced-flow supremum and exact attainability

\`thm:flow-supremum-attainment\` gives a paper-level
characterization of unrestricted exact multinomial likelihood.
The supremum over all finite circular genomes equals the
attained maximum of the concave log-likelihood over the compact
polytope of nonnegative unit-mass balanced read circulations.
A maximizing \`genome\` exists if and only if at least one
optimal flow has rational masses and connected positive-edge
support. Connected rational flows are realized by Eulerian
spelling; positive uniform perturbations of rational cycle
decompositions make realizable genome laws dense in the
balanced polytope.

\`prop:balanced-sample-attainment\` is a more operational
special case: for a balanced observed count vector, the
unique optimal real law is exactly the empirical read
distribution. The unrestricted maximum is attained
iff the observed support graph is connected. Even rational
optimizers can fail to correspond to any one circular genome:
a sample consisting of \`AAA, CCC\` at read length three has
supremum \`1/4\` for ordered reads, approached by
\`A^m C^m\`, but no maximizing genome.

\`scripts/verify_unrestricted_flow_attainment.py\` checks
every binary read-count vector with entries 0--2 for the
eight 3-mers, enumerates connected and disconnected balanced
flows, spells all 114 connected cases, verifies finite
non-attainment for the disconnected two-loop witness,
and constructs connected, full-support rational
approximants. The criterion and density proof are
mathematical arguments, **not new Lean declarations**.

## CI-generated title-page source link

\`paper/build.sh\` computes the exact checked-out
commit via \`git rev-parse HEAD\` and generates
\`paper/build-identity.tex\` on every build. The
first page contains only a compact, clickable
\`Source commit\` label at the bottom, pointing to
\`https://github.com/ottojung/assemblyp1/commit/<SHA>\`.
The previously visible version and long commit block
is absent. The Documents CI workflow verifies the
compiled PDF annotation against the exact Git commit
used to build it through
\`scripts/verify_paper_source_link.py\`.
Neither the source SHA nor the release tag is
hard-coded into the title-page link.


## Primitive-P2 strand-collapsed molecule-class ambiguity (GitHub #422)

The paper-level Proposition
[rc-p2-ambiguity](../paper/sections/06-discussion.tex) proves that
for each read length L>=2 the two primitive, maximal-repeat-P2
circles A^L C T^(L-1) and A^L G T^(L-1) are not dihedrally
equivalent but have the same length-L reverse-complement-class
law. See [precise model and general proof](rc-p2-molecule-ambiguity.md)
and [exact small-size regression](../scripts/verify_rc_p2_ambiguity.py)
for L=2..12. This is **a mathematical proof, not a new Lean
theorem**. It does not assert correspondence with the historical
bidirected MB09 molecule likelihood; that source bridge is open.
