# White-paper verification index

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
| Chernoff refinement of the finite-family recovery bound (`Σ_D exp(-n C(p_S,p_D)) ≤ \|C_S\| exp(-n C_*)`, `C_* ≥ ln(1/ρ_*)`); `C_*` is the exact finite-family exact-ML error exponent; bound still loose at finite `n` (~3.7× exact at `n=16`) | [Section 3 proposition](../paper/sections/03-open-question.tex): **prop:chernoff-refinement**, **rem:chernoff-sharp** | **Paper-level, classical (EXTERNAL)**: Chernoff bound / Sanov, Cover & Thomas 2006, Tsybakov 2009; NOT kernel-checked. Kernel-checked constant remains the Hellinger `ρ_*` ([FiniteReadRecovery.lean](../AssemblyP1/FiniteReadRecovery.lean)). Note [chernoff-exponent-finite-recovery-265.md](chernoff-exponent-finite-recovery-265.md); exact check [verify_chernoff_finite_recovery_265.py](../scripts/verify_chernoff_finite_recovery_265.py) |
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
