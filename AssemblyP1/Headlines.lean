import AssemblyP1.FixedLengthExactCounterexample
import AssemblyP1.FixedLengthBinomialCounterexample
import AssemblyP1.Issue94Complete
import AssemblyP1.SameLength62Uniqueness
import AssemblyP1.PrimitiveP2FiniteClass
import AssemblyP1.PrimitiveP2UniformSeparation
import AssemblyP1.FiniteBayesDecision
import AssemblyP1.ExactReadLikelihoodAdapters

/-!
# Paper headline theorem contracts

The following named wrappers refer *only* to fully kernel-checked existing
Lean theorem endpoints, without altering their hypotheses or conclusions.
Source-faithful modeling assumptions are part of the statements. Paper-only
historical equivalences, conditional source facts, and numerical experiments
are NOT silently promoted to Lean theorems here.

All exact and binomial witness objectives are now bridged to the
shared uniform-start circular-read interface in
ExactReadLikelihoodAdapters.lean. The two objectives remain distinct.
-/

namespace AssemblyP1.Headlines

/-- The realized read placements obey the full source-faithful information
predicate, yet the true fixed-length genome is not an exact-ML maximizer. -/
theorem exact_finite_sample_counterexample :
    SourceFaithfulIs.InformationFeasible
      FixedLengthExactCounterexample.truthGenome 3
      FixedLengthExactCounterexample.readStarts ∧
      ¬ FixedLengthExactCounterexample.IsMaximumLikelihoodFixedLength
        FixedLengthExactCounterexample.truth :=
  FixedLengthExactCounterexample.fixed_length_exact_counterexample

/-- Same source-faithful information predicate, but the fixed-external-length
product-binomial surrogate rather than the exact multinomial likelihood. -/
theorem binomial_finite_sample_counterexample :
    SourceFaithfulIs.InformationFeasible
      FixedLengthBinomialCounterexample.truthGenome 3
      FixedLengthBinomialCounterexample.readStarts ∧
      ¬ FixedLengthBinomialCounterexample.IsMaximumLikelihoodFixedLength
        FixedLengthBinomialCounterexample.truth :=
  FixedLengthBinomialCounterexample.fixed_length_binomial_counterexample

/-- The oriented primitive-P2 population uniqueness theorem, with candidate
admissibility included in the actual quantified endpoint statement. -/
abbrev population_unique_among_P2 := @Issue94Complete.population_unique_ML

/-- The proved same-length oriented support+bridging uniqueness endpoint;
the extra truth-candidacy hypothesis remains visible in its full type. -/
abbrev restricted_same_length_uniqueness :=
  @SameLength62Uniqueness.unique_62_maximizer_up_to_rotation

/-- A finite MAP decision is optimal under the stated joint scoring law. -/
abbrev finite_MAP_optimal :=
  @FiniteBayesDecision.pointwise_MAP_optimal

/-- A pointwise MAP rule also dominates all normalized randomized rules. -/
abbrev randomized_MAP_optimal :=
  @FiniteBayesDecision.pointwise_MAP_optimal_randomized

/-- Uniform primitive-P2 exact-ML error upper bound, including its
explicit dependence on the read count and finite candidate universe. -/
abbrev primitiveP2_exponential_error_bound :=
  @PrimitiveP2UniformSeparation.primitiveP2_exponential_error_bound

/-- The eventual finite-read primitive-P2 confidence theorem. -/
abbrev primitiveP2_ML_confidence :=
  @PrimitiveP2FiniteClass.all_primitiveP2_ML_confidence

/-- The exact witness is wrong-scoring under the common exact model. -/
abbrev canonical_exact_counterexample :=
  @ExactReadLikelihoodAdapters.Exact.shared_counterexample

/-- The product-binomial witness is wrong-scoring under the common surrogate. -/
abbrev canonical_binomial_counterexample :=
  @ExactReadLikelihoodAdapters.Binomial.shared_counterexample

end AssemblyP1.Headlines
