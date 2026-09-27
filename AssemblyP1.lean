import AssemblyP1.BBTMaximalExtension
import AssemblyP1.P2RepeatResidual
import AssemblyP1.BBTUniqueEulerian
import AssemblyP1.BBTLadder
import AssemblyP1.InterleavingNeededCounterexample
import AssemblyP1.ScalarPrimitiveSpellings
import AssemblyP1.LyndonSchutzenberger
import AssemblyP1.AmpBmpPrimitivity
import AssemblyP1.WordPeriodicity
import AssemblyP1.Model
import AssemblyP1.OpenProblem
import AssemblyP1.SourceFaithfulIs
import AssemblyP1.ExactVariantECounterexample
import AssemblyP1.FixedLengthExactCounterexample
import AssemblyP1.FixedLengthBinomialCounterexample
import AssemblyP1.Section62BridgingCounterexample
import AssemblyP1.SameLengthSection62Counterexample
import AssemblyP1.Section62BidirectedFlow
import AssemblyP1.FiniteSamplingCounterexample
import AssemblyP1.PopulationReduction
import AssemblyP1.OrientedRigidity
import AssemblyP1.RepeatAdapter
import AssemblyP1.OrientedFinalRigidity
import AssemblyP1.BridgingBridge
import AssemblyP1.OrientedSameLengthML
import AssemblyP1.SameLengthExactMLCounterexample
import AssemblyP1.SameLength62Maximizer
import AssemblyP1.WraparoundTripleRepeat
import AssemblyP1.MLEscape
import AssemblyP1.PopulationUniqueness
import AssemblyP1.AAABConverse

/-!
## The exported #88 endpoints

The integration gate is this trio. Each states source-faithful `I_s` **at the
exact realized start set** `realizedStarts ρ` of the realization itself, plus
genuine strict-oriented literal §6.2 truth and candidate certificates, and
concludes that the truth is an exact finite maximum-likelihood sequence. None of
them carries a `¬ HasLongTripleRepeat` (`hno`), spectral-escape or culprit
premise, and none of them takes an auxiliary start set `R`:

* `AssemblyP1.SameLength62Maximizer.informationFeasible_62_maximizer` — the
  exact same-length Medvedev–Brudno ML inequality, candidate certificate given;
* `AssemblyP1.OrientedSameLengthML.informationFeasible_exactLik_maximizer` — the
  same inequality over `IsSameLengthSpelledCandidate`, i.e. for **every** actual
  same-length spelled candidate `D`;
* `AssemblyP1.MLEscape.informationFeasible_62_spelledML` — the same packaged as
  the §6.2 maximizer predicate `Is62SpelledMLMax`, membership included.

The arbitrary-`R` surfaces are named `*_of_superset_starts` and are **strictly
weaker** (`R` may carry bridging starts that were never sampled); the
`*_of_exact_R` / `*_of_exact_subset` surfaces are faithful, with `R` pinned to
`realizedStarts ρ` by `hanti`. See `docs/bridging-lift-audit.md` §5 and §6.
-/

/-! ## Axiom audit for the #88 deliverable (issue #88) -/

#print axioms AssemblyP1.SameLengthExactMLCounterexample.same_length_exact_ML_refutation_62
#print axioms AssemblyP1.SameLengthExactMLCounterexample.competitor_spelledFeasible62
#print axioms AssemblyP1.SameLengthExactMLCounterexample.section62_maxLikelihood_refuted
#print axioms AssemblyP1.SameLengthExactMLCounterexample.truth_information_feasible
#print axioms AssemblyP1.SameLengthExactMLCounterexample.truth_no_long_triple_repeat
#print axioms AssemblyP1.BridgingBridge.bridgingLength
#print axioms AssemblyP1.BridgingBridge.informationFeasible_tripleRepeat_ge_G_sub_L
#print axioms AssemblyP1.BridgingBridge.informationFeasible_no_long_triple_repeat
#print axioms AssemblyP1.SourceFaithfulIs.bridgesCopy_length
#print axioms AssemblyP1.SourceFaithfulIs.bridgesCopy_lifted_iff
#print axioms AssemblyP1.OrientedSameLengthML.informationFeasible_exactLik_maximizer
#print axioms AssemblyP1.OrientedSameLengthML.covering_constant_reads_is_constant
#print axioms AssemblyP1.OrientedSameLengthML.truth_is_spelled_candidate_of_realization
#print axioms AssemblyP1.SameLength62Maximizer.informationFeasible_62_maximizer
#print axioms AssemblyP1.SameLength62Maximizer.genuine62_is_spelled_candidate
#print axioms AssemblyP1.SameLength62Maximizer.genuine62_support_eq
#print axioms AssemblyP1.SameLength62Maximizer.genuine62_molecule_eq
#print axioms AssemblyP1.SameLength62Maximizer.visited_of_positive_throughput
#print axioms AssemblyP1.SameLength62Maximizer.oriented_support_eq_of_genuine62
#print axioms AssemblyP1.WraparoundTripleRepeat.informationFeasible_excludes_this_instance
#print axioms AssemblyP1.WraparoundTripleRepeat.aaaab_not_information_feasible
#print axioms AssemblyP1.WraparoundTripleRepeat.aaaab_has_long_triple_repeat

/-! ## Axiom audit for the §6.2 maximum-likelihood result of #88
(`AssemblyP1.MLEscape`).

`informationFeasible_62_spelledML` is the exported #88 endpoint: full
**source-faithful** `I_s` at the **exact realized start set**
`realizedStarts ρ` of the realization itself, plus the §6.2 truth certificate,
and **no** long-triple-repeat, escape or culprit premise of any kind. Its
conclusion is `Is62SpelledMLMax`: the truth is an exact finite maximum-likelihood
sequence over the literal same-length §6.2 class, *with* the membership clause.

The two `*_of_superset_starts` names below are the deliberately **weaker**
one-sided surfaces (`R` may carry unsampled bridging starts); they are listed so
that the audit is explicit about them, and they are not the endpoint. The
`*_of_exact_subset` / `*_of_exact_R` names are the faithful statements through a
start set pinned down to `realizedStarts ρ`. -/

#print axioms AssemblyP1.MLEscape.Is62SpelledMLMax
#print axioms AssemblyP1.MLEscape.informationFeasible_62_spelledML
#print axioms AssemblyP1.MLEscape.informationFeasible_62_spelledML_of_exact_subset
#print axioms AssemblyP1.MLEscape.informationFeasible_62_spelledML_of_no_long_triple
#print axioms AssemblyP1.MLEscape.informationFeasible_62_spelledML_of_subset_starts
#print axioms AssemblyP1.MLEscape.HasMidRangeTripleRepeat.longTriple
#print axioms AssemblyP1.MLEscape.informationFeasible_no_midRangeTriple
#print axioms AssemblyP1.MLEscape.longTripleFree_no_midRangeTriple
#print axioms AssemblyP1.MLEscape.exactLik_le_of_spec_le
#print axioms AssemblyP1.MLEscape.observed_spectral_excess_of_ml_failure
#print axioms AssemblyP1.MLEscape.candidate_is_massG_positive_circulation
#print axioms AssemblyP1.MLEscape.eq_specCount_of_massG_le
#print axioms AssemblyP1.MLEscape.ml_failure_gives_spectral_escape
#print axioms AssemblyP1.MLEscape.isMaximalTriple_of_mod
#print axioms AssemblyP1.MLEscape.spectralEscape_contradiction
#print axioms AssemblyP1.MLEscape.spectralEscape_gives_longTriple
#print axioms AssemblyP1.MLEscape.informationFeasible_no_escape
#print axioms AssemblyP1.MLEscape.mem_realizedStarts
#print axioms AssemblyP1.MLEscape.informationFeasible_of_exact_subset
#print axioms AssemblyP1.MLEscape.culprit_instance_checked
#print axioms AssemblyP1.MLEscape.cand0_is_escape
#print axioms AssemblyP1.MLEscape.truth0_has_midrange_triple

/-! ## Axiom audit for the exact-realized-start-set target theorem

These are the same statements with the hypothesis `I_s` at `realizedStarts ρ`
stated at the level of the objective rather than through the §6.2 certificate
layer, plus the two weaker one-sided surfaces and the two pinning conversions.

The target-shape theorem the integration gate is about is
`AssemblyP1.SameLength62Maximizer.informationFeasible_62_maximizer`: full
source-faithful `I_s` at the actual realized start set, a genuine strict-oriented
literal §6.2 truth certificate, and a genuine one for the candidate, conclude the
exact finite same-length ML inequality, with no `hno` / escape / culprit premise
and no auxiliary start set. -/

#print axioms AssemblyP1.SameLength62Maximizer.informationFeasible_62_maximizer
#print axioms AssemblyP1.SameLength62Maximizer.informationFeasible_62_maximizer_of_exact_R
#print axioms AssemblyP1.SameLength62Maximizer.informationFeasible_62_maximizer_of_superset_starts
#print axioms AssemblyP1.OrientedSameLengthML.informationFeasible_exactLik_maximizer
#print axioms AssemblyP1.OrientedSameLengthML.informationFeasible_exactLik_maximizer_of_exact_R
#print axioms AssemblyP1.OrientedSameLengthML.informationFeasible_exactLik_maximizer_of_superset_starts
#print axioms AssemblyP1.OrientedSameLengthML.informationFeasible_of_exact_subset
#print axioms AssemblyP1.OrientedSameLengthML.realizedStarts
#print axioms AssemblyP1.OrientedSameLengthML.mem_realizedStarts
#print axioms AssemblyP1.OrientedSameLengthML.mem_realizedStarts_self

/-! ## Axiom audit for the seven `I_s` witnesses re-run under the canonical
bridging predicate

Each of these is a single `decide` on the *whole* `InformationFeasible`
predicate -- coverage, every triple repeat all-bridged, every interleaved pair of
repeats bridged, quantified over every admissible repeat length and every
selection of starts -- for a concrete circular genome and realized start set.
They were all re-run after `SourceFaithfulIs.BridgesCopy` was migrated to the
source's single-lift span semantics; the migration makes `I_s` a *smaller* set,
so a witness that is `I_s`-feasible under the weaker endpoint-only reading is
still feasible under the canonical one, and each of these is re-checked rather
than assumed. -/

#print axioms AssemblyP1.ExactVariantECounterexample.truth_information_feasible
#print axioms AssemblyP1.FiniteSamplingCounterexample.truth_information_feasible
#print axioms AssemblyP1.FixedLengthBinomialCounterexample.truth_information_feasible
#print axioms AssemblyP1.FixedLengthExactCounterexample.truth_information_feasible
#print axioms AssemblyP1.SameLengthExactMLCounterexample.truth_information_feasible
#print axioms AssemblyP1.SameLengthSection62Counterexample.truth_information_feasible
#print axioms AssemblyP1.Section62BridgingCounterexample.truth_information_feasible
