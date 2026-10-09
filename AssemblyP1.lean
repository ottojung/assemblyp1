import AssemblyP1.BBTLadder
import AssemblyP1.BBTCrossingCoalesce
import AssemblyP1.Issue89GapMap
import AssemblyP1.Issue94IterSlide
import AssemblyP1.Issue94OrbitSearch
import AssemblyP1.Issue94OrbitChecks
import AssemblyP1.Issue94OrbitGeneral
import AssemblyP1.Issue94Step4Prop
import AssemblyP1.Issue94Step5Heads
import AssemblyP1.Issue94HeadCollision
import AssemblyP1.Issue94Step5NoChord
import AssemblyP1.Issue94NoCollision
import AssemblyP1.Issue94CaseSplit
import AssemblyP1.P2Multiplicity
import AssemblyP1.P2RepeatAdapter
import AssemblyP1.BBTMaximalExtension
import AssemblyP1.BBTFibrePeriod
import AssemblyP1.P2RepeatResidual
import AssemblyP1.BBTUniqueEulerian
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
import AssemblyP1.PerOccurrenceSameLengthCounterexample
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
import AssemblyP1.Issue94GcdOneP2
import AssemblyP1.P2GcdOne
import AssemblyP1.Issue94R1LongWindow
import AssemblyP1.BBTVertexCycleReduction
-- REPAIRED (board 94, front 94th): Issue94EulerianTheta now elaborates.  The
-- quarantined draft proved a false intermediate (`hwin : window E i = window S i`,
-- kernel-refuted in scratch94/Probe3.lean, namespace `Probe94c`: `RotEquiv hG4 E4 S4`
-- with k = 1 but `window E4 0 != window S4 0`), and its §2 shift-invariance lemmas
-- were false as well (`window_rotAdd_refuted`, `vtx_rotAdd_refuted`, both `decide`).
-- The relation a rotation actually carries is the shifted one, `window E s =
-- window S (rotAdd hG (G - k) s)` (`window_rotEquiv`), which is what
-- `vertexCycleEq_of_RotEquiv_pullback` now uses.  §4's `BadThetaObstruction` is now
-- well typed (`σ : Fin K ≃ Fin K`).  See /workspace/BOARD94-THETA-1420Z.md.
import AssemblyP1.Issue94EulerianTheta
-- REFUTED (board 94, front 94wit): the extraction theorem
-- `Issue94WitnessPair.InterlacedBranchPair` --- "an alternative Eulerian cycle
-- with a foreign vertex cycle forces two interlacing chords of the pairing
-- `AltF σ`" --- is FALSE.  Smallest counterexample: K = 5, L = 2, S = 00102
-- over Fin 3, listing σ = (1 3)(2 4): an Eulerian cycle
-- (`cex_EulerianCycle`), a foreign vertex cycle (`cex_not_vertexCycleEq`), and
-- NO chord at all in `AltF σ` (`cex_no_chord`), so no interlaced pair
-- (`cex_no_interlaced_pair`).  The word IS primitive (`cex_is_primitive`); it
-- fails `P2` because of the maximal triple repeat at length L-1 = 1
-- (`cex_triple_repeat`).  The missing hypothesis is `Interleaved` on two
-- distinct chords, i.e. exactly what `BBTLadder.LadderVertexCycle` assumes and
-- `BBTLadder.CrossingChordsCoalesce` is about.  Minimality is decide-closed
-- (`no_foreign_eulerianCycle_Fin{a}_K{k}`).  See
-- /workspace/BOARD94-WITNESS-2010Z.md.
import AssemblyP1.Issue94WitnessPair
import AssemblyP1.Issue94TW1
import AssemblyP1.Issue94TW1EdgeType
import AssemblyP1.Issue94TW4Coalesce
-- BOARD 94, front 94cross: `BBTLadder.CrossingChordsCoalesce` as written ---
-- which carries neither `2 <= L` nor `L <= K` --- is REFUTED, and it is
-- refuted already over the SMALLEST possible alphabet, `Fin 2`, at the
-- smallest possible circle size `K = 4`: `S = 0011`, `L = 1`,
-- `sigma = (1 3)`, quadruple `0 2 1 3`.  The word satisfies `P2`
-- (`cex_P2`), primitivity (`cex_is_primitive`) and `Ukkonen` (`cex_Ukkonen`),
-- `sigma` is a genuine alternative Eulerian cycle (`cex_EulerianCycle`) whose
-- `AltF` is the double transposition `(0 2)(1 3)` (`cex_AltF0`..`cex_AltF3`),
-- the two chords cross (`cex_interleaved`), and the conclusion fails
-- (`cex_not_SameExtension`).  `crossingChordsCoalesce_refuted` is the
-- refutation `~(forall L, CrossingChordsCoalesce (Fin 2) L)`.  It STRENGTHENS
-- `Issue94TW4Coalesce.not_crossingChordsCoalesce_one`, which refutes the same
-- statement over `Fin 4` with `S = (0,1,2,3)`: the binary instance cannot use
-- the "all symbols distinct" device, so the refuted regime does not depend on a
-- large alphabet.  This also makes the "Not established" note further down
-- (`CrossingChordsCoalesce` "neither proved nor refuted") stale --- it is
-- settled in both directions by `Issue94TW4Coalesce` and sharpened here.  The
-- missing hypothesis is named: `2 <= L`, i.e. `L - 1 >= 1`, so that the
-- `(L-1)`-mer is a non-degenerate window; `L <= K` is NOT independently
-- necessary (at `L > K` the `def` is vacuous).  The repair is proved at
-- arbitrary `[DecidableEq alpha]` as `CrossingChordsCoalesce_ge2`, and over
-- `Fin 2` the `def` is exactly characterised by
-- `crossingChordsCoalesce_sharp_bin` (true for every `L >= 2`, false at
-- `L = 1`).  Minimality: `no_interleaved_on_K3` (four pairwise distinct starts
-- are impossible on `Fin 3`) and `no_primitive_on_Fin1` (a one-letter circle is
-- never primitive).  `BBTLadder.LadderVertexCycle` still has NO inhabitant.
-- See /workspace/BOARD94-CROSSCHORDS-*.md.
import AssemblyP1.Issue94CrossingChords


-- Board 94, front `94comp` (the interlace graph on chords, in the
-- Arratia--Bollobas--Coppersmith--Sorkin style): `SameExtension` is packaged as
-- an equivalence (`SameExtension_iff_pairEq`, `SE_refl`/`SE_symm`/`SE_trans`,
-- `BlockClass`), and coalescing along an interlace edge plus that transitivity
-- forces every connected component of the interlace graph into ONE
-- maximal-extension ladder (`connected_block`, `InterlaceComponent_block`,
-- `InterlaceComponents_ladder` --- all inhabitants).  The reverse direction
-- (block => connected) is isolated as `ShiftPairInterlace` and NOT proved; the
-- component-independence / component-repair route is REFUTED at `G = 5` by
-- `scripts/verify_interlace_components_94.py` (predicates T6 and T7).
-- `BBTLadder.LadderVertexCycle` still has NO inhabitant.
import AssemblyP1.Issue94InterlaceComponents
-- BOARD 94, front 94transpose: the ONE-STEP transposition lemma for
-- `VertexCycleEq`.  `BBTTranspose.vertexCycleEq_transposition`: a transposition
-- of two starts spelling the same `(L-1)`-mer (i.e. of the two listing
-- positions of the two occurrences of one branch object) is vertex-INVISIBLE,
-- so it preserves `VertexCycleEq` with the SAME rotation witness.  This is why
-- no transport of the four chord occurrences through the rotation witness, and
-- no re-application of `CrossingPairsCoalesce_general` in truth coordinates, is
-- needed: `VertexCycleEq` at witness `k` is the pointwise statement
-- `vtx (σ i) = vtx (rotAdd k i)`.  Corollaries discharge the hypothesis from
-- `AltF_vtx'` (the two ends of any chord of `AltF`) and from `DoubledPair`.
-- NO hypothesis of interlacement, `SameExtension`, `EulerianCycle`, `P2`,
-- `Ukkonen`, primitivity or `AltF = id` is used.
--
-- The sharp boundary is also here: `BBTTranspose.interlaceAlone_insufficient`
-- REFUTES the formulation in which the two transposition points are only
-- required to be DISTINCT (which is all an interlacement-only / raw
-- final-support reading supplies, since on a circle of <= 3 positions every
-- pair of distinct points alternates): smallest instance `K = 3`, `L = 3`,
-- `S = 001`, `sigma = refl`, transposition `{0, 1}`.
-- `BBTLadder.LadderVertexCycle` still has NO inhabitant and its real
-- obstruction (that the traversal walks the laminar blocks in geometric
-- order) is untouched.  See /workspace/BOARD94-TRANSPOSE-*.md.
import AssemblyP1.Issue94TransposePreserve
import AssemblyP1.Issue94TW5Single
import AssemblyP1.Issue94TW6Lemma1
import AssemblyP1.Issue94TW7AltF
import AssemblyP1.Issue94TW8Contraction
import AssemblyP1.Issue94KShort
import AssemblyP1.Issue94P2Iff
import AssemblyP1.Issue94TruthTraversal
import AssemblyP1.AAABConverse
import AssemblyP1.Issue94Step2Path
import AssemblyP1.Issue94Transposition
import AssemblyP1.Issue94ObstructionEquiv
import AssemblyP1.Issue94EulerianRealize
import AssemblyP1.Issue94P2PrimInterface
import AssemblyP1.Issue94LadderAligned
import AssemblyP1.Issue94DeleteAdapter
import AssemblyP1.Issue94P2DoubledPair
import AssemblyP1.Issue94FibreCommute
import AssemblyP1.Issue94ComponentAlgebra
import AssemblyP1.Issue94AlignedPairs
import AssemblyP1.Issue94GF2Parity
import AssemblyP1.Issue94Parity
import AssemblyP1.Issue94InterlaceParity
import AssemblyP1.Issue94SameAltF
import AssemblyP1.Issue94Antiderivative
import AssemblyP1.Issue94IntervalCore
import AssemblyP1.Issue94Complete
-- #217 finite-front integrations: same-length §6.2 tie uniqueness (#211); the
-- general (non-spelled) §6.2 flow domain at o_min = 1 (#214) and the
-- full-overlap disconnected flow optimum at o_min = L-1 (#214); the two
-- disjoint-circles duplex model and the 2G-remap non-equivalence (#215); the
-- conclusion-schema implication lattice (#216); the oriented unrestricted-length
-- §6.2 classification (#210); the variable-length per-occurrence audit (#213);
-- the E/A audit (#209); the Bresler-remap compatibility (#215); and the
-- fibre-count arithmetic (#219, terminal B219 `81d29c6`).  Each is
-- self-contained; the imports carry their own modules.
import AssemblyP1.SameLength62TieUniqueness
import AssemblyP1.Section62NonSpelledFlow
import AssemblyP1.Section62FullOverlapDisconnected
import AssemblyP1.DoubleStrandBridgingTransfer
import AssemblyP1.TwoDisjointCirclesDuplex
import AssemblyP1.ImplicationLattice
import AssemblyP1.OrientedVariableLengthSe62
import AssemblyP1.Section62VarlenPerOccurrence
import AssemblyP1.BreslerRemapCompatibility
import AssemblyP1.Issue209EAudit
import AssemblyP1.FibreCountArithmetic

/-! ## `Issue94Transposition`: the Kotzig/Ukkonen/Pevzner descent, and an obstruction

The classical transposition step deletes one transposition factor of the
transition-difference set, lowering `|W|` by `2`.  Re-expressed in this
repository's `Succ` / `AltF` / `Support` language that step is impossible: the
reachable `AltF`s are even permutations, so `|W| = 2t` has `t` even and `|W|` is
always a multiple of four (`involution_support_mod_four_5/6`, `altF_even_5`);
hence the `|W| = 2` base case cannot occur
(`involution_support_two_impossible_5`) and no two reachable `AltF`s differ by a
single factor (`no_single_factor_step_5/6`).

This is a statement about the translation, not a refutation of the classical
theorem: `Support (AltF hG σ)` counts positions, so `t = |W| / 2` counts each
differing transition twice, and the reaching map lands in the even-sign half.  The
descent step compatible with this language deletes a *pair* of factors; it is
stated as the unproved `Prop` `Issue94Transposition.PairDeletionDescent`, and its
`t = 2` base case is the already-refuted `TwoTranspositionsBlock` shape, which is
not re-attacked.  See `docs/transposition-descent-94.md`. -/

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

/-! ## Axiom audit for the `#89` fibre/period lemma

`AssemblyP1.BBTFibrePeriod` proves the fibre/period bound of the `#89`
dichotomy: three occurrences of one `(L-1)`-mer of an `Ukkonen` word collapse
modulo the least period, and in the primitive stratum every fibre of the
vertex labelling has at most two starts.  `EulerianCycleGap` itself remains a
`Prop` with no inhabitant; the statements below are the whole of what the
module adds. -/

#print axioms AssemblyP1.BBTEulerian.three_occurrences_collapse_or_tripleRepeat
#print axioms AssemblyP1.BBTEulerian.three_occurrences_collapse_of_Ukkonen
#print axioms AssemblyP1.BBTEulerian.fibre_subset_two_classes
#print axioms AssemblyP1.BBTEulerian.fibre_card_le_two_of_primitive
#print axioms AssemblyP1.BBTEulerian.leastPeriod_eq_G_of_primitive
#print axioms AssemblyP1.BBTEulerian.backAgr3F_add
#print axioms AssemblyP1.BBTEulerian.agr3F_G_of_shifted

/-! ## Axiom audit for the word-level crossing/coalescence route of `#89`
(`AssemblyP1.BBTCrossingCoalesce`).

§1--§4 are proved and are audited below.  The §5 target and its two
ingredients were `def`s of type `Prop` with **no inhabitant** anywhere in the
library: `CrossingPairsCoalesce`, `SlidePreservesInterleaved`,
`ShiftLeftPersistence`.  Nothing *in this section* discharges them, and the two
ingredients still have no inhabitant; `CrossingPairsCoalesce` was discharged
afterwards, by `AssemblyP1.Issue94CaseSplit.crossingPairsCoalesce_general`
(`d0aa0aa`).  See the audit of that theorem in
`AssemblyP1/Issue94CaseSplit.lean`. -/

#print axioms AssemblyP1.BBTCrossingCoalesce.vtx_eq_iff
#print axioms AssemblyP1.BBTCrossingCoalesce.mem_nodeStartsOf_vtx
#print axioms AssemblyP1.BBTCrossingCoalesce.three_starts_ne
#print axioms AssemblyP1.BBTCrossingCoalesce.collision_forces_pair
#print axioms AssemblyP1.BBTCrossingCoalesce.vtx_maxPairStart
#print axioms AssemblyP1.BBTCrossingCoalesce.CrossingPairsCoalesce
#print axioms AssemblyP1.BBTCrossingCoalesce.ShiftLeftPersistence
#print axioms AssemblyP1.BBTCrossingCoalesce.SlidePreservesInterleaved

/-!
## Board 94: the `#89` gap map

`AssemblyP1.Issue89GapMap` states each step of the §5 five-step reduction as a
separate `Prop`, classifies it, and --- the load-bearing part --- **refutes
`ShiftLeftPersistence` and `SlidePreservesInterleaved` as they are stated**.
Both of those are `def`s with no inhabitant, so this changes nothing about the
two central `Prop`s; it records exactly what stands between §5 and
`CrossingPairsCoalesce`. -/

#print axioms AssemblyP1.Issue89GapMap.SlidePreservesInterleaved_refuted
#print axioms AssemblyP1.Issue89GapMap.ShiftLeftPersistence_refuted
#print axioms AssemblyP1.Issue89GapMap.shift_left_persistence_corrected
#print axioms AssemblyP1.Issue89GapMap.step1_proved
#print axioms AssemblyP1.Issue89GapMap.step3_shared_endpoint_forces_pair
#print axioms AssemblyP1.Issue89GapMap.step5_contradiction

/-!
## Board 94, second pass: the corrected **iterated** slide statement

`AssemblyP1.Issue94IterSlide` states §5 step 4 in its corrected form --- the
pair `c, d` slides, not `a, b` --- on the decidable `InterK` layer, with no
word and no `vtx`, and **proves** it by induction on the number of steps, for
every `K` and every slide count `n ≤ K`.  The intermediate guards are
necessary: with the guards only at the endpoint the statement is false at
`K = 6, 8, 10`. -/

#print axioms AssemblyP1.Issue94IterSlide.inArc_prev_iff
#print axioms AssemblyP1.Issue94IterSlide.slide_one
#print axioms AssemblyP1.Issue94IterSlide.slide_iter
#print axioms AssemblyP1.Issue94IterSlide.IterSlide_of_InterK
#print axioms AssemblyP1.Issue94IterSlide.step4_slide_iterates_cyclic
#print axioms AssemblyP1.Issue94IterSlide.step4_slide_iterates_word
#print axioms AssemblyP1.Issue94IterSlide.not_EndpointIter_6
#print axioms AssemblyP1.Issue94IterSlide.not_EndpointIter_8_10
#print axioms AssemblyP1.Issue94IterSlide.FullIter_6_8
#print axioms AssemblyP1.Issue94IterSlide.NonVacuous_6_10

/-!
## Board 94, front 94a4: the §5 step-4 obligation, proved in general

`AssemblyP1.Issue94OrbitGeneral` proves `Issue94OrbitSearch.IterStep4` for
**every** circle size, with no finite search and no `decide`.  The
observation is that `IterStep4` carries no primitivity hypothesis and that
`pairBackC hK S a b ≤ K` holds unconditionally, because `pairBackC`
maximises over a `filter` of `Finset.range (K + 1)`.  So its shift bound
`ti.val ≤ pairBackC` supplies the `t ≤ K` that the already-proved
`step4_slide_iterates_word` needs, and step 4's cyclic content is done.

This replaces the `by decide` checks of `IterStep4 5 .. 8`, which reached
`K = 4` and then exhausted a 30.0 GiB cgroup at `K = 5`.  The §5 step-2
obligation `Step2_components_are_paths` is **not** settled by this and
remains a `Prop` with no inhabitant. -/

#print axioms AssemblyP1.Issue94OrbitGeneral.pairBackC_le_K
#print axioms AssemblyP1.Issue94OrbitGeneral.slideGuards_of_fin
#print axioms AssemblyP1.Issue94OrbitGeneral.IterStep4_all
#print axioms AssemblyP1.Issue94OrbitChecks.iterStep4_5_8

/-! `AssemblyP1.Issue94Step4Prop` discharges
the *guarded* form of §5 step 4, for every `L` and every `K`, with no
primitivity hypothesis, and REFUTES `Step4_slide_iterates` as literally
written, whose guard clause is implication-shaped rather than a conjunction. -/
#print axioms AssemblyP1.Issue94Step4Prop.pairBack_le_K
#print axioms AssemblyP1.Issue94Step4Prop.slideGuards_iff
#print axioms AssemblyP1.Issue94Step4Prop.pairBackC_eq'
#print axioms AssemblyP1.Issue94Step4Prop.step4_guarded
#print axioms AssemblyP1.Issue94Step4Prop.step4_guarded_rotAdd
#print axioms AssemblyP1.Issue94Step4Prop.step4_guarded_pairBackC
#print axioms AssemblyP1.Issue94Step4Prop.step4LitK_of_step4
#print axioms AssemblyP1.Issue94Step4Prop.not_Step4LitK_4
#print axioms AssemblyP1.Issue94Step4Prop.not_Step4_slide_iterates_1

#print axioms AssemblyP1.Issue94Step2Path.step2_components_are_paths_proved

/-! `AssemblyP1.Issue94Step5Heads` REFUTES
`Issue89GapMap.Step5_heads_interleave` as written, with a kernel-checked
witness: on the `P2` primitive word `S = AABAB` at `L = 3`, the chords
`{1, 3}` and `{2, 4}` interleave, while their head-pairs *coincide* at
`{1, 3}`, so the four heads `1, 3, 1, 3` do not interleave.  The corrected
step 5 is the dichotomy `head_dichotomy` (`SameExtension ∨ heads interleave`),
whose second disjunct is already `False`. -/
#print axioms AssemblyP1.Issue94Step5Heads.maxPairStart_of_pairBackC
#print axioms AssemblyP1.Issue94Step5Heads.headWord_primitive
#print axioms AssemblyP1.Issue94Step5Heads.headWord_is_p2
#print axioms AssemblyP1.Issue94Step5Heads.head_cex_interleaved
#print axioms AssemblyP1.Issue94Step5Heads.head_cex_not_interleaved
#print axioms AssemblyP1.Issue94Step5Heads.Step5_heads_interleave_cex
#print axioms AssemblyP1.Issue94Step5Heads.not_Step5_heads_interleave_3
#print axioms AssemblyP1.Issue94Step5Heads.head_cex_SameExtension
#print axioms AssemblyP1.Issue94Step5Heads.heads_of_one_chord_ne
#print axioms AssemblyP1.Issue94Step5Heads.head_dichotomy_second_is_false

/-! `AssemblyP1.Issue94HeadCollision` proves the **positive** reading of the
step-5 failure: a cross-chord **head collision** is not to be excluded, it
immediately forces the target conclusion.  If the head-pairs of two chords
share a point, `collision_forces_pair` forces the two unordered extension
pairs to coincide, giving `SameExtension`.  So the collision case of
`head_dichotomy` is free.  `heads_ne_of_chord` is the general-`α` form of
`Issue94Step5Heads.heads_of_one_chord_ne`, re-derived here so that the helper
does not depend on the `Bin` specialisation. -/
#print axioms AssemblyP1.Issue94HeadCollision.heads_ne_of_chord
#print axioms AssemblyP1.Issue94HeadCollision.head_collision_implies_sameExtension

/-! `AssemblyP1.Issue94Step5NoChord` shows that at read length `L = K` a
primitive circular word has **no chord at all**: two distinct starts agreeing
on their `(K-1)`-mers would make the word invariant under the nonzero shift
`(b - a) mod K`, which `IsPrimitive` forbids.  No `P2` hypothesis is used.
This makes the `L = K` specialisation of the §5 reduction degenerate (it has
no instance at genome size `= L`); it is *not* progress on `head_dichotomy` at
`2 ≤ L < K`, which remains open. -/
#print axioms AssemblyP1.Issue94Step5NoChord.fibre_card
#print axioms AssemblyP1.Issue94Step5NoChord.one_exception_impossible
#print axioms AssemblyP1.Issue94Step5NoChord.shift_bijective
#print axioms AssemblyP1.Issue94Step5NoChord.chord_agreement_off_one
#print axioms AssemblyP1.Issue94Step5NoChord.chord_at_L_eq_K_shiftInvariant
#print axioms AssemblyP1.Issue94Step5NoChord.no_chord_at_L_eq_K
#print axioms AssemblyP1.Issue94Step5NoChord.head_dichotomy_at_genome_eq_read

/-! ## `Issue94NoCollision`: the no-collision half of the `CrossingPairsCoalesce`
case split

The human pointer of 2026-09-28 21:33:33Z / 21:34:57Z on board issue 94 splits
`BBTCrossingCoalesce.CrossingPairsCoalesce` on whether a **cross-head equality**
holds.  `AssemblyP1/Issue94NoCollision.lean` is the other half: assuming all four
cross-head **inequalities**, it proves the heads interleave (composing
`Issue94Step4Prop.step4_guarded` with `P2RepeatResidual.chord_shift_left`,
`P2RepeatResidual.pairBack_shift` and
`BBTCrossingCoalesce.vtx_maxPairStart`) and closes by `P2.imp_ExtCrossing`.
Distinctness of the slid pair comes from `Issue94NoCollision.slide_pair_ne`
(via `rotAdd_inj_any`), **not** from
`Issue94Step2Path.step2_components_are_paths_proved`, which this file does not
invoke.  It is proved **independently** of the cross-head-equality helper, which
it neither imports nor assumes.  Note also that its hypothesis set is empty on
every regime an exhaustive binary sweep reaches (`K ≤ 9`): all 7704 admissible
interleaving chord quadruples have a cross-head collision and 0 satisfy all four
inequalities.  It is therefore the **refuted case** of the split, and the
composite rests on the collision half alone.  The `Bin` restriction on `S` is
inherited from `step4_guarded` and was removed at arbitrary `[DecidableEq α]` in
`AssemblyP1/Issue94NoCollisionAlpha.lean`. -/
#print axioms AssemblyP1.Issue94NoCollision.pairBack_mod
#print axioms AssemblyP1.Issue94NoCollision.head_of_slide
#print axioms AssemblyP1.Issue94NoCollision.head_of_head
#print axioms AssemblyP1.Issue94NoCollision.chord_of_slide
#print axioms AssemblyP1.Issue94NoCollision.slide_meets_head
#print axioms AssemblyP1.Issue94NoCollision.interleavedStarts_pair_swap
#print axioms AssemblyP1.Issue94NoCollision.slide_guards_down
#print axioms AssemblyP1.Issue94NoCollision.slide_guards_down_heads
#print axioms AssemblyP1.Issue94NoCollision.no_collision_heads_interleave
#print axioms AssemblyP1.Issue94NoCollision.no_collision_contradiction

/-! ## `Issue94CaseSplit`: `CrossingPairsCoalesce` by the case split on a cross-head equality

This is the **direct assembly** the external orchestration pointer of
2026-09-28 21:34:57Z asked for (item 3): "attempt `CrossingPairsCoalesce`
directly as a case split between (1) and (2) ... The target is the exact
existing `CrossingPairsCoalesce` Prop inhabitant."  No `head_dichotomy` is
introduced, as the pointer required.

The split is on whether a **cross-head EQUALITY** holds.  If one does, front
`2463a1f`'s `head_collision_implies_sameExtension` closes the goal.  If none
does, all four cross-head inequalities are available and front `a23872a`'s
`no_collision_contradiction` refutes the configuration outright.

`crossingPairsCoalesce` below is an inhabitant of the existing
`BBTCrossingCoalesce.CrossingPairsCoalesce (α := Bin)`, with that `def`'s
hypotheses verbatim.

`Issue94NoCollisionAlpha` removes the `Bin` restriction, and
`crossingPairsCoalesce_general` below is the **α-general** inhabitant of that
same existing `Prop`, for every `[DecidableEq α]`, with its hypotheses verbatim
and no residual assumption on the alphabet.  The `Bin` restriction turned out to
be inherited plumbing over an α-general core, not a property of the argument.
`crossingPairsCoalesce_of_noCollision` remains as the conditional form.  See
`/workspace/BOARD94-ALPHAGEN.md`. -/
#print axioms AssemblyP1.Issue94NoCollisionAlpha.pairBack_mod_alpha
#print axioms AssemblyP1.Issue94NoCollisionAlpha.pairBack_slide_alpha
#print axioms AssemblyP1.Issue94NoCollisionAlpha.head_of_slide_alpha
#print axioms AssemblyP1.Issue94NoCollisionAlpha.pairBack_of_head_alpha
#print axioms AssemblyP1.Issue94NoCollisionAlpha.head_of_head_alpha
#print axioms AssemblyP1.Issue94NoCollisionAlpha.chord_of_slide_alpha
#print axioms AssemblyP1.Issue94NoCollisionAlpha.slide_pair_ne_alpha
#print axioms AssemblyP1.Issue94NoCollisionAlpha.step3_shared_endpoint_alpha
#print axioms AssemblyP1.Issue94NoCollisionAlpha.step4_guarded_alpha
#print axioms AssemblyP1.Issue94NoCollisionAlpha.slide_meets_head_alpha
#print axioms AssemblyP1.Issue94NoCollisionAlpha.slide_guards_down_alpha
#print axioms AssemblyP1.Issue94NoCollisionAlpha.slide_guards_down_heads_alpha
#print axioms AssemblyP1.Issue94NoCollisionAlpha.no_collision_heads_interleave_alpha
#print axioms AssemblyP1.Issue94NoCollisionAlpha.no_collision_contradiction_alpha
#print axioms AssemblyP1.Issue94CaseSplit.crossingPairsCoalesce_of_noCollision
#print axioms AssemblyP1.Issue94CaseSplit.crossingPairsCoalesce_bin
#print axioms AssemblyP1.Issue94CaseSplit.crossingPairsCoalesce
#print axioms AssemblyP1.Issue94CaseSplit.crossingPairsCoalesce_alpha
#print axioms AssemblyP1.Issue94CaseSplit.crossingPairsCoalesce_general

/-! ## Board 94, front 94a10: the edge-type obligation

`AssemblyP1.Issue94TW1` (front 94e7) **refutes** the board's `t_w = 1` step
at `not_UniqueInArb_3`.  `AssemblyP1.Issue94TW1EdgeType` (this front) carries
out the three steps the board directed on top of it:

* the "208 instances with a simple `D`" claim is an **evaluator bug** in
  `scripts/verify_tw1_94.js` (`hasParallelEdges` is identically `false`); with
  a correct predicate there are **zero** simple-`D`, `t_w > 1` instances at
  `K ≤ 12`, so the parallel-edge division is the whole repair;
* the corrected edge-type obligation is **equivalent to
  `BBTEulerian.UniqueEulerianCycle`**, i.e. it is the endpoint the tree already
  has rather than a new `Prop` (`edgeTypeUnique_iff_uniqueEulerianCycle`);
* the interface audit of §3 was resolved by option **(b)**: the exact bounded
  bridge `crossingChordsCoalesce_bounded`, and `support_blocks_coalesce` in
  the shape `LadderVertexCycle` consumes.

**Not established:** `BBTLadder.LadderVertexCycle` still has no inhabitant, the
unbounded `CrossingChordsCoalesce` is neither proved nor refuted, and
`PopulationUniqueness.population_unique_ML_up_to_rotation` still **retains**
its `hPevzner : EulerianCycleObstruction` premise.  The public endpoint is not
discharged.

**Board 94, fronts tw5-tw7 — status of `thm:BBT` on this object.**  The
`single` clause of `EulerianCycle` is a tautology (`Issue94TW5Single`), the
innermost-chord obstruction is free and unconditional
(`Issue94TW5Single.altF_no_innermost_chord`), the degree fact of Lemma 1 is
proved in `Finset`-maximum form with its exact condition
(`Issue94TW6Lemma1`), and the statement the board had been treating as the last
purely combinatorial step, "`Ukkonen` + label-preserving ⟹ `AltF = id`", is
**FALSE**: `Issue94TW7AltF.altF_eq_id_iff_rotation` proves it equivalent to
`σ` being a rotation of the circle, and `Issue94TW7AltF.not_ukk_then_not_altF`
refutes it at `S = 0101`, `G = 4`, `L = 3`.  The correct target is
`VertexCycleEq`, and `Issue94TW7AltF.node_prefix` gives the unconditional
combinatorial content of that route together with the exact point at which it
stops.  **`hPevzner` is still a hypothesis at `PopulationUniqueness.lean`
lines 178, 231, 261 and is not discharged by any of these fronts.** -/
#print axioms AssemblyP1.Issue94TW1.not_UniqueInArb_3
#print axioms AssemblyP1.Issue94TW1.S10100_two_arbs
#print axioms AssemblyP1.Issue94TW1EdgeType.sameType_equiv
#print axioms AssemblyP1.Issue94TW1EdgeType.vtx_eq_of_sameType
#print axioms AssemblyP1.Issue94TW1EdgeType.edgeTypeOf_eq_iff
#print axioms AssemblyP1.Issue94TW1EdgeType.EType_eq
#print axioms AssemblyP1.Issue94TW1EdgeType.VertexCycleEq_of_EType_cycle
#print axioms AssemblyP1.Issue94TW1EdgeType.EType_cycle_of_VertexCycleEq
#print axioms AssemblyP1.Issue94TW1EdgeType.VertexCycleEq_iff_EType_cycle
#print axioms AssemblyP1.Issue94TW1EdgeType.T1_T2_same_edgeTypes
#print axioms AssemblyP1.Issue94TW1EdgeType.edgeTypeUnique_iff_uniqueEulerianCycle
#print axioms AssemblyP1.Issue94TW1EdgeType.crossingChordsCoalesce_bounded
#print axioms AssemblyP1.Issue94TW1EdgeType.support_blocks_coalesce
#print axioms AssemblyP1.PopulationUniqueness.population_unique_ML_up_to_rotation
#print axioms AssemblyP1.PopulationUniqueness.population_unique_ML_up_to_rotation_same_length
#print axioms AssemblyP1.Issue94TW1EdgeType.ladderVertexCycle_of_blockless
#print axioms AssemblyP1.Issue94TW1EdgeType.ladderVertexCycle_iff_blockless
#print axioms AssemblyP1.Issue94TW1EdgeType.blockless_of_uniqueEulerianCycle
#print axioms AssemblyP1.Issue94TW1EdgeType.ladderVertexCycle_of_uniqueEulerianCycle
#print axioms AssemblyP1.Issue94TW4Coalesce.vtx_injective_of_prim
#print axioms AssemblyP1.Issue94TW4Coalesce.altF_eq_id_of_prim_window
#print axioms AssemblyP1.Issue94TW4Coalesce.crossingChordsCoalesce_above
#print axioms AssemblyP1.Issue94TW4Coalesce.agree_S4_ne
#print axioms AssemblyP1.Issue94TW4Coalesce.no_repeat_S4
#print axioms AssemblyP1.Issue94TW4Coalesce.no_triple_S4
#print axioms AssemblyP1.Issue94TW4Coalesce.p2_S4_L1
#print axioms AssemblyP1.Issue94TW4Coalesce.ukkonen_S4_L1
#print axioms AssemblyP1.Issue94TW4Coalesce.primitive_S4
#print axioms AssemblyP1.Issue94TW4Coalesce.vtx_trivial_L1
#print axioms AssemblyP1.Issue94TW4Coalesce.eulerianCycle_S4
#print axioms AssemblyP1.Issue94TW4Coalesce.maxPairStart_S4
#print axioms AssemblyP1.Issue94TW4Coalesce.not_sameExtension_S4
#print axioms AssemblyP1.Issue94TW4Coalesce.altF_chords_S4
#print axioms AssemblyP1.Issue94TW4Coalesce.not_crossingChordsCoalesce_one
#print axioms AssemblyP1.Issue94TW4Coalesce.crossingChordsCoalesce_iff_two_le
#print axioms AssemblyP1.Issue94TW4Coalesce.crossingChordsCoalesce_of_two_le
#print axioms AssemblyP1.P2RepeatResidual.pairBack_eq_zero_of_back_ne
#print axioms AssemblyP1.Issue94TW5Single.succ_visitsAll
#print axioms AssemblyP1.Issue94TW5Single.eulerianCycle_iff_traverses
#print axioms AssemblyP1.Issue94TW5Single.altF_no_innermost_chord
#print axioms AssemblyP1.Issue94TW5Single.altF_nextPos_visitsAll
#print axioms AssemblyP1.Issue94TW5Single.labelPreserving_iff_traverses
#print axioms AssemblyP1.Issue94TW5Single.uniqueEulerianCycle_iff_labelPreserving
#print axioms AssemblyP1.Issue94TW5Single.obstruction_iff_labelPreserving
#print axioms AssemblyP1.Issue94TW5Single.labelPreserving_implies_eulerianCycle
#print axioms AssemblyP1.Issue94TW5Single.not_labelPreserving_S3
#print axioms AssemblyP1.Issue94TW5Single.labelPreserving_S4
#print axioms AssemblyP1.Issue94TW5Single.single_clauses_S4
#print axioms AssemblyP1.Issue94TW5Single.altF_S4_ne
#print axioms AssemblyP1.Issue94TW6Lemma1.agr3_iff_agree3
#print axioms AssemblyP1.Issue94TW6Lemma1.mem_span
#print axioms AssemblyP1.Issue94TW6Lemma1.max_span_tripleRepeat
#print axioms AssemblyP1.Issue94TW6Lemma1.max_span_escape
#print axioms AssemblyP1.Issue94TW6Lemma1.max_span_escape_congruent
#print axioms AssemblyP1.Issue94TW6Lemma1.deg_fact
#print axioms AssemblyP1.Issue94TW6Lemma1.deg_fact_of_primitive
#print axioms AssemblyP1.Issue94TW6Lemma1.no_three_of_primitive
#print axioms AssemblyP1.Issue94TW6Lemma1.deg_fact_node
#print axioms AssemblyP1.Issue94TW6Lemma1.no_three_of_Ukkonen_K
#print axioms AssemblyP1.Issue94TW6Lemma1.no_three_of_Ukkonen_L
#print axioms AssemblyP1.Issue94TW6Lemma1.no_three_of_P2
#print axioms AssemblyP1.Issue94TW6Lemma1.prim_deg_le_two
#print axioms AssemblyP1.Issue94TW6Lemma1.escape_iff_leastPeriod
#print axioms AssemblyP1.Issue94TW6Lemma1.escape_iff_not_IsPrimitive
#print axioms AssemblyP1.Issue94TW6Lemma1.period_iff_shiftInvariant
#print axioms AssemblyP1.Issue94TW6Lemma1.deg_fact_escape_only
#print axioms AssemblyP1.Issue94TW6Lemma1.vtx9_three
#print axioms AssemblyP1.Issue94TW6Lemma1.deg9_012
#print axioms AssemblyP1.Issue94TW6Lemma1.no_tripleRepeat_012012012
#print axioms AssemblyP1.Issue94TW6Lemma1.no_tripleRepeat4_012012012
#print axioms AssemblyP1.Issue94TW6Lemma1.no_tripleRepeat8_012012012
#print axioms AssemblyP1.Issue94TW6Lemma1.leastPeriod9
#print axioms AssemblyP1.Issue94TW6Lemma1.period3_9
#print axioms AssemblyP1.Issue94TW6Lemma1.not_IsPrimitive9

/-! ## #94 front tw8: the contraction rule of `Defn. d:condensed` -/
#print axioms AssemblyP1.Issue94TW8Contraction.length_drop_le'
#print axioms AssemblyP1.Issue94TW8Contraction.Merge
#print axioms AssemblyP1.Issue94TW8Contraction.Contractible
#print axioms AssemblyP1.Issue94TW8Contraction.contractNodes
#print axioms AssemblyP1.Issue94TW8Contraction.contractEdges
#print axioms AssemblyP1.Issue94TW8Contraction.Contract
#print axioms AssemblyP1.Issue94TW8Contraction.mem_contractNodes_merge
#print axioms AssemblyP1.Issue94TW8Contraction.mem_contractNodes_of_mem
#print axioms AssemblyP1.Issue94TW8Contraction.merge_not_mem_erase
#print axioms AssemblyP1.Issue94TW8Contraction.edges_contract_subset
#print axioms AssemblyP1.Issue94TW8Contraction.mem_contractEdges_of_ne
#print axioms AssemblyP1.Issue94TW8Contraction.card_contractNodes_lt
#print axioms AssemblyP1.Issue94TW8Contraction.card_contractNodes_le
#print axioms AssemblyP1.Issue94TW8Contraction.nodeMult_ge_of_mem
#print axioms AssemblyP1.Issue94TW8Contraction.inMult_ge_of_mem
#print axioms AssemblyP1.Issue94TW8Contraction.nodeMult_ge_add
#print axioms AssemblyP1.Issue94TW8Contraction.inMult_ge_add
#print axioms AssemblyP1.Issue94TW8Contraction.twiceTraversed_outDeg_eq_one
#print axioms AssemblyP1.Issue94TW8Contraction.twiceTraversed_inDeg_eq_one
#print axioms AssemblyP1.Issue94TW8Contraction.twiceTraversed_contractible
#print axioms AssemblyP1.Issue94TW8Contraction.not_twiceTraversed_of_not_contractible
#print axioms AssemblyP1.Issue94TW8Contraction.wellFormed_GA
#print axioms AssemblyP1.Issue94TW8Contraction.balanced_GA
#print axioms AssemblyP1.Issue94TW8Contraction.edgeSurj_GA
#print axioms AssemblyP1.Issue94TW8Contraction.noTriple_GA
#print axioms AssemblyP1.Issue94TW8Contraction.mA_ab
#print axioms AssemblyP1.Issue94TW8Contraction.outDeg_GA_a
#print axioms AssemblyP1.Issue94TW8Contraction.inDeg_GA_b
#print axioms AssemblyP1.Issue94TW8Contraction.GA_ab_contractible
#print axioms AssemblyP1.Issue94TW8Contraction.outDeg_GB_a
#print axioms AssemblyP1.Issue94TW8Contraction.mB_ab
#print axioms AssemblyP1.Issue94TW8Contraction.nodeMult_GB_a
#print axioms AssemblyP1.Issue94TW8Contraction.not_outDeg_GB_a
#print axioms AssemblyP1.Issue94TW8Contraction.not_noTriple_GB
#print axioms AssemblyP1.Issue94TW7AltF.comm_nextPos_isRotation
#print axioms AssemblyP1.Issue94TW7AltF.altF_eq_id_iff_rotation
#print axioms AssemblyP1.Issue94TW7AltF.ukk_S4
#print axioms AssemblyP1.Issue94TW7AltF.labelPreserving_S4
#print axioms AssemblyP1.Issue94TW7AltF.altF_S4_ne
#print axioms AssemblyP1.Issue94TW7AltF.not_ukk_then_not_altF
#print axioms AssemblyP1.Issue94TW7AltF.not_ukk_then_not_rotation
#print axioms AssemblyP1.Issue94TW7AltF.refutation_is_nonvacuous
#print axioms AssemblyP1.Issue94TW7AltF.vtx_nextPos_shift
#print axioms AssemblyP1.Issue94TW7AltF.node_prefix
#print axioms AssemblyP1.Issue94TW7AltF.S4_length
#print axioms AssemblyP1.Issue94TW7AltF.S4_vtx_02
#print axioms AssemblyP1.Issue94TW7AltF.S4_vtx_13
#print axioms AssemblyP1.Issue94TW7AltF.S4_vtx_01
#print axioms AssemblyP1.Issue94TW7AltF.S4_consistent
#print axioms AssemblyP1.Issue94TW7AltF.not_labelPreserving_altF_id
#print axioms AssemblyP1.Issue94TW7AltF.traverses_is_restrictive

/-! ## `Issue94TruthTraversal`: the word-to-multigraph bridge, and the
kernel-checked refutation of `BOARD94-HPEV-MAP.md` §5b.

`not_edgeSurj_S2` REFUTES the map's statement of Obligation B: the hypothesis
`G ≤ nodeCount v` forces `nodeCount v = G` (because `deg ≤ G`), so every start
spells `v` and the conclusion can only hold for `w = v`.  `not_nodeMult_eq_deg`
refutes the draft's own `nodeMult_eq_deg`.  `edgeCount_le_specCount` is the
true form of the bridge, an inequality.  All kernel-checked. -/
#print axioms AssemblyP1.Issue94TruthTraversal.not_edgeSurj_S2
#print axioms AssemblyP1.Issue94TruthTraversal.nodeCount_eq_G_imp
#print axioms AssemblyP1.Issue94TruthTraversal.vtx_S2
#print axioms AssemblyP1.Issue94TruthTraversal.nodeCount_S2_zero
#print axioms AssemblyP1.Issue94TruthTraversal.truth_traversal_edgeSurj
#print axioms AssemblyP1.Issue94TruthTraversal.truth_edgeSurj
#print axioms AssemblyP1.Issue94TruthTraversal.mem_edgeStarts_iff
#print axioms AssemblyP1.Issue94TruthTraversal.winPrefix_window'
#print axioms AssemblyP1.Issue94TruthTraversal.winSuffix_window'
#print axioms AssemblyP1.Issue94TruthTraversal.glue_winPrefix
#print axioms AssemblyP1.Issue94TruthTraversal.glue_last
#print axioms AssemblyP1.Issue94TruthTraversal.window_eq_glue
#print axioms AssemblyP1.Issue94TruthTraversal.window_eq_glue_of_pair
#print axioms AssemblyP1.Issue94TruthTraversal.winPrefix_window_eq
#print axioms AssemblyP1.Issue94TruthTraversal.winSuffix_window_eq
#print axioms AssemblyP1.Issue94TruthTraversal.edgeCount_le_specCount
#print axioms AssemblyP1.Issue94TruthTraversal.nodeMult_eq_deg
#print axioms AssemblyP1.Issue94TruthTraversal.not_nodeMult_eq_deg

/-! ## #94 front `94c20`: residual R2 of `hPevzner` discharged

The `K ≤ L - 1` half of `BBTEulerian.EulerianCycleObstruction` is proved for
an **arbitrary** circular word: `AssemblyP1.Issue94KShort.obstruction_short_window`
now carries **no** `RepeatAdapter.IsPrimitive` hypothesis.  The range
`L ≤ K` (R1) is untouched and remains open. -/
#print axioms AssemblyP1.Issue94KShort.R2_cyc_congr
#print axioms AssemblyP1.Issue94KShort.R2_cyc_period
#print axioms AssemblyP1.Issue94KShort.R2_cyc_add_mod
#print axioms AssemblyP1.Issue94KShort.R2_vtx_eq_shiftEq
#print axioms AssemblyP1.Issue94KShort.R2_period_mk_shiftEq
#print axioms AssemblyP1.Issue94KShort.R2_shiftEq_mk_period
#print axioms AssemblyP1.Issue94KShort.R2_window_to_period
#print axioms AssemblyP1.Issue94KShort.R2_period_is_invisible
#print axioms AssemblyP1.Issue94KShort.vtx_sigma_eq_vtx_rotAdd_general
#print axioms AssemblyP1.Issue94KShort.vertexCycleEq_short_window_general
#print axioms AssemblyP1.Issue94KShort.obstruction_short_window_general
#print axioms AssemblyP1.Issue94KShort.obstruction_short_window_general'
#print axioms AssemblyP1.Issue94KShort.obstruction_short_window
#print axioms AssemblyP1.Issue94KShort.obstruction_short_window'

/-!
## `P2GcdOne`: gcd one for a primitive `P2` truth, with **no** BBT premise

`AssemblyP1.P2GcdOne` proves that the complete `(L-1)`-read spectrum of a
primitive truth satisfying the actual `def:P1P2` predicate `P2` at
`2 ≤ L ≤ G` has gcd one (`gcd_one_of_primitive_P2`), and hence that normalized
equality of two such spectra forces equal genome lengths and equal complete
spectra (`population_uniqueness_of_primitive_P2`).  The argument uses only two
project-side ingredients: the multiplicity cap
`P2Multiplicity.P2.imp_nodeCount_le_two_of_powerPrimitive` (from the
triple-repeat clause of `P2`) and the nonbranching-gcd-one classification
`ScalarPrimitive.gcdOne_of_nonbranching_primitive`.  No `hBBT`, no
`BBTUniqueAt`, no `BBTCompleteSpectrumUniqueness` and no `AdmP2` is mentioned.

`AssemblyP1.Issue94GcdOneP2` proves the same gcd-one fact by the same two
ingredients, reached through the spectrum-support graph directly
(`nonbranching_of_common_divisor`, `gcdOne_of_primitive_P2`); it is an
independent kernel-checked duplicate route.

**This does not settle `thm:population`.**  `hPevzner` is still bound at
`PopulationUniqueness.lean` lines 178, 231 and 261, because those three sites
need a *second* thing that gcd one does not give: from equal complete spectra
at equal length, `RotEquiv` (`BBTUniqueAt`).  Gcd one discharges the
proportional-cancellation half of the reduction only.
-/
#print axioms AssemblyP1.P2GcdOne.winPrefix_window
#print axioms AssemblyP1.P2GcdOne.nodeCount_ge_two_specs
#print axioms AssemblyP1.P2GcdOne.nonbranching_of_primitive_P2_of_divisible
#print axioms AssemblyP1.P2GcdOne.gcd_one_of_primitive_P2
#print axioms AssemblyP1.P2GcdOne.population_uniqueness_of_primitive_P2
#print axioms AssemblyP1.Issue94GcdOneP2.nonbranching_of_common_divisor
#print axioms AssemblyP1.Issue94GcdOneP2.gcdOne_of_primitive_P2
#print axioms AssemblyP1.PopulationReduction.population_uniqueness_of_spectra
#print axioms AssemblyP1.Issue94Transposition.succ_eq_altF_nextPos
#print axioms AssemblyP1.Issue94Transposition.succ_eq_conj_nextPos
#print axioms AssemblyP1.Issue94Transposition.involution_support_mod_four_5
#print axioms AssemblyP1.Issue94Transposition.involution_support_mod_four_6
#print axioms AssemblyP1.Issue94Transposition.involution_support_two_impossible_5
#print axioms AssemblyP1.Issue94Transposition.altF_even_5
#print axioms AssemblyP1.Issue94Transposition.no_single_factor_step_5
#print axioms AssemblyP1.Issue94Transposition.no_single_factor_step_6


/-!
## `Issue94ObstructionEquiv`: an audit of the residual hypothesis of the #89 endpoint

`AssemblyP1/Issue94ObstructionEquiv.lean` does **not** prove
`EulerianCycleObstruction L ↔ BBTUniqueAt L`. It records the surviving library
direction, the per-length decomposition, and a kernel-checked refutation of the
false claim that every start permutation is the pull-back of a `Matching`.
The converse is named as the open `Prop` `BBT94.ObstructionFromBBT` and left unproved.
See `docs/issue-94-obstruction-equiv.md`.

**SUPERSEDED IN PART** (board 94, front `94real`, see
`docs/issue-94-eulerian-realize.md`). The converse is now proved, in
`AssemblyP1/Issue94EulerianRealize.lean`: every `EulerianCycle` *is* the
pull-back of a `Matching`, so `EulerianCycleObstruction L ↔ BBTUniqueAt L` at
`2 ≤ L`. The refutation of "every start permutation" above stands and is not
contradicted --- its instance `σ = (2 3)` is not an `EulerianCycle`.
-/


/-!
## `Issue94P2PrimInterface`: the interface a route has to hit

`AssemblyP1/Issue94P2PrimInterface.lean` isolates the residual of #89 in the
weakest form the endpoint actually consumes. Reading the proof of
`PopulationUniqueness.population_unique_ML_up_to_rotation`, its single hypothesis
`hPevzner : EulerianCycleObstruction L` is used at exactly two sites
(`PopulationUniqueness.lean:212` and `:214`), and at both the word it applies to
satisfies `P2` **and** primitivity, the competitor ranges over all words, and the
genome length is unrestricted. So the residual is not `BBTUniqueAt L` and not
`EulerianCycleObstruction L`; it is

  `BBTP2Prim L` --- complete-`L`-spectrum uniqueness at `P2`-and-primitive truths.

`BBTP2Prim L` is then split into the two genome-length ranges. The `K ≤ L - 1`
half is **already a theorem** for arbitrary words
(`Issue94KShort.vertexCycleEq_short_window_general`), so the residual is the
long half `P2LongUnique L` alone, and `population_unique_ML_of_long_unique`
turns that, plus assumptions the endpoint already carries, into `thm:population`.
A route --- including a Cohn--Lempel block-deletion argument --- has one named
target and one line to apply afterwards. The interface is stated on the
project's own objects with no graph vocabulary, so it can be proved in isolation.

`P2LongUnique L` is a `Prop` and is **not** an inhabitant; issue #89 is not
settled. `bbTP2Prim_of_obstruction` and `population_unique_ML_of_BBTUniqueAt`
show nothing is lost: the interface is implied by the already-postulated
obstruction, and after the `Issue94EulerianRealize` bridge the endpoint follows
from `thm:BBT` in its source form with no Eulerian-cycle object named.

See `docs/issue-94-long-window-interface-94.md`. The companion
`AssemblyP1/Issue94LongWindowSplit.lean` instantiates the short half from
`Issue94KShort`; it is **not** registered here because its import chain reaches
`AssemblyP1.Issue94OrbitSearch`, which is OOM-killed (exit 137) under this
container's 8 GiB cgroup --- pre-existing, see
`docs/issue-94-eulerian-realize.md` §7.
-/
#print axioms AssemblyP1.Issue94Interface.bbTP2Prim_iff_bbTP2Prim'
#print axioms AssemblyP1.Issue94Interface.bbtCompleteSpec_of_P2Prim'
#print axioms AssemblyP1.Issue94Interface.bbtCompleteSpec_of_P2Prim
#print axioms AssemblyP1.Issue94Interface.long_short_of_long
#print axioms AssemblyP1.Issue94Interface.population_unique_ML_of_P2Prim
#print axioms AssemblyP1.Issue94Interface.population_unique_ML_of_long_unique
#print axioms AssemblyP1.Issue94Interface.population_unique_ML_same_length_of_P2Prim
#print axioms AssemblyP1.Issue94Interface.population_tie_implies_rotation_of_P2Prim
#print axioms AssemblyP1.Issue94Interface.p2LongUnique_of_bbtUniqueAt
#print axioms AssemblyP1.Issue94Interface.bbTP2Prim_of_bbtUniqueAt
#print axioms AssemblyP1.Issue94Interface.bbTP2Prim_of_obstruction

/-! ## Axiom audit for the #217 finite-front integrations

These five modules are the novel artifacts of the live finite leaves, integrated
on `agent/board-217-978a0a`; each is self-contained and namespace-isolated.  The
finite same-length tie/uniqueness module (#211) still carries the complete-
spectrum uniqueness input as an explicit premise (`FibreFreedomForcesLongRepeat`),
so its rotation conclusion is conditional; the *population* theorem
`AssemblyP1.Issue94Complete.population_unique_ML` is unconditional.  The two
general-flow modules (#214: `Section62NonSpelledFlow` at `o_min = 1`, whose
optimum has a non-spellable throughput, and `Section62FullOverlapDisconnected`
at `o_min = L-1`, whose disconnected optimum's throughput *is* spellable), the
two duplex modules (#215) and the implication lattice (#216) are unconditional.
#219's fibre-count arithmetic module (`FibreCountArithmetic`) is committed
(leaf #219 terminal, `81d29c6`) and imported here: it is the kernel-checked
divisor-sum core (Möbius inversion, totient rearrangement); the BEST/Matrix-Tree
graph content remains external. -/
#print axioms AssemblyP1.SameLength62TieUniqueness.informationFeasible_62_exact_tie
#print axioms AssemblyP1.SameLength62TieUniqueness.maximizer_and_tie_of_Is_and_62
#print axioms AssemblyP1.SameLength62TieUniqueness.no_interleaved_long_repeats_of_Is
#print axioms AssemblyP1.SameLength62TieUniqueness.bbt_premise_refuted_G6_L2
#print axioms AssemblyP1.Section62NonSpelledFlow.nonspelled_se62_flow_domain_countermodel
#print axioms AssemblyP1.Section62NonSpelledFlow.star_argmax
#print axioms AssemblyP1.Section62NonSpelledFlow.half_integral_strictly_better
#print axioms AssemblyP1.Section62NonSpelledFlow.no_sequence_has_star_spectrum
#print axioms AssemblyP1.Section62NonSpelledFlow.spelled_subset_general
#print axioms AssemblyP1.Section62FullOverlapDisconnected.full_overlap_disconnected_optimum
#print axioms AssemblyP1.Section62FullOverlapDisconnected.disc_support_disconnected
#print axioms AssemblyP1.Section62FullOverlapDisconnected.dStar_argmax
#print axioms AssemblyP1.DoubleStrandBridgingTransfer.doubled_not_information_feasible
#print axioms AssemblyP1.TwoDisjointCirclesDuplex.partner_window_rc
#print axioms AssemblyP1.TwoDisjointCirclesDuplex.rcS_information_feasible
#print axioms AssemblyP1.TwoDisjointCirclesDuplex.specDuplex_eq
#print axioms AssemblyP1.TwoDisjointCirclesDuplex.two_readings_diverge
#print axioms AssemblyP1.ImplicationLattice.unique_implies_maximizer_with_membership
#print axioms AssemblyP1.ImplicationLattice.strict_refutes_unique
#print axioms AssemblyP1.ImplicationLattice.membership_failure_refutes_maximizer_with_membership
#print axioms AssemblyP1.ImplicationLattice.conversion
#print axioms AssemblyP1.ImplicationLattice.population_D_le_S
#print axioms AssemblyP1.ImplicationLattice.population_eq_iff_spectra
#print axioms AssemblyP1.ImplicationLattice.amplification_strict_of_qMul_gt_one
#print axioms AssemblyP1.ImplicationLattice.ConcretePanel.sigma_oriented_strict
#print axioms AssemblyP1.ImplicationLattice.ConcretePanel.upsilon_molecular_strict
#print axioms AssemblyP1.ImplicationLattice.ConcretePanel.lambda1_A_tie
#print axioms AssemblyP1.OrientedVariableLengthSe62.oriented_variable_length_se62_counterexample
#print axioms AssemblyP1.OrientedVariableLengthSe62.oriented_variable_length_se62_counterexample'
#print axioms AssemblyP1.Section62VarlenPerOccurrence.truth_not_maximizer_in_general_flow_universe
#print axioms AssemblyP1.Section62VarlenPerOccurrence.competitor_is_unique_optimizer
#print axioms AssemblyP1.FibreCount.sum_antidiagonal_eq_sum_divisors
#print axioms AssemblyP1.FibreCount.sum_divisors_inv_mul_eq
#print axioms AssemblyP1.FibreCount.sum_divisors_divisors
#print axioms AssemblyP1.FibreCount.sum_moebius_div_eq_totient
#print axioms AssemblyP1.FibreCount.fibre_mobius_inversion
#print axioms AssemblyP1.FibreCount.fibre_totient
#print axioms AssemblyP1.Issue94Interface.population_unique_ML_of_BBTUniqueAt
