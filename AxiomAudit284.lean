import AssemblyP1.Section62GlobalSkippedBridge
import AssemblyP1.Section62ObservedMoleculeCount
import AssemblyP1.Section62GenericAnchorSpelling
import AssemblyP1.Section62RcWordLaw
import AssemblyP1.Section62MyersIdealTransitivity
import AssemblyP1.Section62ReductionDependencyAudit
import AssemblyP1.Section62SimultaneousReduction
import AssemblyP1.Section62VisitTransport
import AssemblyP1.Section62VisitWindowBridge
import AssemblyP1.Section62WindowBoxSharpness
import AssemblyP1.Section62SpellChainWindowTransport

/-!
# #284 axiom audit

Prints the axiom dependency of every endpoint of the corrected §6.2
transitive-reduction / spelling-fidelity chain. Every declaration below must
depend only on `propext`, `Classical.choice`, `Quot.sound` (or nothing), with no
`sorryAx`. This mirrors `AxiomAudit211/257/271/300`; the CI job "Audit axioms in
every theorem module" additionally audits every module via `--modules-from
AssemblyP1`, so this file is a human-readable summary, not the sole gate.
-/

-- Circular window adapter / abstract partition
#print axioms AssemblyP1.Section62CircularWindowAdapter.window_count_decomposition
#print axioms AssemblyP1.Section62CircularWindowAdapter.window_count_eq_anchors_iff
#print axioms AssemblyP1.Section62CircularWindowAdapter.observation7_window_count
#print axioms AssemblyP1.Section62CircularWindowAdapter.observation7_range_count

-- Generic periodic-window / anchor bridges
#print axioms AssemblyP1.Section62PeriodicSeam.seam_periodic_prefix
#print axioms AssemblyP1.Section62AnchoredWindowBridge.periodic_window_eq_drop_take
#print axioms AssemblyP1.Section62AnchoredWindowBridge.signed_circuit_window_eq_linear
#print axioms AssemblyP1.Section62AnchorSourceWords.aligned_source_words
#print axioms AssemblyP1.Section62AnchorSourceWords.pathTail_len_eq_extensions_sum
#print axioms AssemblyP1.Section62AnchorSourceWords.signed_circuit_anchors_are_read_words

-- Generic (graph-free) anchored-window identity, new in #284
#print axioms AssemblyP1.Section62GenericAnchorSpelling.appendedTails_length
#print axioms AssemblyP1.Section62GenericAnchorSpelling.generic_anchors_window_eq_sources
#print axioms AssemblyP1.Section62GenericAnchorSpelling.generic_circular_spelling_anchors

-- The constructed CircularSpelling and the occurrence theorem
#print axioms AssemblyP1.Section62GlobalSkippedBridge.reduced_graph_no_observed_steps
#print axioms AssemblyP1.Section62GlobalSkippedBridge.reduced_signed_circuit_no_skipped_windows
#print axioms AssemblyP1.Section62GlobalSkippedBridge.reduced_signed_circuit_circular_spelling
#print axioms AssemblyP1.Section62GlobalSkippedBridge.observation7_reduced_signed_circuit_range_count

-- RC observed molecule-class corollary and its word-level law
#print axioms AssemblyP1.Section62ObservedMoleculeCount.classWordCount_rc_invariant
#print axioms AssemblyP1.Section62ObservedMoleculeCount.observation7_observed_rc_class_count
#print axioms AssemblyP1.Section62RcWordLaw.toList3_rc3
#print axioms AssemblyP1.Section62RcWordLaw.rc3_involutive
#print axioms AssemblyP1.Section62RcWordLaw.classWordCount_eq_rc_class_count

-- Idealized Myers two-hop equivalence and the dependency re-audit
#print axioms AssemblyP1.Section62MyersIdealTransitivity.reducible_iff_ideal_two_hop
#print axioms AssemblyP1.Section62MyersIdealTransitivity.reduced_mem_iff_no_ideal_detour
#print axioms AssemblyP1.Section62MyersIdealTransitivity.overlapLens_gt_direct_of_comp
#print axioms AssemblyP1.Section62MyersIdealTransitivity.twoHop_overlap_sum
#print axioms AssemblyP1.Section62MyersIdealTransitivity.twoHop_overlaps_gt_direct
#print axioms AssemblyP1.Section62ReductionDependencyAudit.transitivelyReducedSpelling_eq_self_of_full
#print axioms AssemblyP1.Section62ReductionDependencyAudit.stepsSurviveReductionSpelling_of_maximal

-- Simultaneous (global) language preservation via the well-founded decrease
#print axioms AssemblyP1.Section62SimultaneousReduction.exists_detour_of_reducible
#print axioms AssemblyP1.Section62SimultaneousReduction.exists_irreducible_expansion
#print axioms AssemblyP1.Section62SimultaneousReduction.reduction_preserves_language
#print axioms AssemblyP1.Section62SimultaneousReduction.cascade_spell

-- Physical visit-count transport diagnostic (negative half)
#print axioms AssemblyP1.Section62VisitTransport.windows_detour_eq
#print axioms AssemblyP1.Section62VisitTransport.no_transport_function
#print axioms AssemblyP1.Section62VisitTransport.transport_required_false

-- Physical visit-count transport bound (positive half, new in #284)
#print axioms AssemblyP1.Section62VisitWindowBridge.genuineWalk_length
#print axioms AssemblyP1.Section62VisitWindowBridge.spellWalk_cons_drop
#print axioms AssemblyP1.Section62VisitWindowBridge.windows_spellWalk_cons
#print axioms AssemblyP1.Section62VisitWindowBridge.genuineWalk_dominates
#print axioms AssemblyP1.Section62VisitWindowBridge.visitCount_le_windowCount
#print axioms AssemblyP1.Section62VisitWindowBridge.windowCount_detour_eq
#print axioms AssemblyP1.Section62VisitWindowBridge.witness_bound_strict
#print axioms AssemblyP1.Section62VisitWindowBridge.witness_bound_holds

-- Window-box sharpness refutation (new in #284): no observed-window designation
-- hypothesis sharpens the invariant box to the exact physical image.
#print axioms AssemblyP1.Section62WindowBoxSharpness.physImage_subset_windowBox
#print axioms AssemblyP1.Section62WindowBoxSharpness.genuineWalk_spell_length_le
#print axioms AssemblyP1.Section62WindowBoxSharpness.prefix_delta_mem_box
#print axioms AssemblyP1.Section62WindowBoxSharpness.delta_prefix_not_mem_image
#print axioms AssemblyP1.Section62WindowBoxSharpness.no_prefix_support_designation_sharpens
#print axioms AssemblyP1.Section62WindowBoxSharpness.endpoint_prefix_refuted
#print axioms AssemblyP1.Section62WindowBoxSharpness.endpoint_pair_refuted

-- Real-model `spellChain` window-multiset bridge (new in #284): the §6.2 spelling
-- function agrees with the walk spelling, and its window multiset dominates the
-- physical visited reads of a genuine chain.
#print axioms AssemblyP1.Section62SpellChainWindowTransport.spellChain_eq_spellWalk
#print axioms AssemblyP1.Section62SpellChainWindowTransport.spellChain_windows_congr
#print axioms AssemblyP1.Section62SpellChainWindowTransport.reduction_preserves_language_windows
#print axioms AssemblyP1.Section62SpellChainWindowTransport.genuineChain_of_overlapEdges
#print axioms AssemblyP1.Section62SpellChainWindowTransport.chainStrands_subset_strandsOf
#print axioms AssemblyP1.Section62SpellChainWindowTransport.chain_visited_dominated
#print axioms AssemblyP1.Section62SpellChainWindowTransport.genuineChain_visited_dominated
