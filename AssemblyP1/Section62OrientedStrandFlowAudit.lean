import AssemblyP1.Section62ReversalInvolution
import AssemblyP1.Section62OrientedMLClassification

/-!
# Axiom audit for the corrected oriented-strand source model and its ML classification (#261)

Audits every new declaration of
`AssemblyP1.Section62OrientedStrandFlow` and
`AssemblyP1.Section62OrientedMLClassification`.  The expected axiom set is
`[propext, Classical.choice, Quot.sound]` (most `decide`/structural lemmas use
none), with no `sorryAx`.  No `sorry` / `admit` / `axiom` / `native_decide`.
-/

/-! ## Source model -/

#print axioms AssemblyP1.Section62OrientedStrandFlow.sgnRep_oRep
#print axioms AssemblyP1.Section62OrientedStrandFlow.sgnTgt_oRep
#print axioms AssemblyP1.Section62OrientedStrandFlow.oRep_ne_self_rc
#print axioms AssemblyP1.Section62OrientedStrandFlow.oRc_involutive
#print axioms AssemblyP1.Section62OrientedStrandFlow.strandsOf_oVerts
#print axioms AssemblyP1.Section62OrientedStrandFlow.bdEdge_oRep_sgnX
#print axioms AssemblyP1.Section62OrientedStrandFlow.bdEdge_oRep_sgnY
#print axioms AssemblyP1.Section62OrientedStrandFlow.oWord_pal
#print axioms AssemblyP1.Section62OrientedStrandFlow.oWord_oRc
#print axioms AssemblyP1.Section62OrientedStrandFlow.strandsOf_pal
#print axioms AssemblyP1.Section62OrientedStrandFlow.historical_pal_sign_collision
#print axioms AssemblyP1.Section62OrientedStrandFlow.historical_pal_edge_collision
#print axioms AssemblyP1.Section62OrientedStrandFlow.tagged_pal_edge_distinct
#print axioms AssemblyP1.Section62OrientedStrandFlow.rcB_involutive
#print axioms AssemblyP1.Section62OrientedStrandFlow.pal4_is_palindrome
#print axioms AssemblyP1.Section62OrientedStrandFlow.np3_not_palindrome
#print axioms AssemblyP1.Section62OrientedStrandFlow.repB_pal4
#print axioms AssemblyP1.Section62OrientedStrandFlow.repB_np3
#print axioms AssemblyP1.Section62OrientedStrandFlow.repB_rcB_np3
#print axioms AssemblyP1.Section62OrientedStrandFlow.historical_pal_graph_quadruple
#print axioms AssemblyP1.Section62OrientedStrandFlow.historical_pal_sign_pairs
#print axioms AssemblyP1.Section62OrientedStrandFlow.corrected_pal_graph_nodup
#print axioms AssemblyP1.Section62OrientedStrandFlow.corrected_pal_sign_pairs
#print axioms AssemblyP1.Section62OrientedStrandFlow.corrected_pal_graph_words
#print axioms AssemblyP1.Section62OrientedStrandFlow.corrected_pal_throughput_one
#print axioms AssemblyP1.Section62OrientedStrandFlow.corrected_pal_balance_zero
#print axioms AssemblyP1.Section62OrientedStrandFlow.corrected_pal_feasible_one
#print axioms AssemblyP1.Section62OrientedStrandFlow.historical_pal_throughput_four
#print axioms AssemblyP1.Section62OrientedStrandFlow.historical_pal_not_feasible_one
#print axioms AssemblyP1.Section62OrientedStrandFlow.nonpal_graph_lengths_eq
#print axioms AssemblyP1.Section62OrientedStrandFlow.nonpal_sign_pairs_eq
#print axioms AssemblyP1.Section62OrientedStrandFlow.nonpal_words_eq
#print axioms AssemblyP1.Section62OrientedStrandFlow.nonpal_corrected_nodup
#print axioms AssemblyP1.Section62OrientedStrandFlow.nonpal_historical_nodup

/-! ## ML classification in the corrected domain -/

#print axioms AssemblyP1.Section62OrientedMLClassification.oriented_maximal_iff_image
#print axioms AssemblyP1.Section62OrientedMLClassification.oriented_spelled_visits_mem_image
#print axioms AssemblyP1.Section62OrientedMLClassification.oriented_spelled_maximal_of_flow_maximal
#print axioms AssemblyP1.Section62OrientedMLClassification.oriented_flow_not_maximal_of_spelled_witness
#print axioms AssemblyP1.Section62OrientedMLClassification.oriented_maximal_iff_spelled_maximal_of_image_eq

-- Bounded representation-reversal / overlap-orbit audit (#261).
#print axioms AssemblyP1.Section62ReversalInvolution.revPair_involutive
#print axioms AssemblyP1.Section62ReversalInvolution.orientPairs_orbit_count
#print axioms AssemblyP1.Section62ReversalInvolution.orientPairs_orbit_exact
#print axioms AssemblyP1.Section62ReversalInvolution.orientPairs_orbit_cover
#print axioms AssemblyP1.Section62ReversalInvolution.oOverlap_revEdge
#print axioms AssemblyP1.Section62ReversalInvolution.oOverlap_revEdge_rcB
#print axioms AssemblyP1.Section62ReversalInvolution.atat_orbit_count_eq_orientPairs
