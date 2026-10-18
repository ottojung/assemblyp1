import AssemblyP1.Section62ReductionDependencyAudit
import AssemblyP1.PerOccurrenceSameLengthCounterexample

/-!
# #284: explicit survival of the §6.2 finite witnesses under the corrected
spelling-preserving transitive reduction

Issue #284 requires that every existing §6.2 counterexample or proof whose formal
statement references the *old* literal predicate
`Section62Flow.transitivelyReduced` be re-evaluated under the corrected
spelling-preserving reduction
`Section62SpellingReductionCandidate.transitivelyReducedSpelling`, and that the
surviving conclusions be distinguished from those that must be re-proved.

`Section62ReductionDependencyAudit` supplies the general bridge
(`transitivelyReducedSpelling_eq_self_of_full`,
`stepsSurviveReductionSpelling_of_maximal`) and the genuinely nontrivial
`oMin = 1` case (`Section62NonSpelledFlow`).  It *asserts* that the three
`oMin = readLen − 1 = 2` witnesses — `Section62BridgingCounterexample`,
`SameLengthSection62Counterexample` and
`PerOccurrenceSameLengthCounterexample` — survive because their graphs are
already reduced.  This module discharges that assertion **explicitly and in the
kernel** for each witness, rather than by prose.

For each of the three witnesses it proves, over that witness's own generated
`overlapEdges` graph:

* the corrected reduction is the identity on the graph
  (`…_graph_spelling_reduction_eq_self`);
* both the truth's and the competitor's cyclic-walk steps survive the corrected
  reduction (`…_truth_steps_survive_spelling`,
  `…_competitor_steps_survive_spelling`);
* the witnesses satisfy the corrected, spelling-preserving analogue
  `SpelledFeasible62Spelling` of `SpelledFeasible62`
  (`…_truth_spelled_feasible62_spelling`,
  `…_competitor_spelled_feasible62_spelling`).

The reason is uniform and kernel-checked: every edge of these graphs has the
maximal proper overlap length `readLen − 1 = 2`, and
`fullOverlap_not_reducible` shows no such edge is spelling-preservingly
reducible.  Hence the old and corrected reductions coincide on these graphs, so
the old conclusions survive verbatim.  Nothing here re-proves
`spellPath_eq_spellDirect`, `replacement_overlaps_longer`, or the
`Section62ReductionDependencyAudit` bridges; nothing here changes any existing
symbol.  This module is the requirement-(6) close-out for the corrected graph
model handed to #261/#262.
-/

namespace AssemblyP1.Section62ReductionWitnessAudit

open Section62Flow Section62SpellingReductionCandidate

set_option maxHeartbeats 8000000

/-! ## Corrected predicates, parallel to the audited originals

`StepsSurviveReduction` and `SpelledFeasible62` in `Section62BidirectedFlow`
reference the old `transitivelyReduced`.  The two definitions below are their
verbatim spelling-preserving analogues; the originals are left untouched as the
model being audited (issue #284 requirement 1). -/

/-- The corrected spelling-preserving analogue of
`Section62Flow.StepsSurviveReduction`: every step of a spelling walk lies on the
spelling-preserving transitive reduction of `edges`.  Unlike the old predicate
this carries the overlap threshold `oMin`, because the spelling-preserving
reduction depends on which path overlaps exist in the graph. -/
def StepsSurviveReductionSpelling (A : Type) (W : Type) [DecidableEq A] [DecidableEq W]
    {n : Nat} (toList : W → List A) (rep rc : W → W) (readLen oMin : Nat)
    (verts : List W) (sp : Spelling A W n) (edges : List (BdEdge A W)) : Prop :=
  ∀ i : Fin n,
    sp.step rep readLen i ∈
      transitivelyReducedSpelling W toList rc readLen oMin verts edges

/-- The corrected spelling-preserving analogue of `Section62Flow.SpelledFeasible62`:
the last conjunct of `Section62Flow.SpelledFeasible62` is unchanged, but the
walk lives on the *spelling-reduced* graph rather than the literally reduced
(and vacuous) one. -/
def SpelledFeasible62Spelling (A : Type) (W : Type) [DecidableEq A] [DecidableEq W]
    {n : Nat} (toList : W → List A) (rep rc : W → W) (readLen oMin : Nat)
    (verts : List W) (sp : Spelling A W n) (f : BdFlow A W) (t : SuperTerminals W)
    (d : W → ℕ) : Prop :=
  VisitsObserved rep sp verts ∧
    StepsInGraph rep readLen sp (overlapEdges A W toList rep rc readLen oMin verts) ∧
    StepsSurviveReductionSpelling A W toList rep rc readLen oMin verts sp
      (overlapEdges A W toList rep rc readLen oMin verts) ∧
    BidirectedCircuit rep readLen sp ∧
    Feasible62 A W rep verts (overlapEdges A W toList rep rc readLen oMin verts) f t d

/-! ## The uniform reason: a full-overlap graph is already reduced -/

/-- On a graph all of whose edges have the maximal proper overlap length
`readLen − 1`, the spelling-preserving step-survival predicate is equivalent to
plain membership of the steps in the graph: the corrected reduction deletes
nothing. -/
theorem stepsSurviveReductionSpelling_iff_stepsInGraph_of_full
    {A W : Type} [DecidableEq A] [DecidableEq W] {n : Nat}
    (toList : W → List A) (rep rc : W → W) (readLen oMin : Nat) (verts : List W)
    (sp : Spelling A W n) (edges : List (BdEdge A W))
    (hfull : ∀ e ∈ edges, e.len = readLen - 1) :
    StepsSurviveReductionSpelling A W toList rep rc readLen oMin verts sp edges ↔
      StepsInGraph rep readLen sp edges := by
  unfold StepsSurviveReductionSpelling StepsInGraph
  rw [Section62ReductionDependencyAudit.transitivelyReducedSpelling_eq_self_of_full
    toList rc readLen oMin verts edges hfull]

/-! ## `Section62BridgingCounterexample` (`AAATT` vs `AAAATT`, `oMin = 2`) -/

section BridgingAudit

open AssemblyP1.Section62BridgingCounterexample

/-- The corrected reduction removes no edge of the bridging witness graph: every
overlap has length `readLen − 1 = 2`. -/
theorem bridging_graph_spelling_reduction_eq_self :
    transitivelyReducedSpelling Strand3 toList3 rc3 readLen oMin readVerts
      graphList = graphList := by
  decide

/-- The generated bridging graph and its written-out edge list are the same, so
the corrected predicates over `overlapEdges` can be checked on `graphList`. -/
theorem bridging_overlapEdges_eq_graphList :
    overlapEdges Base Strand3 toList3 rep3 rc3 readLen oMin readVerts = graphList := by
  show graph = graphList
  exact graph_eq

/-- Every step of the truth's cyclic walk survives the *corrected* reduction. -/
theorem bridging_truth_steps_survive_spelling :
    StepsSurviveReductionSpelling Base Strand3 toList3 rep3 rc3 readLen oMin readVerts
      spellTruth graphList := by
  unfold StepsSurviveReductionSpelling
  rw [bridging_graph_spelling_reduction_eq_self]
  exact truth_steps_in_graph

/-- Every step of the competitor's cyclic walk survives the corrected reduction. -/
theorem bridging_competitor_steps_survive_spelling :
    StepsSurviveReductionSpelling Base Strand3 toList3 rep3 rc3 readLen oMin readVerts
      spellCompetitor graphList := by
  unfold StepsSurviveReductionSpelling
  rw [bridging_graph_spelling_reduction_eq_self]
  exact competitor_steps_in_graph

/-- The truth `AAATT` remains a spelled §6.2 candidate under the corrected
spelling-preserving reduction. -/
theorem bridging_truth_spelled_feasible62_spelling :
    SpelledFeasible62Spelling Base Strand3 toList3 rep3 rc3 readLen oMin readVerts
      spellTruth truthCircuitFlow noTerm dS' := by
  refine ⟨truth_visits_observed, ?_, ?_, truth_bidirected_circuit, ?_⟩
  · rw [bridging_overlapEdges_eq_graphList]; exact truth_steps_in_graph
  · rw [bridging_overlapEdges_eq_graphList]; exact bridging_truth_steps_survive_spelling
  · rw [bridging_overlapEdges_eq_graphList]; exact truth_feasible62

/-- The competitor `AAAATT` remains a spelled §6.2 candidate under the corrected
reduction. -/
theorem bridging_competitor_spelled_feasible62_spelling :
    SpelledFeasible62Spelling Base Strand3 toList3 rep3 rc3 readLen oMin readVerts
      spellCompetitor competitorCircuitFlow noTerm dD' := by
  refine ⟨competitor_visits_observed, ?_, ?_, competitor_bidirected_circuit, ?_⟩
  · rw [bridging_overlapEdges_eq_graphList]; exact competitor_steps_in_graph
  · rw [bridging_overlapEdges_eq_graphList]
    exact bridging_competitor_steps_survive_spelling
  · rw [bridging_overlapEdges_eq_graphList]; exact competitor_feasible62

end BridgingAudit

/-! ## `SameLengthSection62Counterexample` (`AAATAT` vs `AAAAAT`, `oMin = 2`) -/

section SameLengthAudit

open AssemblyP1.SameLengthSection62Counterexample

/-- The corrected reduction removes no edge of the same-length witness graph. -/
theorem sameLength_graph_spelling_reduction_eq_self :
    transitivelyReducedSpelling Strand3 toList3 rc3 readLen oMin readVerts
      graphList = graphList := by
  decide

/-- The generated same-length graph equals its written-out edge list. -/
theorem sameLength_overlapEdges_eq_graphList :
    overlapEdges Base Strand3 toList3 rep3 rc3 readLen oMin readVerts = graphList := by
  show graph = graphList
  exact graph_eq

/-- Every step of the truth's cyclic walk survives the corrected reduction. -/
theorem sameLength_truth_steps_survive_spelling :
    StepsSurviveReductionSpelling Base Strand3 toList3 rep3 rc3 readLen oMin readVerts
      spellTruth graphList := by
  unfold StepsSurviveReductionSpelling
  rw [sameLength_graph_spelling_reduction_eq_self]
  exact truth_steps_in_graph

/-- Every step of the competitor's cyclic walk survives the corrected reduction. -/
theorem sameLength_competitor_steps_survive_spelling :
    StepsSurviveReductionSpelling Base Strand3 toList3 rep3 rc3 readLen oMin readVerts
      spellCompetitor graphList := by
  unfold StepsSurviveReductionSpelling
  rw [sameLength_graph_spelling_reduction_eq_self]
  exact competitor_steps_in_graph

/-- The truth remains a spelled §6.2 candidate under the corrected reduction. -/
theorem sameLength_truth_spelled_feasible62_spelling :
    SpelledFeasible62Spelling Base Strand3 toList3 rep3 rc3 readLen oMin readVerts
      spellTruth truthCircuitFlow noTerm dS' := by
  refine ⟨truth_visits_observed, ?_, ?_, truth_bidirected_circuit, ?_⟩
  · rw [sameLength_overlapEdges_eq_graphList]; exact truth_steps_in_graph
  · rw [sameLength_overlapEdges_eq_graphList]; exact sameLength_truth_steps_survive_spelling
  · rw [sameLength_overlapEdges_eq_graphList]; exact truth_feasible62

/-- The competitor remains a spelled §6.2 candidate under the corrected
reduction. -/
theorem sameLength_competitor_spelled_feasible62_spelling :
    SpelledFeasible62Spelling Base Strand3 toList3 rep3 rc3 readLen oMin readVerts
      spellCompetitor competitorCircuitFlow noTerm dD' := by
  refine ⟨competitor_visits_observed, ?_, ?_, competitor_bidirected_circuit, ?_⟩
  · rw [sameLength_overlapEdges_eq_graphList]; exact competitor_steps_in_graph
  · rw [sameLength_overlapEdges_eq_graphList]
    exact sameLength_competitor_steps_survive_spelling
  · rw [sameLength_overlapEdges_eq_graphList]; exact competitor_feasible62

end SameLengthAudit

/-! ## `PerOccurrenceSameLengthCounterexample` (`ATATACAC` vs `ATACACAC`, `oMin = 2`) -/

section PerOccurrenceAudit

open AssemblyP1.PerOccurrenceSameLengthCounterexample

/-- The corrected reduction removes no edge of the per-occurrence witness graph. -/
theorem perOccurrence_graph_spelling_reduction_eq_self :
    transitivelyReducedSpelling W3 toList3 rc3 readLen oMin readVerts
      graphList = graphList := by
  decide

/-- The generated per-occurrence graph equals its written-out edge list. -/
theorem perOccurrence_overlapEdges_eq_graphList :
    overlapEdges Base W3 toList3 rep3 rc3 readLen oMin readVerts = graphList := by
  show graph = graphList
  exact graph_eq

/-- Every step of the truth's cyclic walk survives the corrected reduction. -/
theorem perOccurrence_truth_steps_survive_spelling :
    StepsSurviveReductionSpelling Base W3 toList3 rep3 rc3 readLen oMin readVerts
      spellTruth graphList := by
  unfold StepsSurviveReductionSpelling
  rw [perOccurrence_graph_spelling_reduction_eq_self]
  exact truth_steps_in_graph

/-- Every step of the competitor's cyclic walk survives the corrected reduction. -/
theorem perOccurrence_competitor_steps_survive_spelling :
    StepsSurviveReductionSpelling Base W3 toList3 rep3 rc3 readLen oMin readVerts
      spellCompetitor graphList := by
  unfold StepsSurviveReductionSpelling
  rw [perOccurrence_graph_spelling_reduction_eq_self]
  exact competitor_steps_in_graph

/-- The truth remains a spelled §6.2 candidate under the corrected reduction. -/
theorem perOccurrence_truth_spelled_feasible62_spelling :
    SpelledFeasible62Spelling Base W3 toList3 rep3 rc3 readLen oMin readVerts
      spellTruth truthCircuitFlow noTerm dS' := by
  refine ⟨truth_visits_observed, ?_, ?_, truth_bidirected_circuit, ?_⟩
  · rw [perOccurrence_overlapEdges_eq_graphList]; exact truth_steps_in_graph
  · rw [perOccurrence_overlapEdges_eq_graphList]
    exact perOccurrence_truth_steps_survive_spelling
  · rw [perOccurrence_overlapEdges_eq_graphList]; exact truth_feasible62

/-- The competitor remains a spelled §6.2 candidate under the corrected
reduction. -/
theorem perOccurrence_competitor_spelled_feasible62_spelling :
    SpelledFeasible62Spelling Base W3 toList3 rep3 rc3 readLen oMin readVerts
      spellCompetitor competitorCircuitFlow noTerm dD' := by
  refine ⟨competitor_visits_observed, ?_, ?_, competitor_bidirected_circuit, ?_⟩
  · rw [perOccurrence_overlapEdges_eq_graphList]; exact competitor_steps_in_graph
  · rw [perOccurrence_overlapEdges_eq_graphList]
    exact perOccurrence_competitor_steps_survive_spelling
  · rw [perOccurrence_overlapEdges_eq_graphList]; exact competitor_feasible62

end PerOccurrenceAudit

/-! ## Axiom audit -/

#print axioms stepsSurviveReductionSpelling_iff_stepsInGraph_of_full
#print axioms bridging_graph_spelling_reduction_eq_self
#print axioms bridging_truth_spelled_feasible62_spelling
#print axioms bridging_competitor_spelled_feasible62_spelling
#print axioms sameLength_graph_spelling_reduction_eq_self
#print axioms sameLength_truth_spelled_feasible62_spelling
#print axioms sameLength_competitor_spelled_feasible62_spelling
#print axioms perOccurrence_graph_spelling_reduction_eq_self
#print axioms perOccurrence_truth_spelled_feasible62_spelling
#print axioms perOccurrence_competitor_spelled_feasible62_spelling

end AssemblyP1.Section62ReductionWitnessAudit
