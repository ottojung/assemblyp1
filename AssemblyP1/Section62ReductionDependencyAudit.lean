import AssemblyP1.Section62SpellingReductionCandidate
import AssemblyP1.Section62NonSpelledFlow

/-!
# #284: re-audit of §6.2 results that depended on the vacuous `transitivelyReduced`

Issue #284 requires that every existing §6.2 counterexample or proof whose formal
statement references the *old* literal predicate `Section62Flow.transitivelyReduced`
be re-evaluated under the corrected *spelling-preserving* reduction
`Section62SpellingReductionCandidate.transitivelyReducedSpelling`, and that the
surviving conclusions be distinguished from those that must be re-proved.

The old predicate is provably the identity on proper-overlap edge lists
(`Section62ReductionVacuityAudit.transitivelyReduced_eq_self_of_proper`), so any
statement of the form "these walk steps survive the reduction" was *vacuous*: its
real content was membership in the unreduced `overlapEdges` graph.  This module
supplies the kernel-checked bridge that lets those results be read in the
corrected model:

* `transitivelyReducedSpelling_eq_self_of_full` — if every edge of a list has the
  maximal proper overlap length `readLen − 1`, the spelling-preserving reduction
  removes none of them.  This covers every witness whose read length is `3` and
  whose threshold is `oMin = readLen − 1 = 2` (the bridging, same-length and
  per-occurrence witnesses): their graph is *already* reduced, so their
  conclusions survive verbatim.
* `stepsSurviveReductionSpelling_of_maximal` — the steps of any spelling walk are
  maximal overlaps, so any spelled walk that lives on `overlapEdges` also lives on
  the spelling-reduced graph.  This is the corrected replacement for the old,
  vacuous `StepsSurviveReduction`.
* `nonspelled_reduction_spelling_eq` — the one genuinely nontrivial case: at
  `oMin = 1` the `Section62NonSpelledFlow` graph has length-`1` edges, and the
  spelling-preserving reduction removes exactly the sixteen that are spelled
  through an *observed* read, leaving precisely the repository's
  longer-overlap reduction `reducedList`.  Hence the non-spellable flow
  countermodel survives, because the single length-`1` edge it uses
  (`AAT → TAA`) has only the *unobserved* intermediate `ATA` as a spelling
  detour.

Nothing here re-proves `fullOverlap_not_reducible`/`fullOverlap_survives`
(already kernel-checked in `Section62SpellingReductionCandidate`), and nothing
here claims Myers/MB09 algorithm equivalence or ML maximality.  This is a
dependency audit for the corrected graph model handed to #261/#262.
-/

namespace AssemblyP1.Section62ReductionDependencyAudit

open Section62Flow Section62SpellingReductionCandidate

set_option maxHeartbeats 4000000

/-! ## A list all of whose edges are maximal proper overlaps is already reduced -/

/-- If every edge of `edges` has the maximal proper overlap length `readLen − 1`,
the spelling-preserving transitive reduction removes none of them.  This is the
general reason the `oMin = readLen − 1` witnesses survive the correction. -/
theorem transitivelyReducedSpelling_eq_self_of_full
    {A W : Type} [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rc : W → W) (readLen oMin : Nat) (verts : List W)
    (edges : List (BdEdge A W))
    (hfull : ∀ e ∈ edges, e.len = readLen - 1) :
    transitivelyReducedSpelling W toList rc readLen oMin verts edges = edges := by
  unfold transitivelyReducedSpelling
  apply List.filter_eq_self.mpr
  intro e he
  have hnr := fullOverlap_not_reducible toList rc readLen oMin verts e (hfull e he)
  cases hb : isReducibleSpellingB W toList rc readLen oMin verts e with
  | false => rfl
  | true => exact absurd hb hnr

/-! ## Steps of a spelling walk survive the corrected reduction -/

/-- Every step of a spelling walk is a maximal proper overlap of length
`readLen − 1` (the shared window of two consecutive length-`readLen` windows of a
circular molecule). -/
theorem spelling_step_len {A W : Type} [DecidableEq W] {n : Nat}
    (rep : W → W) (readLen : Nat) (sp : Spelling A W n) (i : Fin n) :
    (sp.step rep readLen i).len = readLen - 1 := rfl

/-- **Corrected replacement for the vacuous `StepsSurviveReduction`.**  Any
spelled walk whose steps lie on the `overlapEdges` graph also lies on the
spelling-preserving transitive reduction of that graph, because its steps are
maximal overlaps. -/
theorem stepsSurviveReductionSpelling_of_maximal
    {A W : Type} [DecidableEq A] [DecidableEq W] {n : Nat}
    (toList : W → List A) (rep rc : W → W) (readLen oMin : Nat) (verts : List W)
    (sp : Spelling A W n) (edges : List (BdEdge A W))
    (hsteps : StepsInGraph rep readLen sp edges) :
    ∀ i : Fin n, sp.step rep readLen i ∈
      transitivelyReducedSpelling W toList rc readLen oMin verts edges := by
  intro i
  exact fullOverlap_survives toList rc readLen oMin verts edges (sp.step rep readLen i)
    (spelling_step_len rep readLen sp i) (hsteps i)

/-! ## The genuinely nontrivial case: `Section62NonSpelledFlow` at `oMin = 1` -/

open AssemblyP1.Section62NonSpelledFlow

/-- At `oMin = 1` the spelling-preserving reduction of the `AAATT` witness graph
removes exactly the sixteen length-`1` edges that are spelled through an observed
read, leaving precisely the repository's longer-overlap reduction `reducedList`.
This is the kernel-checked content of "the non-spellable countermodel is stable
under the correction". -/
theorem nonspelled_reduction_spelling_eq :
    transitivelyReducedSpelling Strand3 toList3 rc3 readLen oMin readVerts graph1
      = reducedList := by
  decide

/-- Consequently the spelling-preserving reduction and the longer-overlap
reduction agree on this instance (both equal `reducedList`). -/
theorem nonspelled_spelling_eq_longer :
    transitivelyReducedSpelling Strand3 toList3 rc3 readLen oMin readVerts graph1
      = transitivelyReducedLonger Base Strand3 toList3 rc3 readLen readVerts graph1 := by
  rw [nonspelled_reduction_spelling_eq, reducedList_eq]

/-- The non-spellable flow `d*` is a §6.2 admissible flow on the *spelling-reduced*
graph, not merely on the longer-overlap reduction.  This transfers the existing
kernel certificate `star21_feasible62_reduced` across the graph equality. -/
theorem star21_feasible62_spelling_reduced :
    Feasible62 Base Strand3 rep3 readVerts
      (transitivelyReducedSpelling Strand3 toList3 rc3 readLen oMin readVerts graph1)
      starFlow21 noTerm dStar' := by
  rw [nonspelled_reduction_spelling_eq]
  exact star21_feasible62_reduced

/-- The truth-induced flow of `AAATT` is also §6.2 admissible on the
spelling-reduced graph. -/
theorem truth_feasible62_spelling_reduced :
    Feasible62 Base Strand3 rep3 readVerts
      (transitivelyReducedSpelling Strand3 toList3 rc3 readLen oMin readVerts graph1)
      truthFlow noTerm dS' := by
  rw [nonspelled_reduction_spelling_eq]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun _ => ⟨rfl, rfl⟩⟩ <;> decide

/-- The alternative optimal non-spellable flow `d*₃` is §6.2 admissible on the
spelling-reduced graph. -/
theorem star31_feasible62_spelling_reduced :
    Feasible62 Base Strand3 rep3 readVerts
      (transitivelyReducedSpelling Strand3 toList3 rc3 readLen oMin readVerts graph1)
      starFlow31 noTerm dStar3' := by
  rw [nonspelled_reduction_spelling_eq]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun _ => ⟨rfl, rfl⟩⟩ <;> decide

#print axioms transitivelyReducedSpelling_eq_self_of_full
#print axioms stepsSurviveReductionSpelling_of_maximal
#print axioms nonspelled_reduction_spelling_eq
#print axioms nonspelled_spelling_eq_longer
#print axioms star21_feasible62_spelling_reduced
#print axioms truth_feasible62_spelling_reduced
#print axioms star31_feasible62_spelling_reduced

end AssemblyP1.Section62ReductionDependencyAudit
