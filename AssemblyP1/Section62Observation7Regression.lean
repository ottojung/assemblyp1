import AssemblyP1.Section62GlobalSkippedBridge
import AssemblyP1.Section62SignedAdapterRegression

/-!
Non-vacuity regression for the full #284 Observation 7 proof. The previously
checked signed cycles (including readLen 5 > genome length 3) are shown to
survive the actual spelling-preserving reduction, not just the complete graph.
No reduction/signed-walk assumptions are left as abstract hypotheses here.
-/

namespace AssemblyP1.Section62Observation7Regression

open AssemblyP1.Section62GlobalSkippedBridge
open AssemblyP1.Section62SignedAdapterRegression
open AssemblyP1.Section62CircularWindowAdapter
open AssemblyP1.Section62GlobalSpellingPreservation
open Section62Flow Section62SpellingReductionCandidate

theorem cycle_reduced_edges :
    ∀ e ∈ cycleEdges,
      e ∈ transitivelyReducedSpelling (List Nat) id id 3 1 cycleVerts
        (overlapEdges Nat (List Nat) id id id 3 1 cycleVerts) := by
  intro e he
  simp only [cycleEdges, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · decide
  · decide
  · decide
  · decide

theorem cycle5_reduced_edges :
    ∀ e ∈ cycle5Edges,
      e ∈ transitivelyReducedSpelling (List Nat) id id 5 1 cycle5Verts
        (overlapEdges Nat (List Nat) id id id 5 1 cycle5Verts) := by
  intro e he
  simp only [cycle5Edges, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · decide
  · decide
  · decide

/-- The full theorem specializes to a nontrivial G=4, L=3 signed circuit. -/
theorem cycle_observation7 :
    wordCount abc ((List.range cycD.length).map (window cycD 3)) =
      wordCount abc (cycleEdges.map (fun e => id e.sx)) := by
  simpa [cycD, cycX, cycPathTail] using
    (observation7_reduced_signed_circuit_range_count id id id 3 1
      cycleVerts 0 cycle_hLen cycleEdges abc (by rfl)
      cycle_hsp cycle_reduced_edges abc (by decide))

/-- The full theorem works for a shorter circular genome G=3 than L=5,
where each read wraps around the seam more than once. -/
theorem cycle5_observation7 :
    wordCount e5ab ((List.range cyc5D.length).map (window cyc5D 5)) =
      wordCount e5ab (cycle5Edges.map (fun e => id e.sx)) := by
  simpa [cyc5D, cyc5X, cyc5PathTail] using
    (observation7_reduced_signed_circuit_range_count id id id 5 1
      cycle5Verts 0 cycle5_hLen cycle5Edges e5ab (by rfl)
      cycle5_hsp cycle5_reduced_edges e5ab (by decide))

example : wordCount e5ab ((List.range cyc5D.length).map (window cyc5D 5)) = 1 := by
  decide
example : wordCount abc ((List.range cycD.length).map (window cycD 3)) = 1 := by
  decide


#print axioms cycle_reduced_edges
#print axioms cycle5_reduced_edges
#print axioms cycle_observation7
#print axioms cycle5_observation7

end AssemblyP1.Section62Observation7Regression
