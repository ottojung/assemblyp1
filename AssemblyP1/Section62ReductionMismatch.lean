import AssemblyP1.Section62SpellingReductionCandidate

/-!
# Separation between longer-overlap-only and spelling-preserving reductions

An equal-length error-free oriented-read example. The longer-overlap-only
predicate removes an edge which cannot be replaced by the observed detour with
the same spelling. This does not claim Myers's original algorithm does so.
-/

namespace AssemblyP1.Section62ReductionMismatch

open Section62Flow Section62SpellingReductionCandidate

private def readWord : Fin 3 → List Nat
  | 0 => [0, 0, 0, 1] -- AAAT
  | 1 => [1, 0, 0, 0] -- TAAA
  | _ => [0, 1, 1, 0] -- ATTA

private def readVerts : List (Fin 3) := [0, 1, 2]
private def identityRc : Fin 3 → Fin 3 := id
private def identityRep : Fin 3 → Fin 3 := id

private def graph : List (BdEdge Nat (Fin 3)) :=
  overlapEdges Nat (Fin 3) readWord identityRep identityRc 4 1 readVerts

private def direct : BdEdge Nat (Fin 3) :=
  bdEdge identityRep (0 : Fin 3) (1 : Fin 3) 1

theorem direct_in_overlap_graph : direct ∈ graph := by decide

theorem is_reducible_longer_without_spelling :
    isReducibleLongerB Nat (Fin 3) readWord identityRc 4 readVerts direct = true := by
  decide

theorem longer_reduction_deletes_direct :
    direct ∉ transitivelyReducedLonger Nat (Fin 3)
      readWord identityRc 4 readVerts graph := by decide

theorem not_reducible_by_equal_spelling :
    isReducibleSpellingB (Fin 3) readWord identityRc 4 1
      readVerts direct = false := by decide

theorem direct_survives_spelling_reduction :
    direct ∈ transitivelyReducedSpelling (Fin 3)
      readWord identityRc 4 1 readVerts graph := by decide

theorem direct_spelling :
    spellDirect (readWord 0) (readWord 1) 1 =
      [0, 0, 0, 1, 0, 0, 0] := by decide

theorem detour_spelling :
    spellPath (readWord 0) (readWord 2) (readWord 1) 2 2 =
      [0, 0, 0, 1, 1, 0, 0, 0] := by decide

theorem detour_spelling_differs :
    spellPath (readWord 0) (readWord 2) (readWord 1) 2 2 ≠
      spellDirect (readWord 0) (readWord 1) 1 := by decide

theorem internal_windows_not_observed :
    (∀ w ∈ readVerts,
      readWord w ≠ [0, 0, 1, 0] ∧ readWord w ≠ [0, 1, 0, 0]) := by decide

theorem longer_is_not_spelling_preserving :
    direct ∈ graph ∧
      direct ∉ transitivelyReducedLonger Nat (Fin 3)
        readWord identityRc 4 readVerts graph ∧
      direct ∈ transitivelyReducedSpelling (Fin 3)
        readWord identityRc 4 1 readVerts graph ∧
      spellPath (readWord 0) (readWord 2) (readWord 1) 2 2 ≠
        spellDirect (readWord 0) (readWord 1) 1 :=
  ⟨direct_in_overlap_graph, longer_reduction_deletes_direct,
    direct_survives_spelling_reduction, detour_spelling_differs⟩

#print axioms longer_is_not_spelling_preserving

end AssemblyP1.Section62ReductionMismatch
