import Mathlib
import AssemblyP1.Section62SpellingReductionCandidate

/-!
# Global spelling reduction: path-tail algebra

This module lays out the elementary word-concatenation interface used by a
subsequent well-founded expansion proof. It does not yet prove global graph
language equivalence or Observation 7.
-/

namespace AssemblyP1.Section62GlobalSpellingPreservation

open Section62Flow

variable {A W : Type} [DecidableEq W]

/-- The newly spelled letters contributed by a given oriented overlap edge. -/
def edgeTail (toList : W → List A) (e : BdEdge A W) : List A :=
  (toList e.sy).drop e.len

/-- The extension spelled by a sequence of overlap edges. -/
def pathTail (toList : W → List A) (edges : List (BdEdge A W)) : List A :=
  edges.flatMap (edgeTail toList)

theorem pathTail_nil (toList : W → List A) :
    pathTail toList [] = [] := by
  rfl

theorem pathTail_cons (toList : W → List A)
    (e : BdEdge A W) (edges : List (BdEdge A W)) :
    pathTail toList (e :: edges) = edgeTail toList e ++ pathTail toList edges := by
  rfl

theorem pathTail_append (toList : W → List A)
    (left right : List (BdEdge A W)) :
    pathTail toList (left ++ right) =
      pathTail toList left ++ pathTail toList right := by
  induction left with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.cons_append, pathTail_cons, ih, List.append_assoc]

#print axioms pathTail_append

end AssemblyP1.Section62GlobalSpellingPreservation
