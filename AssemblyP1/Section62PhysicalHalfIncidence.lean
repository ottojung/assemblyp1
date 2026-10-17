import AssemblyP1.Section62BidirectedFlow

/-!
A bounded repair audit for #261: physical signed half-edge incidences.

The two endpoints of a bidirected overlap must be counted separately,
including for self-loops.  The oriented ordered edge and its opposite
reverse-complement representation interchange endpoints, but preserve
their physical molecule classes and their incidence signs.

This does not prove the quotient graph is MB09's source graph, nor
identify its feasible flows with single circular genomes.
-/

namespace AssemblyP1.Section62PhysicalHalfIncidence

-- The single class-flip identity does not need edge equality decisions.
set_option linter.unusedSectionVars false

open AssemblyP1.Section62Flow


abbrev Tagged (W : Type) := W × Bool

def cls {W : Type} (s : Tagged W) : Tagged W := (s.1, false)

def flip {W : Type} (s : Tagged W) : Tagged W := (s.1, !s.2)

variable {A W : Type} [DecidableEq W]

/-- One *positive* half-edge at each endpoint with sign +1, counted
separately even if the endpoints belong to the same read class. -/
def posHalf (e : BdEdge A (Tagged W)) (v : Tagged W) : ℕ :=
  (if cls e.sx = v ∧ e.sgnX = 1 then 1 else 0) +
  (if cls e.sy = v ∧ e.sgnY = 1 then 1 else 0)

/-- One *negative* half-edge at each endpoint with sign -1. -/
def negHalf (e : BdEdge A (Tagged W)) (v : Tagged W) : ℕ :=
  (if cls e.sx = v ∧ e.sgnX = -1 then 1 else 0) +
  (if cls e.sy = v ∧ e.sgnY = -1 then 1 else 0)

/-- Reversing an oriented representation changes the traversal order,
not the physical bidirected edge's signed incidences. -/
def reverseEdge (e : BdEdge A (Tagged W)) : BdEdge A (Tagged W) :=
  { sx := flip e.sy, sy := flip e.sx, len := e.len,
    sgnX := e.sgnY, sgnY := e.sgnX }

/-- Reverse-complement orientation does not change the molecule class. -/
theorem class_flip (s : Tagged W) : cls (flip s) = cls s := by
  cases s with
  | mk w b => cases b <;> rfl

/-- Positive half-incidences are independent of the oriented
representation of a physical bidirected edge. -/
theorem posHalf_reverse (e : BdEdge A (Tagged W)) (v : Tagged W) :
    posHalf (reverseEdge e) v = posHalf e v := by
  simp only [posHalf, reverseEdge, class_flip]
  ac_rfl

theorem negHalf_reverse (e : BdEdge A (Tagged W)) (v : Tagged W) :
    negHalf (reverseEdge e) v = negHalf e v := by
  simp only [negHalf, reverseEdge, class_flip]
  ac_rfl

/-- The two representations form an involution on signed edge values. -/
theorem reverseEdge_involutive :
    Function.Involutive (reverseEdge (A := A) (W := W)) := by
  intro e
  cases e
  simp [reverseEdge, flip, Bool.not_not]

/-- Legacy departure-based edge counting is NOT invariant under reversal. -/
def departureCount (e : BdEdge A (Tagged W)) (v : Tagged W) : ℕ :=
  if cls e.sx = v then 1 else 0

def sampleEdge : BdEdge Bool (Tagged Bool) :=
  {sx := (false,false), sy := (true,false), len := 1,
    sgnX := 1, sgnY := -1}

theorem sample_departure_failure :
    departureCount sampleEdge (false,false) = 1 ∧
    departureCount (reverseEdge sampleEdge) (false,false) = 0 := by
  decide

/-- A mixed-sign self-loop contributes one of EACH, not zero visits. -/
def mixedLoop : BdEdge Bool (Tagged Bool) :=
  {sx := (false,false), sy := (false,false), len := 1,
    sgnX := 1, sgnY := -1}

theorem mixedLoop_count :
    posHalf mixedLoop (false,false) = 1 ∧
    negHalf mixedLoop (false,false) = 1 := by
  decide

/-- A ++ self-loop contributes TWO positive half-edge occurrences. -/
def positiveLoop : BdEdge Bool (Tagged Bool) :=
  {sx := (false,false), sy := (false,true), len := 1,
    sgnX := 1, sgnY := 1}

theorem positiveLoop_count :
    posHalf positiveLoop (false,false) = 2 := by decide

end AssemblyP1.Section62PhysicalHalfIncidence
