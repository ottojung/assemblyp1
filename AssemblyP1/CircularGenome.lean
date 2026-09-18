import Mathlib

namespace AssemblyP1

/--
A finite nonempty circular genome over an alphabet `α`.

This is deliberately only a source-stable substrate: it exposes intrinsic genome
length and cyclic indexing, but makes no choice about the admissible ML
competitor universe or the likelihood objective.
-/
structure CircularGenome (α : Type) where
  length : ℕ
  length_pos : 0 < length
  base : Fin length → α

namespace CircularGenome

variable {α : Type}

/-- Read the symbol at an arbitrary natural position, wrapping around the circle. -/
def symbol (g : CircularGenome α) (i : ℕ) : α :=
  g.base ⟨i % g.length, Nat.mod_lt i g.length_pos⟩

/-- The fixed-length circular read beginning at natural start position `start`. -/
def window (g : CircularGenome α) (readLength start : ℕ) : List α :=
  List.ofFn fun i : Fin readLength => g.symbol (start + i)

@[simp] theorem window_length (g : CircularGenome α) (readLength start : ℕ) :
    (g.window readLength start).length = readLength := by
  simp [window]

/--
Exact multiplicity of a read type in a candidate circular genome: the number of
start positions in one traversal whose circular window equals the read.

The traversal domain is represented intrinsically as `Fin g.length`. This is the
same set of starts as naturals below `g.length`, while exposing the canonical
finite cyclic permutations needed for rotation arguments.
-/
def occurrenceCount [DecidableEq α] (g : CircularGenome α) (read : List α) : ℕ :=
  ((Finset.univ : Finset (Fin g.length)).filter fun start : Fin g.length =>
    g.window read.length start.val = read).card

/-- A read type cannot occur at more start positions than the genome has positions. -/
theorem occurrenceCount_le_length [DecidableEq α]
    (g : CircularGenome α) (read : List α) :
    g.occurrenceCount read ≤ g.length := by
  unfold occurrenceCount
  calc
    ((Finset.univ : Finset (Fin g.length)).filter fun start : Fin g.length =>
      g.window read.length start.val = read).card ≤
        (Finset.univ : Finset (Fin g.length)).card := Finset.card_filter_le _ _
    _ = g.length := by simp

/-- A tiny hand-checkable circular genome `A B A`. -/
def aba : CircularGenome Bool where
  length := 3
  length_pos := by decide
  base := ![true, false, true]

/-- In `A B A`, the length-two circular read `A B` occurs exactly once. -/
example : aba.occurrenceCount [true, false] = 1 := by
  native_decide

end CircularGenome

end AssemblyP1
