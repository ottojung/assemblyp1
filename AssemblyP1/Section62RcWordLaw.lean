import AssemblyP1.Section62ObservedMoleculeCount
import AssemblyP1.Section62BridgingCounterexample

/-!
# The word-level reverse-complement law for the implemented witness (#284)

`Section62ObservedMoleculeCount` proves the observed reverse-complement
molecule-class occurrence equality, but its module docstring is explicit that
the *word-level* law — that the implemented strand involution `rc3` really acts
on the spelled word as the DNA reverse complement — is an external model
interpretation and is **not proved there**.

This module closes that gap for the concrete implemented `Strand3` witness of
`Section62BridgingCounterexample`:

* `rcWord` is the DNA reverse complement on `List Base`;
* `toList3_rc3` shows the implemented `rc3` maps the spelled word to exactly its
  word-level reverse complement (definitional for `toList3 = id`);
* `rc3_involutive` shows `rc3` is an involution, the hypothesis consumed by
  `Section62ObservedMoleculeCount.classWordCount_rc_invariant` and
  `rc_mem_strands`;
* `classWordCount_eq_rc_class_count` rewrites the `classWordCount` palindrome
  test into the literal word-level fixed-point test `rcWord w = w`, so the
  class count is a count of the actual reverse-complement molecule class, with
  palindromes counted once.

The abstract `observation7_observed_rc_class_count` then has a kernel-checked
word-level interpretation on this witness. This does not prove the law for an
arbitrary abstract `rc`, nor does it settle the full unobserved §6.1 universe.
-/

namespace AssemblyP1.Section62RcWordLaw

open AssemblyP1.Section62BridgingCounterexample
open AssemblyP1.Section62ObservedMoleculeCount
open AssemblyP1.Section62CircularWindowAdapter

/-- The word-level DNA reverse complement on the two-symbol alphabet. -/
def rcWord (w : List Base) : List Base := w.reverse.map comp

/-- `comp` is an involution on the two-symbol alphabet. -/
theorem comp_involutive : Function.Involutive comp := by
  intro x
  cases x <;> rfl

/-- The implemented strand reverse complement `rc3` acts on the spelled word as
the word-level reverse complement. Definitional because `toList3 = id`. -/
theorem toList3_rc3 (w : Strand3) : toList3 (rc3 w) = rcWord (toList3 w) := rfl

/-- `rc3` is an involution on strands. -/
theorem rc3_involutive : Function.Involutive rc3 := by
  intro w
  unfold rc3
  rw [← List.map_reverse, List.reverse_reverse, List.map_map]
  have hcomp : comp ∘ comp = id := by
    funext x
    cases x <;> rfl
  rw [hcomp, List.map_id]

/-- The `classWordCount` palindrome test coincides with the word-level
reverse-complement fixed-point test. -/
theorem classWordCount_toList3_rc3 (m : Strand3) (reads : List (List Base)) :
    classWordCount toList3 rc3 m reads =
      (if rcWord (toList3 m) = toList3 m then wordCount (toList3 m) reads
       else wordCount (toList3 m) reads + wordCount (rcWord (toList3 m)) reads) := by
  unfold classWordCount
  rw [toList3_rc3]

/-- `classWordCount` on the implemented witness is exactly the reverse-complement
molecule-class occurrence count of the word `toList3 m`, with a palindromic word
counted once. -/
theorem classWordCount_eq_rc_class_count (m : Strand3) (reads : List (List Base)) :
    classWordCount toList3 rc3 m reads =
      wordCount (toList3 m) reads +
        (if rcWord (toList3 m) = toList3 m then 0
         else wordCount (rcWord (toList3 m)) reads) := by
  rw [classWordCount_toList3_rc3]
  split_ifs <;> omega

/-- Regression: `AAT` and `ATT` are a reverse-complement pair under the
implemented `rc3`. -/
example : rc3 (m3 .A .A .T) = m3 .A .T .T := by
  decide

/-- Regression: a non-palindromic strand counts both orientations of its class
(`AAT` twice and `ATT` once gives class count `3`). -/
example : classWordCount toList3 rc3 (m3 .A .A .T)
    [[.A, .A, .T], [.A, .T, .T], [.A, .A, .T]] = 3 := by
  decide

/-- Regression: on `{A,T}` the length-2 word `AT` is its own reverse
complement, so it is a palindromic molecule class counted once. -/
example : rcWord ([Base.A, Base.T] : List Base) = [Base.A, Base.T] := by
  decide

#print axioms comp_involutive
#print axioms toList3_rc3
#print axioms rc3_involutive
#print axioms classWordCount_toList3_rc3
#print axioms classWordCount_eq_rc_class_count

end AssemblyP1.Section62RcWordLaw
