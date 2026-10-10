import Mathlib
import AssemblyP1.Section62BidirectedFlow

/-!
# Finite regression for the spelled transitive edge reduction (MB09 §6.2)

This module kernel-checks the two finite regressions that pin down the
*spelled* reading of transitive edge reduction on the §6.2 bidirected overlap
graph, against the literal MB09 §6.2 construction of
`AssemblyP1.Section62Flow`.  It changes no existing definition and preserves
every original theorem; the predicates under test are the additive
`isReducibleSpelledB` (Myers-style spelled reduction) and the existing
`isReducibleB` (literal "two shorter overlaps") and `isReducibleLongerB`
(length-only "longer overlaps").

1. **L3 positive.**  On the observed strands `AAB`, `ABA`, `BAB` (read length
   `3`), the direct overlap edge `AAB → BAB` of length `1` is spelled by the
   two-step path `AAB → ABA → BAB` of overlaps `2` and `2`: both spell `AABAB`.
   The edge is reducible under the spelled reading.
2. **L4 negative.**  On the observed strands `AAAB`, `ABBA`, `BAAA` (read
   length `4`), the direct overlap edge `AAAB → BAAA` of length `1` spells
   `AAABAAA`, while the two-step path `AAAB → ABBA → BAAA` of overlaps `2` and
   `2` spells the *different* string `AAABBAAA`.  The edge is **not** reducible
   under the spelled reading, even though the repository's length-only
   `isReducibleLongerB` removes it.

The regressions are finite computations, discharged by `decide`.  They are
statements about the molecule reading of §6.2 (MB09 §3.1, §4.1: a read is an
unordered reverse-complement strand pair, represented once): `ABA` is the
reverse complement of `BAB`, so it is observed as a molecule even when only
`BAB` is sampled.  The intermediate strands range over `strandsOf rc verts`,
so both orientations of every observed molecule class are tried, exactly as
`overlapEdges` enumerates both orientations of every read.

## Source

* MB09 §6.2: "we remove any overlap that is spelled by two shorter overlaps"
  (<https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/>).
* Myers (2005), *The fragment assembly string graph*, Bioinformatics
  21(Suppl. 2):ii79–ii85
  (<https://www.cs.utoronto.ca/~brudno/csc2427/myers.pdf>): an edge is removed
  when a two-edge path through an intermediate read spells the *same* string.
-/

namespace AssemblyP1.Section62SpelledReduction

/-! ## The two-symbol alphabet and molecule classes -/

/-- Two-symbol alphabet with reverse-complement involution `A ↔ B` (MB09 §3.1). -/
inductive Base where
  | A
  | B
  deriving DecidableEq, Inhabited, Repr

/-- Reverse complement of a symbol. -/
def comp : Base → Base
  | .A => .B
  | .B => .A

/-- A strand is a word over `Base`; its linearization is the identity. -/
abbrev Strand := List Base

/-- Reverse complement of a strand (MB09 §3.1). -/
def rc (w : Strand) : Strand := w.reverse.map comp

/-- Bit encoding of a symbol (`A ↦ 0`, `B ↦ 1`). -/
def bitA : Base → Nat
  | .A => 0
  | .B => 1

/-- Binary code of a strand, most significant symbol first. -/
def code (w : Strand) : Nat := w.foldl (fun a b => a * 2 + bitA b) 0

/-- Molecule-class representative: the minimum-code strand of `{w, rc w}`
(MB09 §4.1 represents each `k`-molecule only once). -/
def rep (w : Strand) : Strand := if code w ≤ code (rc w) then w else rc w

/-- The length-`3` strand `abc`. -/
def m3 (a b c : Base) : Strand := [a, b, c]

/-- The length-`4` strand `abcd`. -/
def m4 (a b c d : Base) : Strand := [a, b, c, d]

/-! ## Regression 1 (L3): the direct edge is spelled by the two-step path -/

/-- The observed strands of the L3 regression: `AAB`, `ABA`, `BAB`. -/
def verts3 : List Strand := [m3 .A .A .B, m3 .A .B .A, m3 .B .A .B]

/-- The read length `L = 3`. -/
def readLen3 : Nat := 3

/-- The direct overlap edge `AAB → BAB` of length `1`. -/
def edgeAAB_BAB : AssemblyP1.Section62Flow.BdEdge Base Strand :=
  AssemblyP1.Section62Flow.bdEdge rep (m3 .A .A .B) (m3 .B .A .B) 1

/-- The direct edge is reducible under the spelled reading: the intermediate
`ABA` has both overlaps (`2` and `2`) strictly longer than `1`, and the two-step
path spells the same `AABAB`. -/
theorem edgeAAB_BAB_reducibleSpelled :
    AssemblyP1.Section62Flow.isReducibleSpelledB Base Strand id rc readLen3 verts3
      edgeAAB_BAB = true := by
  decide

/-- The direct overlap spells `AABAB`. -/
theorem edgeAAB_BAB_direct_spelling :
    (edgeAAB_BAB.sx ++ edgeAAB_BAB.sy.drop edgeAAB_BAB.len) =
      [.A, .A, .B, .A, .B] := by
  decide

/-- The two-step path through `ABA` spells the same `AABAB`. -/
theorem edgeAAB_BAB_composed_spelling :
    (edgeAAB_BAB.sx ++ (m3 .A .B .A).drop 2 ++ edgeAAB_BAB.sy.drop 2) =
      [.A, .A, .B, .A, .B] := by
  decide

/-- The two spellings are equal: the path spells exactly the direct overlap. -/
theorem edgeAAB_BAB_spellings_eq :
    (edgeAAB_BAB.sx ++ edgeAAB_BAB.sy.drop edgeAAB_BAB.len) =
      (edgeAAB_BAB.sx ++ (m3 .A .B .A).drop 2 ++ edgeAAB_BAB.sy.drop 2) := by
  decide

/-- The length-only reading also removes this edge (here the strings coincide,
so the two readings agree). -/
theorem edgeAAB_BAB_reducibleLonger :
    AssemblyP1.Section62Flow.isReducibleLongerB Base Strand id rc readLen3 verts3
      edgeAAB_BAB = true := by
  decide

/-- The literal "two shorter overlaps" reading removes nothing (it is
arithmetically vacuous on every proper edge). -/
theorem edgeAAB_BAB_not_reducibleB :
    AssemblyP1.Section62Flow.isReducibleB Base Strand id rc readLen3 verts3
      edgeAAB_BAB = false := by
  decide

/-! ## Regression 2 (L4): the two-step path spells a different string -/

/-- The observed strands of the L4 regression: `AAAB`, `ABBA`, `BAAA`. -/
def verts4 : List Strand := [m4 .A .A .A .B, m4 .A .B .B .A, m4 .B .A .A .A]

/-- The read length `L = 4`. -/
def readLen4 : Nat := 4

/-- The direct overlap edge `AAAB → BAAA` of length `1`. -/
def edgeAAAB_BAAA : AssemblyP1.Section62Flow.BdEdge Base Strand :=
  AssemblyP1.Section62Flow.bdEdge rep (m4 .A .A .A .B) (m4 .B .A .A .A) 1

/-- The direct edge is **not** reducible under the spelled reading: the only
longer-overlap two-step path, through `ABBA`, spells a different string. -/
theorem edgeAAAB_BAAA_not_reducibleSpelled :
    AssemblyP1.Section62Flow.isReducibleSpelledB Base Strand id rc readLen4 verts4
      edgeAAAB_BAAA = false := by
  decide

/-- The length-only reading removes this edge, because it compares only overlap
lengths and never checks the spelled string. -/
theorem edgeAAAB_BAAA_reducibleLonger :
    AssemblyP1.Section62Flow.isReducibleLongerB Base Strand id rc readLen4 verts4
      edgeAAAB_BAAA = true := by
  decide

/-- The direct overlap spells `AAABAAA`. -/
theorem edgeAAAB_BAAA_direct_spelling :
    (edgeAAAB_BAAA.sx ++ edgeAAAB_BAAA.sy.drop edgeAAAB_BAAA.len) =
      [.A, .A, .A, .B, .A, .A, .A] := by
  decide

/-- The two-step path through `ABBA` spells the different string `AAABBAAA`. -/
theorem edgeAAAB_BAAA_composed_spelling :
    (edgeAAAB_BAAA.sx ++ (m4 .A .B .B .A).drop 2 ++ edgeAAAB_BAAA.sy.drop 2) =
      [.A, .A, .A, .B, .B, .A, .A, .A] := by
  decide

/-- The two spellings differ, which is exactly why the spelled reading retains
the edge. -/
theorem edgeAAAB_BAAA_spellings_ne :
    (edgeAAAB_BAAA.sx ++ edgeAAAB_BAAA.sy.drop edgeAAAB_BAAA.len) ≠
      (edgeAAAB_BAAA.sx ++ (m4 .A .B .B .A).drop 2 ++ edgeAAAB_BAAA.sy.drop 2) := by
  decide

/-- The literal "two shorter overlaps" reading removes nothing here either. -/
theorem edgeAAAB_BAAA_not_reducibleB :
    AssemblyP1.Section62Flow.isReducibleB Base Strand id rc readLen4 verts4
      edgeAAAB_BAAA = false := by
  decide

/-! ## Positive L4 control: the spelled reading is not vacuous at `L = 4` -/

/-- Adding the intermediate strand `ABAA` makes the same direct edge reducible:
the path `AAAB → ABAA → BAAA` of overlaps `2` and `3` spells the same
`AAABAAA`.  This shows the negative answer above is caused by the string
mismatch through `ABBA`, not by a defect of the predicate. -/
def verts4pos : List Strand := [m4 .A .A .A .B, m4 .A .B .A .A, m4 .B .A .A .A]

/-- With `ABAA` observed, the direct edge is reducible under the spelled
reading. -/
theorem edgeAAAB_BAAA_reducibleSpelled_with_ABAA :
    AssemblyP1.Section62Flow.isReducibleSpelledB Base Strand id rc readLen4 verts4pos
      edgeAAAB_BAAA = true := by
  decide

/-! ## Kernel and axiom audit -/

#print axioms edgeAAB_BAB_reducibleSpelled
#print axioms edgeAAB_BAB_direct_spelling
#print axioms edgeAAB_BAB_composed_spelling
#print axioms edgeAAB_BAB_spellings_eq
#print axioms edgeAAB_BAB_reducibleLonger
#print axioms edgeAAB_BAB_not_reducibleB
#print axioms edgeAAAB_BAAA_not_reducibleSpelled
#print axioms edgeAAAB_BAAA_reducibleLonger
#print axioms edgeAAAB_BAAA_direct_spelling
#print axioms edgeAAAB_BAAA_composed_spelling
#print axioms edgeAAAB_BAAA_spellings_ne
#print axioms edgeAAAB_BAAA_not_reducibleB
#print axioms edgeAAAB_BAAA_reducibleSpelled_with_ABAA

end AssemblyP1.Section62SpelledReduction
