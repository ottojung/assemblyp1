import Mathlib
import AssemblyP1.Section62BidirectedFlow
import AssemblyP1.Section62SpellingReductionCandidate
import AssemblyP1.Section62CircularStarts
import AssemblyP1.Section62CircularWindowAdapter

/-!
# Measured RC-class witnesses for issue #284 (source-fidelity increment)

This module is a *measured* increment, not a re-proof of any merged theorem.
It kernel-checks two concrete witnesses about the reverse-complement (RC)
molecule-class indexing of MB09 §6.1–§6.2, against the *implemented* objects:

1. **The unobserved-class extension of Observation 7 is false.**  The merged
   `Section62CircularWindowAdapter.observation7_window_count` proves, for a
   coherent circular spelling of a signed walk, that for every *observed*
   strand `m` the number of circular `readLen`-windows of the genome `D`
   spelling `toList m` equals the number of walk vertices spelling `toList m`.
   The natural RC-collapsed extension — for every oriented word `u` (observed
   or not), the molecule count of the class `[u]` in `D` (windows spelling
   `u`, plus windows spelling `rc u` for non-palindromic `u`; palindromic
   classes counted once) equals the walk's visit count to the class `[u]` —
   **fails**: an unobserved class can have positive molecule count in `D`
   while no walk can visit it (it is not a graph vertex).  The smallest
   witness is kernel-checked below (`rcOccurrenceExtension_false`): a walk of
   two proper `1`-overlaps at read length `3` over the two-symbol alphabet,
   whose genome `D = [T,T,F,T]` has the interior window `u = [T,F,T]`, an
   unobserved word, so `moleculeCount [u] = 1` but `classVisits [u] = 0`.

   The extension does hold on the *observed* classes of the same instance
   (`rcOccurrenceExtension_observed_holds`), and the scoped hypothesis that
   repairs the full-universe statement is exactly the §6.2 support
   constraint: every window of `D` spells an observed strand (equivalently,
   the candidate's molecule spectrum is supported on the observed classes).
   Under that hypothesis the extension is the two-line additive consequence
   of `observation7_window_count` at `m` and `rc m`, with the palindrome
   case (`m = rc m`) counted once.

2. **The implemented graph doubles palindrome strands.**  `strandsOf rc verts`
   (`Section62BidirectedFlow.lean`) lists the class representative *and* its
   reverse complement; for a palindromic class these coincide, so the
   representative appears twice and every edge incident to the class is
   generated with doubled multiplicity.  For the DNA length-`4` palindrome
   `p = [A,T,A,T]` (`rc p = p`) the complete `overlapEdges` graph at
   `oMin = 2` contains the signed self-loop edge `bdEdge rep p p 2` with
   multiplicity `4`, where the MB09 §3.3 bidirected graph has one such signed
   edge at the class vertex (`palindrome_self_loop_multiplicity`).  The
   shipped regression toy (`Section62SpellingReductionCandidate.lean`) uses a
   fixed-point-free six-strand alphabet with no palindromes, so this
   divergence is unexercised by every existing witness.

No `sorry`, `admit`, `axiom`, or `native_decide` is used; every proof is
`decide`/`rfl` on concrete finite data, so the axiom footprint is at most
`[propext, Classical.choice, Quot.sound]` (`#print axioms` below).
-/

namespace AssemblyP1.Section62RCClassIndexWitness

set_option maxHeartbeats 4000000

open Section62Flow Section62SpellingReductionCandidate Section62CircularStarts
open Section62CircularWindowAdapter

/-! ## The unobserved-class witness (two-symbol alphabet, read length 3)

The alphabet is `Bool` (`true = A`, `false = T`); the reverse complement is
`rc u = (reverse u).map not`.  The four strands are

* strand `0`: `sx  = [T,T,F]`,
* strand `1`: `m   = [F,T,T]` (genuine `1`-overlap `sx → m`),
* strand `2`: `rc sx = [T,F,F]`,
* strand `3`: `rc m  = [F,F,T]`.

The observed molecule classes are `[sx]` and `[m]` (`verts = [0,1]`).  The
walk is the two-edge signed path `sx → m → rc sx` of proper `1`-overlaps;
its extensions are `[2,2]`, so the coherent genome is `D = [T,T,F,T]`, whose
four circular length-`3` windows are `[T,T,F] = sx`, `[T,F,T]` (unobserved),
`[F,T,T] = m`, `[T,T,T]` (unobserved). -/

/-- The strand linearization of the toy. -/
def toyToList : Fin 4 → List Bool
  | 0 => [true, true, false]
  | 1 => [false, true, true]
  | 2 => [true, false, false]
  | 3 => [false, false, true]

/-- The strand-level reverse complement: strand `0 ↔ 2`, `1 ↔ 3`. -/
def toyRc : Fin 4 → Fin 4
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | 3 => 1

/-- The molecule-class representative: classes `[0] = {0,2}`, `[1] = {1,3}`. -/
def toyRep : Fin 4 → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 1

/-- The observed molecule classes. -/
def toyVerts : List (Fin 4) := [0, 1]

/-- The first walk edge: the proper `1`-overlap `sx → m`. -/
def toyEdge1 : BdEdge Bool (Fin 4) := bdEdge toyRep (0 : Fin 4) (1 : Fin 4) 1

/-- The second walk edge: the proper `1`-overlap `m → rc sx`. -/
def toyEdge2 : BdEdge Bool (Fin 4) := bdEdge toyRep (1 : Fin 4) (2 : Fin 4) 1

/-- The walk: the two-edge signed path `sx → m → rc sx` of proper `1`-overlaps. -/
def toyWalk : List (BdEdge Bool (Fin 4)) := [toyEdge1, toyEdge2]

/-- The coherent circular genome spelled by the walk: extensions `[2,2]`, so
`D` has length `4`. -/
def toyD : List Bool := [true, true, false, true]

/-- The circular windows of the genome `D` at every start. -/
def toyWindows : List (List Bool) :=
  (List.range toyD.length).map (window toyD 3)

/-- The reverse complement of a word: reverse, then complement every symbol. -/
def rcWord (comp : Bool → Bool) (u : List Bool) : List Bool :=
  u.reverse.map comp

/-- The RC-collapsed molecule count of the class of `u` in a genome whose
windows are `windows`: the number of windows spelling `u`, plus the number
spelling `rc u` when `u` is not a reverse-complement palindrome (palindromic
classes are counted once). -/
def moleculeCount (comp : Bool → Bool) (windows : List (List Bool)) (u : List Bool) : Nat :=
  wordCount u windows +
    (if decide (u = rcWord comp u) then 0 else wordCount (rcWord comp u) windows)

/-- The walk's visit count to the class of `u`: the number of walk edges
whose departure strand spells `u` or `rc u`. -/
def classVisits (walk : List (BdEdge Bool (Fin 4))) (u rcU : List Bool) : Nat :=
  (walk.filter (fun e => decide (toyToList e.sx = u ∨ toyToList e.sx = rcU))).length

/-- The reverse-complement involution on strands is an involution. -/
theorem toyRc_involutive : Function.Involutive toyRc := by
  intro w
  fin_cases w <;> rfl

/-- Strands and representatives respect the RC pairing. -/
theorem toyRep_rc : ∀ w : Fin 4, toyRep (toyRc w) = toyRep w := by
  intro w
  fin_cases w <;> rfl

/-- The complete bidirected overlap graph at read length `3`, `oMin = 1`, on
the observed classes. -/
def toyGraph : List (BdEdge Bool (Fin 4)) :=
  overlapEdges Bool (Fin 4) toyToList toyRep toyRc 3 1 toyVerts

/-- Both walk edges are edges of the complete `overlapEdges` graph. -/
theorem toyWalk_edges_in_graph :
    toyEdge1 ∈ toyGraph ∧ toyEdge2 ∈ toyGraph := by
  decide

/-- The walk spells the genome `D` coherently: the three `CircularSpelling`
hypotheses of `Section62CircularWindowAdapter` hold (extensions sum to
`D.length`, anchors are the visited strands, and no interior window spells an
observed strand). -/
theorem toyCircularSpelling :
    CircularSpelling toyToList toyRc 3 1 toyVerts toyWalk toyD := by
  refine ⟨by decide, by decide, by decide⟩

/-- The walk's visit sequence (departure strands) is exactly `[sx, m]`. -/
theorem toyWalk_departures : toyWalk.map (fun e => toyToList e.sx) =
    [[true, true, false], [false, true, true]] := by
  decide

/-- **The unobserved-class counterexample to the full-universe RC extension of
Observation 7.**  The word `u = [T,F,T]` is the interior window of `D` at
start `1`; it is not an observed strand, its class has molecule count `1` in
`D`, and the walk visits its class `0` times. -/
theorem unobserved_witness :
    (∀ m ∈ strandsOf toyRc toyVerts, [true, false, true] ≠ toyToList m) ∧
      [true, false, true] ∈ (interiors 0 (extensions 3 toyWalk)).map (window toyD 3) ∧
      wordCount [true, false, true] toyWindows = 1 ∧
      wordCount (rcWord not [true, false, true]) toyWindows = 0 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **The measured verdict: the RC-collapsed occurrence equality does NOT
extend to the unobserved universe.**  Formally, the conjecture

    ∀ u : List Bool, u.length = 3 →
      moleculeCount not toyWindows u = classVisits toyWalk u (rcWord not u)

is false; the refuting witness is `u = [T,F,T]` with molecule count `1` and
visit count `0`.  (The same instance satisfies the equality on both observed
classes — `rcOccurrenceExtension_observed_holds` — so the failure is
specifically the unobserved universe, not the reduction.) -/
theorem rcOccurrenceExtension_false :
    ¬ ∀ u : List Bool, u.length = 3 →
      moleculeCount not toyWindows u = classVisits toyWalk u (rcWord not u) := by
  intro h
  have hu := h [true, false, true] (by decide)
  have hcnt : moleculeCount not toyWindows [true, false, true] = 1 := by decide
  have hvis : classVisits toyWalk [true, false, true] (rcWord not [true, false, true]) = 0 := by
    decide
  omega

/-- **Positive control: on the observed classes of the same instance the
RC-collapsed equality holds.**  For each observed class `[sx]` and `[m]` the
molecule count in `D` (palindromes counted once) equals the walk's class
visit count. -/
theorem rcOccurrenceExtension_observed_holds :
    moleculeCount not toyWindows (toyToList 0) =
        classVisits toyWalk (toyToList 0) (rcWord not (toyToList 0)) ∧
      moleculeCount not toyWindows (toyToList 1) =
        classVisits toyWalk (toyToList 1) (rcWord not (toyToList 1)) := by
  decide

#print axioms rcOccurrenceExtension_false
#print axioms rcOccurrenceExtension_observed_holds
#print axioms toyCircularSpelling

/-! ## The palindrome-strand doubling witness (DNA alphabet, read length 4)

`p = [A,T,A,T]` is a reverse-complement palindrome (`rc p = p`).  Its class
has a single strand, but `strandsOf rc verts` lists the representative and
its reverse complement — the same strand twice — so the complete overlap
graph generates the signed self-loop edge with multiplicity `4` (two copies of
the strand as departure times two as arrival), where the MB09 §3.3 bidirected
graph carries exactly one signed edge at the class vertex. -/

/-- The DNA four-base alphabet. -/
inductive DnaBase where
  | A
  | C
  | G
  | T
  deriving DecidableEq, Inhabited, Repr

/-- The DNA base complement: `A ↔ T`, `C ↔ G`. -/
def compDna : DnaBase → DnaBase
  | .A => .T
  | .T => .A
  | .C => .G
  | .G => .C

/-- The length-`4` reverse-complement palindrome `p = [A,T,A,T]`. -/
def palStrand : List DnaBase := [.A, .T, .A, .T]

/-- `p` is a reverse-complement palindrome. -/
theorem palStrand_rc : palStrand.reverse.map compDna = palStrand := by
  decide

/-- The single-strand toy: the only strand is `p`, its own reverse complement. -/
def palToList : Fin 1 → List DnaBase := fun _ => palStrand

def palRep : Fin 1 → Fin 1 := fun _ => 0

def palRc : Fin 1 → Fin 1 := fun _ => 0

/-- The palindromic class contributes its (unique) strand **twice** to the
strand enumeration `strandsOf rc verts`. -/
theorem pal_strandsOf_duplicate : strandsOf palRc [0] = [0, 0] := by
  rfl

/-- The complete bidirected overlap graph at read length `4`, `oMin = 2`, on
the single palindromic class. -/
def palGraph : List (BdEdge DnaBase (Fin 1)) :=
  overlapEdges DnaBase (Fin 1) palToList palRep palRc 4 2 [0]

/-- The signed self-loop edge of the palindromic class vertex. -/
def palLoop : BdEdge DnaBase (Fin 1) := bdEdge palRep (0 : Fin 1) (0 : Fin 1) 2

/-- **Palindrome edge-multiplicity divergence.**  The signed self-loop edge
`bdEdge rep p p 2` occurs with multiplicity `4` in the implemented complete
`overlapEdges` graph (departure strand `p` enumerated twice times arrival
strand `p` enumerated twice), where the MB09 §3.3 bidirected graph has exactly
one signed edge at the class vertex. -/
theorem palindrome_self_loop_multiplicity :
    (palGraph.filter (fun e => decide (e = palLoop))).length = 4 := by
  decide

#print axioms pal_strandsOf_duplicate
#print axioms palindrome_self_loop_multiplicity

end AssemblyP1.Section62RCClassIndexWitness
