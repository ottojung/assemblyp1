import AssemblyP1.Section62BridgingCounterexample
import AssemblyP1.Section62SpellingReductionCandidate

/-!
# Palindromic reverse-complement reads: duplicate graph-edge audit

The legacy source object `strandsOf rc verts = verts ++ verts.map rc`
is a LIST. For a reverse-complement palindrome `rc w = w`, the
enumeration repeats exactly the same strand. Consequently the constructed
`overlapEdges` list can contain identical `BdEdge` values several times,
even if `verts` contains the molecule class exactly once.

**IMPORTANT:** `BdFlow A W := BdEdge A W → ℕ` assigns one flow value to
each EDGE VALUE, not each list position. But `throughput` and `balCore`
FOLD OVER THE EDGE LIST. Therefore an identical edge repeated four times
contributes four copies of the SAME edge's assigned flow. This is a
real representational difference in the implemented feasibility domain.

This audit gives a concrete non-vacuous example in the repository's true
two-base A/T alphabet (length four circular read ATAT, overlap length two),
and introduces a NON-MUTATING canonical-edge-list variant that removes only
literal duplicate edges. Its edge membership is exactly the same as that of
the original, but `throughput`/feasibility for one shared `BdFlow`
is observably different.

It does NOT assert which multiplicity convention Myers/MB09 intends in
palindromic overlap graphs. Any proof identifying the duplicate-list
implementation with a physical source flow should explicitly settle the
intended edge-multiplicity convention first.
-/

namespace AssemblyP1.Section62PalindromeEdgeMultiplicityAudit

open AssemblyP1.Section62BridgingCounterexample
open Section62Flow
open AssemblyP1.Section62SpellingReductionCandidate

/-- The DNA reverse complement on arbitrary A/T words. -/
def rcWord (w : List Base) : List Base := w.reverse.map comp

/-- This length-four read is equal to its own reverse complement. -/
def pal4 : List Base := [.A, .T, .A, .T]

theorem pal4_is_rc_palindrome : rcWord pal4 = pal4 := by decide

/-- Exactly one observed molecule class gives TWO identical oriented strands
under the original `strandsOf` list model. -/
theorem palindrome_strands_duplicate :
    strandsOf rcWord [pal4] = [pal4,pal4] := by decide

/-- Its proper overlap of length 2 spells a legitimate ATAT -> ATAT
two-letter extension. -/
theorem palindrome_genuine_self_overlap :
    sufOf pal4 2 = preOf pal4 2 := by decide

def originalGraph : List (BdEdge Base (List Base)) :=
    overlapEdges Base (List Base) id id rcWord 4 2 [pal4]

def palindromicEdge : BdEdge Base (List Base) :=
  bdEdge id pal4 pal4 2

/-- The exact same overlap is enumerated FOUR TIMES, because both
departures and arrivals enumerate the palindromic strand twice. -/
theorem originalGraph_eq_quadruple :
    originalGraph = [palindromicEdge,palindromicEdge,
                     palindromicEdge,palindromicEdge] := by decide

theorem originalGraph_length : originalGraph.length = 4 := by
  rw [originalGraph_eq_quadruple]
  rfl

/-- A literal-value set representation has just ONE such edge. -/
def dedupGraph : List (BdEdge Base (List Base)) := originalGraph.eraseDups

theorem dedupGraph_singleton : dedupGraph = [palindromicEdge] := by decide

theorem dedupGraph_length : dedupGraph.length = 1 := by
  rw [dedupGraph_singleton]
  rfl

/-- General-purpose non-mutating canonically deduplicated overlap graph.
No existing historical `overlapEdges` or flow definition is changed. -/
def overlapEdgesDedup (A W : Type)
    [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rep rc : W → W)
    (L oMin : Nat) (verts : List W) : List (BdEdge A W) :=
  (overlapEdges A W toList rep rc L oMin verts).eraseDups

/-- Deduplication preserves EXACTLY which oriented overlap edge types exist. -/
theorem mem_overlapEdgesDedup_iff
    {A W : Type} [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rep rc : W → W)
    (L oMin : Nat) (verts : List W) (e : BdEdge A W) :
    e ∈ overlapEdgesDedup A W toList rep rc L oMin verts ↔
      e ∈ overlapEdges A W toList rep rc L oMin verts := by
  simp [overlapEdgesDedup]

/-- The same semantic edge set has different list lengths. Since `BdFlow`
indexes by edge VALUE and `throughput` folds the list, these repetitions
multiply the contributions of one shared edge flow. -/
theorem palindrome_index_dimensions_differ :
    originalGraph.length ≠ dedupGraph.length := by
  rw [originalGraph_length, dedupGraph_length]
  decide


/-- A unit flow on the ONE distinct edge type. The flow is keyed by the
`BdEdge` VALUE, not any list index. -/
def unitPalFlow : BdFlow Base (List Base) :=
  fun e => if e = palindromicEdge then 1 else 0

/-- The one-read candidate spectrum (one occurrence of the palindrome). -/
def singletonSpectrum : List Base → ℕ :=
  fun w => if w = pal4 then 1 else 0

/-- The duplicated graph counts the SAME edge-value flow four times. -/
theorem duplicate_graph_throughput_four :
    throughput Base (List Base) id unitPalFlow originalGraph pal4 = 4 := by
  decide

/-- The canonical edge-list graph counts this flow once. -/
theorem canonical_graph_throughput_one :
    throughput Base (List Base) id unitPalFlow dedupGraph pal4 = 1 := by
  decide

/-- One unit through the palindrome self-loop is a feasible balanced circuit
with ZERO terminal usage when the edge list is canonically deduplicated. -/
theorem palindrome_dedup_feasible_one :
    Feasible62 Base (List Base) id [pal4] dedupGraph
      unitPalFlow (noTerminals (List Base)) singletonSpectrum := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, noTerminals_usage_zero (List Base)⟩
  · intro e he
    exact Nat.zero_le _
  · intro v hv
    have h : v = pal4 := by simpa using hv
    subst v
    rw [canonical_graph_throughput_one]
  · intro v hv
    have h : v = pal4 := by simpa using hv
    subst v
    decide
  · intro v hv
    have h : v = pal4 := by simpa using hv
    subst v
    rw [canonical_graph_throughput_one]
    simp [singletonSpectrum]

/-- For exactly the SAME physical candidate copy number (one) and the SAME
edge-value keyed flow, the original graph list is NOT feasible, because its
`throughput` adds the single flow value four times and forces copy count 4.
This is a concrete difference in the implemented feasibility predicate. -/
theorem palindrome_original_not_feasible_one :
    ¬ Feasible62 Base (List Base) id [pal4] originalGraph
      unitPalFlow (noTerminals (List Base)) singletonSpectrum := by
  intro h
  have hthrough := h.1.2.2.2 pal4 (by simp)
  rw [duplicate_graph_throughput_four] at hthrough
  norm_num [singletonSpectrum] at hthrough


/-! ## Constructive alternative: preserve *orientation tags* even for a
self-reverse-complement DNA word.

MB09 §3.3 defines overlaps by the positive/negative orientation of each
read. A palindromic read has equal POSITIVE and NEGATIVE WORDS, but its
two physical orientations need not collapse into the same graph vertex
strand value. Here Bool explicitly stores that orientation bit. This is
an additive comparison model; it is not a replacement for the current
Section62Flow definitions, nor a full proof of source algorithm fidelity. -/

/-- One physical molecule class, whose two strand orientation tags remain
distinct even though their underlying DNA words are both ATAT. -/
def taggedReadWord (_ : Bool) : List Base := pal4
def taggedRc (s : Bool) : Bool := !s
def taggedRep (_ : Bool) : Bool := false

theorem tagged_rc_involutive : Function.Involutive taggedRc := by
  intro s
  cases s <;> rfl

theorem tagged_strands_are_distinct :
    strandsOf taggedRc [false] = [false,true] := by decide

theorem tagged_words_same :
    taggedReadWord false = taggedReadWord true := rfl

def taggedGraph : List (BdEdge Base Bool) :=
    overlapEdges Base Bool taggedReadWord taggedRep taggedRc 4 2 [false]

/-- All four oriented overlaps have distinct edge VALUES because the
strand TAG is retained, unlike the four identical legacy BdEdge records. -/
theorem tagged_graph_four_edges :
    taggedGraph =
      [bdEdge taggedRep false false 2,
       bdEdge taggedRep false true 2,
       bdEdge taggedRep true false 2,
       bdEdge taggedRep true true 2] := by decide

theorem tagged_graph_nodup : taggedGraph.Nodup := by decide

/-- These four labelled strands yield four distinct incidence SIGN PAIRS:
(+,-), (+,+), (-,-), (-,+). -/
theorem tagged_sign_pairs_distinct :
    (taggedGraph.map fun e => (e.sgnX,e.sgnY)).Nodup := by decide

def taggedUnitFlow : BdFlow Base Bool :=
    fun e => if e = bdEdge taggedRep false false 2 then 1 else 0

/-- Distinct orientation tags make one unit of edge-value flow count once,
even though the underlying DNA word is self-complementary. -/
theorem tagged_unit_throughput_one :
    throughput Base Bool taggedRep taggedUnitFlow taggedGraph false = 1 := by
  decide


/-! ## Bidirected reversal symmetry on explicitly tagged orientations

Reversing a *double-stranded* overlap reverses edge direction AND swaps
the two strand orientations. For the palindrome, the 4 strand-pair choices
have only 3 equivalence classes modulo that involution. This matches the
three abstract incidence-edge types in MB09 Fig. 1C, but is not a theorem
that the complete historical algorithm uses this particular quotient. -/

def reverseTaggedEdge (e : BdEdge Base Bool) : BdEdge Base Bool :=
  bdEdge taggedRep (taggedRc e.sy) (taggedRc e.sx) e.len

/-- The both-positive-orientation overlap and its both-negative mirror
spell the same double-stranded relation under full reversal. -/
theorem tagged_reverse_pairs_both_same :
    reverseTaggedEdge (bdEdge taggedRep false false 2) =
      bdEdge taggedRep true true 2 ∧
    reverseTaggedEdge (bdEdge taggedRep true true 2) =
      bdEdge taggedRep false false 2 := by
  decide

/-- The two mixed-strand endpoint choices each return to themselves. -/
theorem tagged_reverse_fixes_mixed :
    reverseTaggedEdge (bdEdge taggedRep false true 2) =
      bdEdge taggedRep false true 2 ∧
    reverseTaggedEdge (bdEdge taggedRep true false 2) =
      bdEdge taggedRep true false 2 := by
  decide

/-- On the valid graph, reversing an overlap twice is the identity. -/
theorem tagged_reverse_involutive (e : BdEdge Base Bool)
    (he : e ∈ taggedGraph) :
    reverseTaggedEdge (reverseTaggedEdge e) = e := by
  rw [tagged_graph_four_edges] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> decide

/-- Every graph edge stays a graph edge under double-strand reversal. -/
theorem tagged_reverse_mem (e : BdEdge Base Bool)
    (he : e ∈ taggedGraph) :
    reverseTaggedEdge e ∈ taggedGraph := by
  rw [tagged_graph_four_edges] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> decide

/-- Three purely representational orientation-orbit labels:
both tags equal form one class, while the two unequal arrangements each
form a reversal-fixed class. -/
def taggedOrientationClass (e : BdEdge Base Bool) : Nat :=
  if e.sx = e.sy then 0 else if e.sx = false then 1 else 2

theorem tagged_orientation_class_reverse_invariant (e : BdEdge Base Bool)
    (he : e ∈ taggedGraph) :
    taggedOrientationClass (reverseTaggedEdge e) =
      taggedOrientationClass e := by
  rw [tagged_graph_four_edges] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> decide

/-- Four distinct tagged edges yield exactly THREE classes under the
bidirected reversal symmetry. This is a finite, kernel-checked analogue
of the 'three types' in MB09 Fig. 1C. -/
theorem tagged_three_reversal_orbits :
    (taggedGraph.map taggedOrientationClass).eraseDups = [0,1,2] := by
  decide

#print axioms tagged_reverse_pairs_both_same
#print axioms tagged_reverse_fixes_mixed
#print axioms tagged_reverse_involutive
#print axioms tagged_reverse_mem
#print axioms tagged_orientation_class_reverse_invariant
#print axioms tagged_three_reversal_orbits

#print axioms tagged_rc_involutive
#print axioms tagged_strands_are_distinct
#print axioms tagged_graph_four_edges
#print axioms tagged_graph_nodup
#print axioms tagged_sign_pairs_distinct
#print axioms tagged_unit_throughput_one

#print axioms duplicate_graph_throughput_four
#print axioms canonical_graph_throughput_one
#print axioms palindrome_dedup_feasible_one
#print axioms palindrome_original_not_feasible_one

#print axioms pal4_is_rc_palindrome
#print axioms palindrome_strands_duplicate
#print axioms originalGraph_eq_quadruple
#print axioms dedupGraph_singleton
#print axioms mem_overlapEdgesDedup_iff
#print axioms palindrome_index_dimensions_differ

end AssemblyP1.Section62PalindromeEdgeMultiplicityAudit
