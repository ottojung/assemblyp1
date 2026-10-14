import Mathlib
import AssemblyP1.Section62GlobalSpellingPreservation

/-!
# Global circular spelling correspondence (#284)

This module proves the **global circular spelling correspondence** for the
spelling-preserving transitive edge reduction of MB09 §6.2: a *circuit* (a
closed bidirected walk, the object MB09 §6.2 says "the original double-stranded
genome corresponds to") all of whose edges belong to the complete `overlapEdges`
graph expands, under the spelling-preserving reduction, into a circuit of
*transitively reduced* edges spelling the same circular word.

The reading of transitive edge reduction is the spelling-preserving reading of
`Section62SpellingReductionCandidate`: a detour's two overlaps satisfy the
composition law `l₁ + l₂ = L + l` with genuine proper overlaps, so the detour
spells exactly the word the direct edge spells (`spellPath_eq_spellDirect`).
The literal MB09 §6.2 "two shorter overlaps" reading is numerically vacuous
(`Section62ReductionVacuityAudit`); the coarse longer-overlap-only reading is
not spelling-preserving (`Section62ReductionMismatch`).

The per-edge expansions of `Section62GlobalSpellingPreservation` concatenate
along any signed walk.  For a circuit the walk closes, so the concatenation
closes too; the only new content is the **seam**: the last edge of the expanded
circuit arrives at the closing vertex `v` with incidence `sgnTgt v (rep v)`
while the first edge departs from `v` with incidence `sgnRep v (rep v)`, and
these are opposite because both edges are graph edges whose incidences are
determined by their endpoint molecule classes (`edge_signs_of_mem`) and
`sgnRep`/`sgnTgt` are negatives (`sgnRep_neg_sgnTgt`).  This is the MB09 §3.2
signed-walk condition at the closing vertex.

The circular word is preserved because the linear word is preserved
(`global_walk_signed_expansion`) and the two words share the same first read
`toList v`, so their extensions past the first read — the circular word's
linearization — are equal.

MB09/Myers source fidelity (equivalence to the cited algorithm), Observation 7
vertex-throughput equivalence, and the two-flow ML lift remain open; see the
module scope note of `Section62GlobalSpellingPreservation`.
-/

namespace AssemblyP1.Section62GlobalCircularCorrespondence

set_option maxHeartbeats 4000000

open Section62Flow Section62SpellingReductionCandidate Section62GlobalSpellingPreservation

variable {A W : Type} [DecidableEq W]

/-! ## The two homes of the corrected reduction agree

The corrected spelling-preserving reduction has two definitionally identical
homes: the base §6.2 model module `Section62Flow` (added alongside the audited
`isReducibleB`, so the base model carries both) and
`Section62SpellingReductionCandidate` (the predicate consumed by #261/#262).
The two Boolean definitions are the same expression, so the predicates — and
hence the reduced edge lists — are definitionally equal.  This bridge records
that the duplication is benign and lets downstream consumers use either. -/

theorem isReducibleSpelling62B_eq_candidate {A W : Type} [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rc : W → W) (readLen oMin : Nat) (verts : List W)
    (e : BdEdge A W) :
    Section62Flow.isReducibleSpelling62B A W toList rc readLen oMin verts e =
      Section62SpellingReductionCandidate.isReducibleSpellingB W toList rc readLen oMin verts e :=
  rfl

theorem transitivelyReducedSpelling62_eq_candidate {A W : Type} [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rc : W → W) (readLen oMin : Nat) (verts : List W)
    (edges : List (BdEdge A W)) :
    Section62Flow.transitivelyReducedSpelling62 A W toList rc readLen oMin verts edges =
      Section62SpellingReductionCandidate.transitivelyReducedSpelling W toList rc readLen oMin verts edges :=
  rfl

/-! ## Circuits -/

/-- A *circuit* (closed bidirected walk) at the read molecule class `v`: a
signed path from `v` to `v` whose last edge arrives at `v` with the incidence
opposite to the first edge's departure from `v`.  The second conjunct is the
MB09 §3.2 signed-walk condition at the closing vertex: the walk arrives along
its last edge and departs along its first edge, and the two incidences must be
opposite. -/
def Circuit {v : W} (edges : List (BdEdge A W)) : Prop :=
  SignedPath v v edges ∧
    ∃ e₀ e₁, edges.head? = some e₀ ∧ edges.getLast? = some e₁ ∧ e₁.sgnY = -e₀.sgnX

/-- A circuit is a signed path, so its first edge departs from `v` and its last
edge arrives at `v`. -/
theorem circuit_signedPath {v : W} {edges : List (BdEdge A W)}
    (h : Circuit v edges) : SignedPath v v edges :=
  h.1

/-- The seam of a circuit: the arrival incidence of the last edge is the
negative of the departure incidence of the first edge. -/
theorem circuit_seam {v : W} {edges : List (BdEdge A W)}
    (h : Circuit v edges) :
    ∃ e₀ e₁, edges.head? = some e₀ ∧ edges.getLast? = some e₁ ∧ e₁.sgnY = -e₀.sgnX :=
  h.2

/-! ## The seam incidence of a surviving expansion -/

/-- Every edge of a surviving expansion is a graph edge, hence carries exactly
the incidences its endpoint molecule classes determine (MB09 §3.3). -/
theorem surviving_edge_signs {v : W}
    (toList : W → List A) (rep rc : W → W) (readLen oMin : Nat) (verts : List W)
    (p : List (BdEdge A W))
    (hsurv : ∀ g ∈ p, g ∈ transitivelyReducedSpelling W toList rc readLen oMin verts
      (overlapEdges A W toList rep rc readLen oMin verts))
    (e : BdEdge A W) (he : e ∈ p) :
    e.sgnX = sgnRep e.sx (rep e.sx) ∧ e.sgnY = sgnTgt e.sy (rep e.sy) :=
  edge_signs_of_mem ((List.mem_filter.mp (hsurv e he)).1)

/-- The seam of a surviving expansion is automatically opposite: the last edge
arrives at `v` with incidence `sgnTgt v (rep v)` and the first edge departs
from `v` with incidence `sgnRep v (rep v)`, and `sgnRep`/`sgnTgt` are
negatives.  This is the MB09 §3.2 signed-walk condition at the closing vertex,
and it is the only new content of the circular correspondence beyond the
open-walk expansion. -/
theorem surviving_seam_opposite {v : W}
    (toList : W → List A) (rep rc : W → W) (readLen oMin : Nat) (verts : List W)
    (p : List (BdEdge A W))
    (hsurv : ∀ g ∈ p, g ∈ transitivelyReducedSpelling W toList rc readLen oMin verts
      (overlapEdges A W toList rep rc readLen oMin verts))
    (hp : SignedPath v v p) :
    ∃ e₀ e₁, p.head? = some e₀ ∧ p.getLast? = some e₁ ∧ e₁.sgnY = -e₀.sgnX := by
  obtain ⟨e₀, hh₀, hx₀⟩ := hp.1
  obtain ⟨e₁, hl₁, hy₁⟩ := hp.2.1
  refine ⟨e₀, e₁, hh₀, hl₁, ?_⟩
  have hmem₀ : e₀ ∈ overlapEdges A W toList rep rc readLen oMin verts :=
    (List.mem_filter.mp (hsurv e₀ (by
      rw [List.eq_cons_of_mem_head? hh₀]; exact List.mem_cons_self))).1
  have hmem₁ : e₁ ∈ overlapEdges A W toList rep rc readLen oMin verts :=
    (List.mem_filter.mp (hsurv e₁ (mem_of_mem_getLast? hl₁))).1
  have hs₀ : e₀.sgnX = sgnRep v (rep v) := by
    have h := (edge_signs_of_mem hmem₀).1
    rw [hx₀] at h
    exact h
  have hs₁ : e₁.sgnY = sgnTgt v (rep v) := by
    have h := (edge_signs_of_mem hmem₁).2
    rw [hy₁] at h
    exact h
  have hneg := sgnRep_neg_sgnTgt v rep
  rw [hs₀, hs₁, hneg]

/-! ## The global circular spelling correspondence -/

/-- **Global circular spelling correspondence.**  Given a circuit `walk` at
the read molecule class `v`, all of whose edges belong to the complete
`overlapEdges` graph, there is a circuit `p` of edges of the *transitively
reduced* graph spelling the same circular word:

* `p` is a circuit at `v`: `Circuit v p`;
* consecutive edges of `p` have opposite incidences at every common oriented
  strand (MB09 §3.2): `p.IsChain (fun f g => f.sgnY = -g.sgnX)`;
* every edge of `p` survives the spelling-preserving transitive reduction;
* `p` spells the same circular word as the walk:
  `pathTail toList p = pathTail toList walk`.

The proof applies the open-walk expansion `global_walk_signed_expansion` to the
circuit (a circuit is a signed path from `v` to `v`), then closes the seam with
`surviving_seam_opposite`.  The circular word is preserved because the linear
word is preserved and both share the first read `toList v`. -/
theorem global_circuit_signed_expansion [DecidableEq A]
    (toList : W → List A) (rep rc : W → W) (readLen oMin : Nat) (verts : List W)
    (hLen : ∀ s ∈ strandsOf rc verts, (toList s).length = readLen) :
    ∀ {walk : List (BdEdge A W)} {v : W},
      Circuit v walk →
      (∀ e ∈ walk, e ∈ overlapEdges A W toList rep rc readLen oMin verts) →
      ∃ p : List (BdEdge A W),
        Circuit v p ∧
          p.IsChain (fun f g => f.sgnY = -g.sgnX) ∧
          (∀ g ∈ p, g ∈ transitivelyReducedSpelling W toList rc readLen oMin verts
            (overlapEdges A W toList rep rc readLen oMin verts)) ∧
          pathTail toList p = pathTail toList walk := by
  intro walk v hcirc hmem
  obtain ⟨hsp, -⟩ := hcirc
  obtain ⟨p, hp, hchain, hsurv, htail⟩ :=
    global_walk_signed_expansion toList rep rc readLen oMin verts hLen v v hsp hmem
  refine ⟨p, ⟨hp, ?_⟩, hchain, hsurv, ?_⟩
  · exact surviving_seam_opposite toList rep rc readLen oMin verts p hsurv hp
  · exact List.append_right_injective (toList v) htail

/-! ## The circular word of a circuit -/

/-- The circular word spelled by a circuit: the extension past the first read,
`pathTail toList edges`.  Two circuits spell the same circular word exactly
when their extensions past the first read are equal, because the first read is
the same (`toList v`) and the linear words are `toList v ++ pathTail`. -/
def circularWord (toList : W → List A) {v : W} {edges : List (BdEdge A W)}
    (_h : Circuit v edges) : List A :=
  pathTail toList edges

/-- The global circular spelling correspondence, restated as a statement about
circular words: for every circuit `walk` there is a surviving circuit `p`
spelling the same circular word, i.e. `circularWord toList p = circularWord toList walk`. -/
theorem global_circuit_circular_word [DecidableEq A]
    (toList : W → List A) (rep rc : W → W) (readLen oMin : Nat) (verts : List W)
    (hLen : ∀ s ∈ strandsOf rc verts, (toList s).length = readLen) :
    ∀ {walk : List (BdEdge A W)} {v : W},
      Circuit v walk →
      (∀ e ∈ walk, e ∈ overlapEdges A W toList rep rc readLen oMin verts) →
      ∃ p : List (BdEdge A W),
        Circuit v p ∧ circularWord toList p = circularWord toList walk := by
  intro walk v hcirc hmem
  obtain ⟨p, hp, -, -, htail⟩ :=
    global_circuit_signed_expansion toList rep rc readLen oMin verts hLen v hcirc hmem
  exact ⟨p, hp, htail⟩

/-! ## Total spelled length, `G < readLen`, and reverse-complement classes

The circular correspondence is stated about the *spelled word* `pathTail`, not
about a length-`readLen` window decomposition, so it is independent of whether
the spelled genome length `G` is at least the read length.  The total spelled
length is the sum of the edges' extension lengths `readLen − e.len`; the theorem
above carries no hypothesis `readLen ≤ G`, so it already covers the `G < readLen`
regime (the wrap-around windows of a genome shorter than one read).  The two
lemmas below record this explicitly, together with the fact that the intermediate
strand in the reduction is quantified over `strandsOf rc verts`, which enumerates
*both* strands of every observed molecule class, so reverse-complement
intermediates are available. -/

/-- The total spelled length `G` of a walk is the sum of the extension lengths
`readLen − e.len`.  No hypothesis relates `G` to `readLen`: the formula holds in
the `G < readLen` regime as well. -/
theorem pathTail_length [DecidableEq A]
    (toList : W → List A) (readLen : Nat) :
    ∀ (edges : List (BdEdge A W)),
      (∀ e ∈ edges, (toList e.sy).length = readLen) →
      (pathTail toList edges).length =
        (edges.map (fun e => readLen - e.len)).sum := by
  intro edges
  induction edges with
  | nil => intro _; simp [pathTail]
  | cons e rest ih =>
      intro hLen
      have hlen_e : (edgeTail toList e).length = readLen - e.len := by
        unfold edgeTail
        rw [List.length_drop, hLen e List.mem_cons_self]
      have hrest : ∀ x ∈ rest, (toList x.sy).length = readLen :=
        fun x hx => hLen x (List.mem_cons_of_mem e hx)
      rw [pathTail_cons, List.length_append, hlen_e, ih hrest, List.map_cons,
        List.sum_cons]

/-- The spelled circular word of a circuit has length `G = Σ (readLen − e.len)`. -/
theorem circularWord_length [DecidableEq A]
    (toList : W → List A) (readLen : Nat) {v : W} {edges : List (BdEdge A W)}
    (hcirc : Circuit v edges)
    (hLen : ∀ e ∈ edges, (toList e.sy).length = readLen) :
    (circularWord toList hcirc).length =
      (edges.map (fun e => readLen - e.len)).sum :=
  pathTail_length toList readLen edges hLen

/-- Every observed molecule-class representative is one of the enumerated
strands. -/
theorem mem_strandsOf_self {rc : W → W} {verts : List W} {m : W}
    (hm : m ∈ verts) : m ∈ strandsOf rc verts := by
  unfold strandsOf
  exact List.mem_append.mpr (Or.inl hm)

/-- The reverse complement of every observed molecule-class representative is
also one of the enumerated strands, so the spelling-preserving reduction can use
a reverse-complement intermediate. -/
theorem mem_strandsOf_rc {rc : W → W} {verts : List W} {m : W}
    (hm : m ∈ verts) : rc m ∈ strandsOf rc verts := by
  unfold strandsOf
  exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨m, hm, rfl⟩))

#print axioms global_circuit_signed_expansion
#print axioms global_circuit_circular_word
#print axioms surviving_seam_opposite
#print axioms pathTail_length
#print axioms circularWord_length
#print axioms isReducibleSpelling62B_eq_candidate
#print axioms transitivelyReducedSpelling62_eq_candidate

end AssemblyP1.Section62GlobalCircularCorrespondence
