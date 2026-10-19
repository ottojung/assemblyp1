import Mathlib
import AssemblyP1.Section62BidirectedFlow

/-!
# Partial spelling-preserving overlap-reduction candidate (#284)

This module isolates the genuinely overlap-based two-hop spelling predicate and
proofs of the corresponding spelling identity and full-overlap edge persistence.
It is NOT a source-faithful proof of Myers transitive reduction: equivalence to
the cited algorithm, bidirected reverse-complement semantics, global walk-language
preservation, and Observation 7 remain separately open. It does NOT lift either
§6.2 genome flow witness or any likelihood inequality.

Extracted from a preserved, unfinished #262 worktree; the original source remains
in signed Git recovery/assemblyp1-262-20261012, unchanged.
-/

namespace AssemblyP1.Section62SpellingReductionCandidate

set_option maxHeartbeats 4000000

open Section62Flow

variable {A : Type}

/-! ## Spelling length accounting

Every length statement below carries its explicit overlap bound (`l ≤ L`,
`l₁ ≤ L`, `l₂ ≤ L`).  The bounds are not decorative: `List.drop` saturates, so
past `L` the spelled word stops growing and the formulas `2L − l`, `3L − l₁ − l₂`
fail (e.g. `L = 3`, `l = 7` spells `3` bases, not `2·3 − 7 = 0`).  Proper
overlaps `l < L` always satisfy the bounds, so no graph-valid edge is excluded. -/

/-- The word spelled by a direct overlap of length `l` from `sx` to `sy`:
`sx` followed by the part of `sy` past the overlap. -/
def spellDirect (sx sy : List A) (l : Nat) : List A := sx ++ sy.drop l

/-- The word spelled by a two-edge overlap path `sx → m → sy` with overlaps
`l₁`, `l₂`. -/
def spellPath (sx m sy : List A) (l1 l2 : Nat) : List A :=
  sx ++ m.drop l1 ++ sy.drop l2

/-- A direct overlap edge of length `l ≤ L` spells a word of length `2L − l`,
i.e. contributes `L − l` bases beyond the first read. -/
theorem spellDirect_length {L l : Nat} {sx sy : List A}
    (hsx : sx.length = L) (hsy : sy.length = L) (hl : l ≤ L) :
    (spellDirect sx sy l).length = 2 * L - l := by
  unfold spellDirect
  simp only [List.length_append, List.length_drop, hsx, hsy]
  omega

/-- A two-edge overlap path with `l₁ ≤ L` and `l₂ ≤ L` spells a word of length
`3L − l₁ − l₂`. -/
theorem spellPath_length {L l1 l2 : Nat} {sx m sy : List A}
    (hsx : sx.length = L) (hm : m.length = L) (hsy : sy.length = L)
    (hl1 : l1 ≤ L) (hl2 : l2 ≤ L) :
    (spellPath sx m sy l1 l2).length = 3 * L - l1 - l2 := by
  unfold spellPath
  simp only [List.length_append, List.length_drop, hsx, hm, hsy]
  omega

/-- A full-overlap edge (`l = L − 1`) contributes exactly one base beyond the
first read. -/
theorem spellDirect_full_overlap {L : Nat} {sx sy : List A}
    (hsx : sx.length = L) (hsy : sy.length = L) (hL : 2 ≤ L) :
    (spellDirect sx sy (L - 1)).length = L + 1 := by
  unfold spellDirect
  simp only [List.length_append, List.length_drop, hsx, hsy]
  omega

/-- Every proper overlap edge (`l < L`) adds at least one base to the spelling:
the spelled word has length `2L − l ≥ L + 1`. -/
theorem spellDirect_proper_ge_one {L l : Nat} {sx sy : List A}
    (hsx : sx.length = L) (hsy : sy.length = L) (hl : l < L) :
    L + 1 ≤ (spellDirect sx sy l).length := by
  rw [spellDirect_length hsx hsy (by omega)]
  omega

/-- Every two-edge replacement proper path (`l₁ < L`, `l₂ < L`) adds at least
two bases beyond the first read: the spelled word has length
`3L − l₁ − l₂ ≥ L + 2`. -/
theorem spellPath_proper_ge_two {L l1 l2 : Nat} {sx m sy : List A}
    (hsx : sx.length = L) (hm : m.length = L) (hsy : sy.length = L)
    (hl1 : l1 < L) (hl2 : l2 < L) :
    L + 2 ≤ (spellPath sx m sy l1 l2).length := by
  rw [spellPath_length hsx hm hsy (by omega) (by omega)]
  omega
/-! ## The core spelling lemma

The composition law `l₁ + l₂ = L + l` is the exact condition under which a
two-edge overlap path spells the same word as the direct `l`-overlap.  The
proper-overlap bounds `l₁ < L`, `l2 < L`, `l < L` are hypotheses, not
conveniences: without them the lemma is false (the #261 front kernel-checks the
counterexample `L = 4`, `l₁ = 5`, `l₂ = 0`, `l = 1`).  This module re-states and
re-proves the lemma self-contained, so its kernel check stands independently of
that front's in-progress module. -/

/-- **Helper.**  Dropping `X.length + l` from `X ++ B` is the same as dropping
`l` from `B`: first drop all of `X`, then drop `l` more. -/
theorem drop_add_length {α : Type} (X B : List α) (l : Nat) :
    (X ++ B).drop (X.length + l) = B.drop l := by
  have h1 : (X ++ B).drop X.length = B := by
    rw [List.drop_append_of_le_length (h := le_refl _), List.drop_length, List.nil_append]
  rw [← List.drop_drop, h1]

/-- **Helper.**  For `l ≤ l2`, dropping `l` from `sy.take l2` and then appending
`sy.drop l2` recovers `sy.drop l`: the first `l` symbols of `sy` are discarded,
and the remaining `l2 − l` symbols of the `take` together with the `drop l2` part
reconstitute `sy.drop l`. -/
theorem take_drop_cons {α : Type} (sy : List α) (l l2 : Nat) (hl : l ≤ l2) :
    (sy.take l2).drop l ++ sy.drop l2 = sy.drop l := by
  have hstep1 : (sy.take l2).drop l = (sy.drop l).take (l2 - l) := by
    have h0 := List.take_drop (i := l2 - l) (j := l) (l := sy)
    rw [show l + (l2 - l) = l2 from by omega] at h0
    exact h0.symm
  have hstep2 : sy.drop l2 = (sy.drop l).drop (l2 - l) := by
    have h0 := List.drop_drop (i := l2 - l) (j := l) (l := sy)
    rw [show l + (l2 - l) = l2 from by omega] at h0
    exact h0.symm
  rw [hstep1, hstep2, List.take_append_drop]

/-- **Spelling-preserving reduction lemma.**

For three reads `sx`, `m`, `sy` of common length `L`, if the first overlap
genuinely places `m` after `sx` (`suffix l₁ sx = prefix l₁ m`), the second
genuinely places `sy` after `m` (`suffix l₂ m = prefix l₂ sy`), all three
overlaps are proper (`l₁ < L`, `l₂ < L`, `l < L`), and the composition law
`l₁ + l₂ = L + l` holds, then the two-edge path spells exactly the same word as
the direct `l`-overlap from `sx` to `sy`.

No further hypothesis is needed: the conclusion is the word equality, which is
the content of "the path spells the same `W`". -/
theorem spellPath_eq_spellDirect {L l1 l2 l : Nat} {sx m sy : List A}
    (_hsx : sx.length = L) (hm : m.length = L) (hsy : sy.length = L)
    (hl1 : l1 < L) (hl2 : l2 < L) (_hl : l < L)
    (_h1 : sufOf sx l1 = preOf m l1) (h2 : sufOf m l2 = preOf sy l2)
    (h3 : l1 + l2 = L + l) :
    spellPath sx m sy l1 l2 = spellDirect sx sy l := by
  unfold spellPath spellDirect
  have hkey : m.drop l1 ++ sy.drop l2 = sy.drop l := by
    have hmsplit : m = m.take (L - l2) ++ sy.take l2 := by
      have h2' : m.drop (L - l2) = sy.take l2 := by
        simp only [sufOf, preOf, hm] at h2
        exact h2
      exact (List.take_append_drop (L - l2) m).symm.trans (by rw [h2'])
    have hdecomp : l1 = (L - l2) + l := by omega
    have hdrop : m.drop l1 = (sy.take l2).drop l := by
      rw [hmsplit, hdecomp]
      have hlen : (m.take (L - l2)).length = L - l2 := by
        rw [List.length_take]; omega
      rw [show (L - l2) + l = (m.take (L - l2)).length + l from by rw [hlen]]
      exact drop_add_length _ _ _
    have htake : (sy.take l2).drop l ++ sy.drop l2 = sy.drop l :=
      take_drop_cons sy l l2 (by omega)
    rw [hdrop, htake]
  rw [List.append_assoc]
  exact congrArg (sx ++ ·) hkey

/-! ## The spelling-preserving transitive edge reduction

Self-contained re-statement of the reduction predicate: genuine overlaps +
composition law `l₁ + l₂ = L + l`, both legs proper.  The length candidates
range over `List.range readLen`, which enforces the proper-overlap bounds
`l₁, l₂ < readLen` — no invalid overlap length assumptions.  This is the same
object as the `AssemblyP1.Section62SpellingReduction` front's predicate, but
defined here independently so this module's kernel check does not depend on that
front's in-progress file. -/

/-- Whether the direct edge `e : sx → sy` of overlap `e.len` is spelling-
preservingly reducible: there exists an intermediate strand `m` of some observed
molecule class and proper overlap lengths `l₁`, `l₂` (both `≥ oMin`, so the path
edges exist in the graph) such that

* the path overlaps are genuine (`sufOf sx l₁ = preOf m l₁`,
  `sufOf m l₂ = preOf sy l₂`),
* the composition law `l₁ + l₂ = readLen + e.len` holds.

By `spellPath_eq_spellDirect`, these conditions are exactly "the two-edge path
spells the same word as the direct edge", so removing the direct edge preserves
the language of spelled molecules. -/
def isReducibleSpellingB (W : Type) [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rc : W → W) (readLen oMin : Nat) (verts : List W)
    (e : BdEdge A W) : Bool :=
  (strandsOf rc verts).any fun m =>
    (List.range readLen).any fun l1 =>
      (List.range readLen).any fun l2 =>
        decide (oMin ≤ l1) && decide (oMin ≤ l2) &&
          decide (sufOf (toList e.sx) l1 = preOf (toList m) l1) &&
          decide (sufOf (toList m) l2 = preOf (toList e.sy) l2) &&
          decide (l1 + l2 = readLen + e.len)

/-- The spelling-preserving transitive reduction, as a proposition. -/
def isReducibleSpelling (W : Type) [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rc : W → W) (readLen oMin : Nat) (verts : List W)
    (e : BdEdge A W) : Prop :=
  isReducibleSpellingB W toList rc readLen oMin verts e = true

/-- The transitively reduced bidirected overlap graph under the spelling-
preserving reading: those edges not spelling-preservingly reducible. -/
def transitivelyReducedSpelling (W : Type) [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rc : W → W) (readLen oMin : Nat)
    (verts : List W) (edges : List (BdEdge A W)) : List (BdEdge A W) :=
  edges.filter (fun e => !isReducibleSpellingB W toList rc readLen oMin verts e)

/-! ## The omega inequality

For proper overlaps `l₁, l₂ < L` the sum `l₁ + l₂` is at most `2L − 2`, which is
strictly less than `L + (L − 1) = 2L − 1`.  The right-hand side is exactly what
the composition law `l₁ + l₂ = L + l` demands of a two-edge replacement for a
full-overlap edge `l = L − 1`.  Since `2L − 2 < 2L − 1`, no such replacement
exists: no full-overlap edge can ever be spelling-preservingly removed. -/

/-- **The omega inequality.**  For proper overlaps `l₁, l₂ < L`: `l₁ + l₂ ≤ 2L − 2`. -/
theorem omega_two_hop {L l1 l2 : Nat} (hl1 : l1 < L) (hl2 : l2 < L) :
    l1 + l2 ≤ 2 * L - 2 := by omega

/-- **The strict omega inequality.**  For proper overlaps `l₁, l₂ < L`, the sum
is strictly below the `2L − 1` that a two-edge replacement of a full-overlap
edge would demand. -/
theorem omega_strict {L l1 l2 : Nat} (hl1 : l1 < L) (hl2 : l2 < L) :
    l1 + l2 < L + (L - 1) := by omega

/-- **No full-overlap edge can be spelling-preservingly removed.**  An edge of
length `l = L − 1` is spelling-preservingly reducible only if there exist proper
overlaps `l₁, l₂ < L` with `l₁ + l₂ = L + (L − 1) = 2L − 1`.  But the omega
inequality gives `l₁ + l₂ ≤ 2L − 2 < 2L − 1`, a contradiction. -/
theorem fullOverlap_not_reducible {W : Type} [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rc : W → W) (readLen oMin : Nat) (verts : List W)
    (e : BdEdge A W) (hfull : e.len = readLen - 1) :
    ¬ isReducibleSpelling W toList rc readLen oMin verts e := by
  intro h
  unfold isReducibleSpelling isReducibleSpellingB at h
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨m, hm, l1, hl1, l2, hl2, hconds⟩ := h
  rcases hconds with ⟨⟨⟨⟨ho1, ho2⟩, hov1⟩, hov2⟩, hcomp⟩
  have hl1' : l1 < readLen := List.mem_range.mp hl1
  have hl2' : l2 < readLen := List.mem_range.mp hl2
  have key : l1 + l2 ≤ 2 * readLen - 2 := omega_two_hop hl1' hl2'
  have demand : readLen + e.len = 2 * readLen - 1 := by rw [hfull]; omega
  omega

/-- **Every full-overlap edge survives the spelling-preserving transitive
reduction.**  An edge of length `readLen − 1` is never removed by
`transitivelyReducedSpelling`, at any `oMin ≤ readLen − 1`. -/
theorem fullOverlap_survives {W : Type} [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rc : W → W) (readLen oMin : Nat) (verts : List W)
    (edges : List (BdEdge A W)) (e : BdEdge A W)
    (hfull : e.len = readLen - 1) (hem : e ∈ edges) :
    e ∈ transitivelyReducedSpelling W toList rc readLen oMin verts edges := by
  unfold transitivelyReducedSpelling
  rw [List.mem_filter]
  refine ⟨hem, ?_⟩
  cases hb : isReducibleSpellingB W toList rc readLen oMin verts e with
  | false => rfl
  | true => exact absurd hb (fullOverlap_not_reducible toList rc readLen oMin verts e hfull)



/-- A two-step spelling replacement always has *longer* overlap lengths
than the direct edge (equivalently, shorter newly spelled extensions). -/
theorem replacement_overlaps_longer
    (L directLen l1 l2 : Nat)
    (hl1 : l1 < L) (hl2 : l2 < L)
    (hcomp : l1 + l2 = L + directLen) :
    directLen < l1 ∧ directLen < l2 := by
  omega

/-! ## A concrete bidirected regression on the complete `overlapEdges` graph

This is the review gate the PR body set for itself: a positive finite example
where a redundant edge is *really* deleted from the **complete** `overlapEdges`
graph, with its replacement two-edge path present in that same graph.  The
earlier draft filtered the singleton list `[regressionEdge]`, which removed the
edge without its replacement path existing in the graph; that demonstrated only
the predicate, not path-in-graph preservation.  Here the direct edge and both
detour legs are all members of the generated graph, the direct edge is removed
by the candidate reduction, and **both detour legs survive** it.

The instance is genuinely double-stranded (MB09 §3.1, §3.3): the vertex set is
three observed read *molecule* classes, each contributing its representative
strand and its reverse complement.  The strand involution `regressionRc` is a
non-trivial involution (`0↔3`, `1↔4`, `2↔5`) consistent with
`regressionStrand`, so `strandsOf regressionRc regressionVerts` enumerates both
strands of every class.  This exercises the reverse-complement semantics of
`isReducibleSpellingB`, which quantifies the intermediate strand over
`strandsOf rc verts`.  The three forward reads `[0,1,2]`, `[1,2,3]`, `[2,3,4]`
chain by a proper `2`-overlap, so the direct `1`-overlap `0→2` is spelled by the
two-edge path `0→1→2`.

The claim is local, path-in-graph spelling preservation for this one removal.
It is **not** global language preservation and **not** Observation 7 throughput
equivalence; those remain open (see the module scope note above). -/

/-- The DNA complement involution on the eight-symbol alphabet `{0,…,7}`. -/
private def regressionComp : Nat → Nat := fun w => 7 - w

/-- A strand, as the list of its symbols.  Strands `0,1,2` are the three forward
reads; strands `3,4,5` are their reverse complements under `regressionComp`. -/
private def regressionStrand : Fin 6 → List Nat := fun v =>
  if v = 0 then [0, 1, 2]
  else if v = 1 then [1, 2, 3]
  else if v = 2 then [2, 3, 4]
  else if v = 3 then [5, 6, 7]
  else if v = 4 then [4, 5, 6]
  else [3, 4, 5]

/-- The strand-level reverse-complement involution (MB09 §3.1): a non-trivial
involution pairing each forward strand with its reverse complement. -/
private def regressionRc : Fin 6 → Fin 6 := fun w => (w + 3) % 6

/-- The molecule-class representative of a strand (MB09 §4.1): strands `w` and
`regressionRc w` are one class, labelled by the forward strand. -/
private def regressionRep : Fin 6 → Fin 6 := fun w => if w ≥ 3 then w - 3 else w

/-- Involution and molecule-pair compatibility of the finite toy. -/
theorem regression_rc_involution :
    ∀ w : Fin 6, regressionRc (regressionRc w) = w := by decide

theorem regression_representative_rc :
    ∀ w : Fin 6, regressionRep (regressionRc w) = regressionRep w := by decide

theorem regression_read_length :
    ∀ w : Fin 6, (regressionStrand w).length = 3 := by decide

/-- A complementary eight-symbol test alphabet, not yet the DNA four-base alphabet. -/
theorem regression_reverse_complement :
    ∀ w : Fin 6, regressionStrand (regressionRc w) =
      (regressionStrand w).reverse.map (fun x : Nat => 7 - x) := by decide

/-- The three observed read DNA molecules, the vertices of the §6.2 graph. -/
private def regressionVerts : List (Fin 6) := [0, 1, 2]

/-- The complete bidirected overlap graph of MB09 §6.2 on the observed read
molecules, at read length `3` and overlap threshold `o_min = 1`. -/
private def regressionGraph : List (BdEdge Nat (Fin 6)) :=
  overlapEdges Nat (Fin 6) regressionStrand regressionRep regressionRc 3 1 regressionVerts

/-- The direct `1`-overlap edge `0 → 2`: spelled by the two-edge path
`0 → 1 → 2` of two proper `2`-overlaps. -/
private def regressionEdge : BdEdge Nat (Fin 6) :=
  bdEdge regressionRep (0 : Fin 6) (2 : Fin 6) 1

/-- The first detour leg, the proper `2`-overlap `0 → 1`. -/
private def regressionLeg1 : BdEdge Nat (Fin 6) :=
  bdEdge regressionRep (0 : Fin 6) (1 : Fin 6) 2

/-- The second detour leg, the proper `2`-overlap `1 → 2`. -/
private def regressionLeg2 : BdEdge Nat (Fin 6) :=
  bdEdge regressionRep (1 : Fin 6) (2 : Fin 6) 2

/-- The candidate predicate recognizes the direct edge as spelling-preservingly
reducible (witness: intermediate strand `1`, overlaps `2` and `2`). -/
theorem regression_edge_is_reducible :
    isReducibleSpellingB (Fin 6) regressionStrand regressionRc
      3 1 regressionVerts regressionEdge = true := by
  decide

/-- The direct edge is a member of the complete `overlapEdges` graph. -/
theorem regression_direct_edge_in_graph :
    regressionEdge ∈ regressionGraph := by
  decide

/-- Both detour legs are members of the complete `overlapEdges` graph. -/
theorem regression_legs_in_graph :
    regressionLeg1 ∈ regressionGraph ∧ regressionLeg2 ∈ regressionGraph := by
  decide

/-- The direct edge is removed by the candidate reduction of the **complete**
graph. -/
theorem regression_edge_is_removed :
    regressionEdge ∉ transitivelyReducedSpelling (Fin 6) regressionStrand regressionRc
      3 1 regressionVerts regressionGraph := by
  decide

/-- Both detour legs **survive** the candidate reduction of the complete graph:
the replacement two-edge path is present after the removal. -/
theorem regression_legs_survive :
    regressionLeg1 ∈ transitivelyReducedSpelling (Fin 6) regressionStrand regressionRc
      3 1 regressionVerts regressionGraph ∧
    regressionLeg2 ∈ transitivelyReducedSpelling (Fin 6) regressionStrand regressionRc
      3 1 regressionVerts regressionGraph := by
  decide

/-! ### Path-in-graph spelling preservation (justified strengthening)

The source asserts that the transitive reduction leaves "the set of possible DNA
molecules spelled by the graph" unchanged (§6.2) and that a bidirected walk spells
a molecule "for any graph whose edges are bidirected overlaps" (§4.1).  The
local content of that claim for a single removal — the removed edge's replacement
path is *in the graph* and spells the same word — is provable from the lemmas
above.  This is the strongest form of the review gate: not merely a concrete
example, but the general fact that every candidate removal is spelling-preserving
*relative to the graph*.

Only the single-edge, path-in-graph statement is claimed here.  Global language
preservation of the *simultaneous* reduction is proved downstream in
`AssemblyP1.Section62SimultaneousReduction` (well-founded recursion on the
extension length `readLen - e.len`, using `replacement_overlaps_longer` and
`spellPath_eq_spellDirect`); it is not restated in this module to keep the
dependency acyclic.  Observation 7 throughput equivalence is a separate front. -/

/-- **(a) Membership extraction.**  If `e` is an edge of the complete
`overlapEdges` graph, then its overlap length is proper (`o_min ≤ e.len <
readLen`), both endpoint strands are strands of observed molecule classes, and
the direct overlap is genuine. -/
theorem overlapEdges_mem_iff {A : Type} {W : Type} [DecidableEq A] [DecidableEq W]
    {toList : W → List A} {rep rc : W → W} {readLen oMin : Nat} {verts : List W}
    {e : BdEdge A W} (he : e ∈ overlapEdges A W toList rep rc readLen oMin verts) :
    oMin ≤ e.len ∧ e.len < readLen ∧ e.sx ∈ strandsOf rc verts ∧
      e.sy ∈ strandsOf rc verts ∧
      sufOf (toList e.sx) e.len = preOf (toList e.sy) e.len := by
  unfold overlapEdges at he
  rw [List.mem_flatMap] at he
  obtain ⟨len, hlen, he⟩ := he
  have hlen_lt : len < readLen := List.mem_range.mp (List.mem_filter.mp hlen).1
  have hlen_ge : oMin ≤ len := of_decide_eq_true (List.mem_filter.mp hlen).2
  rw [List.mem_flatMap] at he
  obtain ⟨sx, hsx, he⟩ := he
  rw [List.mem_flatMap] at he
  obtain ⟨sy, hsy, he⟩ := he
  by_cases h : sufOf (toList sx) len = preOf (toList sy) len
  · simp [h] at he
    have hlen_e : e.len = len := congrArg BdEdge.len he
    have hsx_e : e.sx = sx := congrArg BdEdge.sx he
    have hsy_e : e.sy = sy := congrArg BdEdge.sy he
    have hov : sufOf (toList e.sx) e.len = preOf (toList e.sy) e.len := by
      rw [hsx_e, hsy_e, hlen_e]
      exact h
    have hnum : oMin ≤ e.len ∧ e.len < readLen := by omega
    exact ⟨hnum.1, hnum.2, by rw [hsx_e]; exact hsx, by rw [hsy_e]; exact hsy, hov⟩
  · simp [h] at he

/-- **(b) Detour membership.**  If `sx` and `m` are strands of observed molecule
classes, `l` is a proper overlap length (`o_min ≤ l < readLen`), and the overlap
is genuine, then the matching `bdEdge` is an edge of the complete `overlapEdges`
graph. -/
theorem bdEdge_mem_overlapEdges {A : Type} {W : Type} [DecidableEq A] [DecidableEq W]
    {toList : W → List A} {rep rc : W → W} {readLen oMin : Nat} {verts : List W}
    {sx m : W} {l : Nat}
    (hsx : sx ∈ strandsOf rc verts) (hm : m ∈ strandsOf rc verts)
    (hl : oMin ≤ l ∧ l < readLen)
    (hov : sufOf (toList sx) l = preOf (toList m) l) :
    bdEdge rep sx m l ∈ overlapEdges A W toList rep rc readLen oMin verts := by
  refine List.mem_flatMap.mpr ⟨l, List.mem_filter.mpr ⟨List.mem_range.mpr hl.2, decide_eq_true hl.1⟩, ?_⟩
  refine List.mem_flatMap.mpr ⟨sx, hsx, ?_⟩
  refine List.mem_flatMap.mpr ⟨m, hm, ?_⟩
  simp [hov]

/-- **Path-in-graph spelling preservation.**  If `e` is an edge of the complete
`overlapEdges` graph, every observed strand linearizes to a read of length
`readLen`, and the candidate predicate reduces `e`, then the two detour edges
are themselves edges of that graph (with the same `rep`) and the two-edge path
spells exactly the word the direct edge spells.  So removing `e` preserves its
spelled word *relative to the graph*. -/
theorem removable_edge_detour_in_graph {W : Type} [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rep rc : W → W) (readLen oMin : Nat) (verts : List W)
    (hLen : ∀ s ∈ strandsOf rc verts, (toList s).length = readLen)
    (e : BdEdge A W)
    (he : e ∈ overlapEdges A W toList rep rc readLen oMin verts)
    (hred : isReducibleSpelling W toList rc readLen oMin verts e) :
    ∃ m l1 l2,
      oMin ≤ l1 ∧ oMin ≤ l2 ∧ l1 < readLen ∧ l2 < readLen ∧
        bdEdge rep e.sx m l1 ∈ overlapEdges A W toList rep rc readLen oMin verts ∧
          bdEdge rep m e.sy l2 ∈ overlapEdges A W toList rep rc readLen oMin verts ∧
          spellPath (toList e.sx) (toList m) (toList e.sy) l1 l2 =
            spellDirect (toList e.sx) (toList e.sy) e.len := by
  have hb := overlapEdges_mem_iff he
  unfold isReducibleSpelling isReducibleSpellingB at hred
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hred
  obtain ⟨m, hm, l1, hl1, l2, hl2, hconds⟩ := hred
  rcases hconds with ⟨⟨⟨⟨ho1, ho2⟩, hov1⟩, hov2⟩, hcomp⟩
  have hsxLen : (toList e.sx).length = readLen := hLen e.sx hb.2.2.1
  have hmLen : (toList m).length = readLen := hLen m hm
  have hsyLen : (toList e.sy).length = readLen := hLen e.sy hb.2.2.2.1
  refine ⟨m, l1, l2, ho1, ho2, List.mem_range.mp hl1, List.mem_range.mp hl2, ?_, ?_, ?_⟩
  · exact bdEdge_mem_overlapEdges hb.2.2.1 hm ⟨ho1, List.mem_range.mp hl1⟩ hov1
  · exact bdEdge_mem_overlapEdges hm hb.2.2.2.1 ⟨ho2, List.mem_range.mp hl2⟩ hov2
  · exact spellPath_eq_spellDirect hsxLen hmLen hsyLen (List.mem_range.mp hl1)
      (List.mem_range.mp hl2) hb.2.1 hov1 hov2 hcomp

#print axioms spellPath_eq_spellDirect
#print axioms fullOverlap_not_reducible
#print axioms fullOverlap_survives
/-- Complementary incidences make the two legs a signed bidirected path. -/
theorem detour_signs_match {W : Type} [DecidableEq W]
    (rep : W → W) (sx m sy : W) (l1 l2 : Nat) :
    (bdEdge (A := A) rep sx m l1).sgnY =
      -(bdEdge (A := A) rep m sy l2).sgnX := by
  change (if m = rep m then (-1 : ℤ) else 1) =
    - (if m = rep m then (1 : ℤ) else -1)
  split_ifs <;> omega

#print axioms detour_signs_match
#print axioms removable_edge_detour_in_graph
#print axioms regression_edge_is_removed
#print axioms regression_legs_survive

end AssemblyP1.Section62SpellingReductionCandidate
