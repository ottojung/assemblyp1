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

/-! A concrete directed-orientation regression. This example is deliberately
not yet a test of the full double-stranded MB09 semantics: its strand RC is
identity. It tests that the candidate predicate can actually remove an edge. -/

private def regressionStrand : Fin 3 → List Nat := fun v =>
  if v = 0 then [0, 1, 2]
  else if v = 1 then [1, 2, 3]
  else [2, 3, 4]

private def regressionVerts : List (Fin 3) := [0, 1, 2]

private def regressionEdge : BdEdge Nat (Fin 3) :=
  bdEdge (fun w => w) (0 : Fin 3) (2 : Fin 3) 1

theorem regression_edge_is_reducible :
    isReducibleSpellingB (Fin 3) regressionStrand (fun w => w)
      3 1 regressionVerts regressionEdge = true := by
  decide

theorem regression_edge_is_removed :
    regressionEdge ∉ transitivelyReducedSpelling (Fin 3) regressionStrand
      (fun w => w) 3 1 regressionVerts [regressionEdge] := by
  decide

#print axioms spellPath_eq_spellDirect
#print axioms fullOverlap_not_reducible
#print axioms fullOverlap_survives

end AssemblyP1.Section62SpellingReductionCandidate
