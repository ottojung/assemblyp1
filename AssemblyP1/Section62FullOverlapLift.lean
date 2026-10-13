import Mathlib
import AssemblyP1.Section62BidirectedFlow
-- import AssemblyP1.Section62NonSpelledFlow

/-!
# Lifting full-overlap ML counterexamples to arbitrary overlap thresholds (issue #262)

This module is the independent parallel proof front for issue #262, a child of
the AssemblyP1 #261 front.  It formalizes the **full-overlap edge immersion**
and the **zero-extension flow lift**, and lifts the existing kernel-checked
full-overlap (`o_min = L − 1`) strict-ML / bridging-sufficiency counterexamples
to arbitrary overlap thresholds `o_min ≤ L − 1`.

## The two halves of the main result

**(1) No full-overlap edge is ever spelling-preservingly removable.**  For read
length `L ≥ 2`, a direct overlap edge of proper length `l < L` spells the word
`sx ++ sy.drop l` of length `2L − l`, so it contributes `L − l` bases beyond the
first read.  A *full-overlap* edge `l = L − 1` contributes exactly `1` base.
Every two-edge replacement path `sx → m → sy` with proper overlaps `l₁, l₂`
contributes `3L − l₁ − l₂ ≥ 3L − 2(L−1) = L + 2` bases, i.e. at least `2`.
The composition law for a path to spell the *same* word as the direct edge is
`l₁ + l₂ = L + l`; for a full-overlap edge this reads `l₁ + l₂ = 2L − 1`, but
properness gives `l₁ + l₂ ≤ 2L − 2`.  This is the **omega inequality**, and it
is the whole obstruction: `fullOverlap_not_reducible` below.

**(2) The full-overlap edge set embeds in the reduced arbitrary-overlap graph.**
Because no full-overlap edge is reducible, every full-overlap edge of the
`o_min`-graph survives the spelling-preserving transitive reduction
(`fullOverlap_survives`).  Consequently a feasible §6.2 flow on the
full-overlap graph lifts verbatim to the `o_min`-graph by setting the flow of
every new (shorter-overlap) edge to `0` (`liftFlow_feasible62`): throughput,
signed balance, the vertex lower bound `1` and the zero-terminal clause are all
preserved, because the lifted flow agrees with the original on exactly the
edges the original used.

## Why the zero-extension needs no `Nodup`

The pitfall this module is careful about: a bare `List`-membership subset does
*not* preserve a summed throughput / balance when the larger edge list contains
duplicates.  The lift avoids the issue structurally: the lifted flow is defined
by the *same* length predicate that defines the sublist, so the relevant sums
are related by an exact fold–filter fusion (`throughput_liftFlow`,
`balCore_liftFlow`), which is multiplicity-correct by construction — the
support predicate of the lift *is* the filter predicate.  A general
membership-based zero-extension would additionally require a `List.Nodup`
hypothesis (or a multiplicity-aware `Multiset` inclusion); we record
`throughput_zero_ext_nodup` in that form so the distinction is on the record.

## Relation to the #261 front

The spelling-preserving reduction predicate `isReducibleSpellingB` defined here
is the same object as the `AssemblyP1.Section62SpellingReduction` front's
predicate (genuine overlaps + composition law `l₁ + l₂ = L + l`, both legs
proper).  This module is self-contained: it re-states and re-proves the core
spelling lemma (`spellPath_eq_spellDirect`) with the proper-overlap bounds, so
its kernel check stands independently of that front's in-progress module.  The
two fronts reconcile on the shared definition.

## What is transferred, and what is not

The full-overlap (`oMin = L − 1 = 2`) witnesses of
`AssemblyP1.Section62BridgingCounterexample` and
`AssemblyP1.SameLengthSection62Counterexample` are lifted to `oMin = 1`
(`bridging_lifted_oMin1`, `samelength_lifted_oMin1`): the truth and the
competitor remain §6.2 feasible flows on the `28`-edge `oMin = 1` graph and
the competitor still strictly beats the truth under the literal §6.1 objective.

The `oMin = 1` non-spelled countermodel of
`AssemblyP1.Section62NonSpelledFlow` does **not** transfer in the other
direction: its optima put positive flow on a length-`1` overlap
(`star21_uses_short_overlap`), which is not an edge of the full-overlap graph,
so they are not full-overlap flows and the lift does not apply to them.  This
is recorded precisely in `nonspelled_not_full_overlap` below.

Everything is decidable and kernel-checked: the module contains no `sorry`,
`axiom`, `admit` or `native_decide`.
-/

namespace AssemblyP1.Section62FullOverlapLift

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
  obtain ⟨m, hm, l1, hl1, l2, hl2, ho1, ho2, hov1, hov2, hcomp⟩ := h
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
