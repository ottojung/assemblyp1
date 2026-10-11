import AssemblyP1.Section62BidirectedFlow

/-!
# Spelling-preserving transitive edge reduction for MB09 §6.2 (issue #261)

This module implements the **correct** spelling-preserving transitive edge
reduction for the MB09 §6.2 bidirected overlap graph at arbitrary
`o_min ≤ L − 1`, replacing the two broken readings in
`AssemblyP1.Section62Flow` (`isReducibleB`, which is arithmetically vacuous, and
`isReducibleLongerB`, which does not check spelling equality).

## The reduction lemma

With uniform read length `L`, a direct `sx → sy` overlap of length
`l` (`0 < l < L`) spells the word `W = sx ++ sy.drop l`.  A two-edge path
`sx → m` (overlap `l1`) and `m → sy` (overlap `l2`) spells the same `W` **iff**

1. `l1`, `l2` are proper overlaps (`l1 < L`, `l2 < L`) and the direct overlap
   is proper (`l < L`),
2. `suffix l1 sx = prefix l1 m` and `suffix l2 m = prefix l2 sy`
   (the overlaps are genuine),
3. `l1 + l2 = L + l` (the composition law: the two-leg path spells a word of
   length `3L − l1 − l2`, the direct edge a word of length `2L − l`; equality
   forces `l1 + l2 = L + l`).

Conditions (2) and (3) are the mathematical core; (1) is the graph-validity
wrapper.  The core is the theorem `spellPath_eq_spellDirect`: under (1)–(3) the
two spellings are definitionally the same word, with no further hypothesis.

## Why the proper-overlap bounds are necessary (kernel-checked)

The composition law `l1 + l2 = L + l` together with the genuine-overlap
hypotheses does **not** by itself force `l1, l2 < L`.  With `L = 4`,
`sx = m = [0,1,2,3]`, `sy = [3,2,1,0]`, `l1 = 5`, `l2 = 0`, `l = 1` we have
`5 + 0 = 4 + 1` and both overlap hypotheses hold, yet the path spells
`[0,1,2,3,3,2,1,0]` while the direct edge spells `[0,1,2,3,2,1,0]`.  Hence the
earlier unbounded reading is false; the bounds are added as explicit hypotheses
and their necessity is witnessed by `bounds_necessary_counterexample`.

## What was wrong before

* `isReducibleB` requires `l1 < l` and `l2 < l` (both legs *shorter* than the
  direct overlap) *and* `l1 + l2 − L = l`.  These are contradictory: `l1, l2 < l`
  gives `l1 + l2 < 2l`, so `L + l < 2l`, i.e. `L < l`, contradicting the
  proper overlap `l < L`.  Hence `isReducibleB` can never fire.
* `isReducibleLongerB` only checks that each leg is longer than `l`; it does not
  require the spelled words to agree, so it can delete edges whose removal
  changes the language of spelled molecules.

The predicate `isReducibleSpellingB` below requires the genuine overlap
conditions and the composition law, and nothing else.
-/

namespace AssemblyP1.Section62SpellingReduction

open Section62Flow

variable {A : Type} [DecidableEq A]

/-! ## The spelling of an overlap -/

/-- The word spelled by a direct overlap of length `l` from `sx` to `sy`:
`sx` followed by the part of `sy` past the overlap. -/
def spellDirect (sx sy : List A) (l : Nat) : List A := sx ++ sy.drop l

/-- The word spelled by a two-edge overlap path `sx → m → sy` with overlaps
`l1`, `l2`: `sx`, then the part of `m` past the first overlap, then the part of
`sy` past the second overlap. -/
def spellPath (sx m sy : List A) (l1 l2 : Nat) : List A :=
  sx ++ m.drop l1 ++ sy.drop l2

/-! ## The proper-overlap bounds are necessary (kernel-checked witness) -/

/-- The departure strand of the counterexample: `ABCD`. -/
def cx : List (Fin 4) := [0, 1, 2, 3]

/-- The intermediate strand: `ABCD` (equal to `cx`, so the first "overlap" is
the trivial full-word identity). -/
def cm : List (Fin 4) := [0, 1, 2, 3]

/-- The arrival strand: `WXYZ`. -/
def cy : List (Fin 4) := [3, 2, 1, 0]

/-- The composition law `5 + 0 = 4 + 1` holds in the counterexample. -/
theorem counter_h3 : 5 + 0 = 4 + 1 := by decide

/-- The first "overlap" is genuine: `suffix 5 cx = prefix 5 cm` (both are the
whole word, because `5 > L = 4` saturates both `drop` and `take`). -/
theorem counter_h1 : sufOf cx 5 = preOf cm 5 := by decide

/-- The second "overlap" is genuine: `suffix 0 cm = prefix 0 sy` (both empty). -/
theorem counter_h2 : sufOf cm 0 = preOf cy 0 := by decide

/-- **The bounds are necessary.**  With `L = 4`, `l1 = 5`, `l2 = 0`, `l = 1`
the composition law and both overlap hypotheses hold, yet the path spells
`[0,1,2,3,3,2,1,0]` while the direct edge spells `[0,1,2,3,2,1,0]`.  Hence any
correct reduction lemma must exclude `l1 ≥ L` (and, symmetrically, `l2 ≥ L`,
`l ≥ L`). -/
theorem bounds_necessary_counterexample :
    ¬ (spellPath cx cm cy 5 0 = spellDirect cx cy 1) := by
  unfold spellPath spellDirect
  decide

/-! ## The core reduction lemma -/

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

omit [DecidableEq A] in
/-- **Spelling-preserving reduction lemma (issue #261).**

For three reads `sx`, `m`, `sy` of common length `L`, if the first overlap
genuinely places `m` after `sx` (`suffix l1 sx = prefix l1 m`), the second
genuinely places `sy` after `m` (`suffix l2 m = prefix l2 sy`), all three
overlaps are proper (`l1 < L`, `l2 < L`, `l < L`), and the composition law
`l1 + l2 = L + l` holds, then the two-edge path spells exactly the same word as
the direct `l`-overlap from `sx` to `sy`.

No further hypothesis is needed: the conclusion is the word equality, which is
the content of "the path spells the same `W`".
-/
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

omit [DecidableEq A] in
/-- The converse: if the two spellings agree and the path overlaps are genuine,
then the composition law holds.  (Length argument; the proper-overlap bounds
are needed so that the truncated-subtraction lengths are `L − l1` etc.) -/
theorem spellDirect_eq_spellPath {L l1 l2 l : Nat} {sx m sy : List A}
    (hsx : sx.length = L) (hm : m.length = L) (hsy : sy.length = L)
    (hl1 : l1 ≤ L) (hl2 : l2 ≤ L) (hl : l ≤ L)
    (_h1 : sufOf sx l1 = preOf m l1) (_h2 : sufOf m l2 = preOf sy l2)
    (heq : spellPath sx m sy l1 l2 = spellDirect sx sy l) :
    l1 + l2 = L + l := by
  unfold spellPath spellDirect at heq
  have hlen : (sx ++ m.drop l1 ++ sy.drop l2).length = (sx ++ sy.drop l).length :=
    congrArg List.length heq
  simp only [List.length_append, List.length_drop, hsx, hm, hsy] at hlen
  omega

omit [DecidableEq A] in
/-- The reduction lemma as a genuine iff, combining both directions. -/
theorem spellPath_eq_spellDirect_iff {L l1 l2 l : Nat} {sx m sy : List A}
    (hsx : sx.length = L) (hm : m.length = L) (hsy : sy.length = L)
    (hl1 : l1 < L) (hl2 : l2 < L) (hl : l < L)
    (h1 : sufOf sx l1 = preOf m l1) (h2 : sufOf m l2 = preOf sy l2) :
    spellPath sx m sy l1 l2 = spellDirect sx sy l ↔ l1 + l2 = L + l :=
  ⟨fun heq => spellDirect_eq_spellPath hsx hm hsy (by omega) (by omega) (by omega) h1 h2 heq,
   fun h3 => spellPath_eq_spellDirect hsx hm hsy hl1 hl2 hl h1 h2 h3⟩

/-! ## The graph-level reduction predicate -/

/-- Whether the direct edge `e : sx → sy` of overlap `e.len` is **spelling-
preservingly reducible**: there exists an intermediate molecule class `m` and
proper overlap lengths `l1`, `l2` (both `≥ oMin`, so the path edges exist in the
graph) such that

* the path overlaps are genuine (`sufOf sx l1 = preOf m l1`,
  `sufOf m l2 = preOf sy l2`),
* the composition law `l1 + l2 = L + e.len` holds.

By `spellPath_eq_spellDirect`, these conditions are exactly "the two-edge path
spells the same word as the direct edge", so removing the direct edge preserves
the language of spelled molecules.  The signed-incidence condition is automatic
in the molecule-class model (see the module docstring). -/
def isReducibleSpellingB (A : Type) (W : Type) [DecidableEq A] [DecidableEq W]
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
def isReducibleSpelling (A : Type) (W : Type) [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rc : W → W) (readLen oMin : Nat) (verts : List W)
    (e : BdEdge A W) : Prop :=
  isReducibleSpellingB A W toList rc readLen oMin verts e = true

/-- The transitively reduced bidirected overlap graph under the spelling-
preserving reading: those edges not spelling-preservingly reducible. -/
def transitivelyReducedSpelling (A : Type) (W : Type) [DecidableEq A]
    [DecidableEq W] (toList : W → List A) (rc : W → W) (readLen oMin : Nat)
    (verts : List W) (edges : List (BdEdge A W)) : List (BdEdge A W) :=
  edges.filter (fun e => !isReducibleSpellingB A W toList rc readLen oMin verts e)

/-- No edge of `edges` is spelling-preservingly reducible. -/
def ReductionSpellingVacuous (A : Type) (W : Type) [DecidableEq A]
    [DecidableEq W] (toList : W → List A) (rc : W → W) (readLen oMin : Nat)
    (verts : List W) (edges : List (BdEdge A W)) : Prop :=
  edges.all (fun e => !isReducibleSpellingB A W toList rc readLen oMin verts e) = true

end AssemblyP1.Section62SpellingReduction
