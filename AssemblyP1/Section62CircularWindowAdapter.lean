import AssemblyP1.Section62CircularStarts
import AssemblyP1.Section62GlobalCircularAudit

/-!
# The circular spelling adapter (#284, MB09 Observation 7)

This module is the missing *adapter* between the two kernel-checked halves of the
corrected §6.2 model and MB09 Observation 7:

* `Section62CircularStarts` proves the abstract cyclic-start partition identity
  `C(c) = V(c) + (skipped internal windows)` and its iff criterion for any
  class-valued function of genomic starts;
* `Section62SkippedWindowFactor` / `Section62GlobalCircularAudit` prove that no
  *surviving* reduced edge of a signed walk can skip an observed internal read
  strand.

The two halves are stated about different objects: the first about an abstract
`f : Nat → W`, the second about `spellDirect` internal windows of edges.  The
adapter here instantiates the abstract partition with the *length-`readLen`
circular window of the spelled genome* and records the spelling hypotheses that
tie the anchored windows to the signed-walk vertices.  Those hypotheses are the
ones the source note `docs/section62-observation7-skipped-windows.md` says "should
be formalized separately rather than inferred from a bare list of graph
vertices": the `j`-th anchor is the read visited by the `j`-th edge, the
extensions agree with the spelled genome, and the circular seam is coherent.

## What is proved here

Given a genome `D` and a signed walk `walk` of `overlapEdges` edges together with
the spelling hypotheses `CircularSpelling`:

* `window_count_decomposition` — the exact partition identity (1) of the note,
  `C_D(w) = V(w) + (internal windows of word w)`;
* `window_count_eq_anchors_iff` — the iff criterion (2);
* `observation7_window_count` — MB09 Observation 7 for the *word* classes: for
  every observed strand `m`, the number of circular `readLen`-windows of `D` whose
  word is `toList m` equals the number of walk vertices whose word is `toList m`.

## What is *not* proved here

The canonical construction of the circular genome `D` from a signed walk and the
proof that it satisfies the `CircularSpelling` hypotheses (the coherence of the
signed overlap data across the seam) remain the next obligation; this module is
the composition interface, not that construction.  Equivalence to the full
Myers 2005 algorithm and the full genome ML lift remain open.
-/

namespace AssemblyP1.Section62CircularWindowAdapter

open AssemblyP1.Section62CircularStarts
open Section62Flow Section62SpellingReductionCandidate

variable {A W : Type}

/-- The length-`readLen` periodic window of the circular genome `D` starting
at `s`, with letters indexed modulo `D.length`.  In particular a read can
wrap around the genome seam *multiple times* when `0 < D.length < readLen`.
The empty word has no circular positions and produces the empty window. -/
def window (D : List A) (readLen s : Nat) : List A :=
  if h : 0 < D.length then
    (List.range readLen).map (fun i =>
      D.get ⟨(s + i) % D.length, Nat.mod_lt _ h⟩)
  else []

/-- Every window of a nonempty circular genome has exactly the requested
read length, even when the read is longer than the genome. -/
theorem window_length_of_nonempty (D : List A) (readLen s : Nat)
    (hD : 0 < D.length) : (window D readLen s).length = readLen := by
  simp [window, hD]

/-- Regression: read length 3 wraps across the seam of the length-2 circle. -/
example : window ([true, false] : List Bool) 3 0 = [true, false, true] := by
  decide

/-- Regression: repeated wrapping, including a nonzero starting offset. -/
example : window ([true, false] : List Bool) 5 1 =
    [false, true, false, true, false] := by
  decide

/-- The extension length `readLen − e.len` contributed by an overlap edge: the
number of new letters the edge adds past the first read. -/
def extension [DecidableEq W] (readLen : Nat) (e : BdEdge A W) : Nat := readLen - e.len

/-- The list of extension lengths of a walk, in order. -/
def extensions [DecidableEq W] (readLen : Nat) (walk : List (BdEdge A W)) : List Nat :=
  walk.map (extension readLen)

/-- Count occurrences of the word `w` in a list of words.  Uses `List.countP`
(hence only `DecidableEq`), avoiding the `BEq`/`DecidableEq` instance diamond that
`List.count` would introduce at the type `List A`. -/
def wordCount [DecidableEq A] (w : List A) (l : List (List A)) : Nat :=
  l.countP (fun x => decide (x = w))

/-- Counting is additive over list concatenation. -/
theorem wordCount_append [DecidableEq A] (w : List A) (l₁ l₂ : List (List A)) :
    wordCount w (l₁ ++ l₂) = wordCount w l₁ + wordCount w l₂ := by
  unfold wordCount
  rw [List.countP_append]

/-- Counting over a cons. -/
theorem wordCount_cons [DecidableEq A] (w x : List A) (l : List (List A)) :
    wordCount w (x :: l) = wordCount w l + (if decide (x = w) = true then 1 else 0) := by
  unfold wordCount
  rw [List.countP_cons]

/-- A word list in which no member equals `w` has zero `w`-count. -/
theorem wordCount_eq_zero_of [DecidableEq A] (w : List A) (l : List (List A))
    (h : ∀ x ∈ l, x ≠ w) : wordCount w l = 0 := by
  unfold wordCount
  rw [List.countP_eq_zero]
  intro x hx hpx
  exact h x hx (of_decide_eq_true hpx)

/-- The spelling hypotheses of a coherent circular spelling of the signed walk
`walk` by the genome `D`.  They are stated at the level of the concrete window
function so that the abstract partition identity applies directly:

* `hLength` — the spelled genome length is the sum of the extensions;
* `hAnchors` — the anchored windows are exactly the visited read strands, in
  order (the `j`-th anchor is the read visited by the `j`-th edge);
* `hInteriorSkipped` — no skipped internal window spells an observed strand. -/
structure CircularSpelling [DecidableEq A] [DecidableEq W] (toList : W → List A) (rc : W → W)
    (readLen oMin : Nat) (verts : List W) (walk : List (BdEdge A W)) (D : List A) : Prop where
  /-- The spelled genome length is the sum of the edge extensions. -/
  hLength : D.length = (extensions readLen walk).sum
  /-- The anchored windows are the visited read strands, in order. -/
  hAnchors : (anchors 0 (extensions readLen walk)).map (window D readLen) =
    walk.map (fun e => toList e.sx)
  /-- No skipped internal window spells an observed strand. -/
  hInteriorSkipped : ∀ m ∈ strandsOf rc verts,
    wordCount (toList m) ((interiors 0 (extensions readLen walk)).map (window D readLen)) = 0

/-- **Exact partition identity (1).**  The circular `readLen`-window counts of the
spelled genome split into the anchored (visited) windows and the skipped internal
windows, for any word `w`.  This is the cyclic-start partition of
`Section62CircularStarts`, instantiated at the circular window function. -/
theorem window_count_decomposition [DecidableEq A]
    (D : List A) (readLen start : Nat) (ds : List Nat) (w : List A)
    (hpos : ∀ d ∈ ds, 0 < d) :
    wordCount w ((covered start ds).map (window D readLen)) =
      wordCount w ((anchors start ds).map (window D readLen)) +
        wordCount w ((interiors start ds).map (window D readLen)) := by
  induction ds generalizing start with
  | nil => simp [covered, anchors, interiors, wordCount]
  | cons d ds ih =>
    have hd : 0 < d := hpos d (by simp)
    have hrest : ∀ x ∈ ds, 0 < x := fun x hx => hpos x (by simp [hx])
    have hi := ih (start + d) hrest
    unfold covered anchors interiors
    simp only [List.map_append, List.map_cons]
    rw [interval_head_and_internal start d hd, List.map_cons]
    simp only [wordCount_append, wordCount_cons]
    rw [hi]
    split_ifs <;> omega

/-- **Iff criterion (2).**  The circular window count of a word equals its anchored
visit count exactly when no skipped internal window spells that word. -/
theorem window_count_eq_anchors_iff [DecidableEq A]
    (D : List A) (readLen start : Nat) (ds : List Nat) (w : List A)
    (hpos : ∀ d ∈ ds, 0 < d) :
    wordCount w ((covered start ds).map (window D readLen)) =
      wordCount w ((anchors start ds).map (window D readLen)) ↔
      wordCount w ((interiors start ds).map (window D readLen)) = 0 := by
  rw [window_count_decomposition D readLen start ds w hpos]
  omega

/-- The `covered` list with the genome length substituted for the extension sum:
the circular starts are exactly `0, …, D.length − 1`. -/
theorem covered_eq_range_of_length [DecidableEq W]
    (D : List A) (readLen : Nat) (walk : List (BdEdge A W))
    (hLength : D.length = (extensions readLen walk).sum) :
    covered 0 (extensions readLen walk) = List.range D.length := by
  rw [covered_zero_eq_all_starts, hLength]

/-- **A pointwise no-observed-window hypothesis forces a zero internal count.**
This is the bridge to `Section62GlobalCircularAudit`: the surviving-edge no-skip
theorem is pointwise (per internal offset), and this lemma turns it into the
count-zero hypothesis the partition identity consumes. -/
theorem interior_count_zero_of_pointwise [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (D : List A) (readLen : Nat)
    (walk : List (BdEdge A W)) (m : W)
    (h : ∀ s ∈ interiors 0 (extensions readLen walk), window D readLen s ≠ toList m) :
    wordCount (toList m) ((interiors 0 (extensions readLen walk)).map (window D readLen)) = 0 := by
  apply wordCount_eq_zero_of
  intro x hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
  exact h s hs

/-- **MB09 Observation 7 for word classes.**  For a coherent circular spelling of
a signed walk by the genome `D`, for every observed strand `m` the number of
circular `readLen`-windows of `D` spelling `toList m` equals the number of walk
vertices spelling `toList m`.  This is the exact occurrence-count content of
Observation 7 for the spelling-preserving candidate. -/
theorem observation7_window_count [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rc : W → W) (readLen oMin : Nat) (verts : List W)
    (walk : List (BdEdge A W)) (D : List A)
    (hsp : CircularSpelling toList rc readLen oMin verts walk D)
    (hpos : ∀ d ∈ extensions readLen walk, 0 < d) (m : W) (hm : m ∈ strandsOf rc verts) :
    wordCount (toList m) ((covered 0 (extensions readLen walk)).map (window D readLen)) =
      wordCount (toList m) (walk.map (fun e => toList e.sx)) := by
  rw [window_count_decomposition D readLen 0 (extensions readLen walk) (toList m) hpos,
    hsp.hAnchors, hsp.hInteriorSkipped m hm, Nat.add_zero]

/-- The same identity with the `covered` list written as all genomic starts. -/
theorem observation7_range_count [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rc : W → W) (readLen oMin : Nat) (verts : List W)
    (walk : List (BdEdge A W)) (D : List A)
    (hsp : CircularSpelling toList rc readLen oMin verts walk D)
    (hpos : ∀ d ∈ extensions readLen walk, 0 < d) (m : W) (hm : m ∈ strandsOf rc verts) :
    wordCount (toList m) ((List.range D.length).map (window D readLen)) =
      wordCount (toList m) (walk.map (fun e => toList e.sx)) := by
  rw [← covered_eq_range_of_length D readLen walk hsp.hLength]
  exact observation7_window_count toList rc readLen oMin verts walk D hsp hpos m hm

#print axioms window_count_decomposition
#print axioms window_count_eq_anchors_iff
#print axioms interior_count_zero_of_pointwise
#print axioms observation7_window_count
#print axioms observation7_range_count

end AssemblyP1.Section62CircularWindowAdapter
