import AssemblyP1.Section62AnchorSourceWords
import AssemblyP1.Section62AnchoredWindowBridge

/-!
# Generic anchor/window spelling identity (#284)

`Section62AnchorSourceWords.aligned_source_words` proves the *linear* anchor
identity for an arbitrary legal overlap path: the length-`L` word starting at
each accumulated extension anchor is the source strand of the corresponding
step. `Section62AnchoredWindowBridge.periodic_window_eq_drop_take` proves that a
periodic circular window of the aligned genome `X.take G` agrees with the linear
drop/take of the closed word `X` (seam `X.take L = X.drop G`, including `G < L`).

`Section62AnchorSourceWords.signed_circuit_anchors_are_read_words` composes these
two facts but only for the *graph-specific* closed signed overlap circuit, where
the seam and the positivity of the extension lengths come from the signed graph.
This module states and proves the **generic** `hAnchors` theorem the #284
interface asks for, decoupled from the graph: for any legally spelled closed
path with strictly positive extension lengths and a coherent seam, the anchored
periodic windows are exactly the visited source words, in order. The graph
theorem is the specialization where the seam is supplied by
`Section62SourceSignedSeamAdapter.signed_circuit_seam` and positivity by
`Section62AnchorSourceWords.graph_extensions_pos`.
-/

namespace AssemblyP1.Section62GenericAnchorSpelling

open AssemblyP1.Section62CircularStarts
open AssemblyP1.Section62OverlapSuffix
open AssemblyP1.Section62AnchorSourceWords
open AssemblyP1.Section62AnchoredWindowBridge
open AssemblyP1.Section62CircularWindowAdapter

variable {A : Type}

/-- The appended extension tails of a legal overlap path have total length equal
to the sum of the individual extension lengths. This is the word-level
`ValidPath` analogue of `pathTail_len_eq_extensions_sum`. -/
theorem appendedTails_length (L : Nat) :
    ∀ (steps : List (Nat × List A)) (u : List A),
      u.length = L → ValidPath L u steps →
      (appendedTails steps).length = (extensionsOf L steps).sum := by
  intro steps
  induction steps with
  | nil =>
      intro u hu hv
      simp [appendedTails, extensionsOf]
  | cons p rest ih =>
      rcases p with ⟨ell, v⟩
      intro u hu hv
      change v.length = L ∧ ell ≤ L ∧
        u.drop (L - ell) = v.take ell ∧ ValidPath L v rest at hv
      obtain ⟨hvlen, hell, hov, hrest⟩ := hv
      have hrec := ih v hvlen hrest
      simp only [appendedTails, extensionsOf] at hrec
      simp only [appendedTails, List.flatMap_cons, extensionsOf,
        List.map_cons, List.sum_cons, List.length_append, List.length_drop,
        hvlen]
      rw [hrec]

/-- **Generic `hAnchors`.**  Let `u` be a length-`L` start word, `steps` a legal
overlap path, `X = u ++ appendedTails steps` its linearized spelling, and
`G = (appendedTails steps).length`. If every extension length is positive and the
spelling is seam-coherent (`X.take L = X.drop G`), then the length-`L` periodic
windows of the aligned circular genome `X.take G` at the accumulated extension
anchors are exactly the visited source words, in order.

This is the abstract content of `CircularSpelling.hAnchors`, stated for an
arbitrary legal overlap path rather than for a signed graph circuit. -/
theorem generic_anchors_window_eq_sources (L : Nat) (default : A)
    (steps : List (Nat × List A)) (u : List A)
    (hu : u.length = L) (hv : ValidPath L u steps)
    (hpos : ∀ d ∈ extensionsOf L steps, 0 < d)
    (hseam : (u ++ appendedTails steps).take L =
      (u ++ appendedTails steps).drop (appendedTails steps).length) :
    (anchors 0 (extensionsOf L steps)).map
        (window ((u ++ appendedTails steps).take (appendedTails steps).length) L)
      = sources u steps := by
  have hlin := aligned_source_words L steps u hu hv
  have hlen := appendedTails_length L steps u hu hv
  rw [← hlin]
  apply List.map_congr_left
  intro s hs
  have hsBound : s < (extensionsOf L steps).sum :=
    anchors_lt_sum (extensionsOf L steps) hpos s hs
  have hsG : s < (appendedTails steps).length := by
    rw [hlen]; exact hsBound
  have hGpos : 0 < (appendedTails steps).length :=
    Nat.lt_of_le_of_lt (Nat.zero_le s) hsG
  have hXlen : (u ++ appendedTails steps).length =
      L + (appendedTails steps).length := by simp [hu]
  exact periodic_window_eq_drop_take (u ++ appendedTails steps) default
    (appendedTails steps).length L s hGpos hXlen hseam hsG

/-- The same statement with the seam and extension positivity discharged from
the two conditions that the signed overlap graph supplies: an explicit seam
identity and pointwise positivity of the extension blocks. This is the form the
`CircularSpelling` construction consumes. -/
theorem generic_circular_spelling_anchors (L : Nat) (default : A)
    (steps : List (Nat × List A)) (u : List A)
    (hu : u.length = L) (hv : ValidPath L u steps)
    (hpos : ∀ d ∈ extensionsOf L steps, 0 < d)
    (hseam : (u ++ appendedTails steps).take L =
      (u ++ appendedTails steps).drop (appendedTails steps).length) :
    (anchors 0 (extensionsOf L steps)).map
        (window ((u ++ appendedTails steps).take (appendedTails steps).length) L)
      = sources u steps :=
  generic_anchors_window_eq_sources L default steps u hu hv hpos hseam

#print axioms appendedTails_length
#print axioms generic_anchors_window_eq_sources
#print axioms generic_circular_spelling_anchors

end AssemblyP1.Section62GenericAnchorSpelling
