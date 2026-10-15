import Std

/-!
# Overlap-edge spelling preserves the current final read

For a legal overlap of length ell between length-L read strands u and v,
the word u ++ v.drop ell ends in the full word v. More generally, any longer
already-spelled word whose last L symbols form u will again end in v after
appending the ell-extension of v.

These lemmas isolate the elementary word identity that the #284 signed
bidirected-circuit-to-circular-genome theorem needs. The actual graph must
still supply legal overlap edges, a closed signed path and its visited-anchor
indices; the lemmas make no claims about arbitrary feasible flows.
-/

namespace AssemblyP1.Section62OverlapSuffix

/-- One legal overlap edge spells a word whose final read is its target. -/
theorem direct_spelling_ends_in_target {α : Type}
    (u v : List α) (L ell : Nat)
    (hu : u.length = L)
    (hEll : ell ≤ L)
    (hOverlap : u.drop (L - ell) = v.take ell) :
    (u ++ v.drop ell).drop (L - ell) = v := by
  rw [List.drop_append_of_le_length (by omega : L - ell ≤ u.length)]
  rw [hOverlap]
  exact List.take_append_drop ell v

/-- The suffix of an already spelled path updates to the new read when
a legal overlap extension is appended. This is the reusable induction step
for path-level spelling and the eventual circular seam theorem. -/
theorem appended_extension_ends_in_target {α : Type}
    (X u v : List α) (L ell : Nat)
    (hXL : L ≤ X.length)
    (hu : u.length = L)
    (hv : v.length = L)
    (hEll : ell ≤ L)
    (hLast : X.drop (X.length - L) = u)
    (hOverlap : u.drop (L - ell) = v.take ell) :
    (X ++ v.drop ell).drop ((X ++ v.drop ell).length - L) = v := by
  have hindex : (X ++ v.drop ell).length - L = X.length - ell := by
    simp only [List.length_append, List.length_drop, hv]
    omega
  rw [hindex]
  rw [List.drop_append_of_le_length (by omega : X.length - ell ≤ X.length)]
  have hadd : X.length - L + (L - ell) = X.length - ell := by omega
  have hshift : X.drop (X.length - ell) =
      (X.drop (X.length - L)).drop (L - ell) := by
    rw [List.drop_drop, hadd]
  rw [hshift, hLast, hOverlap]
  exact List.take_append_drop ell v


/-! ## Arbitrarily long overlap-edge sequences

The next definitions are list-level analogues of a signed path's successive
read strands and overlap lengths. Their legality predicate records only
the word-overlap facts; graph-level strand signs and edge membership are
separate obligations.
-/

/-- Append each visited read's nonoverlapping suffix to the spelling. -/
def pathExt {α : Type} (X : List α) : List (Nat × List α) → List α
  | [] => X
  | (ell, v) :: rest => pathExt (X ++ v.drop ell) rest

/-- The last read encountered along a sequence of overlap extensions. -/
def pathTarget {α : Type} (u : List α) : List (Nat × List α) → List α
  | [] => u
  | (_, v) :: rest => pathTarget v rest

/-- Every step is an equal-read-length legal suffix/prefix overlap. -/
def ValidPath {α : Type} (L : Nat) (u : List α) :
    List (Nat × List α) → Prop
  | [] => True
  | (ell, v) :: rest =>
      v.length = L ∧ ell ≤ L ∧ u.drop (L - ell) = v.take ell ∧
      ValidPath L v rest

/-- A legal overlap walk's spelled word ends in its final visited read. -/
theorem pathExt_ends_in_target {α : Type} (L : Nat) :
    ∀ (steps : List (Nat × List α)) (X u : List α),
      L ≤ X.length →
      u.length = L →
      X.drop (X.length - L) = u →
      ValidPath L u steps →
      (pathExt X steps).drop ((pathExt X steps).length - L) =
        pathTarget u steps := by
  intro steps
  induction steps with
  | nil =>
      intro X u hXL hu hLast hvalid
      simpa [pathExt, pathTarget] using hLast
  | cons p rest ih =>
      rcases p with ⟨ell, v⟩
      intro X u hXL hu hLast hvalid
      change v.length = L ∧ ell ≤ L ∧
          u.drop (L - ell) = v.take ell ∧ ValidPath L v rest at hvalid
      obtain ⟨hv, hell, hov, hrest⟩ := hvalid
      have hXL' : L ≤ (X ++ v.drop ell).length := by
        simp only [List.length_append]
        omega
      have hnew :=
        appended_extension_ends_in_target X u v L ell hXL hu hv hell hLast hov
      exact ih (X ++ v.drop ell) v hXL' hv hnew hrest

/-- Spelling along the walk factors as initial read plus all edge tails. -/
theorem pathExt_eq_append_tails {α : Type}
    (X : List α) (steps : List (Nat × List α)) :
    pathExt X steps =
      X ++ steps.flatMap (fun p => p.2.drop p.1) := by
  induction steps generalizing X with
  | nil => simp [pathExt]
  | cons p rest ih =>
      rcases p with ⟨ell, v⟩
      simp only [pathExt, List.flatMap_cons]
      rw [ih]
      simp [List.append_assoc]

/-- Closing the last read back to the first read forces the exact length-L
cyclic seam. This is the graph-independent bridge to seam_periodic, including
when the total extension length G is shorter than a read. -/
theorem closed_path_seam {α : Type} (L : Nat)
    (start : List α) (steps : List (Nat × List α))
    (hStart : start.length = L)
    (hValid : ValidPath L start steps)
    (hClose : pathTarget start steps = start) :
    let tails := steps.flatMap (fun p => p.2.drop p.1)
    let X := start ++ tails
    X.take L = X.drop tails.length := by
  let tails := steps.flatMap (fun p => p.2.drop p.1)
  let X := start ++ tails
  have hLast : (pathExt start steps).drop
      ((pathExt start steps).length - L) = pathTarget start steps :=
    pathExt_ends_in_target L steps start start (by simp [hStart]) hStart
      (by simp [hStart]) hValid
  rw [pathExt_eq_append_tails, hClose] at hLast
  have hlen : (start ++ tails).length - L = tails.length := by
    simp [hStart]
  change (start ++ tails).drop ((start ++ tails).length - L) = start at hLast
  rw [hlen] at hLast
  change (start ++ tails).take L = (start ++ tails).drop tails.length
  simpa [hStart] using hLast.symm

#print axioms direct_spelling_ends_in_target
#print axioms appended_extension_ends_in_target
#print axioms pathExt_ends_in_target
#print axioms pathExt_eq_append_tails
#print axioms closed_path_seam

end AssemblyP1.Section62OverlapSuffix
