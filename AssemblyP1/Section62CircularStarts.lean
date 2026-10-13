import Mathlib.Data.List.Intervals
import Mathlib.Tactic

/-!
Finite interval decomposition for cyclic-start accounting in Observation 7.
Independent of string graph probability and strand orientation.
-/

namespace AssemblyP1.Section62CircularStarts

/-- Enumerate every genomic start covered by consecutively appended extension
blocks, beginning at start. A block of size d contributes [start,start+d). -/
def covered (start : Nat) : List Nat → List Nat
  | [] => []
  | d :: ds => List.Ico start (start + d) ++ covered (start + d) ds

/-- Consecutive length blocks cover exactly the contiguous set of starts
[start, start + total extension length), without gaps or duplications. -/
theorem covered_eq_interval (start : Nat) (ds : List Nat) :
    covered start ds = List.Ico start (start + ds.sum) := by
  induction ds generalizing start with
  | nil =>
    simp [covered]
  | cons d ds ih =>
    simp only [covered, List.sum_cons]
    rw [ih]
    have h := List.Ico.append_consecutive
      (n := start) (m := start + d) (l := start + (d + ds.sum))
      (by omega) (by omega)
    simpa [Nat.add_assoc] using h

#print axioms covered_eq_interval



/-- A positive extension contributes its anchor and all remaining internal starts. -/
theorem interval_head_and_internal (start d : Nat) (hd : 0 < d) :
    List.Ico start (start + d) =
      start :: List.Ico (start + 1) (start + d) := by
  cases d with
  | zero => omega
  | succ k =>
    simp [List.Ico, List.range'_succ]
    omega



/-- The genomic start of each visited read vertex in a coherent walk. -/
def anchors (start : Nat) : List Nat → List Nat
  | [] => []
  | d :: ds => start :: anchors (start + d) ds

/-- Genomic starts lying strictly inside a traversal extension. -/
def interiors (start : Nat) : List Nat → List Nat
  | [] => []
  | d :: ds => List.Ico (start + 1) (start + d) ++ interiors (start + d) ds

/-- Every positive-length extension's start partition has one anchor and
all remaining interior starts, counted with arbitrary nonnegative weights. -/
theorem covered_weight_sum (f : Nat → Nat) (start : Nat)
    (ds : List Nat) (hpos : ∀ d ∈ ds, 0 < d) :
    ((covered start ds).map f).sum =
      ((anchors start ds).map f).sum + ((interiors start ds).map f).sum := by
  induction ds generalizing start with
  | nil => simp [covered, anchors, interiors]
  | cons d ds ih =>
    have hd : 0 < d := hpos d (by simp)
    have hrest : ∀ x ∈ ds, 0 < x := by
      intro x hx
      exact hpos x (by simp [hx])
    have hi := ih (start + d) hrest
    simp only [covered, anchors, interiors, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons]
    rw [interval_head_and_internal start d hd]
    simp only [List.map_cons, List.sum_cons]
    omega

#print axioms covered_weight_sum



/-- Exact occurrence-count partition for any assignment of a genomic read
class to a start position. Anchor visits and interior starts are disjoint. -/
theorem covered_class_count {W : Type} [DecidableEq W]
    (f : Nat → W) (c : W) (start : Nat)
    (ds : List Nat) (hpos : ∀ d ∈ ds, 0 < d) :
    ((covered start ds).map f).count c =
      ((anchors start ds).map f).count c +
        ((interiors start ds).map f).count c := by
  induction ds generalizing start with
  | nil => simp [covered, anchors, interiors]
  | cons d ds ih =>
    have hd : 0 < d := hpos d (by simp)
    have hrest : ∀ x ∈ ds, 0 < x := by
      intro x hx
      exact hpos x (by simp [hx])
    have hi := ih (start + d) hrest
    simp only [covered, anchors, interiors, List.map_append, List.count_append,
      List.map_cons, List.count_cons]
    rw [interval_head_and_internal start d hd]
    simp only [List.map_cons, List.count_cons]
    omega

#print axioms covered_class_count



/-- Equality between all sampled windows of one class and visits of that
class holds exactly when none of the skipped internal starts has that class. -/
theorem covered_count_eq_anchors_iff_no_internal {W : Type} [DecidableEq W]
    (f : Nat → W) (c : W) (start : Nat) (ds : List Nat)
    (hpos : ∀ d ∈ ds, 0 < d) :
    ((covered start ds).map f).count c =
      ((anchors start ds).map f).count c ↔
      ((interiors start ds).map f).count c = 0 := by
  rw [covered_class_count f c start ds hpos]
  omega

#print axioms covered_count_eq_anchors_iff_no_internal



/-- For a circular genome spelled by positive extensions with total length G,
the linearized start list is exactly the G possible cyclic start indices. -/
theorem covered_zero_eq_all_starts (ds : List Nat) :
    covered 0 ds = List.range ds.sum := by
  rw [covered_eq_interval]
  simpa using List.Ico.zero_bot ds.sum

#print axioms covered_zero_eq_all_starts

end AssemblyP1.Section62CircularStarts
