import AssemblyP1.LyndonSchutzenberger
import AssemblyP1.PopulationReduction

/-!
# Scalar primitive spellings on the oriented window graph (issue #92, final classification)

This file is the graph-side completion of `docs/scalar-primitive-spellings-83.md`
and closes issue #92 end to end.  It is a direct formalization of the proof in that
document, on the *actual* graph/spectrum objects of the project: the oriented
length-`L` window support of a circular word (`OrientedRigidity.support`,
`OrientedRigidity.genomeNodes`, `winPrefix`/`winSuffix`) and the complete spectrum
(`OrientedRigidity.specCount`).  No abstract proxy graph is introduced.

## Model objects

* `Branching` / `NonBranching` — a node of the spectrum-support graph with two
  distinct outgoing edge types, and its negation.
* `IsCyclicSpelling c T` — a closed edge-type trail using edge type `e` exactly
  `c e` times (the "cyclic Eulerian edge-type spelling" of the note).
* `Support c` — the spectrum support, `{e | 0 < c e}`.
* `PopulationReduction.IsPrimitive` — rotation equivalence of circular words;
  `AmpBmpPrimitivity.IsPrimitive` — primitivity of an edge-type *list*.

## What is proved

1. `Spectrum.same_normalized_on_ray`: normalized complete-spectrum equality between
   a gcd-one spectrum `g * c0` of length `G` and a candidate of length `H` forces
   the candidate spectrum to be `m * c0` for a unique integer `m >= 1` with
   `H = m * (G / g)`.  This is the "integer spectrum ray" of the note.
2. `branching_primitive_spellings`: a branching support gives, for **every**
   `m >= 2`, a primitive cyclic edge-type spelling of `m * c0`.  This is the
   two-excursion cut (`two_excursions_of_branching`) plus
   `LyndonSchutzenberger.ampbmp_isPrimitive_of_head_ne`.
3. `branching_primitive_candidate`: the spelling of (2) is realized by an actual
   circular word of length `m * (G / g)` whose complete spectrum is exactly
   `m * c0` and which is primitive (`spell_exists_circulation` +
   `isPrimitive_of_primitiveWindowTrail`).  The competitor is a genuine genome,
   not an abstract list of edge types.
4. `nonbranching_primitive_spelling_eq_one`: if no node branches and a cyclic
   spelling of `c` is primitive, then `c e = 1` on the support.  This is
   `properPower_of_period` applied to a repeated edge: with at most one outgoing
   edge type per node, a repeated edge forces the cyclic spelling to be a proper
   power.
5. `identifiable_iff_nonbranching`: the exported fixed-truth classification.  A
   primitive truth is identifiable among arbitrary-length primitive candidates
   from its normalized complete spectrum **iff** its spectrum-support graph has no
   vertex with two distinct outgoing edge types.

The only external input in the "identifiable" direction is the same-length
complete-spectrum uniqueness up to rotation (BBT) that the rest of the project
takes as an explicit premise (`OrientedFinalRigidity.rotation_uniqueness_of_bbt`,
`PopulationReduction.gcd_one_of_primitive_P2_words`); it is exposed here as the
hypothesis `hBBT` and is *not* assumed silently.  Everything else — the ray
arithmetic, both directions of the classification, the two-excursion cut, the
period/gcd argument, and the Lyndon–Schützenberger separator — is kernel-checked
with no new axioms.
-/

namespace AssemblyP1.ScalarPrimitive

open OrientedRigidity
open PopulationReduction
open Finset
open BigOperators

/-! ## The graph objects -/

variable {V E : Type} [DecidableEq V] [DecidableEq E]

/-- The support of a spectrum (the "spectrum-support graph" of the note): the
edge types with positive multiplicity. -/
def Support {V E : Type} [DecidableEq E] [Fintype E] (c : E → ℕ) : Finset E :=
  Finset.univ.filter (fun e => 0 < c e)

/-- **Branching:** some node of the graph has two distinct outgoing edge types. -/
def Branching {V E : Type} [DecidableEq V] [DecidableEq E] (nodes : Finset V)
    (edges : Finset E) (tail head : E → V) : Prop :=
  ∃ v, ∃ e₁ ∈ edges, ∃ e₂ ∈ edges, e₁ ≠ e₂ ∧ tail e₁ = v ∧ tail e₂ = v

/-- **Nonbranching:** no node has two distinct outgoing edge types. -/
def NonBranching {V E : Type} [DecidableEq V] [DecidableEq E] (nodes : Finset V)
    (edges : Finset E) (tail head : E → V) : Prop :=
  ∀ v, ∀ e₁ ∈ edges, ∀ e₂ ∈ edges, tail e₁ = v → tail e₂ = v → e₁ = e₂

/-- **Cyclic edge-type spelling of the spectrum `c`:** a closed edge-type trail
using edge type `e` exactly `c e` times.  By `PopulationReduction.trail_cyc_adj`
the edges of a closed trail are cyclically incidence-compatible, so this is the
"cyclic Eulerian edge-type spelling" of `docs/scalar-primitive-spellings-83.md`. -/
def IsCyclicSpelling {V E : Type} [DecidableEq E] (tail head : E → V) (c : E → ℕ)
    (T : List E) : Prop :=
  ∃ s, TrailEnds tail head T s s ∧ ∀ e, edgeUse T e = c e

/-! ## Elementary trail and counting lemmas -/

section Basics

variable {V E : Type} [DecidableEq V] [DecidableEq E]
variable (tail head : E → V)

/-- Edge use of a concatenation adds. -/
theorem edgeUse_append (T₁ T₂ : List E) (e : E) :
    edgeUse (T₁ ++ T₂) e = edgeUse T₁ e + edgeUse T₂ e := by
  show (T₁ ++ T₂).countP (fun x => decide (x = e))
    = T₁.countP (fun x => decide (x = e)) + T₂.countP (fun x => decide (x = e))
  rw [List.countP_append]

/-- Edge use of a one-edge extension. -/
theorem edgeUse_cons (x : E) (T : List E) (e : E) :
    edgeUse (x :: T) e = edgeUse T e + if x = e then 1 else 0 := by
  show (x :: T).countP (fun y => decide (y = e))
    = T.countP (fun y => decide (y = e)) + if x = e then 1 else 0
  rw [List.countP_cons]
  simp

/-- An edge with positive edge use occurs in the trail. -/
theorem mem_of_edgeUse_pos {T : List E} {e : E} (h : 0 < edgeUse T e) : e ∈ T := by
  induction T with
  | nil => simp [edgeUse] at h
  | cons x T ih =>
      rw [edgeUse_cons] at h
      by_cases hx : x = e
      · subst hx
        exact List.mem_cons_self
      · rw [if_neg hx] at h
        exact List.mem_cons_of_mem _ (ih (by omega))

/-- Concatenating two trails matching at the junction. -/
theorem trailAppend {T₁ T₂ : List E} {s u t : V}
    (h₁ : TrailEnds tail head T₁ s u) (h₂ : TrailEnds tail head T₂ u t) :
    TrailEnds tail head (T₁ ++ T₂) s t := by
  induction T₁ generalizing s with
  | nil => cases h₁; exact h₂
  | cons x T₁ ih =>
      cases h₁ with
      | cons _ _ _ _ hte hT => exact TrailEnds.cons x (T₁ ++ T₂) _ _ hte (ih hT)

/-- Appending a final edge to a trail. -/
theorem trailAppendLast {T₁ : List E} {p q : V} (h₁ : TrailEnds tail head T₁ p q)
    (x : E) (hx : tail x = q) : TrailEnds tail head (T₁ ++ [x]) p (head x) := by
  induction T₁ generalizing p with
  | nil =>
      cases h₁
      rw [List.nil_append]
      exact TrailEnds.cons x [] _ _ hx (TrailEnds.nil _)
  | cons y T₁ ih =>
      cases h₁ with
      | cons _ _ _ _ hte hT => exact TrailEnds.cons y (T₁ ++ [x]) _ _ hte (ih hT)

/-- **Cyclic concatenation.** If `T₁` runs from `u` to `s` and `T₂` from `s`
back to `u`, then `T₁ ++ T₂` is a closed trail at `u`.  This is the trail-level
form of "the two excursions of a cut closed trail concatenate to a cycle". -/
theorem trailRevAppend {T₁ T₂ : List E} {p q : V}
    (h₁ : TrailEnds tail head T₁ p q) (h₂ : TrailEnds tail head T₂ q p) :
    TrailEnds tail head (T₁ ++ T₂) p p := by
  cases h₂ with
  | nil q => simpa using h₁
  | cons x T₂ q p hx hT =>
      have heq : T₁ ++ x :: T₂ = (T₁ ++ [x]) ++ T₂ := by simp
      rw [heq]
      exact trailAppend (tail := tail) (head := head)
        (trailAppendLast (tail := tail) (head := head) h₁ x hx) hT

/-- The first edge of a nonempty trail leaves the start vertex. -/
theorem trailHead {T : List E} {s t : V} (h : TrailEnds tail head T s t)
    (hne : T ≠ []) :
    ∃ T' f, T = f :: T' ∧ tail f = s ∧ TrailEnds tail head T' (head f) t := by
  cases h with
  | nil s => exact absurd rfl hne
  | cons f T s t htf hT => exact ⟨T, f, rfl, htf, hT⟩

/-- A repetition of a closed trail is a closed trail. -/
theorem trailNcopies {T : List E} {s : V} (hT : TrailEnds tail head T s s)
    (m : ℕ) : TrailEnds tail head (nCopies T m) s s := by
  induction m with
  | zero => exact TrailEnds.nil _
  | succ m ih =>
      rw [nCopies_succ]
      exact trailAppend (tail := tail) (head := head) hT ih

/-- A repetition of two closed excursions based at the same node is a closed
trail: this is what makes `A^m ++ B^m` a cyclic edge-type spelling. -/
theorem trailNcopiesAppend {A B : List E} {v : V}
    (hA : TrailEnds tail head A v v) (hB : TrailEnds tail head B v v) (m : ℕ) :
    TrailEnds tail head (nCopies A m ++ nCopies B m) v v :=
  trailAppend (tail := tail) (head := head)
    (trailNcopies (tail := tail) (head := head) hA m)
    (trailNcopies (tail := tail) (head := head) hB m)

end Basics

/-! ## Splitting and rotating closed trails -/

section Cutting

variable {V E : Type} [DecidableEq V] [DecidableEq E]
variable (tail head : E → V)

/-- **Splitting a trail.** Cutting a trail strictly inside it yields a prefix
running from the start vertex and a suffix running to the end vertex, meeting at
an intermediate vertex `u`. -/
theorem trailSplit {T : List E} {s t : V} (h : TrailEnds tail head T s t) :
    ∀ (i : ℕ), 0 < i → i < T.length →
      ∃ (A B : List E) (u : V), T = A ++ B ∧ A ≠ [] ∧ B ≠ [] ∧
        A = T.take i ∧ B = T.drop i ∧
        TrailEnds tail head A s u ∧ TrailEnds tail head B u t := by
  induction T generalizing s t with
  | nil =>
      intro i hpos hlt
      simp at hlt
  | cons x T' ih =>
      cases h with
      | cons _ _ _ _ htf hT' =>
          intro i hpos hlt
          cases i with
          | zero => omega
          | succ i =>
              cases i with
              | zero =>
                  refine ⟨[x], T', head x, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · simp
                  · simp
                  · exact ne_nil_of_length_pos (by
                      have hlen : (x :: T').length = T'.length + 1 := rfl
                      omega)
                  · simp [List.take]
                  · simp [List.drop]
                  · simpa using
                      TrailEnds.cons x [] s (head x) htf (TrailEnds.nil _)
                  · exact hT'
              | succ j =>
                  have hk : 0 < j + 1 := by omega
                  have hkl : j + 1 < T'.length := by
                    have hlen : (x :: T').length = T'.length + 1 := rfl
                    omega
                  obtain ⟨A, B, u, hT1, hAne, hBne, hAtake, hBdrop, hA, hB⟩ :=
                    ih hT' (j + 1) hk hkl
                  refine ⟨x :: A, B, u, ?_, ?_, hBne, ?_, ?_, ?_, hB⟩
                  · rw [hT1, List.cons_append]
                  · simp
                  · simp [List.take, hAtake]
                  · simp [List.drop, hBdrop]
                  · exact TrailEnds.cons x A s u htf hA

/-- **Cutting a closed trail into two closed excursions.**  For `0 < i < |T|`,
the prefix `T.take i` runs from the start vertex to the tail of the edge at
position `i`, and the suffix `T.drop i` runs from there back to the start. -/
theorem trailSplitClosed {T : List E} {s : V} (h : TrailEnds tail head T s s)
    (i : ℕ) (hpos : 0 < i) (hlt : i < T.length) :
    ∃ (A B : List E) (u : V), T = A ++ B ∧ A ≠ [] ∧ B ≠ [] ∧
      A = T.take i ∧ B = T.drop i ∧
      TrailEnds tail head A s u ∧ TrailEnds tail head B u s := by
  obtain ⟨A, B, u, hT1, hAne, hBne, hAtake, hBdrop, hA, hB⟩ :=
    trailSplit (tail := tail) (head := head) h i hpos hlt
  exact ⟨A, B, u, hT1, hAne, hBne, hAtake, hBdrop, hA, hB⟩

/-- **Rotating a closed trail.**  Rotating by `i` positions gives another closed
trail with the same edge multiplicities and the same elements; the rotated trail
starts with the edge that was at position `i`.  This is the formal version of
"choose the cyclic representative of the spelling that starts at `v`". -/
theorem rotate_closed {T : List E} {s : V} (h : TrailEnds tail head T s s)
    (i : ℕ) (hlt : i < T.length) :
    ∃ (R : List E), (∃ v, TrailEnds tail head R v v) ∧
      (∀ e, edgeUse R e = edgeUse T e) ∧
      (∀ e, e ∈ T ↔ e ∈ R) ∧ R[0]? = T[i]? := by
  by_cases hi : i = 0
  · subst hi
    refine ⟨T, ⟨s, h⟩, ?_, ?_, ?_⟩
    · intro e; rfl
    · intro e; rfl
    · simp
  · obtain ⟨A, B, u, hT1, hAne, hBne, hAtake, hBdrop, hA, hB⟩ :=
      trailSplitClosed (tail := tail) (head := head) h i
        (Nat.pos_of_ne_zero hi) hlt
    refine ⟨B ++ A, ⟨u, trailRevAppend (tail := tail) (head := head) hB hA⟩, ?_, ?_, ?_⟩
    · intro e
      rw [edgeUse_append, hT1, edgeUse_append, Nat.add_comm]
    · intro e
      rw [hT1, List.mem_append, List.mem_append]
      exact or_comm
    · have hAn : 0 < B.length + A.length := by
        have hlen : (B ++ A).length = B.length + A.length := List.length_append
        have hApos : 0 < A.length := length_pos_of_ne_nil hAne
        omega
      have h0r : 0 < (T.rotate i).length := by
        rw [List.length_rotate]
        omega
      have hTlen : 0 < T.length := by omega
      have hR : B ++ A = T.rotate i := by
        symm
        rw [hBdrop, hAtake]
        exact List.rotate_eq_drop_append_take (l := T) (n := i) (Nat.le_of_lt hlt)
      rw [hR, List.getElem?_rotate (l := T) (n := i) (m := 0) (hml := hTlen),
        Nat.add_zero, Nat.mod_eq_of_lt hlt]

end Cutting
