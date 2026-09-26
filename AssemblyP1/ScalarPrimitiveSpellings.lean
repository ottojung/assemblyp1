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
        Nat.zero_add, Nat.mod_eq_of_lt hlt]

end Cutting

/-! ## The two-excursion cut at a branching node -/

section BranchingCut

variable {V E : Type} [DecidableEq V] [DecidableEq E]
variable (tail head : E → V)

/-- **The two-excursion cut.**  Let `T` be a closed edge-type trail spelling the
spectrum `c` on the support `edges`, and suppose the support branches at `v`:
there are two distinct support edge types `e₁`, `e₂` leaving `v`.  Cutting the
cyclic spelling at a visit of `e₁` and at a visit of `e₂` splits it into two
nonempty closed excursions `A`, `B` at `v` whose first edge types are `e₁` and
`e₂` resp., hence differ, and whose edge multiplicities add up to `c`.

This is the graph-side step of `docs/scalar-primitive-spellings-83.md` that the
word-equation step needed and did not have. -/
theorem two_excursions_of_branching {T : List E} {s : V}
    (hT : TrailEnds tail head T s s) (c : E → ℕ) (huse : ∀ e, edgeUse T e = c e)
    (edges : Finset E) (v : V) (e₁ e₂ : E) (he₁ : e₁ ∈ edges) (he₂ : e₂ ∈ edges)
    (he12 : e₁ ≠ e₂) (ht₁ : tail e₁ = v) (ht₂ : tail e₂ = v)
    (hpos : ∀ e ∈ edges, 0 < c e) :
    ∃ (A B : List E), A ≠ [] ∧ B ≠ [] ∧
      (∃ w, TrailEnds tail head A v w) ∧ (∃ w, TrailEnds tail head B v w) ∧
      A[0]? ≠ B[0]? ∧ ∀ e, edgeUse A e + edgeUse B e = c e := by
  -- `e₁` occurs in the spelling, at some position.
  have hpos₁ : 0 < edgeUse T e₁ := huse e₁ ▸ hpos e₁ he₁
  obtain ⟨i, hi, hiT⟩ := List.getElem_of_mem (mem_of_edgeUse_pos hpos₁)
  -- Rotate the cyclic spelling so that it starts at `e₁`.
  obtain ⟨T', hT', huseT', hmemT', hfirst⟩ :=
    rotate_closed (tail := tail) (head := head) hT i hi
  have hfirst' : T'[0]? = some e₁ := by
    have h1 := hfirst
    rwa [List.getElem?_eq_getElem hi, hiT] at h1
  have hne : T' ≠ [] := by
    intro h0
    rw [h0] at hfirst'
    simp at hfirst'
  -- The rotated spelling is a closed trail at `v`: it starts with `e₁`.
  obtain ⟨v₀, hT'⟩ := hT'
  obtain ⟨T'', f, hT'1, htf, hT'2⟩ :=
    trailHead (tail := tail) (head := head) hT' hne
  have hff : f = e₁ := by
    have h1 : T'[0]? = some f := by
      rw [hT'1]
      exact List.getElem?_cons_zero
    rw [hfirst'] at h1
    exact Option.some.inj h1.symm
  have hvv : v₀ = v := by
    calc v₀ = tail f := htf.symm
      _ = tail e₁ := by rw [hff]
      _ = v := ht₁
  -- `e₂` occurs in the rotated spelling, at a nonzero position.
  have hpos₂ : 0 < edgeUse T' e₂ := huseT' e₂ ▸ (huse e₂ ▸ hpos e₂ he₂)
  have hmem₂ : e₂ ∈ T' := (hmemT' e₂).mp (mem_of_edgeUse_pos (huseT' e₂ ▸ hpos₂))
  obtain ⟨q, hq, hqT'⟩ := List.getElem_of_mem hmem₂
  have hq0 : 0 < q := by
    by_contra hcon
    have hq0' : q = 0 := by omega
    subst hq0'
    have hT'len : 0 < T'.length := by
      rw [hT'1]
      simp
    have h1 := hfirst'
    have h2' : T'[0]? = some e₂ :=
      (List.getElem?_eq_getElem hT'len).trans (congrArg some hqT')
    have h3 : e₁ = e₂ := Option.some.inj (h1.symm.trans h2')
    exact he12 h3
  -- Cut the (rotated) closed trail at `q`.
  obtain ⟨A, B, u, hT'3, hAne, hBne, hAtake, hBdrop, hA, hB⟩ :=
    trailSplitClosed (tail := tail) (head := head) (hvv ▸ hT') q hq0 hq
  -- The first edge of `B` is `e₂`, so `B` runs from `v` to `v`.
  have hBhead : B[0]? = some e₂ := by
    rw [hBdrop, List.getElem?_drop, show q + 0 = q by rfl,
      List.getElem?_eq_getElem hq, hqT']
  have hu : u = v := by
    obtain ⟨B', g, hB1, htg, hB2⟩ := trailHead (tail := tail) (head := head) hB hBne
    have hg : g = e₂ := by
      have h1 : B[0]? = some g := by
        rw [hB1]
        exact List.getElem?_cons_zero
      rw [hBhead] at h1
      exact Option.some.inj h1.symm
    have hu' : u = tail e₂ := by
      calc u = tail g := htg.symm
        _ = tail e₂ := by rw [hg]
    exact hu'.trans ht₂
  -- The first edge of `A` is `e₁`.
  have hAhead : A[0]? = some e₁ := by
    simp [hAtake, List.getElem?_take, hq0.ne', hfirst']
  refine ⟨A, B, hAne, hBne, ⟨v, hu ▸ hA⟩, ⟨v, hu ▸ hB⟩, ?_, ?_⟩
  · rw [hAhead, hBhead]
    intro hcon
    exact he12 (Option.some.inj hcon)
  · intro e
    calc edgeUse A e + edgeUse B e = edgeUse (A ++ B) e := (edgeUse_append A B e).symm
      _ = edgeUse T' e := by rw [hT'3]
      _ = c e := huseT' e ▸ huse e

end BranchingCut

/-! ## Cyclic periods: a nontrivial period forces a proper power

This section is the analytic core of the *nonbranching* half of
`docs/scalar-primitive-spellings-83.md`: a cyclic edge-type spelling whose
support has at most one outgoing edge type per node is a cyclic walk of a
functional graph, hence periodic, hence (if not of minimal length) a proper
power. -/

section Periods

variable {E : Type}

/-- `p` is a cyclic period of `T`: shifting an index by `p` does not change the entry. -/
def CyclicPeriod (T : List E) (p : ℕ) : Prop :=
  ∀ (j : ℕ), j < T.length → T[j]? = T[(j + p) % T.length]?

theorem CyclicPeriod.zero (T : List E) : CyclicPeriod T 0 := by
  intro j hj
  rw [Nat.add_zero, Nat.mod_eq_of_lt hj]

theorem CyclicPeriod.self (T : List E) : CyclicPeriod T T.length := by
  intro j hj
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt hj]

theorem CyclicPeriod.add {T : List E} {p q : ℕ} (hp : CyclicPeriod T p) (hq : CyclicPeriod T q) :
    CyclicPeriod T (p + q) := by
  intro j hj
  rw [hp j hj, hq ((j + p) % T.length) (Nat.mod_lt _ (by omega)), Nat.mod_add_mod,
    show j + p + q = j + (p + q) by omega]

theorem CyclicPeriod.neg {T : List E} {q : ℕ} (hq : CyclicPeriod T q)
    (hqn : q < T.length) : CyclicPeriod T (T.length - q) := by
  intro j hj
  have h1 := hq ((j + (T.length - q)) % T.length) (Nat.mod_lt _ (by omega))
  have hidx2 : (j + T.length) % T.length = j := by
    rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hj]
  rw [h1, Nat.mod_add_mod,
    show (j + (T.length - q) + q) = j + T.length by omega, hidx2]

theorem CyclicPeriod.sub {T : List E} {p q : ℕ} (hp : CyclicPeriod T p) (hq : CyclicPeriod T q)
    (hq0 : 0 < q) (hqn : q < T.length) (hpn : p < T.length) (hqp : q ≤ p) :
    CyclicPeriod T (p - q) := by
  intro j hj
  have h1 := CyclicPeriod.neg hq hqn ((j + p) % T.length) (Nat.mod_lt _ (by omega))
  have hjn : (j + T.length) % T.length = j := by
    rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hj]
  have hstep : (j + p + (T.length - q)) % T.length = (j + (p - q)) % T.length := by
    rw [show j + p + (T.length - q) = (j + T.length) + (p - q) by omega]
    rw [Nat.add_mod, hjn, Nat.add_mod, Nat.mod_mod]
    exact (Nat.add_mod j (p - q) T.length).symm
  rw [hp j hj, h1, Nat.mod_add_mod, hstep]

theorem gcd_add_right (a b : ℕ) : Nat.gcd a (a + b) = Nat.gcd a b := by
  apply Nat.dvd_antisymm
  · exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
      ((Nat.dvd_add_right (a := Nat.gcd a (a + b)) (b := a) (c := b)
        (Nat.gcd_dvd_left _ _)).mp (Nat.gcd_dvd_right _ _))
  · exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
      ((Nat.dvd_add_right (a := Nat.gcd a b) (b := a) (c := b)
        (Nat.gcd_dvd_left a b)).mpr (Nat.gcd_dvd_right a b))

theorem gcd_add_left (a b : ℕ) : Nat.gcd (a + b) a = Nat.gcd a b := by
  rw [Nat.gcd_comm, gcd_add_right]

/-- The gcd of two periods is a period. -/
theorem CyclicPeriod.gcd {T : List E} {p q : ℕ} (hp : CyclicPeriod T p) (hq : CyclicPeriod T q)
    (hp0 : 0 < p) (hpn : p < T.length) (hq0 : 0 < q) (hqn : q < T.length) :
    CyclicPeriod T (Nat.gcd p q) := by
  have aux : ∀ n : ℕ, ∀ (a b : ℕ), a + b = n → 0 < a → 0 < b → a < T.length → b < T.length →
      CyclicPeriod T a → CyclicPeriod T b → CyclicPeriod T (Nat.gcd a b) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro a b hab ha hb han hbn hpa hpb
        by_cases hbeq : a = b
        · rw [hbeq, Nat.gcd_self]
          exact hpb
        · by_cases hab' : a < b
          · have hsub0 := CyclicPeriod.sub (p := b) (q := a) hpb hpa ha han hbn hab'.le
            have hrec := ih (a + (b - a)) (by omega) a (b - a) (by omega) (by omega) (by omega)
              (by omega) (by omega) hpa hsub0
            have h1 : Nat.gcd a b = Nat.gcd a (a + (b - a)) := by
              rw [show a + (b - a) = b by omega]
            have hg : Nat.gcd a b = Nat.gcd a (b - a) :=
              h1.trans (gcd_add_right a (b - a))
            rw [hg]
            exact hrec
          · have hle : b ≤ a := Nat.le_of_not_gt hab'
            have hba : b < a := lt_of_le_of_ne hle (fun h => hbeq h.symm)
            have hsub0 := CyclicPeriod.sub (p := a) (q := b) hpa hpb hb hbn han hle
            have hab1 : 0 < a - b := by omega
            have hab2 : a - b < T.length := by omega
            have hrec := ih ((a - b) + b) (by omega) (a - b) b (by omega) hab1 hb hab2 hbn
              hsub0 hpb
            have h1 : Nat.gcd a b = Nat.gcd ((a - b) + b) b := by
              rw [show (a - b) + b = a by omega]
            have h2 : Nat.gcd ((a - b) + b) b = Nat.gcd b (a - b) := by
              rw [show (a - b) + b = b + (a - b) by omega, ← Nat.gcd_comm]
              exact gcd_add_right b (a - b)
            have hg : Nat.gcd a b = Nat.gcd (a - b) b := h1.trans (h2.trans (Nat.gcd_comm _ _))
            rw [hg]
            exact hrec
  exact aux (p + q) p q rfl hp0 hq0 hpn hqn hp hq

theorem CyclicPeriod.iter {T : List E} {g : ℕ} (hg : CyclicPeriod T g) :
    ∀ (j k : ℕ), j < T.length → T[j]? = T[(j + k * g) % T.length]? := by
  intro j k
  induction k with
  | zero =>
      intro hj
      rw [Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt hj]
  | succ k ih =>
      intro hj
      rw [ih hj, hg ((j + k * g) % T.length) (Nat.mod_lt _ (by omega)),
        Nat.mod_add_mod, show j + k * g + g = j + (k + 1) * g by ring]

theorem CyclicPeriod.of_div {T : List E} {g p : ℕ} (hp : CyclicPeriod T p) (hg : CyclicPeriod T g)
    (hg0 : 0 < g) (hgn : g < T.length) (hdiv : g ∣ T.length) :
    ∀ (j : ℕ), j < T.length → T[j]? = T[j % g]? := by
  intro j hj
  have hidx : (j + (T.length / g - j / g) * g) % T.length = j % g := by
    have hq : g * (T.length / g) = T.length := Nat.mul_div_cancel' hdiv
    have hdiv' := Nat.div_add_mod j g
    rw [Nat.mul_comm] at hdiv'
    have hmul : (T.length / g - j / g) * g = T.length - j / g * g := by
      have h1 : (T.length / g - j / g) * g = (T.length / g) * g - (j / g) * g :=
        Nat.sub_mul _ _ _
      have h2 : (T.length / g) * g - (j / g) * g = g * (T.length / g) - g * (j / g) := by
        rw [Nat.mul_comm (T.length / g) g, Nat.mul_comm (j / g) g]
      have h3 : g * (T.length / g) - g * (j / g) = T.length - g * (j / g) := by rw [hq]
      have h4 : T.length - g * (j / g) = T.length - j / g * g := by rw [Nat.mul_comm]
      rw [h1, h2, h3, h4]
    have hstep : j + (T.length / g - j / g) * g = j % g + T.length := by
      rw [hmul]
      have hle1 : j / g * g ≤ j := by omega
      have hjle : j ≤ T.length := by omega
      have hrem : j - j / g * g = j % g := by omega
      omega
    rw [hstep, mod_add_self, Nat.mod_eq_of_lt (by omega)]
  rw [← hidx]
  exact CyclicPeriod.iter hg j (T.length / g - j / g) hj

/-- **A nontrivial cyclic period forces a proper power.** -/
theorem properPower_of_cyclicPeriod {T : List E} (hne : T ≠ [])
    {p : ℕ} (hp : 0 < p) (hpn : p < T.length) (hper : CyclicPeriod T p) :
    ∃ l, l ≠ [] ∧ ∃ k, 2 ≤ k ∧ T = nCopies l k := by
  have hqlen : 0 < T.length := length_pos_of_ne_nil hne
  have hdiv : Nat.gcd p T.length ∣ T.length := Nat.gcd_dvd_right _ _
  have hg0 : 0 < Nat.gcd p T.length :=
    Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left p T.length) hp
  have hgle : Nat.gcd p T.length ≤ p := Nat.le_of_dvd hp (Nat.gcd_dvd_left _ _)
  have hgn : Nat.gcd p T.length < T.length := lt_of_le_of_lt hgle hpn
  have hper' : CyclicPeriod T (T.length - p) := CyclicPeriod.neg hper hpn
  have hsub0 : 0 < T.length - p := by omega
  have hsublt : T.length - p < T.length := by omega
  have hid : Nat.gcd p T.length = Nat.gcd p (T.length - p) := by
    rw [← gcd_add_right p (T.length - p), show p + (T.length - p) = T.length by omega]
  have hgper : CyclicPeriod T (Nat.gcd p T.length) := by
    rw [hid]
    exact CyclicPeriod.gcd (p := p) (q := T.length - p) hper hper' hp hpn hsub0 hsublt
  have hmod := CyclicPeriod.of_div hper hgper hg0 hgn hdiv
  refine ⟨T.take (Nat.gcd p T.length), ?_, T.length / Nat.gcd p T.length, ?_, ?_⟩
  · have hlen0 : 0 < (T.take (Nat.gcd p T.length)).length := by
      rw [List.length_take, Nat.min_eq_left (by omega)]
      exact hg0
    exact ne_nil_of_length_pos hlen0
  · have hq2 : Nat.gcd p T.length * (T.length / Nat.gcd p T.length) = T.length :=
      Nat.mul_div_cancel' hdiv
    by_contra hcon
    have hle : T.length / Nat.gcd p T.length ≤ 1 := by omega
    have h3 : Nat.gcd p T.length * (T.length / Nat.gcd p T.length)
        ≤ Nat.gcd p T.length * 1 := by
      calc Nat.gcd p T.length * (T.length / Nat.gcd p T.length)
          = (T.length / Nat.gcd p T.length) * Nat.gcd p T.length := Nat.mul_comm _ _
        _ ≤ 1 * Nat.gcd p T.length := Nat.mul_le_mul_right (Nat.gcd p T.length) hle
        _ = Nat.gcd p T.length * 1 := by rw [Nat.mul_comm]
    omega
  · apply List.ext_getElem?
    intro j
    have hlen : (nCopies (T.take (Nat.gcd p T.length))
        (T.length / Nat.gcd p T.length)).length = T.length := by
      rw [nCopies_length, List.length_take]
      have hq3 : Nat.gcd p T.length * (T.length / Nat.gcd p T.length) = T.length :=
        Nat.mul_div_cancel' hdiv
      rw [Nat.min_eq_left hgn.le, Nat.mul_comm, hq3]
    by_cases hj : j < T.length
    · have hL : T[j % Nat.gcd p T.length]? =
          (T.take (Nat.gcd p T.length))[j % Nat.gcd p T.length]? := by
        simp [Nat.mod_lt _ hg0]
      have hmin : min (Nat.gcd p T.length) T.length = Nat.gcd p T.length :=
        Nat.min_eq_left hgn.le
      have hjlt : j < (nCopies (T.take (Nat.gcd p T.length))
          (T.length / Nat.gcd p T.length)).length := by
        rw [hlen]
        exact hj
      rw [hmod j hj, hL, nCopies_getElem? hjlt]
      simp only [List.length_take, hmin]
    · have h1 : (nCopies (T.take (Nat.gcd p T.length))
          (T.length / Nat.gcd p T.length))[j]? = none := by
        rw [List.getElem?_eq_none_iff]
        omega
      rw [h1, List.getElem?_eq_none_iff]
      omega

end Periods
