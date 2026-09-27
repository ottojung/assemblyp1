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
5. `gcdOne_of_nonbranching_primitive`: a primitive truth on a nonbranching
   support has a gcd-one complete spectrum (all support counts `1`), so it is
   the primitive point of the integer spectrum ray — with no uniqueness input.
6. `rotEquiv_of_specCount_eq`: same-length complete-spectrum uniqueness on a
   nonbranching support.  Equal spectra give equal supports, so the candidate's
   window at start `0` is *some* truth window, say the one started at `j`; the
   deterministic prefix/suffix step (`winPrefix_winAt`) plus the functional
   support (`winAt_agrees`) then force the two traversals to agree at every
   start, so the candidate reads the truth from a shifted start and is a
   rotation of it (`rotEquiv_of_shift`).  This is the replacement for the BBT
   premise.
7. `identifiable_iff_nonbranching`: the exported fixed-truth classification.  A
   primitive truth is identifiable among arbitrary-length primitive candidates
   from its normalized complete spectrum **iff** its spectrum-support graph has no
   vertex with two distinct outgoing edge types.

The exported `identifiable_iff_nonbranching` has **no** external
complete-spectrum uniqueness hypothesis: there is no `hBBT`, no `AdmP2`
admissibility predicate and no `hP2S`.  The equal-length step is derived from
the deterministic prefix/suffix step of the window walk together with the
functional (out-degree ≤ 1) nonbranching condition, which is strictly easier
than the P2 (`hP2S`) uniqueness of issue #89.  Everything — the ray
arithmetic, both directions of the classification, the two-excursion cut, the
period/gcd argument, the forced-traversal rotation step and the
Lyndon–Schützenberger separator — is kernel-checked with no new axioms.
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
def Support {_V E : Type} [DecidableEq E] [Fintype E] (c : E → ℕ) : Finset E :=
  Finset.univ.filter (fun e => 0 < c e)

/-- **Branching:** some node of the graph has two distinct outgoing edge types. -/
def Branching {V E : Type} [DecidableEq V] [DecidableEq E] (_nodes : Finset V)
    (edges : Finset E) (tail _head : E → V) : Prop :=
  ∃ v, ∃ e₁ ∈ edges, ∃ e₂ ∈ edges, e₁ ≠ e₂ ∧ tail e₁ = v ∧ tail e₂ = v

/-- **Nonbranching:** no node has two distinct outgoing edge types. -/
def NonBranching {V E : Type} [DecidableEq V] [DecidableEq E] (_nodes : Finset V)
    (edges : Finset E) (tail _head : E → V) : Prop :=
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
      · simp [hx] at h
        exact List.mem_cons_of_mem _ (ih (by omega))

omit [DecidableEq V] [DecidableEq E] in
/-- Concatenating two trails matching at the junction. -/
theorem trailAppend {T₁ T₂ : List E} {s u t : V}
    (h₁ : TrailEnds tail head T₁ s u) (h₂ : TrailEnds tail head T₂ u t) :
    TrailEnds tail head (T₁ ++ T₂) s t := by
  induction T₁ generalizing s with
  | nil => cases h₁; exact h₂
  | cons x T₁ ih =>
      cases h₁ with
      | cons _ _ _ _ hte hT => exact TrailEnds.cons x (T₁ ++ T₂) _ _ hte (ih hT)

omit [DecidableEq V] [DecidableEq E] in
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

omit [DecidableEq V] [DecidableEq E] in
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

omit [DecidableEq V] [DecidableEq E] in
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
    ∃ (A B : List E) (w : V), TrailEnds tail head A w w ∧ TrailEnds tail head B w w ∧
      A ≠ [] ∧ B ≠ [] ∧ A[0]? ≠ B[0]? ∧ ∀ e, edgeUse A e + edgeUse B e = c e := by
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
  refine ⟨A, B, v, hu ▸ hA, hu ▸ hB, hAne, hBne, ?_, ?_⟩
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
    (_hq0 : 0 < q) (hqn : q < T.length) (hpn : p < T.length) (hqp : q ≤ p) :
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

theorem CyclicPeriod.of_div {T : List E} {g p : ℕ} (_hp : CyclicPeriod T p) (hg : CyclicPeriod T g)
    (_hg0 : 0 < g) (_hgn : g < T.length) (hdiv : g ∣ T.length) :
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

/-! ## Primitivity forces a proper power on a functional support

This section is where the two halves of the note meet the Lyndon–Schützenberger
step.  All of it is on the real oriented window graph: `edges` is a set of
length-`L` windows, `winPrefix`/`winSuffix` are the tail/head, and a closed trail
of windows is a cyclic edge-type spelling. -/

section FunctionalSupport

variable {α : Type} [DecidableEq α] {L : ℕ}
variable (edges : Finset (Fin L → α))

omit [DecidableEq α] in
/-- The edge at position `j` of a nonempty window trail. -/
private theorem cycEdge_get {T : List (Fin L → α)} (hpos : 0 < T.length) (j : ℕ)
    (hj : j < T.length) : PopulationReduction.cycEdge T hpos j = T.get ⟨j, hj⟩ := by
  unfold PopulationReduction.cycEdge
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt hj)

/-- Incrementing a residue class: `(x + 1) % n = ((x % n) + 1) % n` for `n > 1`. -/
theorem mod_succ_eq (n : ℕ) (hn : 1 < n) (x : ℕ) :
    (x + 1) % n = ((x % n) + 1) % n := by
  have h1 : (x + 1) % n = (x % n + 1 % n) % n := Nat.add_mod x 1 n
  have h2 : 1 % n = 1 := Nat.mod_eq_of_lt hn
  rw [h1, h2]

/-- Arithmetic helper: stepping forward past the end of a modular index. -/
theorem mod_index_add (n i m : ℕ) (hi : i ≤ n) : i + (m + n - i) = m + n := by
  have h2 : i + ((m + n) - i) = m + n := Nat.add_sub_of_le (by omega)
  omega

/-- Arithmetic helper: the same step from a later index. -/
theorem mod_index_add' (n i j m : ℕ) (hi : i ≤ n) (hij : i ≤ j) :
    j + (m + n - i) = (m + (j - i)) + n := by
  have h4 : (j - i) + i = j := Nat.sub_add_cancel hij
  have h1 : j + (m + n - i) = (j - i) + (m + n) := by
    have h5 : j + (m + n - i) = (j - i) + (i + (m + n - i)) := by omega
    rw [h5, mod_index_add n i m hi]
  rw [h1, Nat.add_comm (j - i) (m + n),
    show m + n + (j - i) = m + (j - i) + n by omega]

/-- **A repeated edge in a functional-support trail makes it a proper power.**
If every node of the support has at most one outgoing edge type, the closed
trail is a walk in a functional graph: its successor at each position is
determined by the current edge.  Hence two occurrences of the same edge force a
nontrivial cyclic period, i.e. a proper power. -/
theorem repeatedEdge_properPower_of_uniqueOut {T : List (Fin L → α)} {s : Fin (L - 1) → α}
    (hT : TrailEnds winPrefix winSuffix T s s) (hne : T ≠ [])
    (hin : ∀ e ∈ T, e ∈ edges) (huniq : ∀ e₁ ∈ edges, ∀ e₂ ∈ edges,
      winPrefix e₁ = winPrefix e₂ → e₁ = e₂)
    (i j : ℕ) (hij : i < j) (hjlt : j < T.length)
    (heq : T.get ⟨i, by omega⟩ = T.get ⟨j, hjlt⟩) :
    ∃ l, l ≠ [] ∧ ∃ k, 2 ≤ k ∧ T = nCopies l k := by
  have hpos : 0 < T.length := length_pos_of_ne_nil hne
  have hil : i < T.length := by omega
  have hn2 : 1 < T.length := by omega
  -- One step of a closed window trail is incidence-compatible, cyclically.
  have hstep : ∀ (a b : ℕ) (ha : a < T.length) (hb : b < T.length),
      T.get ⟨a, ha⟩ = T.get ⟨b, hb⟩ →
      T[(a + 1) % T.length]? = T[(b + 1) % T.length]? := by
    intro a b ha hb hab
    have hcyc1 := trail_cyc_adj hT hpos (a % T.length) (Nat.mod_lt _ (by omega))
    have hcyc2 := trail_cyc_adj hT hpos (b % T.length) (Nat.mod_lt _ (by omega))
    have e1 : PopulationReduction.cycEdge T hpos (a % T.length) = T.get ⟨a, ha⟩ := by
      rw [Nat.mod_eq_of_lt ha]
      exact cycEdge_get hpos a ha
    have e2 : PopulationReduction.cycEdge T hpos (b % T.length) = T.get ⟨b, hb⟩ := by
      rw [Nat.mod_eq_of_lt hb]
      exact cycEdge_get hpos b hb
    have e3 : PopulationReduction.cycEdge T hpos ((a % T.length + 1) % T.length)
        = T.get ⟨(a + 1) % T.length, Nat.mod_lt _ (by omega)⟩ := by
      rw [show (a % T.length + 1) % T.length = (a + 1) % T.length by
        rw [Nat.mod_eq_of_lt ha]]
      exact cycEdge_get hpos ((a + 1) % T.length) (Nat.mod_lt _ (by omega))
    have e4 : PopulationReduction.cycEdge T hpos ((b % T.length + 1) % T.length)
        = T.get ⟨(b + 1) % T.length, Nat.mod_lt _ (by omega)⟩ := by
      rw [show (b % T.length + 1) % T.length = (b + 1) % T.length by
        rw [Nat.mod_eq_of_lt hb]]
      exact cycEdge_get hpos ((b + 1) % T.length) (Nat.mod_lt _ (by omega))
    have hqa : (a + 1) % T.length < T.length := Nat.mod_lt _ (by omega)
    have hqb : (b + 1) % T.length < T.length := Nat.mod_lt _ (by omega)
    have h1 : winSuffix (T.get ⟨a, ha⟩) = winPrefix (T.get ⟨(a + 1) % T.length, hqa⟩) := by
      rw [← e3, ← e1]
      exact hcyc1
    have h2 : winSuffix (T.get ⟨b, hb⟩) = winPrefix (T.get ⟨(b + 1) % T.length, hqb⟩) := by
      rw [← e4, ← e2]
      exact hcyc2
    have hmem1 : T.get ⟨(a + 1) % T.length, hqa⟩ ∈ edges :=
      hin _ (List.get_mem T ⟨(a + 1) % T.length, hqa⟩)
    have hmem2 : T.get ⟨(b + 1) % T.length, hqb⟩ ∈ edges :=
      hin _ (List.get_mem T ⟨(b + 1) % T.length, hqb⟩)
    have hEq : T.get ⟨(a + 1) % T.length, hqa⟩ = T.get ⟨(b + 1) % T.length, hqb⟩ :=
      huniq _ hmem1 _ hmem2 (h1.symm.trans ((congrArg winSuffix hab).trans h2))
    have hL1 : T[(a + 1) % T.length]? = some (T.get ⟨(a + 1) % T.length, hqa⟩) :=
      List.getElem?_eq_getElem hqa
    have hL2 : T[(b + 1) % T.length]? = some (T.get ⟨(b + 1) % T.length, hqb⟩) :=
      List.getElem?_eq_getElem hqb
    rw [hL1, hL2]
    exact congrArg some hEq
  -- The trail is determined by its first edge: the two occurrences stay in sync.
  have hprop : ∀ (k : ℕ), T[(i + k) % T.length]? = T[(j + k) % T.length]? := by
    intro k
    induction k with
    | zero =>
        have h1 : (i + 0) % T.length = i := by rw [Nat.add_zero, Nat.mod_eq_of_lt hil]
        have h2 : (j + 0) % T.length = j := by rw [Nat.add_zero, Nat.mod_eq_of_lt hjlt]
        rw [h1, h2, List.getElem?_eq_getElem hil, List.getElem?_eq_getElem hjlt]
        exact congrArg some heq
    | succ k ih =>
        have ha : (i + k) % T.length < T.length := Nat.mod_lt _ (by omega)
        have hb : (j + k) % T.length < T.length := Nat.mod_lt _ (by omega)
        have hq1 : ((i + k) % T.length + 1) % T.length = (i + (k + 1)) % T.length :=
          (mod_succ_eq T.length (by omega) (i + k)).symm
        have hq2 : ((j + k) % T.length + 1) % T.length = (j + (k + 1)) % T.length :=
          (mod_succ_eq T.length (by omega) (j + k)).symm
        have ih' : T.get ⟨(i + k) % T.length, ha⟩ = T.get ⟨(j + k) % T.length, hb⟩ :=
          Option.some.inj ((List.getElem?_eq_getElem ha).symm.trans
            (ih.trans (List.getElem?_eq_getElem hb)))
        have h6 := hstep ((i + k) % T.length) ((j + k) % T.length) ha hb ih'
        rw [hq1, hq2] at h6
        exact h6
  -- A period on all positions.
  have hlink : ∀ (x k : ℕ), (x + k) % T.length = (x + k % T.length) % T.length := by
    intro x k
    simp [Nat.add_mod]
  have hper : CyclicPeriod T (j - i) := by
    intro m hm
    have h1 : (i + (m + T.length - i)) % T.length = m := by
      rw [mod_index_add T.length i m (Nat.le_of_lt hil), mod_add_self,
        Nat.mod_eq_of_lt hm]
    have h2 : (j + (m + T.length - i)) % T.length = (m + (j - i)) % T.length := by
      rw [mod_index_add' T.length i j m (Nat.le_of_lt hil) (Nat.le_of_lt hij),
        mod_add_self]
    have h3 : (i + ((m + T.length - i) % T.length)) % T.length = m :=
      (hlink i (m + T.length - i)).symm.trans h1
    have h4 : (j + ((m + T.length - i) % T.length)) % T.length = (m + (j - i)) % T.length :=
      (hlink j (m + T.length - i)).symm.trans h2
    have h5 := hprop ((m + T.length - i) % T.length)
    rw [h3, h4] at h5
    exact h5
  obtain ⟨l, hl, k, hk, heq⟩ := properPower_of_cyclicPeriod hne (by omega) (by omega) hper
  exact ⟨l, hl, k, hk, heq⟩

end FunctionalSupport

/-! ## The two halves of the note, at the level of cyclic edge-type spellings -/

section Spellings

variable {α : Type} [DecidableEq α] {L : ℕ}

/-- Edge use of a repetition. -/
theorem edgeUse_nCopies (T : List (Fin L → α)) :
    ∀ (m : ℕ) (e : Fin L → α), edgeUse (nCopies T m) e = m * edgeUse T e := by
  intro m
  induction m with
  | zero => intro e; rw [nCopies_zero]; simp [edgeUse]
  | succ m ih =>
      intro e
      rw [nCopies_succ, edgeUse_append, ih, Nat.succ_mul]
      omega

/-- A Finset of cardinality at least two has two distinct elements. -/
theorem two_distinct_of_card {α : Type} (s : Finset α) (h : 2 ≤ s.card) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y := by
  by_cases hall : ∀ a ∈ s, ∀ b ∈ s, a = b
  · have hone : s.card ≤ 1 := Finset.card_le_one.mpr hall
    omega
  · simp only [not_forall] at hall
    obtain ⟨x, hx, y, hy, hxy⟩ := hall
    exact ⟨x, hx, y, hy, hxy⟩

/-- An edge with positive edge use occurs at some position. -/
theorem exists_get_of_edgeUse_pos (T : List (Fin L → α)) (e : Fin L → α)
    (h : 0 < edgeUse T e) :
    ∃ (i : ℕ) (hi : i < T.length), T.get ⟨i, hi⟩ = e := by
  have hcard : 0 < ({j : Fin T.length | T.get j = e} : Finset (Fin T.length)).card := by
    rw [count_bridge T e]
    exact h
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hcard
  refine ⟨x.val, x.isLt, ?_⟩
  exact (Finset.mem_filter.mp hx).2

/-- An edge used at least twice occurs at two distinct positions. -/
theorem two_positions_of_count_ge_two (T : List (Fin L → α)) (e : Fin L → α)
    (h : 2 ≤ edgeUse T e) :
    ∃ (i j : ℕ) (hi : i < j) (hj : j < T.length),
      T.get ⟨i, Nat.lt_trans hi hj⟩ = e ∧ T.get ⟨j, hj⟩ = e := by
  have hcard : 2 ≤ ({j : Fin T.length | T.get j = e} : Finset (Fin T.length)).card := by
    rw [count_bridge T e]
    exact h
  obtain ⟨x, hx, y, hy, hne⟩ := two_distinct_of_card
    ({j : Fin T.length | T.get j = e} : Finset (Fin T.length)) hcard
  have hxg : T.get x = e := (Finset.mem_filter.mp hx).2
  have hyg : T.get y = e := (Finset.mem_filter.mp hy).2
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨x.val, y.val, hlt, y.isLt, hxg, hyg⟩
  · exact ⟨y.val, x.val, hgt, x.isLt, hyg, hxg⟩

/-- **Nonbranching: a primitive spelling uses every support edge exactly once.**
On a support with at most one outgoing edge type per node, a primitive cyclic
edge-type spelling of `c` has `c e = 1` on the whole support. -/
theorem nonbranching_primitive_spelling_eq_one {T : List (Fin L → α)}
    {s : Fin (L - 1) → α} (hT : TrailEnds winPrefix winSuffix T s s) (hne : T ≠ [])
    (c : (Fin L → α) → ℕ) (huse : ∀ e, edgeUse T e = c e) (edges : Finset (Fin L → α))
    (huniq : ∀ e₁ ∈ edges, ∀ e₂ ∈ edges, winPrefix e₁ = winPrefix e₂ → e₁ = e₂)
    (_hvan : ∀ e, e ∉ edges → c e = 0) (hpos : ∀ e ∈ edges, 0 < c e) (hprim : IsPrimitive T) :
    ∀ e ∈ edges, c e = 1 := by
  intro e he
  by_contra hcon
  have hge : 2 ≤ edgeUse T e := by
    rw [huse e]
    have h1 := hpos e he
    omega
  obtain ⟨i, j, hij, hjlt, hiT, hjT⟩ := two_positions_of_count_ge_two T e hge
  have hinT : ∀ w ∈ T, w ∈ edges := by
    intro w hw
    by_contra hcon
    have hzero : c w = 0 := hvan w hcon
    have hle := huse w
    rw [hzero] at hle
    have hz : edgeUse T w = 0 := hle
    have hz' : T.countP (fun x => decide (x = w)) = 0 := by
      show edgeUse T w = 0
      exact hz
    obtain ⟨k, hk, hkw⟩ := List.getElem_of_mem hw
    have hmem : w ∈ T := by
      rw [← hkw]
      exact List.get_mem T ⟨k, hk⟩
    have hnot := (List.countP_eq_zero.mp hz') w hmem
    simp at hnot
  obtain ⟨l, hl, k, hk, hpow⟩ :=
    repeatedEdge_properPower_of_uniqueOut edges hT hne hinT huniq i j hij hjlt (hiT.trans hjT.symm)
  exact hprim ⟨l, hl, k, hk, hpow⟩

/-- **Branching: a primitive spelling of every nontrivial multiple.**  If the
support branches, then for every `m >= 2` the spectrum `m * c` has a *primitive*
cyclic edge-type spelling, namely `A^m ++ B^m` for the two excursions of the
two-excursion cut. -/
theorem branching_primitive_spellings {T : List (Fin L → α)} {s : Fin (L - 1) → α}
    (hT : TrailEnds winPrefix winSuffix T s s) (c : (Fin L → α) → ℕ)
    (huse : ∀ e, edgeUse T e = c e) (nodes : Finset (Fin (L - 1) → α))
    (edges : Finset (Fin L → α)) (hbranch : Branching nodes edges winPrefix winSuffix)
    (hvan : ∀ e, e ∉ edges → c e = 0) (hpos : ∀ e ∈ edges, 0 < c e) (m : ℕ) (hm2 : 2 ≤ m) :
    ∃ (A B : List (Fin L → α)) (v : Fin (L - 1) → α),
      TrailEnds winPrefix winSuffix A v v ∧ TrailEnds winPrefix winSuffix B v v ∧
      A ≠ [] ∧ B ≠ [] ∧ A[0]? ≠ B[0]? ∧
      (∃ w, TrailEnds winPrefix winSuffix (nCopies A m ++ nCopies B m) w w) ∧
      (∀ e, edgeUse (nCopies A m ++ nCopies B m) e = m * c e) ∧
      IsPrimitive (nCopies A m ++ nCopies B m) := by
  obtain ⟨v, e₁, he₁, e₂, he₂, he12, ht₁, ht₂⟩ := hbranch
  obtain ⟨A, B, w, hA, hB, hAne, hBne, hneAB, hadd⟩ :=
    two_excursions_of_branching (tail := winPrefix) (head := winSuffix) hT c huse edges v
      e₁ e₂ he₁ he₂ he12 ht₁ ht₂ hpos
  refine ⟨A, B, w, hA, hB, hAne, hBne, hneAB, ⟨w, trailNcopiesAppend (tail := winPrefix) (head := winSuffix) hA hB m⟩, ?_, ?_⟩
  · intro e
    calc edgeUse (nCopies A m ++ nCopies B m) e
        = edgeUse (nCopies A m) e + edgeUse (nCopies B m) e := edgeUse_append _ _ _
      _ = m * edgeUse A e + m * edgeUse B e := by
        rw [edgeUse_nCopies A m e, edgeUse_nCopies B m e]
      _ = m * (edgeUse A e + edgeUse B e) := (Nat.mul_add m _ _).symm
      _ = m * c e := by rw [hadd e]
  · exact ampbmp_isPrimitive_of_head_ne hAne hBne hm2 hneAB

end Spellings

/-! ## From cyclic edge-type spellings to circular words

The competitors produced by the branching direction must be genuine genomes, not
abstract edge-type lists.  `spell_exists_circulation` is the same Hierholzer +
window-spelling argument as `PopulationReduction.spell_exists_divided`, with no
division (`g = 1`), and `isPrimitive_of_primitiveTrail` transfers primitivity
from the edge-type list to the circular word. -/

section WordLayer

variable {α : Type} [DecidableEq α] {L : ℕ} [Fintype α]

/-- **Any balanced, positive, weakly connected circulation of total mass `G` is
spelled by a circular word of length `G` with exactly that complete spectrum.**
This is the `g = 1` case of `PopulationReduction.spell_exists_divided`: Hierholzer
gives a closed trail with the prescribed multiplicities, and the repository's
`spell_window`/`count_bridge` turn it into a word whose length-`L` windows are the
trail edges. -/
theorem spell_exists_circulation {G : ℕ} (hG : 0 < G) (_S : Fin G → α) (hL : 1 < L)
    (q : (Fin L → α) → ℕ) (hbal : CircBalanced winPrefix winSuffix q)
    (supp : Finset (Fin L → α)) (hsupp : ∀ e, e ∈ supp ↔ 0 < q e)
    (hne : supp.Nonempty) (hconn : WeakConn winPrefix winSuffix supp)
    (htot : ∑ w : Fin L → α, q w = G) :
    ∃ (m : ℕ) (hW : 0 < m) (W : Fin m → α),
      specCount (L := L) hW W = q ∧ m = G := by
  obtain ⟨T, s, hTclosed, hTuse⟩ :=
    eulerian_closed_trail winPrefix winSuffix q hbal supp hsupp hne hconn
  have hTeq := length_eq_sum_edgeUse T
  have hsum : ∑ e, edgeUse T e = ∑ w : Fin L → α, q w :=
    Finset.sum_congr rfl (fun w _ => hTuse w)
  have hTne : T ≠ [] := by
    intro h0
    have hzero : ∀ e, edgeUse T e = 0 := by
      intro e
      rw [h0]
      rfl
    have hq0 : ∑ w : Fin L → α, q w = 0 := by
      rw [← hsum]
      simp only [hzero]
      simp
    omega
  have hlenT : 0 < T.length := length_pos_of_ne_nil hTne
  have hlenT' : T.length = G := by
    rw [hTeq, hsum, htot]
  have hL0 : 0 < L := by omega
  have hadj : ∀ j : Fin T.length, winSuffix (T.get j)
      = winPrefix (T.get ⟨(j.val + 1) % T.length, Nat.mod_lt _ hlenT⟩) := by
    intro j
    have hbase := trail_cyc_adj hTclosed hlenT j.val j.isLt
    have b1 : PopulationReduction.cycEdge T hlenT j.val = T.get j := by
      unfold PopulationReduction.cycEdge
      congr 1
      exact Fin.ext (Nat.mod_eq_of_lt j.isLt)
    have b2 : PopulationReduction.cycEdge T hlenT ((j.val + 1) % T.length)
        = T.get ⟨(j.val + 1) % T.length, Nat.mod_lt _ hlenT⟩ := by
      unfold PopulationReduction.cycEdge
      congr 1
      apply Fin.ext
      exact Nat.mod_mod_of_dvd _ dvd_rfl
    rw [b1, b2] at hbase
    exact hbase
  refine ⟨T.length, hlenT, spellWord hL0 T.get, ?_, hlenT'⟩
  funext w
  have hwin : ∀ r : Fin T.length,
      window (L := L) hlenT (spellWord hL0 T.get) r = T.get r :=
    fun r => spell_window T.get hlenT hL0 hadj r
  have hspec : specCount (L := L) hlenT (spellWord hL0 T.get) w = edgeUse T w := by
    have hset : Finset.univ.filter
        (fun r : Fin T.length => window (L := L) hlenT (spellWord hL0 T.get) r = w)
        = Finset.univ.filter (fun r : Fin T.length => T.get r = w) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hwin r]
    have hsp : specCount (L := L) hlenT (spellWord hL0 T.get) w
        = (Finset.univ.filter
          (fun r : Fin T.length => window (L := L) hlenT (spellWord hL0 T.get) r = w)).card :=
      rfl
    rw [hsp, hset]
    exact count_bridge T w
  rw [hspec]
  exact hTuse w

omit [DecidableEq α] [Fintype α] in
/-- **A circular word whose window trail is a primitive cyclic edge-type
spelling is primitive.**  A nontrivial power `W = U^k` of a word has its
length-`L` window sequence cyclically periodic with period `|U| < |W|`, so the
window trail — and hence the edge-type spelling — is a proper power, contradicting
primitivity of the trail.  This is the word-level counterpart of
`properPower_of_cyclicPeriod`, and it is what makes the branching competitor a
*genome* rather than an edge-type list. -/
theorem isPrimitive_of_primitiveTrail {H : ℕ} (hH0 : 0 < H) (W : Fin H → α)
    (T : List (Fin L → α)) (hlen : T.length = H)
    (hwin : ∀ r : Fin H, window (L := L) hH0 W r
      = PopulationReduction.cycEdge T (by omega) r.val)
    (hprim : IsPrimitive T) :
    PopulationReduction.IsPrimitive W := by
  rintro ⟨H0, hH0', U, q, hq, hG, hrep⟩
  have hH0pos : 0 < H0 := hH0'
  have hHlen : H0 * q = H := hG
  have hqpos : 1 < q := hq
  have hmul : H0 * 1 < H0 * q := Nat.mul_lt_mul_of_pos_left hqpos hH0pos
  have hHp : H0 < H := by rw [← hHlen]; omega
  have hdiv : H0 ∣ H := ⟨q, hHlen.symm⟩
  -- the `hrep` presentation makes the window sequence cyclically `H0`-periodic
  have hWrep : ∀ i : ℕ, W ⟨(i + H0) % H, Nat.mod_lt _ hH0⟩
      = W ⟨i % H, Nat.mod_lt _ hH0⟩ := by
    intro i
    have h3 : ((i + H0) % H) % H0 = i % H0 := by
      rw [Nat.mod_mod_of_dvd _ hdiv, Nat.add_mod, Nat.mod_self, Nat.add_zero,
        Nat.mod_mod]
    have hA : W ⟨(i + H0) % H, Nat.mod_lt _ hH0⟩
        = U ⟨i % H0, Nat.mod_lt _ hH0pos⟩ := by
      have hz := hrep ⟨(i + H0) % H, Nat.mod_lt _ hH0⟩
      rw [hz]
      congr 1
      exact Fin.ext h3
    have hB : W ⟨i % H, Nat.mod_lt _ hH0⟩
        = U ⟨i % H0, Nat.mod_lt _ hH0pos⟩ := by
      have hz := hrep ⟨i % H, Nat.mod_lt _ hH0⟩
      rw [hz]
      congr 1
      exact Fin.ext (Nat.mod_mod_of_dvd _ hdiv)
    exact hA.trans hB.symm
  -- hence the window sequence has `H0` as a cyclic period
  have hposT : 0 < T.length := by rw [hlen]; exact hH0
  have hwin' : ∀ (m : ℕ) (hm : m < T.length) (hmH : m < H),
      T[m]? = some (window (L := L) hH0 W ⟨m, hmH⟩) := by
    intro m hm hmH
    have hz := hwin ⟨m, hmH⟩
    have hce : PopulationReduction.cycEdge T hposT m = T[m]'hm := by
      unfold PopulationReduction.cycEdge
      congr 1
      exact Fin.ext (Nat.mod_eq_of_lt hm)
    rw [hz, hce, List.getElem?_eq_getElem hm]
  have hperiod : CyclicPeriod T H0 := by
    intro m hm
    have hmH : m < H := by rw [← hlen]; exact hm
    have hmT : (m + H0) % T.length < T.length := Nat.mod_lt _ hposT
    have hmmH : (m + H0) % T.length = (m + H0) % H := by
      rw [hlen]
    have hmmH' : (m + H0) % H < H := Nat.mod_lt _ hH0
    have hmmHT : (m + H0) % H < T.length := by rw [hlen]; exact hmmH'
    have h1 := hwin' m hm hmH
    have h2c : T[(m + H0) % H]? = some (window (L := L) hH0 W ⟨(m + H0) % H, hmmH'⟩) :=
      hwin' ((m + H0) % H) hmmHT hmmH'
    have hwinEq : window (L := L) hH0 W ⟨m, hmH⟩
        = window (L := L) hH0 W ⟨(m + H0) % H, hmmH'⟩ := by
      funext d
      change cyc hH0 W (m + d.val) = cyc hH0 W ((m + H0) % H + d.val)
      simp only [OrientedRigidity.cyc]
      have hstep : ((m + H0) % H + d.val) % H = (m + d.val + H0) % H := by
        rw [Nat.mod_add_mod]
        apply congrArg (fun n : ℕ => n % H)
        omega
      have hidx : (⟨((m + H0) % H + d.val) % H, Nat.mod_lt _ hH0⟩ : Fin H)
          = ⟨(m + d.val + H0) % H, Nat.mod_lt _ hH0⟩ := Fin.ext hstep
      rw [hidx]
      exact (hWrep (m + d.val)).symm
    calc T[m]? = some (window (L := L) hH0 W ⟨m, hmH⟩) := h1
      _ = some (window (L := L) hH0 W ⟨(m + H0) % H, hmmH'⟩) := by rw [hwinEq]
      _ = T[(m + H0) % H]? := h2c.symm
      _ = T[(m + H0) % T.length]? := by rw [hmmH]
  have hne : T ≠ [] := by
    intro h0
    rw [h0] at hposT
    simp at hposT
  have hHpT : H0 < T.length := by rw [hlen]; exact hHp
  obtain ⟨l, hl, k, hk, hpow⟩ := properPower_of_cyclicPeriod hne hH0pos hHpT hperiod
  exact hprim ⟨l, hl, k, hk, hpow⟩

end WordLayer

/-! ## The window trail of a circular word -/

section WindowTrail

variable {α : Type} [DecidableEq α] {L : ℕ} [Fintype α]

/-- The cyclic list of the `L`-windows of a circular word of length `H`.  This is
the "cyclic edge-type trail" that reads the genome; by `PopulationReduction`'s
window/node lemmas its edges are incidence-compatible in the cycle. -/
def winTrail {H : ℕ} (hH : 0 < H) (D : Fin H → α) : List (Fin L → α) :=
  List.ofFn fun r : Fin H => window (L := L) hH D r

omit [DecidableEq α] [Fintype α] in
theorem winTrail_length {H : ℕ} (hH : 0 < H) (D : Fin H → α) :
    (winTrail (L := L) hH D).length = H := List.length_ofFn

omit [DecidableEq α] [Fintype α] in
theorem winTrail_get {H : ℕ} (hH : 0 < H) (D : Fin H → α) (i : ℕ) (hi : i < H) :
    (winTrail (L := L) hH D)[i]? = some (window (L := L) hH D ⟨i, hi⟩) := by
  show (List.ofFn (fun r : Fin H => window (L := L) hH D r))[i]? = _
  rw [List.getElem?_ofFn]
  simp [hi]

omit [DecidableEq α] [Fintype α] in
/-- The prefix (node) of the window at `r`. -/
theorem winPrefix_window' {H : ℕ} (hH : 0 < H) (D : Fin H → α) (r : Fin H) :
    winPrefix (window (L := L) hH D r : Fin L → α) = nodeWindow hH D r := by
  funext d
  rfl

omit [DecidableEq α] [Fintype α] in
/-- The suffix (node) of the window at `r` is the node window at the next
start. -/
theorem winSuffix_window' {H : ℕ} (hH : 0 < H) (D : Fin H → α) (r : Fin H) :
    winSuffix (window (L := L) hH D r : Fin L → α)
      = nodeWindow hH D ⟨(r.val + 1) % H, Nat.mod_lt _ hH⟩ := by
  funext d
  have hmod : ((r.val + 1) % H + d.val) % H = (r.val + (d.val + 1)) % H := by
    rw [Nat.mod_add_mod]
    congr 1
    omega
  unfold winSuffix window nodeWindow OrientedRigidity.cyc
  apply congrArg D
  rw [Fin.mk.injEq]
  exact hmod.symm

/-- **An incidence-compatible list is a trail.**  If consecutive entries of a
nonempty list match (`head (T[i]) = tail (T[i+1])` for `i + 1 < |T|`), and the
first entry's tail is `s` while the last entry's head is `s`, then `T` is a
closed trail based at `s`. -/
theorem trail_of_step {E V : Type} [DecidableEq E] [DecidableEq V]
    (tail head : E → V) : ∀ (T : List E) (u v : V), T ≠ [] →
      (∀ (i : ℕ) (_hi : i + 1 < T.length) (e₁ e₂ : E),
        T[i]? = some e₁ → T[i + 1]? = some e₂ → head e₁ = tail e₂) →
      (∃ e, T[0]? = some e ∧ tail e = u) →
      (∃ e, T[T.length - 1]? = some e ∧ head e = v) →
      TrailEnds tail head T u v := by
  intro T
  induction T with
  | nil => intro u v hne _ _ _; exact absurd rfl hne
  | cons a T ih =>
      intro u v hne hstep hfirst hlast
      obtain ⟨e₀, he₀, htail0⟩ := hfirst
      obtain ⟨x, hx, hheadx⟩ := hlast
      by_cases hT : T = []
      · rw [hT] at he₀
        rw [List.getElem?_cons_zero] at he₀
        have hta : tail a = u := by
          rw [← Option.some.inj he₀.symm]
          exact htail0
        have hz : (a :: ([] : List E)).length - 1 = 0 := by simp
        rw [hT, hz, List.getElem?_cons_zero] at hx
        have hha : head a = v := by
          rw [← Option.some.inj hx.symm]
          exact hheadx
        rw [hT]
        exact .cons a [] u v hta (by rw [hha]; exact .nil v)
      · have hpt : 0 < T.length := List.length_pos_of_ne_nil hT
        have hlen : T.length + 1 = (a :: T).length := by simp
        have hsub : T.length + 1 - 1 = T.length := by omega
        -- the last entry of `T` is the last entry of `a :: T`
        have hx' : T[T.length - 1]? = some x := by
          have h3 := hx
          rw [← hlen, hsub, List.getElem?_cons, ite_eq_right (by omega)] at h3
          have h3' := h3
          rwa [List.getElem?_eq_getElem (by omega)] at h3'
        -- the first entry of `T` follows `a`
        have hta0 : tail (T.get ⟨0, hpt⟩) = head a := by
          have h3 := hstep 0 (by omega) a (T.get ⟨0, hpt⟩)
          refine (h3 (by rw [List.getElem?_cons, ite_eq_left rfl]) ?_).symm
          rw [show (0 + 1) = 1 from rfl, List.getElem?_cons_succ]
          exact List.getElem?_eq_getElem hpt
        have hstepT : ∀ (i : ℕ) (hi : i + 1 < T.length) (e₁ e₂ : E),
            T[i]? = some e₁ → T[i + 1]? = some e₂ → head e₁ = tail e₂ := by
          intro i hi e₁ e₂ h1 h2
          have h3 := hstep (i + 1) (by omega) e₁ e₂
          refine h3 ?_ ?_
          · simpa using h1
          · simpa using h2
        have hta : tail a = u := by
          rw [← Option.some.inj he₀.symm]
          exact htail0
        exact .cons a T u v hta
          (ih (head a) v hT hstepT ⟨T.get ⟨0, hpt⟩, List.getElem?_eq_getElem hpt, hta0⟩
            ⟨x, hx', hheadx⟩)

/-- A closed trail from incidence-compatible consecutive entries. -/
theorem trail_closed_of_step {E V : Type} [DecidableEq E] [DecidableEq V]
    (tail head : E → V) (T : List E) (s : V) (hne : T ≠ [])
    (hstep : ∀ (i : ℕ) (_hi : i + 1 < T.length) (e₁ e₂ : E),
      T[i]? = some e₁ → T[i + 1]? = some e₂ → head e₁ = tail e₂)
    (hfirst : ∃ e, T[0]? = some e ∧ tail e = s)
    (hlast : ∃ e, T[T.length - 1]? = some e ∧ head e = s) :
    TrailEnds tail head T s s :=
  trail_of_step tail head T s s hne hstep hfirst hlast

/-- **An incidence-compatible finite sequence is a trail.**  If consecutive
entries of `f : Fin n → E` match (`head (f i) = tail (f (i+1))`), then
`List.ofFn f` runs from the tail of its first entry to the head of its last. -/
theorem ofFn_trail {E V : Type} [DecidableEq E] [DecidableEq V]
    (tail head : E → V) : ∀ (n : ℕ) (f : Fin n → E) (u v : V), 0 < n →
      (∀ (h : n - 1 < n), head (f ⟨n - 1, h⟩) = v) →
      (∀ (i : Fin n) (hi : i.val + 1 < n),
        head (f i) = tail (f ⟨i.val + 1, by omega⟩)) →
      (∀ (h : 0 < n), tail (f ⟨0, h⟩) = u) →
      TrailEnds tail head (List.ofFn f) u v := by
  intro n
  induction n with
  | zero => intro f u v hn _ _ _; omega
  | succ m ihm =>
      intro f u v hn hlastv hadj hfirst
      cases m with
      | zero =>
          have hlast0 : head (f 0) = v := by
            have hEq : (⟨0 + 1 - 1, by omega⟩ : Fin (0 + 1)) = (0 : Fin (0 + 1)) := by
              rw [Fin.mk.injEq]
              omega
            exact hEq ▸ hlastv (by omega)
          rw [List.ofFn_succ, List.ofFn_zero]
          exact .cons (f 0) [] u v (hfirst hn) (by rw [hlast0]; exact .nil v)
      | succ m =>
          rw [List.ofFn_succ]
          refine .cons (f 0) _ u v (hfirst hn) ?_
          have hstart : ∀ (h : 0 < m + 1), tail (f 1) = head (f 0) := by
            intro h
            have h1 := hadj (0 : Fin (m + 1 + 1)) (by
              show (0 : ℕ) + 1 < m + 1 + 1
              omega)
            have hEq : ((⟨(0 : ℕ) + 1, by omega⟩ : Fin (m + 1 + 1)))
                = ((1 : Fin (m + 1 + 1)) : Fin (m + 1 + 1)) := by
              rw [Fin.mk.injEq]
              rfl
            exact (hEq.symm ▸ h1).symm
          have hlast' : ∀ (h : m + 1 + 1 - 1 < m + 1 + 1),
              head (f ⟨m + 1 + 1 - 1, h⟩) = v := by
            intro h
            have hEq : ((⟨m + 1 + 1 - 1, h⟩ : Fin (m + 1 + 1)))
                = ((⟨m + 1, by omega⟩ : Fin (m + 1 + 1)) : Fin (m + 1 + 1)) := by
              rw [Fin.mk.injEq]
              omega
            exact hEq ▸ hlastv (by omega)
          have hlast'' : ∀ (h : m + 1 - 1 < m + 1),
              head ((fun j : Fin (m + 1) => f (Fin.succ j)) ⟨m + 1 - 1, h⟩) = v := by
            intro h
            show head (f (Fin.succ (⟨m + 1 - 1, h⟩ : Fin (m + 1)))) = v
            rw [Fin.succ_mk]
            have hfin : ((⟨m + 1 - 1 + 1, by omega⟩ : Fin (m + 1 + 1)) : Fin (m + 1 + 1))
                = ((⟨m + 1 + 1 - 1, by omega⟩ : Fin (m + 1 + 1)) : Fin (m + 1 + 1)) := by
              apply Fin.ext
              show m + 1 - 1 + 1 = m + 1 + 1 - 1
              omega
            rw [hfin]
            exact hlastv (by omega)
          have hadj' : ∀ (i : Fin (m + 1)) (hi : i.val + 1 < m + 1),
              (head : E → V) ((fun j : Fin (m + 1) => f (Fin.succ j)) i)
                = (tail : E → V)
                    ((fun j : Fin (m + 1) => f (Fin.succ j)) ⟨i.val + 1, by omega⟩) := by
            intro i hi
            have hi' : i.val + 1 + 1 < m + 1 + 1 := by omega
            exact hadj (Fin.succ i) (by simpa using hi')
          exact ihm (fun i : Fin (m + 1) => f (Fin.succ i)) (head (f 0)) v
            (by omega) hlast'' hadj' hstart

/-- **The window trail of a circular word is a closed trail**: the `L`-windows of
a circular word read a closed edge-type trail, since the suffix of the window at
`r` is the prefix of the window at the next start. -/
theorem winTrail_closed {H : ℕ} (hH : 0 < H) (D : Fin H → α) :
    ∃ s, TrailEnds winPrefix winSuffix (winTrail (L := L) hH D) s s := by
  refine ⟨nodeWindow hH D ⟨0, hH⟩, ?_⟩
  have hstep : ∀ (i : Fin H) (hi : i.val + 1 < H),
      winSuffix (window (L := L) hH D i)
        = winPrefix (window (L := L) hH D ⟨i.val + 1, by omega⟩) := by
    intro i hi
    have hA := winSuffix_window' (L := L) hH D ⟨i.val, i.isLt⟩
    have hB := winPrefix_window' (L := L) hH D ⟨i.val + 1, by omega⟩
    rw [hA, hB]
    apply congrArg (nodeWindow hH D)
    apply Fin.ext
    show (i.val + 1) % H = i.val + 1
    exact Nat.mod_eq_of_lt hi
  refine ofFn_trail winPrefix winSuffix H
    (fun r : Fin H => window (L := L) hH D r)
    (nodeWindow hH D ⟨0, hH⟩) (nodeWindow hH D ⟨0, hH⟩) hH
    (by
      intro h
      rw [winSuffix_window' (L := L) hH D ⟨H - 1, h⟩]
      apply congrArg (nodeWindow hH D)
      apply Fin.ext
      show (H - 1 + 1) % H = 0
      rw [Nat.sub_add_cancel (by omega : 1 ≤ H), Nat.mod_self])
    hstep (fun h => winPrefix_window' (L := L) hH D ⟨0, h⟩)

/-- Counting in a list of all indices: `countP` over `List.ofFn` is the card of
the corresponding filtered finset. -/
theorem countP_ofFn {Y : ℕ} {X : Type} (f : Fin Y → X) (p : X → Bool) :
    (List.ofFn f).countP p
      = ((Finset.univ : Finset (Fin Y)).filter (fun r => p (f r))).card := by
  induction Y with
  | zero => simp
  | succ n ih =>
      have h1 : (List.ofFn f).countP p
          = (List.ofFn (fun i : Fin n => f i.succ)).countP p
            + if p (f 0) then 1 else 0 := by
        rw [List.ofFn_succ, List.countP_cons]
      have h2 : ((Finset.univ : Finset (Fin (n + 1))).filter (fun r => p (f r))).card
          = ((Finset.univ : Finset (Fin n)).filter (fun i => p (f i.succ))).card
            + if p (f 0) then 1 else 0 := by
        rw [Fin.card_filter_univ_succ']
        split <;> simp [Nat.add_comm]
      rw [h1, h2, ih]

omit [Fintype α] in
/-- The window trail spells the complete spectrum of the word. -/
theorem winTrail_edgeUse {H : ℕ} (hH : 0 < H) (D : Fin H → α) (e : Fin L → α) :
    edgeUse (winTrail (L := L) hH D) e = specCount (L := L) hH D e := by
  show (winTrail (L := L) hH D).countP (fun x => decide (x = e)) = _
  have h : (winTrail (L := L) hH D).countP (fun x => decide (x = e))
      = ((Finset.univ : Finset (Fin H)).filter
          (fun r : Fin H => decide (window (L := L) hH D r = e))).card := by
    rw [← countP_ofFn (fun r : Fin H => window (L := L) hH D r)
      (fun x : Fin L → α => decide (x = e))]
    rfl
  rw [h, specCount]
  congr 1
  ext r
  simp

end WindowTrail

/-! ## Realizing a closed trail as a circular word

`spell_exists_circulation` produces a word from a balanced circulation.  Here we
need the converse direction: a *given* closed edge-type trail is the window
trail of a circular word of the same length, with exactly the same spectrum.
This is the `TrailEnds → word` half of the same Hierholzer-free argument, and
it is what lets the branching construction hand its primitive trail to the word
layer. -/

section TrailToWord

variable {α : Type} [DecidableEq α] {L : ℕ} [Fintype α]

omit [Fintype α] in
/-- **A closed trail is the window trail of a circular word.**  If `T` is a
closed edge-type trail over `winPrefix`/`winSuffix` of positive length, then
there is a circular word `W` of length `|T|` whose complete spectrum is
`edgeUse T` and whose windows are the entries of `T`. -/
theorem word_of_closed_trail {T : List (Fin L → α)} {s : Fin (L - 1) → α}
    (hT : TrailEnds winPrefix winSuffix T s s) (hTne : T ≠ []) (hL : 1 < L) :
    ∃ (W : Fin T.length → α),
      specCount (L := L) (length_pos_of_ne_nil hTne) W = edgeUse T ∧
      (∀ r : Fin T.length, window (L := L) (length_pos_of_ne_nil hTne) W r = T.get r) := by
  have hlenT : 0 < T.length := length_pos_of_ne_nil hTne
  have hL0 : 0 < L := by omega
  have hadj : ∀ j : Fin T.length, winSuffix (T.get j)
      = winPrefix (T.get ⟨(j.val + 1) % T.length, Nat.mod_lt _ hlenT⟩) := by
    intro j
    have hbase := trail_cyc_adj hT hlenT j.val j.isLt
    have b1 : PopulationReduction.cycEdge T hlenT j.val = T.get j := by
      unfold PopulationReduction.cycEdge
      congr 1
      exact Fin.ext (Nat.mod_eq_of_lt j.isLt)
    have b2 : PopulationReduction.cycEdge T hlenT ((j.val + 1) % T.length)
        = T.get ⟨(j.val + 1) % T.length, Nat.mod_lt _ hlenT⟩ := by
      unfold PopulationReduction.cycEdge
      congr 1
      apply Fin.ext
      exact Nat.mod_mod_of_dvd _ dvd_rfl
    rw [b1, b2] at hbase
    exact hbase
  refine ⟨spellWord hL0 T.get, ?_, ?_⟩
  · funext w
    have hwin : ∀ r : Fin T.length,
        window (L := L) hlenT (spellWord hL0 T.get) r = T.get r :=
      fun r => spell_window T.get hlenT hL0 hadj r
    have hset : Finset.univ.filter
        (fun r : Fin T.length => window (L := L) hlenT (spellWord hL0 T.get) r = w)
        = Finset.univ.filter (fun r : Fin T.length => T.get r = w) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hwin r]
    have hsp : specCount (L := L) hlenT (spellWord hL0 T.get) w
        = (Finset.univ.filter
          (fun r : Fin T.length => window (L := L) hlenT (spellWord hL0 T.get) r = w)).card :=
      rfl
    rw [hsp, hset]
    exact count_bridge T w
  · intro r
    exact spell_window T.get hlenT hL0 hadj r

/-- **A proper power window trail forces a proper power word.**  If the window
trail of a circular word is a nontrivial repetition, then the word itself is a
nontrivial repetition. -/
theorem not_primitive_of_properPowerTrail {H : ℕ} (hH : 0 < H) (hL : 1 < L)
    (S : Fin H → α)
    {l : List (Fin L → α)} {k : ℕ} (hl : l ≠ []) (hk : 2 ≤ k)
    (hpow : winTrail (L := L) hH S = nCopies l k) :
    ¬ PopulationReduction.IsPrimitive S := by
  intro hprim
  have hlen : (winTrail (L := L) hH S).length = H := winTrail_length hH S
  have hL0 : 0 < L := by omega
  have hlenl : 0 < l.length := length_pos_of_ne_nil hl
  have hmul : l.length * k = H := by
    have h1 := congrArg List.length hpow
    rw [nCopies_length] at h1
    rw [hlen] at h1
    rw [Nat.mul_comm] at h1
    exact h1.symm
  have hget : ∀ (i : ℕ) (hi : i < H),
      (winTrail (L := L) hH S)[i]? = l[i % l.length]? := by
    intro i hi
    have hi' : i < (winTrail (L := L) hH S).length := by rw [hlen]; exact hi
    have h2 : (winTrail (L := L) hH S)[i]? = (nCopies l k)[i]? := by rw [hpow]
    rw [h2]
    exact nCopies_getElem? (hpow ▸ hi')
  have hS : ∀ (i : Fin H),
      S i = (l.get (Fin.mk (i.val % l.length) (Nat.mod_lt _ hlenl)) : Fin L → α)
        ⟨0, hL0⟩ := by
    intro i
    have hi : i.val < H := i.isLt
    have h1 := hget i.val hi
    have h2 := winTrail_get (L := L) hH S i.val hi
    have h1' : some (window (L := L) hH S ⟨i.val, hi⟩) = l[i.val % l.length]? :=
      h2.symm.trans (hget i.val hi)
    have hletter : (window (L := L) hH S ⟨i.val, hi⟩ : Fin L → α) ⟨0, hL0⟩ = S i := by
      unfold OrientedRigidity.window
      simp only [OrientedRigidity.cyc]
      congr 1
      apply Fin.ext
      exact Nat.mod_eq_of_lt i.isLt
    have h4 : some (window (L := L) hH S ⟨i.val, hi⟩) = l[i.val % l.length]? := h1'
    rw [List.getElem?_eq_getElem (Nat.mod_lt _ hlenl)] at h4
    have h5 : window (L := L) hH S ⟨i.val, hi⟩
        = l.get (Fin.mk (i.val % l.length) (Nat.mod_lt _ hlenl)) := Option.some.inj h4
    have h6 := congrArg (fun f : Fin L → α => f ⟨0, hL0⟩) h5
    rwa [hletter] at h6
  have hk2 : 1 < k := by omega
  exact hprim ⟨l.length, hlenl,
    fun j : Fin l.length => (l.get j : Fin L → α) ⟨0, hL0⟩,
    k, hk2, hmul, fun i => hS i⟩

end TrailToWord

/-! ## The normalized-spectrum ray

A candidate whose normalized complete spectrum agrees with the truth's has its
count vector on the *same* integer ray, and its length is the corresponding
multiple of the primitive length.  This is the arithmetic behind the "membership
on the same integer ray" step of `docs/scalar-primitive-spellings-83.md`,
stated using the gcd-one property of the primitive point rather than a division
free identity. -/

section Ray

variable {W : Type} [DecidableEq W] [Fintype W]

/-- Cancelling a common left factor in an equation with reassociated products. -/
private theorem mul_cancel_left' {E A C : ℕ} (hE : 0 < E)
    (h : E * A = E * C) : A = C := Nat.mul_left_cancel hE h

omit [DecidableEq W] [Fintype W] in
/-- If `cD w * d = c0 w * H` for every `w`, `0 < d`, and `c0` is gcd-one, then
`d` divides `H` and `cD w = (H / d) * c0 w`. -/
theorem ray_multiple {d H : ℕ} (c0 cD : W → ℕ)
    (hd : 0 < d) (hgcd : IsGcdOne c0) (hmul : ∀ w, cD w * d = c0 w * H) :
    d ∣ H ∧ ∀ w, cD w = (H / d) * c0 w := by
  -- the reduced factors are coprime
  set e := Nat.gcd d H with he
  have hepos : 0 < e := Nat.gcd_pos_of_pos_left H hd
  have hed : e ∣ d := Nat.gcd_dvd_left _ _
  have heH : e ∣ H := Nat.gcd_dvd_right _ _
  have hed' : e * (d / e) = d := Nat.mul_div_cancel' hed
  have heH' : e * (H / e) = H := Nat.mul_div_cancel' heH
  have hcop : Nat.Coprime (d / e) (H / e) := by
    have h1 := Nat.gcd_div hed heH
    have h2 : Nat.gcd (d / e) (H / e) = 1 := by
      rw [h1, he, Nat.div_self hepos]
    rw [Nat.coprime_iff_gcd_eq_one, h2]
  -- the coprime factor of `d` divides every `c0 w`, so gcd-one forces it to be 1
  have hde : d / e = 1 := by
    refine hgcd (d / e) ?_
    intro w
    have h2 := hmul w
    have h3 : cD w * (d / e) = c0 w * (H / e) := by
      have h4 := h2
      rw [← hed', ← heH'] at h4
      have h5 : e * (cD w * (d / e)) = e * (c0 w * (H / e)) := by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h4
      exact mul_cancel_left' hepos h5
    refine Nat.Coprime.dvd_of_dvd_mul_left hcop ?_
    refine ⟨cD w, ?_⟩
    have h4 := h3
    rw [Nat.mul_comm (cD w) (d / e)] at h4
    have h5 := h4.symm
    rwa [Nat.mul_comm (c0 w) (H / e)] at h5
  have hde' : d = e := by
    have h1 := hed'
    rw [hde, Nat.mul_one] at h1
    exact h1.symm
  have hdv : d ∣ H := by rw [hde']; exact heH
  refine ⟨hdv, fun w => ?_⟩
  have h2 := hmul w
  have h3 : c0 w * (H / e) = cD w := by
    have h4 := h2
    rw [← hed', ← heH'] at h4
    have h5 : e * (cD w * (d / e)) = e * (c0 w * (H / e)) := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h4
    have h6 : cD w * (d / e) = c0 w * (H / e) := mul_cancel_left' hepos h5
    rw [hde, Nat.mul_one] at h6
    exact h6.symm
  have h4 : H / e = H / d := by rw [hde']
  rw [h4] at h3
  rw [Nat.mul_comm]
  exact h3.symm

/-- **Normalized-spectrum equality means membership on the same integer ray.**
If the truth spectrum is `g * c0` on the primitive point `c0` (`IsGcdOne c0`),
the truth totals `G`, and a candidate of length `H` has the same normalized
complete spectrum, then its count vector is `m * c0` for some `m >= 1` and
`H = m * (G / g)`. -/
theorem spectrum_on_ray {G H g : ℕ} (hG : 0 < G) (hH : 0 < H) (hg0 : 0 < g)
    (c0 cS cD : W → ℕ)
    (hS : ∀ w, cS w = g * c0 w)
    (hSsum : ∑ w : W, cS w = G)
    (hNorm : ∀ w, cS w * H = cD w * G) (hgcd : IsGcdOne c0) :
    ∃ m, 1 ≤ m ∧ H = m * (G / g) ∧ ∀ w, cD w = m * c0 w := by
  -- `G` is `g` times the mass of `c0`
  have hexp : G = g * (∑ w : W, c0 w) := by
    calc G = ∑ w : W, cS w := hSsum.symm
      _ = ∑ w : W, g * c0 w := Finset.sum_congr rfl (fun w _ => hS w)
      _ = g * ∑ w : W, c0 w := by
          rw [Finset.mul_sum]
  have hcomm := hexp
  rw [Nat.mul_comm] at hcomm
  have hS0 : (∑ w : W, c0 w) = G / g :=
    (Nat.div_eq_of_eq_mul_left hg0 hcomm).symm
  have hS0pos : 0 < G / g := by
    by_contra hcon
    have hz : G / g = 0 := by omega
    have h1 := hexp
    rw [hS0, hz] at h1
    simp at h1
    omega
  -- cancellation of the common factor `g`
  have hmul : ∀ w, cD w * (G / g) = c0 w * H := by
    intro w
    have h1 := hNorm w
    rw [hS w] at h1
    have h2 : G = g * (G / g) := by rw [← hS0, hexp]
    rw [h2] at h1
    have h1' : g * (c0 w * H) = g * (cD w * (G / g)) := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h1
    exact (mul_cancel_left' hg0 h1').symm
  obtain ⟨hdvd, hD⟩ := ray_multiple c0 cD hS0pos hgcd hmul
  refine ⟨H / (G / g), ?_, ?_, ?_⟩
  · have h1 : 0 < H / (G / g) := Nat.div_pos (Nat.le_of_dvd hH hdvd) hS0pos
    omega
  · have h1 : (G / g) * (H / (G / g)) = H := Nat.mul_div_cancel' hdvd
    exact h1.symm.trans (Nat.mul_comm _ _)
  · intro w
    exact hD w

end Ray

/-! ## The final classification

Everything above lives on the real `OrientedRigidity` graph.  We now state the
fixed-truth classification of `docs/scalar-primitive-spellings-83.md`:

> A primitive truth is identifiable among variable-length primitive candidates
> from its normalized complete spectrum **iff** its spectrum support has no
> vertex with two distinct outgoing edge types.

The hypotheses are model-level only: the truth `S` is a circular word of length
`G > 0` over `α` with `L > 1`, and `S` is primitive.  Candidates are *primitive
circular words of arbitrary positive length*; identification is up to cyclic
rotation, as in `PopulationReduction.RotEquiv`.  No complete-spectrum
uniqueness premise is assumed anywhere in this section. -/

section Classification

variable {α : Type} [DecidableEq α] [Fintype α] {G : ℕ} {L : ℕ}

/-- **Identification of a candidate with the truth**: given that the candidate
has the truth's length, it is a rotation of the truth.  This is exactly
`PopulationReduction.RotEquiv` on the identified index carrier. -/
def Identified {G : ℕ} (hG : 0 < G) {m : ℕ} (D : Fin m → α) (hm : m = G)
    (S : Fin G → α) : Prop :=
  RotEquiv hG (fun i => D (Fin.cast hm.symm i)) S

omit [DecidableEq α] [Fintype α] in
/-- Identification is exactly rotation-equivivalence. -/
theorem identified_iff_rotEquiv {G m : ℕ} (hG : 0 < G) (D : Fin m → α) (hm : m = G)
    (S : Fin G → α) :
    Identified hG D hm S ↔ RotEquiv hG (fun i => D (Fin.cast hm.symm i)) S := by
  rfl

/-- **Identifiability from the normalized complete spectrum**, among primitive
candidates of arbitrary length.  A candidate `D : Fin m → α` is identified with
`S` when it has the same length `G` and is a rotation of `S`.  The normalized
spectrum condition is multiplicative (no division): the candidate spectrum
scaled by `G` equals the truth spectrum scaled by the candidate length `m`. -/
def Identifiable {G : ℕ} {L : ℕ} (hG : 0 < G) (_hL : 1 < L) (S : Fin G → α) : Prop :=
  ∀ (m : ℕ) (D : Fin m → α) (hD : 0 < m), PopulationReduction.IsPrimitive D →
    (∀ w, specCount (L := L) hG S w * m = specCount (L := L) hD D w * G) →
    ∃ hm : m = G, Identified hG D hm S

/-- The truth's window trail is a closed edge-type trail, and it spells the
truth's complete spectrum. -/
theorem truth_trail_closed {hG : 0 < G} (S : Fin G → α) :
    ∃ s, TrailEnds winPrefix winSuffix (winTrail (L := L) hG S) s s :=
  winTrail_closed hG S

theorem truth_trail_spectrum {hG : 0 < G} (S : Fin G → α) :
    ∀ w, edgeUse (winTrail (L := L) hG S) w = specCount (L := L) hG S w :=
  fun w => winTrail_edgeUse hG S w

/-- The truth's window trail is primitive, since it is the window reading of a
primitive word. -/
theorem truth_trail_primitive {hG : 0 < G} {hL : 1 < L} (S : Fin G → α)
    (hS : PopulationReduction.IsPrimitive S) : IsPrimitive (winTrail (L := L) hG S) := by
  intro hpow
  obtain ⟨l, hl, k, hk, hp⟩ := hpow
  exact not_primitive_of_properPowerTrail hG hL S hl hk hp hS

omit [Fintype α] in
/-- **Every support edge type of the truth has at most one successor.**  This is
the "uniqueness" hypothesis extracted from nonbranching of the spectrum-support
graph: two support edges leaving the same node are equal. -/
theorem uniqueOut_of_nonbranching {hG : 0 < G} {_hL : 1 < L} {S : Fin G → α}
    (hnb : NonBranching (genomeNodes (L := L) hG S) (support (L := L) hG S)
      (winPrefix (L := L)) (winSuffix (L := L)))
    (e₁ e₂ : Fin L → α) (h₁ : e₁ ∈ support (L := L) hG S)
    (h₂ : e₂ ∈ support (L := L) hG S)
    (ht : winPrefix (L := L) e₁ = winPrefix (L := L) e₂) : e₁ = e₂ := by
  exact hnb (winPrefix (L := L) e₁) e₁ h₁ e₂ h₂ (by rfl) ht.symm

omit [Fintype α] in
/-- Off the support the truth's complete spectrum vanishes. -/
theorem truth_van {hG : 0 < G} (S : Fin G → α) (w : Fin L → α)
    (hw : w ∉ support (L := L) hG S) : specCount (L := L) hG S w = 0 := by
  have h1 := (mem_support_iff (L := L) hG S w).mpr
  by_contra hc
  exact absurd (h1 (by omega)) hw

/-- **The truth's complete spectrum on a nonbranching support.**  A primitive
truth whose spectrum-support graph does not branch has `specCount = 1` on its
whole support: its own window trail is a primitive cyclic spelling of its
complete spectrum (`truth_trail_primitive`), and a primitive spelling of a
nonbranching support uses every support edge exactly once
(`nonbranching_primitive_spelling_eq_one`). -/
theorem one_on_support_of_nonbranching_primitive {hG : 0 < G} {hL : 1 < L}
    {S : Fin G → α} (hS : PopulationReduction.IsPrimitive S)
    (hnb : NonBranching (genomeNodes (L := L) hG S) (support (L := L) hG S)
      (winPrefix (L := L)) (winSuffix (L := L))) :
    ∀ e ∈ support (L := L) hG S, specCount (L := L) hG S e = 1 := by
  obtain ⟨s, hT⟩ := truth_trail_closed (L := L) S
  have hne : winTrail (L := L) hG S ≠ [] := by
    intro h0
    have hz : (winTrail (L := L) hG S).length = 0 := by rw [h0, List.length_nil]
    have h1 := winTrail_length (L := L) hG S
    rw [h1] at hz
    omega
  exact nonbranching_primitive_spelling_eq_one hT hne (specCount (L := L) hG S)
    (truth_trail_spectrum (L := L) S) (support (L := L) hG S)
    (fun e₁ he₁ e₂ he₂ ht => uniqueOut_of_nonbranching (hL := hL) hnb e₁ e₂ he₁ he₂ ht)
    (fun e' he' => truth_van (L := L) S e' he')
    (fun e' he' => truth_pos_on_support (L := L) hG S e' he')
    (truth_trail_primitive (L := L) (hL := hL) S hS)

/-- The truth's complete spectrum totals `G` over the whole read-type space:
the support sum is the total, since off-support counts vanish. -/
theorem truth_total_all {hG : 0 < G} (S : Fin G → α) :
    ∑ w : Fin L → α, specCount (L := L) hG S w = G := by
  have h1 := truth_total (L := L) hG S
  have h2 : ∑ w : Fin L → α, specCount (L := L) hG S w
      = ∑ w ∈ support (L := L) hG S, specCount (L := L) hG S w :=
    (Finset.sum_subset (fun b _ => Finset.mem_univ _)
      (fun b _ hb => truth_van (L := L) S b hb)).symm
  rw [h2]
  exact h1

omit [Fintype α] in
/-- The truth's support is nonempty: its complete spectrum totals `G > 0`. -/
theorem support_ne_nil_of_truth {hG : 0 < G} (S : Fin G → α) :
    (support (L := L) hG S).Nonempty := by
  have h1 := truth_total (L := L) hG S
  by_contra hcon
  have h5 : support (L := L) hG S = ∅ := by simpa using hcon
  have h1' : (∑ w ∈ support (L := L) hG S, specCount (L := L) hG S w) = 0 := by
    rw [h5]
    simp
  rw [h1'] at h1
  omega

/-- **Nonbranching makes the truth's spectrum gcd-one.**  Every support count is
`1` and every off-support count is `0`, so the gcd of the complete spectrum is
`1`.  This is the primitive point of the integer spectrum ray, and it is
obtained from the *deterministic graph condition alone* — no complete-spectrum
uniqueness input of any kind. -/
theorem gcdOne_of_nonbranching_primitive {hG : 0 < G} {hL : 1 < L} {S : Fin G → α}
    (hS : PopulationReduction.IsPrimitive S)
    (hnb : NonBranching (genomeNodes (L := L) hG S) (support (L := L) hG S)
      (winPrefix (L := L)) (winSuffix (L := L))) :
    IsGcdOne (W := Fin L → α) (specCount (L := L) hG S) := by
  intro g hg
  have hone := one_on_support_of_nonbranching_primitive (L := L) (hL := hL) hS hnb
  obtain ⟨e, he⟩ := support_ne_nil_of_truth (L := L) (hG := hG) S
  have hz := hg e
  rw [hone e he] at hz
  exact Nat.eq_one_of_dvd_one hz

/-! ## Forced traversal: one agreeing window pins down the whole walk

The lemmas below replace the external same-length complete-spectrum uniqueness
(BBT) that the rest of the project takes as an explicit premise.

The key point is that a *walk* along a circular word moves deterministically: the
length-`(L-1)` prefix of the window read at start `i + 1` is the length-`(L-1)`
suffix of the window read at start `i` (`winPrefix_winAt`).  Note that this alone
does **not** determine the next window — `winPrefix` records the letters at
positions `0 … L-2`, so the last letter of the next window is new information,
and a branching support can supply it in more than one way.  What closes the gap
is exactly the hypothesis of issue #92: on a **nonbranching** support two edges
out of the same node are equal, so the two windows at the next start, being two
support edges out of one node, are equal.  Induction on the offset therefore
pins the whole traversal (`winAt_agrees`): the candidate reads the truth from a
shifted start, and `rotEquiv_of_shift` turns that into
`PopulationReduction.RotEquiv`. -/

/-- The `L`-window of `D` read `t` steps after the start `j`. -/
def winAt {H : ℕ} (hH : 0 < H) (D : Fin H → α) (j : Fin H) (t : ℕ) : Fin L → α :=
  window (L := L) hH D ⟨(j.val + t) % H, Nat.mod_lt _ hH⟩

omit [DecidableEq α] [Fintype α] in
/-- `winAt` at step `0` is the window itself. -/
theorem winAt_zero' {H : ℕ} (hH : 0 < H) (D : Fin H → α) (r : Fin H) :
    winAt (L := L) hH D r 0 = window (L := L) hH D r := by
  unfold winAt
  congr 1
  apply Fin.ext
  exact Nat.mod_eq_of_lt r.isLt

omit [DecidableEq α] [Fintype α] in
/-- The prefix of the window at the next start is the suffix of the current one:
the deterministic step of the walk. -/
theorem winPrefix_winAt {H : ℕ} (hH : 0 < H) (D : Fin H → α) (j : Fin H) (t : ℕ) :
    winPrefix (L := L) (winAt (L := L) hH D j (t + 1))
      = winSuffix (L := L) (winAt (L := L) hH D j t) := by
  funext d
  have hmod : ((j.val + (t + 1)) % H + d.val) % H = ((j.val + t + (d.val + 1)) % H) := by
    rw [Nat.mod_add_mod]
    congr 1
    omega
  unfold winSuffix winPrefix winAt window OrientedRigidity.cyc
  apply congrArg D
  exact Fin.ext (by simpa using hmod)

omit [DecidableEq α] [Fintype α] in
/-- `winAt` read from the zero start. -/
theorem winAt_B {H : ℕ} (hH : 0 < H) (B : Fin H → α) (t : ℕ) :
    winAt (L := L) hH B ⟨0, hH⟩ t
      = window (L := L) hH B ⟨t % H, Nat.mod_lt _ hH⟩ := by
  unfold winAt
  congr 1
  apply Fin.ext
  simp

omit [DecidableEq α] [Fintype α] in
/-- `winAt` from an arbitrary start is the window at the shifted start. -/
theorem winAt_A {H : ℕ} (hH : 0 < H) (B : Fin H → α) (j : Fin H) (t : ℕ) :
    winAt (L := L) hH B j t
      = window (L := L) hH B ⟨(j.val + t) % H, Nat.mod_lt _ hH⟩ := rfl

omit [Fintype α] in
/-- A support window is a member of the support. -/
theorem mem_support_window (S : Fin G → α) (hG : 0 < G) (j : Fin G) :
    window (L := L) hG S j ∈ support (L := L) hG S :=
  Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

/-- **Forced traversal on a nonbranching support.**  If the truth's and the
candidate's windows agree at one start, they agree at every start.

Proof.  Induction on the offset.  The window at offset `t + 1` is a support
window on both sides, and its length-`(L-1)` prefix is the length-`(L-1)` suffix
of the window at offset `t` (`winPrefix_winAt`), which the induction hypothesis
already matches.  So the two windows at offset `t + 1` are two support edges out
of the *same* node, and a nonbranching support admits at most one such edge
(`uniqueOut_of_nonbranching`). -/
theorem winAt_agrees {G : ℕ} (hG : 0 < G) {hL : 1 < L} (S D : Fin G → α) (j : Fin G)
    (hsup : support (L := L) hG S = support (L := L) hG D)
    (hnb : NonBranching (genomeNodes (L := L) hG S) (support (L := L) hG S)
      (winPrefix (L := L)) (winSuffix (L := L)))
    (h0 : winAt (L := L) hG S j 0 = winAt (L := L) hG D ⟨0, hG⟩ 0) (t : ℕ) :
    winAt (L := L) hG S j t = winAt (L := L) hG D ⟨0, hG⟩ t := by
  induction t with
  | zero => exact h0
  | succ t ih =>
      have hpf : winPrefix (L := L) (winAt (L := L) hG S j (t + 1))
          = winPrefix (L := L) (winAt (L := L) hG D ⟨0, hG⟩ (t + 1)) := by
        rw [winPrefix_winAt, winPrefix_winAt,
          congrArg (fun e : Fin L → α => winSuffix (L := L) e) ih]
      exact uniqueOut_of_nonbranching (hL := hL) hnb
        (winAt (L := L) hG S j (t + 1)) (winAt (L := L) hG D ⟨0, hG⟩ (t + 1))
        (by unfold winAt; exact mem_support_window S hG _)
        (by refine hsup ▸ ?_; unfold winAt; exact mem_support_window D hG _)
        hpf

/-- A window prefix of a support window is a prefix of a support element. -/
theorem winPrefix_mem_image (S : Fin G → α) (hG : 0 < G) (j : Fin G) :
    winPrefix (L := L) (window (L := L) hG S j)
      ∈ (support (L := L) hG S).image (winPrefix (L := L)) :=
  Finset.mem_image.mpr ⟨window (L := L) hG S j,
    Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, winPrefix_window' (L := L) hG S j⟩

omit [DecidableEq α] [Fintype α] in
/-- **Rotation from a forward shift, in the exact orientation of
`PopulationReduction.RotEquiv`.**  If the candidate reads the truth shifted
forward by `s < G`, i.e. `D n = S ((s + n) mod G)`, then `D` rotated forward by
`k = G - s` spells `S`: for each `i`, apply `hs` at
`q = (i + (G - s)) mod G`, and note `(s + q) mod G = i`.  That index fact is the
whole content, and it is arithmetic only:
`(s + (i + (G - s)) mod G) mod G = (i + G) mod G = i mod G = i`, by
`Nat.add_mod_mod`, `Nat.sub_add_cancel` (using `s ≤ G`), the repository's
`AmpBmpPrimitivity.mod_add_self` and `Nat.mod_eq_of_lt`. -/
theorem rotEquiv_of_shift {G : ℕ} (hG : 0 < G) {D S : Fin G → α} (s : ℕ)
    (hslt : s < G)
    (hs : ∀ (n : ℕ) (hn : n < G), D ⟨n, hn⟩
      = S ⟨(s + n) % G, Nat.mod_lt _ hG⟩) : RotEquiv hG D S := by
  refine ⟨G - s, fun i => ?_⟩
  have h1 := hs ((i.val + (G - s)) % G) (Nat.mod_lt (i.val + (G - s)) hG)
  have hstep : s + (i.val + (G - s)) = i.val + G := by omega
  have hmod : (s + (i.val + (G - s)) % G) % G = i.val := by
    calc (s + (i.val + (G - s)) % G) % G
        = (s + (i.val + (G - s))) % G := Nat.add_mod_mod _ _ _
      _ = (i.val + G) % G := by rw [hstep]
      _ = i.val % G := mod_add_self G i.val
      _ = i.val := Nat.mod_eq_of_lt i.isLt
  rw [h1]
  congr 1
  apply Fin.ext
  exact hmod

/-- **Same-length complete-spectrum uniqueness.**  Two circular words of the same
length with the same complete `L`-spectrum differ by a rotation.

Proof.  Equal spectra give equal supports, and the candidate's window at start
`0` is a support window of the truth, so it is *some* truth window, say the one
started at `j`.  The support is a functional graph, so two support edges out of
the same node are equal: the two traversals, which agree at start `0` and share
the deterministic prefix/suffix step, agree at every start (`winAt_agrees`).
The candidate's window at start `i` is therefore the truth's window at start
`j + i`.  Reading the window's first letter gives `D n = S ((j + n) mod G)`, and
`rotEquiv_of_shift` turns that into `RotEquiv`.

This is the replacement for the BBT premise; it is used only in the
nonbranching direction, which is where the support is functional. -/
theorem rotEquiv_of_specCount_eq {G : ℕ} (hG : 0 < G) {hL : 1 < L} (S D : Fin G → α)
    (hnb : NonBranching (genomeNodes (L := L) hG S) (support (L := L) hG S)
      (winPrefix (L := L)) (winSuffix (L := L)))
    (hspec : specCount (L := L) hG S = specCount (L := L) hG D) :
    RotEquiv hG D S := by
  have hsup : support (L := L) hG S = support (L := L) hG D := by
    ext w
    rw [mem_support_iff (L := L) hG S w, mem_support_iff (L := L) hG D w,
      congrFun hspec w]
  -- align: some truth window is the candidate's window at start `0`
  obtain ⟨j, hj⟩ : ∃ j : Fin G, window (L := L) hG S j = window (L := L) hG D ⟨0, hG⟩ := by
    have hmem : window (L := L) hG D ⟨0, hG⟩ ∈ support (L := L) hG D :=
      mem_support_window D hG ⟨0, hG⟩
    rw [← hsup] at hmem
    obtain ⟨r, hr, hwr⟩ := Finset.mem_image.mp hmem
    exact ⟨r, hwr⟩
  -- the walk is pinned: agreeing at start `0` forces agreement at every start
  have hj' : winAt (L := L) hG S j 0 = winAt (L := L) hG D ⟨0, hG⟩ 0 :=
    (winAt_zero' (L := L) hG S j).trans
      (hj.trans (winAt_zero' (L := L) hG D ⟨0, hG⟩).symm)
  have halign : ∀ (i : Fin G), window (L := L) hG D i
      = window (L := L) hG S ⟨(j.val + i.val) % G, Nat.mod_lt _ hG⟩ := by
    intro i
    have h := winAt_agrees hG (L := L) (hL := hL) S D j hsup hnb hj' i.val
    rw [winAt_A, winAt_B] at h
    calc window (L := L) hG D i
        = window (L := L) hG D ⟨i.val % G, Nat.mod_lt _ hG⟩ := by
          apply congrArg (fun r : Fin G => window (L := L) hG D r)
          apply Fin.ext
          exact (Nat.mod_eq_of_lt i.isLt).symm
      _ = window (L := L) hG S ⟨(j.val + i.val) % G, Nat.mod_lt _ hG⟩ := h.symm
  -- aligned windows give aligned letters: the candidate reads the truth shifted
  have hs : ∀ (n : ℕ) (hn : n < G), D ⟨n, hn⟩
      = S ⟨(j.val + n) % G, Nat.mod_lt _ hG⟩ := by
    intro n hn
    have h1 := congrArg (fun e : Fin L → α => e ⟨0, by omega⟩)
      (halign ⟨n, hn⟩)
    unfold window OrientedRigidity.cyc at h1
    have hDfin : (⟨(n + 0) % G, Nat.mod_lt _ hG⟩ : Fin G) = ⟨n, hn⟩ :=
      Fin.ext (Nat.mod_eq_of_lt hn)
    have hSfin : (⟨((j.val + n) % G + 0) % G, Nat.mod_lt _ hG⟩ : Fin G)
        = ⟨(j.val + n) % G, Nat.mod_lt _ hG⟩ := Fin.ext (by simp)
    calc D ⟨n, hn⟩
        = D (⟨(n + 0) % G, Nat.mod_lt _ hG⟩ : Fin G) := by rw [hDfin]
      _ = S (⟨((j.val + n) % G + 0) % G, Nat.mod_lt _ hG⟩ : Fin G) := h1
      _ = S ⟨(j.val + n) % G, Nat.mod_lt _ hG⟩ := by rw [hSfin]
  exact rotEquiv_of_shift hG j.val j.isLt hs

/-- **The nonbranching direction.**  If the truth's spectrum-support graph does
not branch, then any primitive candidate with the truth's normalized complete
spectrum is identified with the truth.

Proof.  Nonbranching plus primitivity of the truth make its complete spectrum
`gcdOne` with all support counts `1` (`gcdOne_of_nonbranching_primitive`), so the
ray lemma `spectrum_on_ray` puts the candidate at some multiplier `mm ≥ 1` on the
same ray.  The candidate's window trail is a cyclic spelling of `cD = mm * cS`
and is primitive, so `nonbranching_primitive_spelling_eq_one` again forces every
support count of `cD` to be `1`; since the support counts of `cS` are `1` too,
`mm = 1`, the candidate has the truth's length and the truth's complete
spectrum, and `rotEquiv_of_specCount_eq` — determinism of the window walk —
makes it a rotation of the truth.

No complete-spectrum uniqueness premise is used: the equal-length step is
proved from the traversal itself. -/
theorem identifiable_of_nonbranching {hG : 0 < G} {hL : 1 < L} {S : Fin G → α}
    (hS : PopulationReduction.IsPrimitive S)
    (hnb : NonBranching (genomeNodes (L := L) hG S) (support (L := L) hG S)
      (winPrefix (L := L)) (winSuffix (L := L))) :
    Identifiable hG hL S := by
  intro m D hD hDprim hNorm
  -- the truth spectrum is gcd-one, from the nonbranching support alone
  have hgcdS : IsGcdOne (W := Fin L → α) (specCount (L := L) hG S) :=
    gcdOne_of_nonbranching_primitive (L := L) (hL := hL) hS hnb
  have honeS := one_on_support_of_nonbranching_primitive (L := L) (hL := hL) hS hnb
  have hSsum : ∑ w : Fin L → α, specCount (L := L) hG S w = G :=
    truth_total_all (L := L) (hG := hG) S
  -- the candidate is on the same integer ray of spectra
  obtain ⟨mm, hmm1, hmmG, hDm⟩ :=
    spectrum_on_ray hG hD (Nat.succ_pos 0)
      (specCount (L := L) hG S) (specCount (L := L) hG S) (specCount (L := L) hD D)
      (fun w => by rw [Nat.one_mul]) hSsum
      (fun w => by rw [← hNorm w]) hgcdS
  have hsupD : ∀ w : Fin L → α, w ∈ support (L := L) hG S ↔ w ∈ support (L := L) hD D := by
    intro w
    rw [mem_support_iff (L := L) hG S w, mem_support_iff (L := L) hD D w]
    have h := hDm w
    constructor
    · intro hpos
      rw [h]
      exact Nat.mul_pos hmm1 hpos
    · intro hpos
      by_contra hzero
      have hz : specCount (L := L) hG S w = 0 := by omega
      rw [hz] at h
      simp at h
      omega
  -- the candidate's window trail is a primitive cyclic spelling of `cD`
  obtain ⟨sD, hTrailD⟩ := winTrail_closed (L := L) hD D
  have huseD : ∀ e, edgeUse (winTrail (L := L) hD D) e = specCount (L := L) hD D e :=
    fun e => winTrail_edgeUse hD D e
  have hprimD : IsPrimitive (winTrail (L := L) hD D) :=
    truth_trail_primitive (L := L) (hG := hD) (hL := hL) D hDprim
  have htrailNe : winTrail (L := L) hD D ≠ [] := by
    intro h0
    have hz : (winTrail (L := L) hD D).length = 0 := by rw [h0, List.length_nil]
    have h1 := winTrail_length (L := L) hD D
    rw [h1] at hz
    omega
  -- nonbranching forces every support count of the candidate to be one
  have honeD : ∀ e ∈ support (L := L) hG S, specCount (L := L) hD D e = 1 := by
    intro e he
    have heD : e ∈ support (L := L) hD D := (hsupD e).mp he
    exact nonbranching_primitive_spelling_eq_one hTrailD htrailNe
      (specCount (L := L) hD D) huseD (support (L := L) hD D)
      (fun e₁ he₁ e₂ he₂ ht => uniqueOut_of_nonbranching (hL := hL) hnb e₁ e₂
        ((hsupD e₁).mpr he₁) ((hsupD e₂).mpr he₂) ht)
      (fun e' he' => by
        have h4 := hDm e'
        by_cases hz : specCount (L := L) hG S e' = 0
        · rw [h4, hz]
          rfl
        · exfalso
          have hposD : 0 < specCount (L := L) hD D e' := by
            rw [h4]
            exact Nat.mul_pos hmm1 (by omega)
          exact absurd ((mem_support_iff (L := L) hD D e').mpr hposD) he')
      (fun e' he' => by
        rw [hDm e']
        exact Nat.mul_pos hmm1
          ((mem_support_iff (L := L) hG S e').mp ((hsupD e').mpr he')))
      hprimD e heD
  -- hence the ray multiplier is one
  obtain ⟨e, he⟩ := support_ne_nil_of_truth (L := L) (hG := hG) S
  have hmm : mm = 1 := by
    have hone1 := honeD e he
    have hone2 := honeS e he
    have h1 := hDm e
    rw [hone1, hone2] at h1
    omega
  have hmmG' : m = G := by
    have h1 := hmmG
    rw [hmm, Nat.succ_eq_add_one, Nat.div_one, Nat.one_mul] at h1
    exact h1
  subst hmmG'
  -- same length and same complete spectrum: forced traversal gives the rotation
  have hspec : specCount (L := L) hG S = specCount (L := L) hG D := by
    funext w
    rw [hDm w, hmm, one_mul]
  refine ⟨rfl, ?_⟩
  exact (identified_iff_rotEquiv hG D rfl S).mpr
    (rotEquiv_of_specCount_eq (L := L) (hL := hL) hG S D hnb hspec)

/-- **The branching direction.**  If the truth's spectrum-support graph branches,
then the truth is *not* identifiable from the normalized complete spectrum among
primitive candidates: doubling the two excursions of the truth's window trail and
concatenating them yields a primitive circular word of length `2 * G` whose
complete spectrum is exactly twice the truth's, hence which satisfies the
normalized-spectrum condition but has a different length.

Proof.  `branching_primitive_spellings` splits the truth's window trail (a closed
spelling of the truth's complete spectrum) at a branching node into two nonempty
closed excursions `A` and `B` with `edgeUse A + edgeUse B = cS`, and shows that for
every `m >= 2` the closed trail `nCopies A m ++ nCopies B m` is a primitive trail
whose edge use is `m * cS`.  With `m = 2` the length is `2 * G > 0`, and
`word_of_closed_trail` turns it into a circular word of that length with exactly
that spectrum; `isPrimitive_of_primitiveTrail` transfers primitivity. -/
theorem not_identifiable_of_branching {hG : 0 < G} {hL : 1 < L} {S : Fin G → α}
    (hbr : Branching (genomeNodes (L := L) hG S) (support (L := L) hG S)
      (winPrefix (L := L)) (winSuffix (L := L))) :
    ¬ Identifiable hG hL S := by
  intro hIdent
  have hout : ∀ w, w ∉ support (L := L) hG S → specCount (L := L) hG S w = 0 := by
    intro w hw
    have h1 := (mem_support_iff (L := L) hG S w).mpr
    by_contra hc
    exact absurd (h1 (by omega)) hw
  have hSsum : ∑ w : Fin L → α, specCount (L := L) hG S w = G := by
    have h2 : ∑ w : Fin L → α, specCount (L := L) hG S w
        = ∑ w ∈ support (L := L) hG S, specCount (L := L) hG S w :=
      (Finset.sum_subset (fun b _ => Finset.mem_univ _)
        (fun b _ hb => hout b hb)).symm
    rw [h2]
    exact truth_total (L := L) hG S
  obtain ⟨s0, hTclosed⟩ := truth_trail_closed (L := L) S
  obtain ⟨A, B, v, hA, hB, hAne, hBne, hneAB, hclosedT', huseT', hprimT'⟩ :=
    branching_primitive_spellings
      hTclosed (specCount (L := L) hG S)
      (truth_trail_spectrum (L := L) S)
      (genomeNodes (L := L) hG S) (support (L := L) hG S) hbr hout
      (fun w hw => truth_pos_on_support (L := L) hG S w hw) 2 (by omega)
  have hT'ne : nCopies A 2 ++ nCopies B 2 ≠ [] := by
    intro h0
    have h1 := congrArg List.length h0
    simp only [List.length_append, List.length_nil, nCopies_length] at h1
    have h3 : 0 < A.length := List.length_pos_iff_ne_nil.mpr hAne
    omega
  have hlenT' : (nCopies A 2 ++ nCopies B 2).length = 2 * G := by
    have h1 := length_eq_sum_edgeUse (nCopies A 2 ++ nCopies B 2)
    have h2 : ∑ e : Fin L → α, edgeUse (nCopies A 2 ++ nCopies B 2) e = 2 * G := by
      have h3 : ∑ e : Fin L → α, edgeUse (nCopies A 2 ++ nCopies B 2) e
          = ∑ w : Fin L → α, 2 * specCount (L := L) hG S w :=
        Finset.sum_congr rfl (fun e _ => huseT' e)
      have h4 : ∑ w : Fin L → α, 2 * specCount (L := L) hG S w
          = 2 * ∑ w : Fin L → α, specCount (L := L) hG S w := by
        rw [Finset.mul_sum]
      rw [h3, h4, hSsum]
    rw [h1, h2]
  obtain ⟨s', hT'closed⟩ := hclosedT'
  have hHpos : 0 < (nCopies A 2 ++ nCopies B 2).length := by rw [hlenT']; omega
  obtain ⟨W, hspecW, hwinW⟩ := word_of_closed_trail hT'closed hT'ne hL
  have hcyc : ∀ r : Fin (nCopies A 2 ++ nCopies B 2).length,
      window (L := L) hHpos W r
        = PopulationReduction.cycEdge (nCopies A 2 ++ nCopies B 2) hHpos r.val := by
    intro r
    rw [hwinW r]
    exact (cycEdge_get hHpos r.val r.isLt).symm
  have hWprim : PopulationReduction.IsPrimitive W :=
    isPrimitive_of_primitiveTrail hHpos W (nCopies A 2 ++ nCopies B 2) rfl hcyc hprimT'
  have h2 : ∀ w : Fin L → α,
      specCount (L := L) hHpos W w = 2 * specCount (L := L) hG S w := by
    intro w
    rw [congrFun hspecW w, huseT' w]
  have hNorm : ∀ w : Fin L → α,
      specCount (L := L) hG S w * (nCopies A 2 ++ nCopies B 2).length
        = specCount (L := L) hHpos W w * G := by
    intro w
    calc specCount (L := L) hG S w * (nCopies A 2 ++ nCopies B 2).length
        = specCount (L := L) hG S w * (2 * G) := by rw [hlenT']
      _ = (2 * specCount (L := L) hG S w) * G := by ring
      _ = specCount (L := L) hHpos W w * G := by rw [h2 w]
  obtain ⟨hm, hIdent'⟩ :=
    hIdent (nCopies A 2 ++ nCopies B 2).length W hHpos hWprim hNorm
  rw [hlenT'] at hm
  omega

/-- **Classification (issue #92).**  A primitive truth is identifiable from the
normalized complete spectrum among primitive candidates of arbitrary length if
and only if its spectrum-support graph does not branch.

This is the fixed-truth statement of the issue: the hypotheses are the
model-level ones only — a circular word `S` of length `G > 0` over `α`, a window
length `L > 1`, and primitivity of `S`.  There is **no** external
complete-spectrum uniqueness premise (`hBBT`), no `AdmP2` admissibility
predicate, and no `hP2S`: the equal-length step is proved from the deterministic
prefix/suffix step of the window walk plus the functional nonbranching support,
by `rotEquiv_of_specCount_eq`. -/
theorem identifiable_iff_nonbranching {hG : 0 < G} {hL : 1 < L} {S : Fin G → α}
    (hS : PopulationReduction.IsPrimitive S) :
    Identifiable hG hL S ↔
      NonBranching (genomeNodes (L := L) hG S) (support (L := L) hG S)
        (winPrefix (L := L)) (winSuffix (L := L)) := by
  constructor
  · intro hI hnb
    by_contra hcon
    have hbr : Branching (genomeNodes (L := L) hG S) (support (L := L) hG S)
        (winPrefix (L := L)) (winSuffix (L := L)) := by
      unfold Branching
      push Not at hcon
      obtain ⟨e₁, he₁, e₂, he₂, hp₁, hp₂, hne⟩ := hcon
      have h12 : winPrefix e₁ = winPrefix e₂ := hp₁.trans hp₂.symm
      exact ⟨winPrefix e₁, e₁, he₁, e₂, he₂, hne, rfl, h12.symm⟩
    exact not_identifiable_of_branching hbr hI
  · intro hnb
    exact identifiable_of_nonbranching hS hnb

end Classification
