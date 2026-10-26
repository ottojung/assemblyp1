import AssemblyP1.Section62PhysicalHalfIncidence

/-!
# Physical edge-orbit flows and representation-invariant vertex throughput (#261)

This module formalizes the *next* bounded step after the tagged-strand reversal
audit: it does **not** assign a separate flow variable to both oriented
representations of one physical bidirected edge.  Instead it

1. defines the reversal equivalence `RevRel` on tagged signed edges
   (`e ≈ e'` iff `e' = e` or `e' = reverseEdge e`) and proves it is a setoid
   (`revSetoid`) using `reverseEdge_involutive` from
   `AssemblyP1.Section62PhysicalHalfIncidence`;
2. forms the **physical edge type** `PhysEdge A W` as the quotient of this
   setoid, with quotient map `physMk : e ↦ [e]`;
3. lifts the *separate* positive/negative half-incidences of merged PR #300
   (`posHalf`, `negHalf`) to the quotient (`physPos`, `physNeg`), which is
   well-defined precisely because #300 proves `posHalf`/`negHalf` are invariant
   under `reverseEdge`;
4. defines a physical flow indexed by a **finite list of orbit IDs**, its
   representation-invariant positive/negative visit totals
   (`physPosTotal`/`physNegTotal`) and physical balance (`PhysBalanced`).

The finite list retains the overlap length, and `RevRel` only relates an edge to
its own `reverseEdge`, which preserves `len`; so genuinely distinct parallel
overlaps (same ordered strand pair, different overlap length) are never
identified (`revRel_len`, `not_revRel_of_len_ne`).

## The ATAT witness: orbit counting is not yet source-faithful

On the length-`4` RC-palindrome `ATAT` the four tagged orientations fall into
exactly three unordered reversal orbits `{E1,E4}`, `{E2}`, `{E3}`.  The
mixed-sign loop orbit `{E1,E4}` has *physical* positive incidence one and
negative incidence one (`mixedLoop_posHalf`, `mixedLoop_negHalf`), while the
`++` loop `{E2}` has two positive half-incidences and the `--` loop `{E3}` two
negative ones.  A physical flow with weight one on the mixed-sign orbit is
balanced with visit count one (`orbit_balanced`, `orbit_visit_one`).

The inherited departure-based `throughput`, however, is a function of an
*oriented* flow.  Copying the orbit weight onto both oriented representatives
(`inducedFlow`) makes both `E1` and `E4` depart the class, so the inherited
count is **two**, not one (`inherited_throughput_two`,
`inherited_throughput_not_physical`).  Hence the three-orbit count alone does
not make the inherited departure throughput source-faithful: physical
throughput must be computed from `physPos`, not from `throughput`.

## What is *not* claimed

* No proof that the quotient graph is MB09's physical §6.2 graph, and no
  transport of the actual overlap set, vertex lower bounds, spells, contig /
  genome walks, or ML objectives to physical orbits.  Those remain OPEN.
* No claim that a physical flow is a single circular genome; an Eulerian /
  spelled hypothesis would be required.
* No `sorry` / `admit` / `axiom` / `native_decide`.
-/

namespace AssemblyP1.Section62PhysicalEdgeOrbit

open AssemblyP1.Section62Flow
open AssemblyP1.Section62PhysicalHalfIncidence

variable {A W : Type} [DecidableEq W]

/-! ## The reversal setoid on tagged signed edges -/

/-- Two tagged signed edges are **reversal-equivalent** when they are equal or
one is the `reverseEdge` of the other.  This is the physical-edge identification:
an oriented overlap and its reverse-complement read are two representations of
one physical bidirected edge. -/
def RevRel (e e' : BdEdge A (Tagged W)) : Prop := e' = e ∨ e' = reverseEdge e

theorem revRel_refl : ∀ e : BdEdge A (Tagged W), RevRel e e := fun _ => Or.inl rfl

theorem revRel_symm : ∀ {e e' : BdEdge A (Tagged W)}, RevRel e e' → RevRel e' e := by
  intro a b h
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, reverseEdge_involutive])

theorem revRel_trans :
    ∀ {e e' e'' : BdEdge A (Tagged W)}, RevRel e e' → RevRel e' e'' → RevRel e e'' := by
  intro a b c hab hbc
  rcases hab with hab | hab
  · rcases hbc with hbc | hbc
    · exact Or.inl (hbc.trans hab)
    · exact Or.inr (by rw [hbc, hab])
  · rcases hbc with hbc | hbc
    · exact Or.inr (by rw [hbc, hab])
    · exact Or.inl (by rw [hbc, hab, reverseEdge_involutive])

/-- The **physical-edge reversal setoid** on tagged signed edges. -/
def revSetoid : Setoid (BdEdge A (Tagged W)) where
  r := RevRel
  iseqv := ⟨revRel_refl, revRel_symm, revRel_trans⟩

/-- The **physical edge type**: tagged signed edges modulo physical reversal. -/
abbrev PhysEdge (A : Type) (W : Type) [DecidableEq W] :=
  Quotient (revSetoid (A := A) (W := W))

/-- The quotient map from an oriented tagged edge to its physical edge orbit. -/
def physMk (e : BdEdge A (Tagged W)) : PhysEdge A W :=
  Quotient.mk (revSetoid (A := A) (W := W)) e

/-- An edge and its reversal have the same physical orbit. -/
theorem physMk_reverse (e : BdEdge A (Tagged W)) :
    physMk (reverseEdge e) = physMk e :=
  (Quotient.sound (Or.inr rfl : RevRel e (reverseEdge e))).symm

/-- Reversal preserves the overlap length, so the quotient never identifies
genuinely distinct parallel overlaps. -/
theorem revRel_len {e e' : BdEdge A (Tagged W)} (h : RevRel e e') : e'.len = e.len := by
  rcases h with h | h
  · rw [h]
  · rw [h]; rfl

/-- Edges of different overlap length are never reversal-equivalent. -/
theorem not_revRel_of_len_ne {e e' : BdEdge A (Tagged W)} (h : e'.len ≠ e.len) :
    ¬ RevRel e e' := fun hr => h (revRel_len hr)

/-! ## Well-defined physical half-incidences -/

/-- Physical positive half-incidence count at `v`, well-defined on physical
orbits because `posHalf` is `reverseEdge`-invariant (merged #300). -/
def physPos (v : Tagged W) : PhysEdge A W → ℕ :=
  Quotient.lift (fun e => posHalf e v) (by
    intro a b h
    rcases h with h | h
    · rw [h]
    · rw [h, posHalf_reverse])

/-- Physical negative half-incidence count at `v`, well-defined on physical
orbits because `negHalf` is `reverseEdge`-invariant (merged #300). -/
def physNeg (v : Tagged W) : PhysEdge A W → ℕ :=
  Quotient.lift (fun e => negHalf e v) (by
    intro a b h
    rcases h with h | h
    · rw [h]
    · rw [h, negHalf_reverse])

theorem physPos_mk (v : Tagged W) (e : BdEdge A (Tagged W)) :
    physPos v (physMk e) = posHalf e v := rfl

theorem physNeg_mk (v : Tagged W) (e : BdEdge A (Tagged W)) :
    physNeg v (physMk e) = negHalf e v := rfl

theorem physPos_reverse (v : Tagged W) (e : BdEdge A (Tagged W)) :
    physPos v (physMk (reverseEdge e)) = physPos v (physMk e) := by
  rw [physPos_mk, physPos_mk, posHalf_reverse]

theorem physNeg_reverse (v : Tagged W) (e : BdEdge A (Tagged W)) :
    physNeg v (physMk (reverseEdge e)) = physNeg v (physMk e) := by
  rw [physNeg_mk, physNeg_mk, negHalf_reverse]

/-! ## Orbit-indexed physical flows -/

/-- Total physical positive half-incidences at `v` of the orbit-indexed flow
`f`, over a finite list `reps` of orbit IDs whose orbit `i` is represented by
the oriented edge `rep i`. -/
def physPosTotal {ι : Type} (reps : List ι) (rep : ι → BdEdge A (Tagged W))
    (f : ι → ℕ) (v : Tagged W) : ℕ :=
  (reps.map (fun i => f i * physPos v (physMk (rep i)))).sum

/-- Total physical negative half-incidences at `v`. -/
def physNegTotal {ι : Type} (reps : List ι) (rep : ι → BdEdge A (Tagged W))
    (f : ι → ℕ) (v : Tagged W) : ℕ :=
  (reps.map (fun i => f i * physNeg v (physMk (rep i)))).sum

/-- **Physical balance** at `v`: positive and negative physical visit counts
coincide.  This is a representation-invariant statement: it is computed from the
physical orbits, not from oriented departures. -/
def PhysBalanced {ι : Type} (reps : List ι) (rep : ι → BdEdge A (Tagged W))
    (f : ι → ℕ) (v : Tagged W) : Prop :=
  physPosTotal reps rep f v = physNegTotal reps rep f v

/-- The physical positive total is unchanged when a representative is replaced
by its reversal: the orbit ID, not the oriented representative, carries the
weight. -/
theorem physPosTotal_reverse {ι : Type} (reps : List ι)
    (rep : ι → BdEdge A (Tagged W)) (f : ι → ℕ) (v : Tagged W) :
    physPosTotal reps (fun i => reverseEdge (rep i)) f v = physPosTotal reps rep f v := by
  simp only [physPosTotal, physPos_reverse]

theorem physNegTotal_reverse {ι : Type} (reps : List ι)
    (rep : ι → BdEdge A (Tagged W)) (f : ι → ℕ) (v : Tagged W) :
    physNegTotal reps (fun i => reverseEdge (rep i)) f v = physNegTotal reps rep f v := by
  simp only [physNegTotal, physNeg_reverse]

/-- Physical balance is unchanged by replacing representatives with their
reversals. -/
theorem physBalanced_reverse {ι : Type} (reps : List ι)
    (rep : ι → BdEdge A (Tagged W)) (f : ι → ℕ) (v : Tagged W) :
    PhysBalanced reps (fun i => reverseEdge (rep i)) f v ↔ PhysBalanced reps rep f v := by
  simp only [PhysBalanced, physPosTotal_reverse, physNegTotal_reverse]

/-! ## The ATAT witness: three orbits, and why inherited throughput is not enough -/

/-! ## A forward-oriented loop occurrence

The endpoint-occurrence convention is local and does not require a loop to
have distinct endpoint classes.  When a window occurrence and its successor
are both represented by their forward tagged strands, a loop edge has one
positive source half and one negative target half.  In particular, a
self-reverse-complement *word* does not force us to identify the two endpoint
occurrences or to count the orbit twice: the tag records the chosen traversal
orientation, while the quotient identifies only reversal of the whole edge.

This lemma establishes that incidence calculation for the canonical
forward-tagged loop.  It does not construct such an edge from a genome's
windows or prove membership in `overlapEdges`; those remain separate graph-map
obligations.
-/

namespace ForwardLoop

/-- The edge occurrence whose two endpoints are the same forward-tagged
molecule-class representative. -/
def edge (w : W) (len : Nat) : BdEdge A (Tagged W) :=
  bdEdge cls (w, false) (w, false) len

/-- A unit occurrence of this loop contributes exactly one positive and one
negative physical half-incidence at its vertex.  The same calculation applies
when `w` is a self-reverse-complement window: palindrome status does not merge
the two endpoint occurrences. -/
theorem loop_halfIncidence (w : W) (len : Nat) :
    posHalf (edge (A := A) w len) (w, false) = 1 ∧
    negHalf (edge (A := A) w len) (w, false) = 1 := by
  simp [edge, bdEdge, posHalf, negHalf, cls, sgnRep, sgnTgt]

/-- The quotient orbit has the same one-and-one incidence, independently of
which of its two oriented representatives is used. -/
theorem orbit_loop_halfIncidence (w : W) (len : Nat) :
    physPos (w, false) (physMk (edge (A := A) w len)) = 1 ∧
    physNeg (w, false) (physMk (edge (A := A) w len)) = 1 ∧
    physPos (w, false) (physMk (reverseEdge (edge (A := A) w len))) = 1 ∧
    physNeg (w, false) (physMk (reverseEdge (edge (A := A) w len))) = 1 := by
  have h := loop_halfIncidence (A := A) w len
  have hPos : physPos (w, false) (physMk (edge (A := A) w len)) = 1 := by
    rw [physPos_mk]
    exact h.1
  have hNeg : physNeg (w, false) (physMk (edge (A := A) w len)) = 1 := by
    rw [physNeg_mk]
    exact h.2
  exact ⟨hPos, hNeg,
    (physPos_reverse (w, false) (edge (A := A) w len)).trans hPos,
    (physNeg_reverse (w, false) (edge (A := A) w len)).trans hNeg⟩

end ForwardLoop

namespace Atat

/-- The tagged strand type on `Bool`-words. -/
abbrev V : Type := Tagged (List Bool)

/-- The length-`4` RC-palindrome `ATAT`. -/
def pal4 : List Bool := [true, false, true, false]

/-- The observed molecule class of `ATAT`. -/
def v0 : V := (pal4, false)

/-- The four tagged orientations of the palindrome self-overlap of length `2`,
with signed incidences derived from the orientation bit (`cls`). -/
def E1 : BdEdge Bool V := bdEdge (A := Bool) cls ((pal4, false) : V) ((pal4, false) : V) 2
def E2 : BdEdge Bool V := bdEdge (A := Bool) cls ((pal4, false) : V) ((pal4, true) : V) 2
def E3 : BdEdge Bool V := bdEdge (A := Bool) cls ((pal4, true) : V) ((pal4, false) : V) 2
def E4 : BdEdge Bool V := bdEdge (A := Bool) cls ((pal4, true) : V) ((pal4, true) : V) 2

theorem reverse_E1 : reverseEdge E1 = E4 := by decide
theorem reverse_E4 : reverseEdge E4 = E1 := by decide
theorem reverse_E2 : reverseEdge E2 = E2 := by decide
theorem reverse_E3 : reverseEdge E3 = E3 := by decide

/-- `E1` and `E4` are the two representations of one physical edge. -/
theorem orbit_E1_E4 : physMk E1 = physMk E4 := by
  rw [← reverse_E1, physMk_reverse]

theorem physMk_E2_ne_E1 : physMk E2 ≠ physMk (E1 : BdEdge Bool V) := by
  intro h
  have hrel : RevRel (A := Bool) (W := List Bool) E2 E1 := Quotient.exact h
  rcases hrel with h' | h' <;> exact absurd h' (by decide)

theorem physMk_E3_ne_E1 : physMk E3 ≠ physMk (E1 : BdEdge Bool V) := by
  intro h
  have hrel : RevRel (A := Bool) (W := List Bool) E3 E1 := Quotient.exact h
  rcases hrel with h' | h' <;> exact absurd h' (by decide)

theorem physMk_E3_ne_E2 : physMk E3 ≠ physMk (E2 : BdEdge Bool V) := by
  intro h
  have hrel : RevRel (A := Bool) (W := List Bool) E3 E2 := Quotient.exact h
  rcases hrel with h' | h' <;> exact absurd h' (by decide)

/-- The three orbit IDs. -/
def orbitIds : List (Fin 3) := [0, 1, 2]

/-- Three orbit representatives: the mixed-sign loop `{E1,E4}`, the `++` loop
`{E2}`, and the `--` loop `{E3}`. -/
def orbitRep : Fin 3 → BdEdge Bool V
  | 0 => E1
  | 1 => E2
  | 2 => E3

/-- Weight one on the mixed-sign loop orbit `{E1,E4}`. -/
def orbFlow : Fin 3 → ℕ
  | 0 => 1
  | 1 => 0
  | 2 => 0

/-- A mixed-sign loop contributes one positive half-incidence. -/
theorem mixedLoop_posHalf : posHalf E1 v0 = 1 := by decide

/-- A mixed-sign loop contributes one negative half-incidence. -/
theorem mixedLoop_negHalf : negHalf E1 v0 = 1 := by decide

/-- A `++` loop contributes two positive half-incidences. -/
theorem positiveLoop_posHalf : posHalf E2 v0 = 2 := by decide

/-- A `--` loop contributes two negative half-incidences. -/
theorem negativeLoop_negHalf : negHalf E3 v0 = 2 := by decide

/-- The unit mixed-sign orbit flow is physically balanced at the class. -/
theorem orbit_balanced : PhysBalanced orbitIds orbitRep orbFlow v0 := by
  simp only [PhysBalanced]
  decide

/-- Its physical positive visit count is one. -/
theorem orbit_visit_one : physPosTotal orbitIds orbitRep orbFlow v0 = 1 := by decide

/-- Its physical negative visit count is one. -/
theorem orbit_visit_one_neg : physNegTotal orbitIds orbitRep orbFlow v0 = 1 := by decide

/-- The induced oriented flow: the orbit weight is copied onto both oriented
representatives. -/
def inducedFlow : BdFlow Bool V := fun e => if e = E1 ∨ e = E4 then 1 else 0

/-- The inherited departure throughput of the induced oriented flow is two:
both `E1` and `E4` depart the class. -/
theorem inherited_throughput_two :
    throughput Bool V cls inducedFlow [E1, E2, E3, E4] v0 = 2 := by decide

/-- **The inherited departure throughput is not the physical visit count.**
The unit mixed-sign orbit flow is physically balanced with visit count one, but
the inherited `throughput` on the induced oriented flow reports two.  Orbit
counting alone therefore does not make the inherited departure throughput
source-faithful. -/
theorem inherited_throughput_not_physical :
    throughput Bool V cls inducedFlow [E1, E2, E3, E4] v0
      ≠ physPosTotal orbitIds orbitRep orbFlow v0 := by
  rw [inherited_throughput_two, orbit_visit_one]
  decide

end Atat

end AssemblyP1.Section62PhysicalEdgeOrbit
