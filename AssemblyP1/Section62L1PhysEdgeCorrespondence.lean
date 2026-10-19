import AssemblyP1.Section62PhysicalEdgeOrbit

/-!
# L1 source-graph correspondence: physical RC overlap multigraph ↔ PhysEdge quotient (#261)

This module is a **bounded, checkable increment** on the L1 link of the #255
chain.  It does **not** claim the full L1 correspondence or any ML maximality
result.  It makes precise the *candidate* edge/multiplicity mapping from a small
explicit physical RC overlap multigraph to the `PhysEdge` quotient and
kernel-checks one concrete instance of it.

## The candidate mapping (formal definition)

The **physical RC overlap multigraph** (MB09 §6.2, §3.1, §3.3) has:

* **Vertices** = molecule classes.  A class `c` has a representative strand
  `s(c)` and its reverse complement `n(c) = rc s(c)` (§3.1: a DNA molecule is an
  unordered RC strand pair).
* **Edges** = bidirected overlaps (§3.3: "all possible bidirected overlaps of
  length at least `o_min`").  For an ordered pair of distinct classes
  `(c1, c2)` and a length `len` there are up to **four** physical edges, one per
  strand-overlap case, each carrying a signed incidence at each endpoint class:

  | case | strand overlap        | sign at `c1` | sign at `c2` |
  |------|-----------------------|--------------|--------------|
  | 1    | `suf(s1)=pre(s2)`     | `+1`         | `-1`         |
  | 2    | `suf(s1)=pre(n2)`     | `+1`         | `+1`         |
  | 3    | `suf(n1)=pre(s2)`     | `-1`         | `-1`         |
  | 4    | `suf(n1)=pre(n2)`     | `-1`         | `+1`         |

  For a **self-loop** at `c` there are up to **three** physical edges (the mixed
  loop, the `++` loop, the `--` loop), with signed incidences `(pos,neg)` at `c`
  equal to `(1,1)`, `(2,0)`, `(0,2)` respectively.

The **candidate mapping** sends each physical edge to the reversal orbit
(`PhysEdge` quotient) of any tagged edge that represents it.  Concretely, a
tagged strand is `(word, bit)` with `cls (w,b) = (w,0)`; the *string content* is
`word` when `bit = 0` and `rc word` when `bit = 1` (the content-tracking
reading of `Tagged W`).  Case `k` above is represented by the tagged edge

* case 1: `bdEdge cls (s1,0) (s2,0) len`   (signs `+1,-1`)
* case 2: `bdEdge cls (s1,0) (s2,1) len`   (signs `+1,+1`)
* case 3: `bdEdge cls (s1,1) (s2,0) len`   (signs `-1,-1`)
* case 4: `bdEdge cls (s1,1) (s2,1) len`   (signs `-1,+1`)

and the mapping is `physical edge ↦ physMk (tagged edge)`.

## What is proved here

`twoClass_fourOrbits` (below): for two distinct classes, the four tagged edges
above have **four distinct** `physMk` values, with the four distinct sign
patterns.  This is the *edge-multiplicity* half of the correspondence: the four
physical edges are **not** identified by the quotient (in particular the two
mixed-type edges, cases 1 and 4, are distinct orbits).  Together with the
already-merged ATAT self-loop witness (`Section62PhysicalEdgeOrbit.Atat`: three
loop orbits with `(pos,neg) = (1,1),(2,0),(0,2)`), this pins the orbit
structure for both distinct-class and self-loop edges.

`twoClass_fourOrbits_gen` generalizes this from the concrete words to **any**
two distinct words `w1 ≠ w2`, so the four-orbit distinctness is not an artifact
of the chosen witness words.

The exhaustive finite cross-check is `scripts/verify_261_l1_physedge_quotient.py`
(594 small overlap graphs, checks W1-W6, exit 0).

## What is *not* claimed

* No proof that the quotient graph *is* MB09's §6.2 graph in full (the
  content-tracking reading is a modeling choice; the transport of the actual
  overlap set, vertex lower bounds, spells, and ML objectives remains OPEN).
* No claim that a physical orbit flow is a single circular genome.
* No `sorry` / `admit` / `axiom` / `native_decide`.
-/

namespace AssemblyP1.Section62L1PhysEdgeCorrespondence

open AssemblyP1.Section62Flow
open AssemblyP1.Section62PhysicalHalfIncidence
open AssemblyP1.Section62PhysicalEdgeOrbit

set_option linter.unusedSectionVars false

/-! ## Two distinct classes: four physical edges ↔ four orbits -/

namespace TwoClass

/-- The tagged strand type on `Bool`-words. -/
abbrev V : Type := Tagged (List Bool)

/-- Two distinct molecule classes, `w1 = [false,false]` and `w2 = [false,true]`. -/
def w1 : List Bool := [false, false]
def w2 : List Bool := [false, true]

/-- The representative strands of the two classes. -/
def s1 : V := (w1, false)
def s2 : V := (w2, false)

/-- The four tagged edges between the two classes (cases 1-4), at a fixed length. -/
def len : Nat := 1

def e11 : BdEdge Bool V := bdEdge (A := Bool) cls s1 s2 len
def e12 : BdEdge Bool V := bdEdge (A := Bool) cls s1 (w2, true) len
def e21 : BdEdge Bool V := bdEdge (A := Bool) cls (w1, true) s2 len
def e22 : BdEdge Bool V := bdEdge (A := Bool) cls (w1, true) (w2, true) len

/-- Case 1 has signs `+1` at `c1` and `-1` at `c2`. -/
theorem e11_signs : e11.sgnX = 1 ∧ e11.sgnY = -1 := by decide

/-- Case 2 has signs `+1` at both. -/
theorem e12_signs : e12.sgnX = 1 ∧ e12.sgnY = 1 := by decide

/-- Case 3 has signs `-1` at both. -/
theorem e21_signs : e21.sgnX = -1 ∧ e21.sgnY = -1 := by decide

/-- Case 4 has signs `-1` at `c1` and `+1` at `c2`. -/
theorem e22_signs : e22.sgnX = -1 ∧ e22.sgnY = 1 := by decide

/-- **The four physical edges between two distinct classes are four distinct
orbits.**  In particular the two mixed-type edges (cases 1 and 4) are *not*
identified by the quotient. -/
theorem twoClass_fourOrbits :
    physMk e11 ≠ physMk e12 ∧ physMk e11 ≠ physMk e21 ∧ physMk e11 ≠ physMk e22 ∧
    physMk e12 ≠ physMk e21 ∧ physMk e12 ≠ physMk e22 ∧ physMk e21 ≠ physMk e22 := by
  constructor
  · intro h
    have : RevRel (A := Bool) (W := List Bool) e11 e12 := Quotient.exact h
    rcases this with h' | h' <;> exact absurd h' (by decide)
  constructor
  · intro h
    have : RevRel (A := Bool) (W := List Bool) e11 e21 := Quotient.exact h
    rcases this with h' | h' <;> exact absurd h' (by decide)
  constructor
  · intro h
    have : RevRel (A := Bool) (W := List Bool) e11 e22 := Quotient.exact h
    rcases this with h' | h' <;> exact absurd h' (by decide)
  constructor
  · intro h
    have : RevRel (A := Bool) (W := List Bool) e12 e21 := Quotient.exact h
    rcases this with h' | h' <;> exact absurd h' (by decide)
  constructor
  · intro h
    have : RevRel (A := Bool) (W := List Bool) e12 e22 := Quotient.exact h
    rcases this with h' | h' <;> exact absurd h' (by decide)
  · intro h
    have : RevRel (A := Bool) (W := List Bool) e21 e22 := Quotient.exact h
    rcases this with h' | h' <;> exact absurd h' (by decide)

/-- The sign-at-each-endpoint is a function of the orbit, not the
representative: `physPos`/`physNeg` at `c1` take the expected values on each
of the four orbits. -/
theorem twoClass_orbit_signs :
    physPos s1 (physMk e11) = 1 ∧ physNeg s1 (physMk e11) = 0 ∧
    physPos s1 (physMk e12) = 1 ∧ physNeg s1 (physMk e12) = 0 ∧
    physPos s1 (physMk e21) = 0 ∧ physNeg s1 (physMk e21) = 1 ∧
    physPos s1 (physMk e22) = 0 ∧ physNeg s1 (physMk e22) = 1 := by
  simp only [physPos_mk, physNeg_mk]
  decide

/-! ## General distinctness: arbitrary distinct words -/

/-- The four tagged edges between the classes of arbitrary words `w1`, `w2`
(cases 1-4), at the fixed length `len`. -/
def g11 (w1 w2 : List Bool) : BdEdge Bool V :=
  bdEdge (A := Bool) cls (w1, false) (w2, false) len

def g12 (w1 w2 : List Bool) : BdEdge Bool V :=
  bdEdge (A := Bool) cls (w1, false) (w2, true) len

def g21 (w1 w2 : List Bool) : BdEdge Bool V :=
  bdEdge (A := Bool) cls (w1, true) (w2, false) len

def g22 (w1 w2 : List Bool) : BdEdge Bool V :=
  bdEdge (A := Bool) cls (w1, true) (w2, true) len

/-- Case 1 signs are `+1,-1` for arbitrary words. -/
theorem g11_signs {w1 w2 : List Bool} : (g11 w1 w2).sgnX = 1 ∧ (g11 w1 w2).sgnY = -1 := by
  simp [g11, bdEdge, sgnRep, sgnTgt, cls]

/-- Case 2 signs are `+1,+1` for arbitrary words. -/
theorem g12_signs {w1 w2 : List Bool} : (g12 w1 w2).sgnX = 1 ∧ (g12 w1 w2).sgnY = 1 := by
  simp [g12, bdEdge, sgnRep, sgnTgt, cls]

/-- Case 3 signs are `-1,-1` for arbitrary words. -/
theorem g21_signs {w1 w2 : List Bool} : (g21 w1 w2).sgnX = -1 ∧ (g21 w1 w2).sgnY = -1 := by
  simp [g21, bdEdge, sgnRep, sgnTgt, cls]

/-- Case 4 signs are `-1,+1` for arbitrary words. -/
theorem g22_signs {w1 w2 : List Bool} : (g22 w1 w2).sgnX = -1 ∧ (g22 w1 w2).sgnY = 1 := by
  simp [g22, bdEdge, sgnRep, sgnTgt, cls]

/-- Case 1 and case 2 are distinct orbits for arbitrary distinct words. -/
theorem fourOrbits_ne_11_12 {w1 w2 : List Bool} (h : w1 ≠ w2) :
    physMk (g11 w1 w2) ≠ physMk (g12 w1 w2) := by
  intro hq
  have : RevRel (A := Bool) (W := List Bool) (g11 w1 w2) (g12 w1 w2) := Quotient.exact hq
  rcases this with h' | h'
  · simp [g11, g12, bdEdge] at h'
  · simp [g11, g12, bdEdge, reverseEdge, AssemblyP1.Section62PhysicalHalfIncidence.flip, h] at h'

/-- Case 1 and case 3 are distinct orbits for arbitrary distinct words. -/
theorem fourOrbits_ne_11_21 {w1 w2 : List Bool} (h : w1 ≠ w2) :
    physMk (g11 w1 w2) ≠ physMk (g21 w1 w2) := by
  intro hq
  have : RevRel (A := Bool) (W := List Bool) (g11 w1 w2) (g21 w1 w2) := Quotient.exact hq
  rcases this with h' | h'
  · simp [g11, g21, bdEdge] at h'
  · simp [g11, g21, bdEdge, reverseEdge, AssemblyP1.Section62PhysicalHalfIncidence.flip, h] at h'

/-- Case 1 and case 4 are distinct orbits for arbitrary distinct words. -/
theorem fourOrbits_ne_11_22 {w1 w2 : List Bool} (h : w1 ≠ w2) :
    physMk (g11 w1 w2) ≠ physMk (g22 w1 w2) := by
  intro hq
  have : RevRel (A := Bool) (W := List Bool) (g11 w1 w2) (g22 w1 w2) := Quotient.exact hq
  rcases this with h' | h'
  · simp [g11, g22, bdEdge] at h'
  · simp [g11, g22, bdEdge, reverseEdge, AssemblyP1.Section62PhysicalHalfIncidence.flip, h] at h'

/-- Case 2 and case 3 are distinct orbits for arbitrary distinct words. -/
theorem fourOrbits_ne_12_21 {w1 w2 : List Bool} (h : w1 ≠ w2) :
    physMk (g12 w1 w2) ≠ physMk (g21 w1 w2) := by
  intro hq
  have : RevRel (A := Bool) (W := List Bool) (g12 w1 w2) (g21 w1 w2) := Quotient.exact hq
  rcases this with h' | h'
  · simp [g12, g21, bdEdge] at h'
  · simp [g12, g21, bdEdge, reverseEdge, AssemblyP1.Section62PhysicalHalfIncidence.flip, h] at h'

/-- Case 2 and case 4 are distinct orbits for arbitrary distinct words. -/
theorem fourOrbits_ne_12_22 {w1 w2 : List Bool} (h : w1 ≠ w2) :
    physMk (g12 w1 w2) ≠ physMk (g22 w1 w2) := by
  intro hq
  have : RevRel (A := Bool) (W := List Bool) (g12 w1 w2) (g22 w1 w2) := Quotient.exact hq
  rcases this with h' | h'
  · simp [g12, g22, bdEdge] at h'
  · simp [g12, g22, bdEdge, reverseEdge, AssemblyP1.Section62PhysicalHalfIncidence.flip, h] at h'

/-- Case 3 and case 4 are distinct orbits for arbitrary distinct words. -/
theorem fourOrbits_ne_21_22 {w1 w2 : List Bool} (h : w1 ≠ w2) :
    physMk (g21 w1 w2) ≠ physMk (g22 w1 w2) := by
  intro hq
  have : RevRel (A := Bool) (W := List Bool) (g21 w1 w2) (g22 w1 w2) := Quotient.exact hq
  rcases this with h' | h'
  · simp [g21, g22, bdEdge] at h'
  · simp [g21, g22, bdEdge, reverseEdge, AssemblyP1.Section62PhysicalHalfIncidence.flip, h] at h'

/-- **Generalized edge multiplicity.**  For *any* two distinct words `w1 ≠ w2`,
the four tagged edges (cases 1-4) between their molecule classes have **four
distinct** `physMk` orbits.  The edge-multiplicity correspondence is therefore
not an artifact of the concrete words used in `twoClass_fourOrbits`. -/
theorem twoClass_fourOrbits_gen {w1 w2 : List Bool} (h : w1 ≠ w2) :
    physMk (g11 w1 w2) ≠ physMk (g12 w1 w2) ∧
    physMk (g11 w1 w2) ≠ physMk (g21 w1 w2) ∧
    physMk (g11 w1 w2) ≠ physMk (g22 w1 w2) ∧
    physMk (g12 w1 w2) ≠ physMk (g21 w1 w2) ∧
    physMk (g12 w1 w2) ≠ physMk (g22 w1 w2) ∧
    physMk (g21 w1 w2) ≠ physMk (g22 w1 w2) :=
  ⟨fourOrbits_ne_11_12 h, fourOrbits_ne_11_21 h, fourOrbits_ne_11_22 h,
    fourOrbits_ne_12_21 h, fourOrbits_ne_12_22 h, fourOrbits_ne_21_22 h⟩

end TwoClass

end AssemblyP1.Section62L1PhysEdgeCorrespondence
