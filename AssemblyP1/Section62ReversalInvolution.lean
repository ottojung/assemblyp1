import AssemblyP1.Section62OrientedStrandFlow

/-!
# Physical reversal: RC overlap anti-morphism and the ATAT 4→3 orbit count (#261)

This module proves the two orthogonal kernel facts:

1. **The overlap predicate is preserved by physical reversal** under a
   Watson–Crick reverse-complement anti-automorphism (`oOverlap_revEdge`).
   The content is the RC anti-morphism `sufOf (rc b) l = rc (preOf b l)`,
   proved for arbitrary lists (no fixed-read-length premise), with the
   equivalence going through the **injectivity** of the involutive
   list-level RC — not definitional reflexivity.

2. **The four ordered tagged ATAT overlaps fall under exactly three reversal
   orbits** — counted here at the orientation-bit level (`revPair`) and lifted
   to edges in `Section62OrientedStrandFlow` (`atat_orbit_count`).

## The orbit quotient is unordered (Finset)

The reversal orbit of an edge is the **Finset** `{e, revEdge e}`, so
`revOrbit e = revOrbit (revEdge e)` definitionally.  The four ATAT edges give
exactly three distinct Finsets.  `revEdge` only identifies an edge with its own
reverse and preserves `len`, so genuine parallel overlaps (same ordered strand
pair, different overlap length) are never identified.  No `eraseDups` is
applied anywhere.

## What is *not* claimed

* No full MB09 §6.2 source-equivalence theorem (edge multiplicity transport,
  signed self-loop incidence correspondence, transitive-reduction interaction
  all stay OPEN).
* No quotient-flow model: the orbit count is a statement about the tagged edge
  set, not a redefinition of `BdFlow` or `Feasible62`.
* No genome realization or ML classification claim.
* No `sorry` / `admit` / `axiom` / `native_decide`.
-/

namespace AssemblyP1.Section62ReversalInvolution

open AssemblyP1.Section62Flow
open AssemblyP1.Section62OrientedStrandFlow

/-! ## The orientation-bit reversal `revPair` (bounded, exhaustive Bool cases) -/

/-- Physical reversal of an ordered pair of orientation bits. -/
def revPair : Bool × Bool → Bool × Bool := fun p => (!p.2, !p.1)

/-- **`revPair` is involutive.** -/
theorem revPair_involutive : Function.Involutive revPair := by
  intro p
  obtain ⟨a, b⟩ := p
  cases a <;> cases b <;> rfl

theorem revPair_false_false : revPair (false, false) = (true, true) := rfl
theorem revPair_true_true : revPair (true, true) = (false, false) := rfl
theorem revPair_false_true : revPair (false, true) = (false, true) := rfl
theorem revPair_true_false : revPair (true, false) = (true, false) := rfl

/-- The four ordered orientation pairs. -/
def orientPairs : List (Bool × Bool) := [(false, false), (false, true), (true, false), (true, true)]

/-- The unordered reversal orbit of an orientation pair. -/
def pairOrbit : Bool × Bool → Finset (Bool × Bool) := fun p => {p, revPair p}

/-- **The four ordered orientation pairs fall under exactly three reversal
orbits**: `{(false,false),(true,true)}`, `{(false,true)}`, `{(true,false)}`. -/
theorem orientPairs_orbit_count :
    ((orientPairs.map pairOrbit).dedup).length = 3 := by
  decide

/-- The exact Finset orbit equalities for the four orientation pairs. -/
theorem orientPairs_orbit_exact :
    pairOrbit (false, false) = {(false, false), (true, true)} ∧
      pairOrbit (true, true) = {(false, false), (true, true)} ∧
      pairOrbit (false, true) = {(false, true)} ∧
      pairOrbit (true, false) = {(true, false)} := by
  decide

/-- The three orbits are distinct and cover all four orientation pairs. -/
theorem orientPairs_orbit_cover :
    ∀ p ∈ orientPairs,
      ∃ o ∈ [pairOrbit (false, false), pairOrbit (false, true), pairOrbit (true, false)],
        p ∈ o ∧ ∀ o' ∈ [pairOrbit (false, false), pairOrbit (false, true), pairOrbit (true, false)],
          o' ≠ o → p ∉ o' := by
  decide

/-! ## The overlap predicate is preserved (arbitrary word lengths) -/

/-- **RC overlap anti-morphism (general, arbitrary word lengths).**  Under an
involutive reverse complement `rcW`, a linearization commuting with `rcW`
through an involutive list anti-automorphism `rcA`, and the list-level
RC/suffix/prefix commutation, the overlap predicate is preserved by physical
reversal:

```text
oOverlap sx sy len  ↔  oOverlap (oRc sy) (oRc sx) len
```

No fixed-read-length hypothesis is needed: the RC/suffix/prefix commutation is
stated for arbitrary lists, and the equivalence uses the **injectivity** of
the involutive `rcA` (`Function.Involutive.injective`), not definitional
reflexivity. -/
theorem oOverlap_revEdge {A W : Type} (toListW : W → List A) (rcW : W → W)
    (rcA : List A → List A) (len : Nat)
    (hrc : Function.Involutive rcW) (hrcA : Function.Involutive rcA)
    (hcomm : ∀ w, toListW (rcW w) = rcA (toListW w))
    (hsufpre : ∀ a : List A, sufOf (rcA a) len = rcA (preOf a len))
    (hpresuf : ∀ a : List A, preOf (rcA a) len = rcA (sufOf a len))
    (sx sy : OStrand W) :
    oOverlap toListW rcW sx sy len ↔ oOverlap toListW rcW (oRc sy) (oRc sx) len := by
  simp only [oOverlap, oTo]
  have hwx : oWord rcW sx = rcW (oWord rcW (oRc sx)) := by
    rw [← oWord_oRc hrc (oRc sx), oRc_involutive sx]
  have hwy : oWord rcW sy = rcW (oWord rcW (oRc sy)) := by
    rw [← oWord_oRc hrc (oRc sy), oRc_involutive sy]
  rw [hwx, hwy, hcomm, hcomm, hsufpre, hpresuf]
  have hinj : Function.Injective rcA := hrcA.injective
  apply Iff.intro
  · intro h
    exact (hinj h).symm
  · intro h
    exact (congrArg rcA h).symm

/-! ### The concrete Bool-DNA instance -/

/-- `l.take l.length = l`. -/
theorem take_length_le {a : List Bool} {len : Nat} (h : a.length ≤ len) :
    a.take len = a :=
  List.take_of_length_le h

/-- `a.take (a.length - (a.length - len)) = a.take len` for arbitrary `a`, `len`. -/
theorem take_sub_sub (a : List Bool) (len : Nat) :
    a.take (a.length - (a.length - len)) = a.take len := by
  by_cases h : len ≤ a.length
  · rw [Nat.sub_sub_self h]
  · have hlt : a.length < len := Nat.lt_of_not_le h
    have h0 : a.length - len = 0 := Nat.sub_eq_zero_of_le (le_of_lt hlt)
    rw [h0, Nat.sub_zero, List.take_length]
    exact (List.take_of_length_le (le_of_lt hlt)).symm

/-- List-level Watson–Crick RC commutes with suffix, for **arbitrary** lists. -/
theorem rcB_sufOf_preOf (a : List Bool) (len : Nat) :
    sufOf (rcB a) len = rcB (preOf a len) := by
  simp only [rcB, sufOf, preOf, List.length_map, List.length_reverse]
  rw [← List.map_drop, List.reverse_take]

/-- List-level Watson–Crick RC commutes with prefix, for **arbitrary** lists. -/
theorem rcB_preOf_sufOf (a : List Bool) (len : Nat) :
    preOf (rcB a) len = rcB (sufOf a len) := by
  simp only [rcB, preOf, sufOf]
  rw [← List.map_take, List.take_reverse]

/-- **RC overlap anti-morphism, concrete Bool-DNA instance.**  For `Bool`-words
with Watson–Crick `rcB`, the overlap predicate is preserved by physical
reversal, at every overlap length and for arbitrary words. -/
theorem oOverlap_revEdge_rcB (sx sy : OStrand (List Bool)) (len : Nat) :
    oOverlap id rcB sx sy len ↔ oOverlap id rcB (oRc sy) (oRc sx) len := by
  refine oOverlap_revEdge id rcB rcB len rcB_involutive rcB_involutive ?_ ?_ ?_ sx sy
  · intro w; rfl
  · intro a; exact rcB_sufOf_preOf a len
  · intro a; exact rcB_preOf_sufOf a len

/-! ## `revEdge` acts as `revPair` on the ATAT orientation bits -/

/-- On the ATAT palindrome (a single molecule class), `revEdge` acts on the
orientation bits exactly as `revPair`. -/
theorem revEdge_atat_revPair (b1 b2 : Bool) :
    revEdge (bdEdge (A := Bool) oRep ((pal4, b1) : OStrand (List Bool))
      ((pal4, b2) : OStrand (List Bool)) 2)
      = bdEdge (A := Bool) oRep ((pal4, !b2) : OStrand (List Bool))
        ((pal4, !b1) : OStrand (List Bool)) 2 :=
  revEdge_bdEdge (pal4, b1) (pal4, b2) 2

/-- The four ATAT edge orbits under `revEdge` are the `revPair` orbits of the
orientation bits, so there are exactly three physical bidirected types. -/
theorem atat_orbit_count_eq_orientPairs :
    (([atatE1, atatE2, atatE3, atatE4].map revOrbit).dedup).length
      = ((orientPairs.map pairOrbit).dedup).length := by
  decide

end AssemblyP1.Section62ReversalInvolution
