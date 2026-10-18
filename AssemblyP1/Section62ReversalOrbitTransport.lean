import AssemblyP1.Section62PhysicalEdgeOrbit

/-!
# Reversal-orbit flow transport: the symmetric-oriented-flow discipline fails (#255/#261)

The pinned remaining lemma of
`docs/section62-reversal-orbit-correspondence-gap-255.md` has three layers:

* **L1 (correspondence)** — a correspondence between the reversal-quotient of the
  tagged overlap edges and MB09's physical bidirected edge set;
* **L2 (flow transport)** — a flow discipline on quotient orbits, "either a
  requirement `f e = f (rev e)` on tagged edge values, or flow defined directly
  on quotient edge orbits, with a proof that the physical feasible set is
  unchanged";
* **L3 (throughput invariance)** — the total positive half-edge incidence at a
  vertex equals the legacy departure throughput on the quotient.

This module settles the **first disjunct of L2 by refutation** and identifies the
second as the correct route, using the *smallest possible* witness.

## The general obstruction

`throughput` (`AssemblyP1.Section62BidirectedFlow.lean`) counts an oriented edge
as departing the molecule class of its stored `sx` end.  For a **self-loop**
`e` (both endpoints in the same molecule class) its reverse-complement
representation `reverseEdge e` departs the *same* class.  Consequently, for any
flow `f` on the two-element edge list `[e, reverseEdge e]`,

`throughput cls f [e, reverseEdge e] v = f e + f (reverseEdge e)`.

If the flow is **reversal-symmetric** (`f e = f (reverseEdge e)`, the natural
"define the flow on physical orbits" discipline for the legacy `BdFlow`), the
inherited departure count is `2 * f e` — always **even**.  A physical unit orbit
flow on a mixed-sign self-loop is balanced with physical visit count **one**, an
odd number.  Hence:

> No reversal-symmetric oriented flow realizes the unit physical loop flow.

So imposing `f e = f (rev e)` does **not** leave the physical feasible set
unchanged; the correct discipline is a flow defined directly on the quotient
edge orbits (`physPos`/`physNeg`/`physPosTotal` of
`AssemblyP1.Section62PhysicalEdgeOrbit`).

## The minimal witness

The obstruction already appears at the smallest possible data: the length-`1`
mixed-sign self-loop `mixedLoop` on `Tagged Bool`
(`AssemblyP1.Section62PhysicalHalfIncidence.lean`), whose two representations
`mixedLoop` and `reverseEdge mixedLoop` are distinct but lie in one physical
reversal orbit.  No palindrome of length `4` (the `ATAT` witness) is needed.

## What is *not* claimed

* No full MB09 §6.2 source-graph correspondence (L1) and no transport of the
  exact ML objective to physical orbits; those stay OPEN.
* No claim that a physical orbit flow is a spelled genome.
* No `sorry` / `admit` / `axiom` / `native_decide`.
-/

namespace AssemblyP1.Section62ReversalOrbitTransport

open AssemblyP1.Section62Flow
open AssemblyP1.Section62PhysicalHalfIncidence
open AssemblyP1.Section62PhysicalEdgeOrbit

variable {A W : Type} [DecidableEq W]

/-! ## Reversal-symmetric oriented flows -/

/-- A flow on tagged signed edges is **reversal-symmetric** when it assigns the
same weight to an edge and to its reverse-complement representation.  This is the
first (legacy-oriented) disjunct of the L2 flow-transport discipline: define the
physical flow by symmetrizing over the two representatives of each orbit. -/
def RevSymm (f : BdFlow A (Tagged W)) : Prop := ∀ e, f (reverseEdge e) = f e

/-! ## The general self-loop transport identity -/

/-- The inherited departure throughput on the two-element edge list
`[e, reverseEdge e]` splits into the two departure indicators: the `sx` end of
`reverseEdge e` is the `flip` of the `sy` end of `e`, and `cls` forgets the
orientation bit. -/
theorem throughput_pair_cls (f : BdFlow A (Tagged W)) (e : BdEdge A (Tagged W))
    (v : Tagged W) :
    throughput A (Tagged W) cls f [e, reverseEdge e] v =
      (if cls e.sx = v then f e else 0) +
        (if cls e.sy = v then f (reverseEdge e) else 0) := by
  simp only [throughput, List.foldr_cons, List.foldr_nil, reverseEdge, class_flip]
  by_cases h1 : cls e.sx = v <;> by_cases h2 : cls e.sy = v <;> simp [h1, h2]

/-- **Self-loop transport identity.**  If `e` is a self-loop (both endpoints in
the same molecule class `v`), the inherited departure throughput of any flow on
`[e, reverseEdge e]` counts both representatives' weights. -/
theorem throughput_pair_selfloop (f : BdFlow A (Tagged W)) (e : BdEdge A (Tagged W))
    (v : Tagged W) (hs : cls e.sx = cls e.sy) (hv : cls e.sx = v) :
    throughput A (Tagged W) cls f [e, reverseEdge e] v =
      f e + f (reverseEdge e) := by
  rw [throughput_pair_cls]
  have hsy : cls e.sy = v := by rw [← hs]; exact hv
  simp only [hv, hsy, ↓reduceIte]

/-- **Evenness.**  A reversal-symmetric flow on a self-loop orbit has even
inherited departure throughput. -/
theorem throughput_pair_selfloop_symm (f : BdFlow A (Tagged W)) (e : BdEdge A (Tagged W))
    (v : Tagged W) (hf : RevSymm f) (hs : cls e.sx = cls e.sy) (hv : cls e.sx = v) :
    throughput A (Tagged W) cls f [e, reverseEdge e] v = 2 * f e := by
  rw [throughput_pair_selfloop f e v hs hv, hf e]
  ring

/-- The inherited departure throughput of a reversal-symmetric flow on a
self-loop orbit is always even. -/
theorem throughput_pair_selfloop_symm_even (f : BdFlow A (Tagged W))
    (e : BdEdge A (Tagged W)) (v : Tagged W) (hf : RevSymm f)
    (hs : cls e.sx = cls e.sy) (hv : cls e.sx = v) :
    ∃ k, throughput A (Tagged W) cls f [e, reverseEdge e] v = 2 * k :=
  ⟨f e, throughput_pair_selfloop_symm f e v hf hs hv⟩

/-! ## The minimal witness: the length-`1` mixed-sign self-loop -/

/-- The reverse-complement representation of the mixed-sign self-loop. -/
def mixedRev : BdEdge Bool (Tagged Bool) := reverseEdge mixedLoop

/-- The two representations of the physical mixed-sign loop are distinct tagged
edges. -/
theorem mixedRev_ne_mixedLoop : mixedRev ≠ mixedLoop := by decide

/-- They are the *same* physical edge (one reversal orbit). -/
theorem mixedRev_same_orbit :
    physMk (A := Bool) (W := Bool) mixedRev = physMk mixedLoop := by
  rw [mixedRev, physMk_reverse]

/-- The mixed-sign loop is a self-loop: both endpoints lie in the class
`(false, false)`. -/
theorem mixedLoop_selfloop : cls mixedLoop.sx = cls mixedLoop.sy := by decide

/-- Its departure end lies in the class `(false, false)`. -/
theorem mixedLoop_cls_sx : cls mixedLoop.sx = ((false, false) : Tagged Bool) := by decide

/-- The **physical** positive half-incidence of the unit mixed-sign orbit at the
class is one: the quotient model counts the loop once. -/
theorem mixed_physical_visit_one :
    physPos ((false, false) : Tagged Bool) (physMk (A := Bool) (W := Bool) mixedLoop) = 1 := by
  rw [physPos_mk]
  exact (mixedLoop_count).1

/-- The physical visit count is the same for the other representative, by
representation invariance of `physPos`. -/
theorem mixed_physical_visit_one_rev :
    physPos ((false, false) : Tagged Bool)
      (physMk (A := Bool) (W := Bool) (reverseEdge mixedLoop)) = 1 := by
  rw [physPos_mk, posHalf_reverse]
  exact (mixedLoop_count).1

/-- **No reversal-symmetric oriented flow realizes the unit physical loop flow.**
The inherited departure throughput is even, the physical visit count is one. -/
theorem no_revsymm_throughput_one (f : BdFlow Bool (Tagged Bool)) (hf : RevSymm f) :
    throughput Bool (Tagged Bool) cls f [mixedLoop, reverseEdge mixedLoop]
      ((false, false) : Tagged Bool) ≠ 1 := by
  intro h
  have h2 := throughput_pair_selfloop_symm f mixedLoop ((false, false) : Tagged Bool)
    hf mixedLoop_selfloop mixedLoop_cls_sx
  rw [h2] at h
  omega

/-- **The L2 obstruction, stated as a non-existence theorem.**  There is no
reversal-symmetric oriented flow on the minimal mixed-sign loop orbit whose
inherited departure throughput equals the physical visit count one. -/
theorem no_revsymm_flow_realizes_unit_loop :
    ¬ ∃ f : BdFlow Bool (Tagged Bool), RevSymm f ∧
        throughput Bool (Tagged Bool) cls f [mixedLoop, reverseEdge mixedLoop]
          ((false, false) : Tagged Bool) = 1 := by
  rintro ⟨f, hf, h⟩
  exact no_revsymm_throughput_one f hf h

/-- **The two disjuncts of L2 differ.**  The quotient orbit model realizes the
unit mixed-sign loop (physical visit count one, `mixed_physical_visit_one`),
while no reversal-symmetric oriented flow does
(`no_revsymm_flow_realizes_unit_loop`).  Hence the `f e = f (rev e)` discipline
does not leave the physical feasible set unchanged; the correct route is a flow
defined directly on the quotient edge orbits. -/
theorem symmetric_discipline_refuted :
    (physPos ((false, false) : Tagged Bool)
        (physMk (A := Bool) (W := Bool) mixedLoop) = 1) ∧
      (¬ ∃ f : BdFlow Bool (Tagged Bool), RevSymm f ∧
        throughput Bool (Tagged Bool) cls f [mixedLoop, reverseEdge mixedLoop]
          ((false, false) : Tagged Bool) = 1) :=
  ⟨mixed_physical_visit_one, no_revsymm_flow_realizes_unit_loop⟩

end AssemblyP1.Section62ReversalOrbitTransport
