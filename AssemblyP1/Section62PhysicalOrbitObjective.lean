import AssemblyP1.Section62PhysicalEdgeOrbit
import AssemblyP1.Section62FlowCountVectorAdapter

/-!
# Transporting the §6.2 ML objective to physical edge-orbit totals (#255/#261, L3)

The #255/#261 source-fidelity note
`docs/section62-reversal-orbit-correspondence-gap-255.md` pins the remaining
gap after the merged reversal-orbit work as *"the exact ML objective is not yet
transported to physical orbit totals"* (L3 remainder).  The merged quotient
model `AssemblyP1.Section62PhysicalEdgeOrbit` settles reversal-orbit transport of
*signed half-incidences* pointwise (`physPos`, `physNeg`, `physPosTotal`,
`physNegTotal`, `PhysBalanced`), but it defines no **objective argument**, no
**vertex bound**, and no **maximality reduction** on those totals.

This module supplies exactly that transport, and nothing else:

1. **Read-copy / visit-count vector.**  `physVisitVec` is the vector whose `v`-th
   coordinate is the total physical positive half-incidence at the molecule
   class `v`.  By MB09 Observation 7 this coordinate is the number of times a
   candidate visits `v`, so `physVisitVec` is the argument the §6.2 ML objective
   is a function of.

2. **Well-definedness on orbit totals.**  `physVisitVec_reverse` shows the vector
   is unchanged when every orbit representative is replaced by its
   reverse-complement reversal.  Thus the transported objective is a function of
   the *physical orbit totals*, not of the oriented representatives — this is the
   property the legacy departure-based `throughput` fails
   (`Atat.inherited_throughput_not_physical`).

3. **Additivity.**  `physVisitVec_add` decomposes the visit vector of a sum of
   orbit flows into the sum of the visit vectors.  This is the linearity that
   lets a signed circuit be scored after decomposing it into its physical loops
   (the circle-tree / barbell picture of Chen–Wang–Zaslavsky 2017 and
   Máčajová–Škoviera 2016).

4. **Vertex lower-bound transport.**  `PhysVertexBound` is the §6.2 clause
   "each vertex has a lower bound of 1" (MB09 §6.2) written on physical visit
   totals, and `physVertexBound_reverse` shows it is representative-invariant.

5. **The ML objective transport.**  `physMaximal_image_iff` is the
   flow-to-count-vector reduction of
   `AssemblyP1.Section62FlowCountVectorAdapter.maximal_image_iff`, transported to
   the physical orbit domain: for any score that is a function of the visit
   vector — the exact iid score, the fixed-`N` product-binomial score, or any
   count-vector criterion — ML maximality over a set of physical orbit flows is
   equivalent to ML maximality over its physical visit-vector image.
   `physMaximal_reverse_iff` adds that this transported objective does not depend
   on the representative choice.

## What is *not* claimed here

* No proof that the quotient edge set is MB09's physical §6.2 overlap multigraph
  (that is L1, still OPEN), and no identification of a physical flow with a
  single circular spelled genome.
* No claim that the physical visit-vector image equals the spelled-spectrum set;
  the `AAATT` obstruction of `AssemblyP1.Section62NonSpelledFlow` shows the
  throughput image strictly contains the spelled one, so no spelling-based
  characterization can be complete.
* No `sorry` / `admit` / `axiom` / `native_decide`.
-/

namespace AssemblyP1.Section62PhysicalOrbitObjective

open AssemblyP1.Section62Flow
open AssemblyP1.Section62PhysicalHalfIncidence
open AssemblyP1.Section62PhysicalEdgeOrbit
open AssemblyP1.Section62FlowCountVectorAdapter

variable {A W : Type} [DecidableEq W]

/-! ## The physical visit-count vector (the objective argument) -/

/-- The **physical visit-count vector** of an orbit-indexed flow `f`: the total
physical positive half-incidence at each molecule class.  This is the vector the
§6.2 maximum-likelihood objective is a function of; by MB09 Observation 7 its
`v`-th coordinate is the number of times the candidate visits `v`. -/
def physVisitVec {ι : Type} (reps : List ι) (rep : ι → BdEdge A (Tagged W))
    (f : ι → ℕ) : Tagged W → ℕ :=
  fun v => physPosTotal reps rep f v

@[simp] theorem physVisitVec_apply {ι : Type} (reps : List ι)
    (rep : ι → BdEdge A (Tagged W)) (f : ι → ℕ) (v : Tagged W) :
    physVisitVec reps rep f v = physPosTotal reps rep f v := rfl

/-- **Well-definedness on physical orbit totals.**  Replacing every orbit
representative by its reverse-complement reversal does not change the
visit-count vector: the weight lives on the physical orbit, not on the oriented
representative. -/
theorem physVisitVec_reverse {ι : Type} (reps : List ι)
    (rep : ι → BdEdge A (Tagged W)) (f : ι → ℕ) :
    physVisitVec reps (fun i => reverseEdge (rep i)) f = physVisitVec reps rep f := by
  funext v
  simp only [physVisitVec_apply]
  exact physPosTotal_reverse reps rep f v

/-- **Additivity.**  The visit vector of a sum of orbit flows is the sum of the
visit vectors: physical visits are counted linearly, so a circuit can be scored
after decomposing it into its physical loops. -/
theorem physPosTotal_add {ι : Type} (reps : List ι)
    (rep : ι → BdEdge A (Tagged W)) (f g : ι → ℕ) (v : Tagged W) :
    physPosTotal reps rep (fun i => f i + g i) v
      = physPosTotal reps rep f v + physPosTotal reps rep g v := by
  induction reps with
  | nil => simp [physPosTotal]
  | cons i rest ih =>
    simp only [physPosTotal, List.map_cons, List.sum_cons] at *
    rw [ih]
    ring

/-- The vector form of `physPosTotal_add`. -/
theorem physVisitVec_add {ι : Type} (reps : List ι)
    (rep : ι → BdEdge A (Tagged W)) (f g : ι → ℕ) :
    physVisitVec reps rep (fun i => f i + g i)
      = fun v => physVisitVec reps rep f v + physVisitVec reps rep g v := by
  funext v
  simp only [physVisitVec_apply]
  exact physPosTotal_add reps rep f g v

/-! ## The §6.2 vertex lower bound, transported to physical totals -/

/-- The §6.2 vertex lower-bound clause ("Each vertex has a lower bound of 1 since
it represents a read that must be present in the genome at least once", MB09
§6.2) written on **physical visit totals** rather than on the oriented departure
throughput. -/
def PhysVertexBound {ι : Type} (reps : List ι) (rep : ι → BdEdge A (Tagged W))
    (f : ι → ℕ) (verts : List (Tagged W)) (lb : ℕ) : Prop :=
  ∀ v ∈ verts, lb ≤ physVisitVec reps rep f v

/-- The transported vertex lower-bound clause is representative-invariant. -/
theorem physVertexBound_reverse {ι : Type} (reps : List ι)
    (rep : ι → BdEdge A (Tagged W)) (f : ι → ℕ) (verts : List (Tagged W))
    (lb : ℕ) :
    PhysVertexBound reps (fun i => reverseEdge (rep i)) f verts lb
      ↔ PhysVertexBound reps rep f verts lb := by
  simp only [PhysVertexBound, physVisitVec_reverse]

/-! ## The ML objective transport -/

/-- **The §6.2 ML objective transported to physical orbit totals.**  For a set
`F` of physical orbit flows and a score `score` that is a function of the
visit-count vector, ML maximality of the truth orbit flow `f₀` over `F` is
equivalent to ML maximality of its physical visit vector `physVisitVec f₀` over
the visit-vector image `physVisitVec '' F`.

This is the physical-orbit counterpart of
`AssemblyP1.Section62FlowCountVectorAdapter.maximal_image_iff`: it is the exact
sense in which the count-vector likelihood criteria (exact iid, fixed-`N`
product-binomial, and their scoped classifications) apply to the physical orbit
domain, whose objective argument is `physVisitVec` rather than the non-invariant
departure `throughputVec`. -/
theorem physMaximal_image_iff {ι : Type} (reps : List ι)
    (rep : ι → BdEdge A (Tagged W)) (F : Set (ι → ℕ))
    (score : (Tagged W → ℕ) → ℚ) (f₀ : ι → ℕ) :
    Maximal (Set.image (physVisitVec reps rep) F) score (physVisitVec reps rep f₀)
      ↔ Maximal F (fun f => score (physVisitVec reps rep f)) f₀ := by
  constructor
  · intro h f hf
    exact h (physVisitVec reps rep f) ⟨f, hf, rfl⟩
  · intro h B hB
    obtain ⟨f, hf, rfl⟩ := hB
    exact h f hf

/-- The transported objective does not depend on the oriented representative
chosen for each orbit: replacing every representative by its reversal leaves the
maximality condition unchanged. -/
theorem physMaximal_reverse_iff {ι : Type} (reps : List ι)
    (rep : ι → BdEdge A (Tagged W)) (F : Set (ι → ℕ))
    (score : (Tagged W → ℕ) → ℚ) (f₀ : ι → ℕ) :
    Maximal F (fun f => score (physVisitVec reps (fun i => reverseEdge (rep i)) f)) f₀
      ↔ Maximal F (fun f => score (physVisitVec reps rep f)) f₀ := by
  simp only [physVisitVec_reverse]

/-! ## Non-vacuity: the length-`1` mixed-sign loop witness -/

/-! On the minimal mixed-sign self-loop witness of
`AssemblyP1.Section62PhysicalHalfIncidence` (`mixedLoop` on `Tagged Bool`), the
transported physical objective is genuinely different from the naive
departure-based objective: the unit orbit flow visits the class once physically,
while the induced oriented flow's departure throughput reports two. -/

namespace Witness

open AssemblyP1.Section62PhysicalEdgeOrbit.Atat

/-- The physical visit vector of the unit mixed-sign orbit flow is one at the
observed class (the physical visit count of the mixed-sign loop). -/
theorem mixed_visit_one :
    physVisitVec orbitIds orbitRep orbFlow v0 = 1 := by
  simpa only [physVisitVec_apply] using orbit_visit_one

/-- **The transported objective is not the naive one.**  The physical visit
count of the unit mixed-sign orbit flow at the observed class (`1`) differs from
the departure throughput of the induced oriented flow (`2`), so the objective
transport is not a vacuous renaming of the non-invariant departure count. -/
theorem mixed_physical_ne_departure :
    physVisitVec orbitIds orbitRep orbFlow v0
      ≠ throughputVec (A := Bool) (W := Tagged (List Bool)) cls inducedFlow
          [E1, E2, E3, E4] v0 := by
  rw [mixed_visit_one, throughputVec, inherited_throughput_two]
  decide

end Witness

end AssemblyP1.Section62PhysicalOrbitObjective
