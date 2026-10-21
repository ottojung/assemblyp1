# Physical edge-orbit objective transport: uniqueness does NOT transport (#255/#261, L3 remainder)

_Status: 2026-10-21, kernel-checked increment on branch
`agent/RQu7BlU7QWqrxn7vs2BwCw-neurotic-issue255-l3-uniqueness`._

## The claim

The merged L3 transport
(`AssemblyP1.Section62PhysicalOrbitObjective`, PR #353) reduces **maximality**
(ties admitted) of a physical orbit flow `f₀` over a candidate flow set `F` to
maximality of its physical visit vector `physVisitVec f₀` over the image
`physVisitVec '' F`, for any score that is a function of the visit vector (the
exact iid score, the fixed-`N` product-binomial score, or any count-vector
criterion).

The #255 umbrella asks for the transport of the exact oriented ML likelihood
objective **or its argmax / uniqueness**.  This note settles the uniqueness
half, and finds that it does **not** transport.

**Module:** `AssemblyP1/Section62PhysicalOrbitObjectiveUniqueness.lean`
(+ `AssemblyP1/Section62PhysicalOrbitObjectiveUniquenessAudit.lean`).

Landed, all kernel-checked (axioms `⊆ {propext, Classical.choice, Quot.sound}`,
no `sorry`/`admit`/`axiom`/`native_decide`):

* `UniqueMaximal` — a maximizer with no distinct tie.
* `physUniqueMaximal_image_of_flow` — uniqueness transports **forward**: a
  unique flow maximizer has a unique visit-vector maximizer.
* `physUniqueMaximal_of_injective` and `physUniqueMaximal_iff_of_injective` —
  uniqueness transports **backward only when the visit map is injective** on
  `F` at the truth `f₀`.
* `MixedLoop.physMk_twoRep_eq` — the minimal length-`1` mixed-sign self-loop
  `mixedLoop` on `Tagged Bool` and its reverse-complement are one physical edge.
* `MixedLoop.physVisitVec_twoRep_eq` — two distinct orbit flows with disjoint
  support have the **same** physical visit vector, so the visit map is not
  injective on orbit flows.
* `MixedLoop.flowA_ne_flowB` — the two flows are distinct.
* `MixedLoop.physUniqueMaximal_not_transported` — on the witness the visit
  vector is the unique image maximizer, but the flow is not a unique maximizer,
  for **every** score that is a function of the visit vector, including the
  exact oriented ML objective.

## Cell and regime

Axis 4 candidate domain: MB09 §6.2 bidirected flows, physical reversal-quotient
representation.  Axis 2 likelihood: any score that is a function of the visit
vector (the transport is objective-agnostic, as in `physMaximal_image_iff`).
Regime: the forward direction covers both (A) and (B); the failure is
structural (non-injectivity) and independent of the regime.

## What is *not* claimed (still OPEN)

* **L1 (source-graph correspondence).**  No proof that the quotient edge set is
  MB09's physical RC overlap multigraph (edge multiplicity,
  transitive-reduction contract).  OPEN, owned by live #284/#261.
* **Spelled-genome identification.**  No proof that a physical orbit flow is a
  single circular spelled genome.  OPEN.
* **General §6.2 classification.**  Uniqueness of the *flow* maximizer is not
  recovered without an injectivity hypothesis on the visit map; the physical
  edge quotient does not provide it for the two representations of one physical
  edge.  #261 remains OPEN.

## Validation

* `lake build --wfail AssemblyP1.Section62PhysicalOrbitObjectiveUniquenessAudit`
  — exit 0, zero warnings.
* `lake env leanchecker AssemblyP1.Section62PhysicalOrbitObjectiveUniqueness`
  — exit 0.
* `#print axioms` on every new declaration — subset of
  `{propext, Classical.choice, Quot.sound}`; no `sorryAx`.
