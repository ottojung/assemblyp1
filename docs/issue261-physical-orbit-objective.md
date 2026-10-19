# Physical edge-orbit ML-objective transport (#255/#261, L3)

_Status: 2026-10-19, kernel-checked increment landed by agent d6defaa76e2f on
`origin/main` @ `b7f561043a3b3a37a0daff5187533a3af4ec90fc` (base). This note
records a single scoped claim, its cell, and the exact remaining OPEN work._

## The claim

For the #255/#261 source-fidelity gap pinned in
`docs/section62-reversal-orbit-correspondence-gap-255.md`, the **L3 remainder**
("the exact ML objective is *not* yet transported to physical orbit totals")
is now settled at the level of the objective argument and the maximality
reduction, on the physical-orbit domain of
`AssemblyP1.Section62PhysicalEdgeOrbit`.

**Module:** `AssemblyP1/Section62PhysicalOrbitObjective.lean`
(+ `AssemblyP1/Section62PhysicalOrbitObjectiveAudit.lean`).

The §6.2 objective is a function of the candidate's read-copy / visit-count
vector (MB09 Observation 7). On the oriented §6.2 flow domain the objective
argument is `Section62FlowCountVectorAdapter.throughputVec`, the departure-based
`throughput`. On the physical-orbit domain the objective argument is the new
`physVisitVec`, whose `v`-coordinate is the total physical positive
half-incidence `physPosTotal` at the molecule class `v`.

Landed, all kernel-checked (axioms `⊆ {propext, Quot.sound}`, no
`sorry`/`admit`/`axiom`/`native_decide`):

* `physVisitVec` — the physical visit-count / read-copy vector (the objective
  argument).
* `physVisitVec_reverse` — the objective argument is unchanged when every orbit
  representative is replaced by its reverse-complement reversal. This is the
  well-definedness the legacy departure `throughput` fails
  (`Atat.inherited_throughput_not_physical`).
* `physPosTotal_add` / `physVisitVec_add` — additivity: a sum of orbit flows has
  the sum of visit vectors, so a circuit can be scored after decomposition into
  physical loops (the signed circle-tree / barbell picture of Chen–Wang–Zaslavsky
  2017, arXiv:1701.04494, and Máčajová–Škoviera 2016).
* `PhysVertexBound` / `physVertexBound_reverse` — the §6.2 vertex lower-bound
  clause ("Each vertex has a lower bound of 1", MB09 §6.2) written on physical
  visit totals, and its representative-invariance.
* `physMaximal_image_iff` — the flow-to-count-vector reduction transported to
  physical orbit totals: for any score that is a function of the visit vector
  (exact iid, fixed-`N` product-binomial, or any count-vector criterion), ML
  maximality over a set of physical orbit flows is equivalent to ML maximality
  over its physical visit-vector image.
* `physMaximal_reverse_iff` — the transported objective is independent of the
  oriented representative chosen per orbit.
* `Witness.mixed_visit_one` / `Witness.mixed_physical_ne_departure` — on the
  length-`1` mixed-sign self-loop witness the physical visit count is `1` while
  the induced oriented flow's departure throughput is `2`, so the transport is
  not a vacuous renaming.

## Cell and regime

Axis 4 candidate domain: MB09 §6.2 bidirected flows, physical reversal-quotient
representation. Axis 2 likelihood: **any** score that is a function of the visit
vector (the transport is objective-agnostic, matching
`maximal_image_iff`). Regime: both (A) and (B) inherit the transport, since it is
a reduction of the maximization domain, not a criterion.

## What is *not* claimed (still OPEN)

* **L1 (source-graph correspondence).** No proof that the quotient edge set
  (including genuinely parallel overlaps and the transitive-reduction contract)
  is MB09's physical RC overlap multigraph. OPEN.
* **Spelled-genome identification.** No proof that a physical orbit flow is a
  single circular spelled genome, and no identification of the physical
  visit-vector image with the spelled-spectrum set. The `AAATT` obstruction of
  `AssemblyP1.Section62NonSpelledFlow` shows the throughput image strictly
  contains the spelled throughputs, so no spelling-based characterization can be
  complete. OPEN.
* No classification of the general §6.2 flow domain; #261 remains OPEN.

## Validation

* `lake build --wfail` — exit 0, 9230 jobs, zero warnings.
* `LEAN_NUM_THREADS=1 lake env leanchecker AssemblyP1` — exit 0 (whole-library
  kernel replay).
* `axiom-audit --allow propext,Classical.choice,Quot.sound --root AssemblyP1
  --modules-from AssemblyP1` — exit 0, 10099 declarations within allowlist.
* `python3 scripts/check-research-docs.py` — exit 0.
