# AssemblyP1 umbrella #255 — remaining-open matrix

_Status: 2026-10-11. Source-fidelity / whitepaper-theorem-matrix integration
front. Base: `main` @ `02406aa26239eab1d224f2d434df7628f04be8d1` (green).
This matrix is a proposed, reviewable status record for the #255 research
umbrella, not a declaration that the remaining proofs are finished. It is
updated only when a scoped claim is proved, refuted, or explicitly
re-scoped with evidence. Conjectures remain OPEN until proved or refuted._

## Epistemic classes

Every material result is classified as one of:

- **source fact** — directly supported by a cited primary source
- **modeling decision** — deliberate formal interpretation
- **conjecture** — believed useful but not proved
- **computational evidence** — bounded search with explicit scope
- **mathematical proof** — human-readable proof with explicit assumptions
- **kernel-checked result** — Lean theorem without `sorry`, `admit`, or new axioms

---

## LANDED — kernel-checked, merged to main, independently reviewed

### #256 (CLOSED) — exact multinomial, same-length, oriented, sample-uniform (B): PROVED iff

- **Artifact:** `AssemblyP1/RobustSameLengthIff.lean`
- **Branch:** `agent/board-256-robust-iff-20261010` @ `737cc9d`; merged `2655d29`
- **Statement:** For circular oriented `S`, `G ≥ L ≥ 2`, `A` = length-`L` spectrum,
  `E = supp(A)`, `F` = all positive balanced circulations of total `G` on `E`:
  `(∀ x positive on EVERY edge, ∀ B ∈ F, Lik(B;x) ≤ Lik(A;x)) ↔ F = {A}`.
- **Key structural point:** No `I_s`/balance/repeat assumption in the iff
  (balance enters only via `A ∈ F`). Constructive beating witness for every
  `B ≠ A`.
- **Axioms:** `{propext, Classical.choice, Quot.sound}`
- **Python exhaustive scan:** 809280 words / 2460318 witnesses exact-verified.

### #260 (CLOSED) — exact multinomial, fixed-length, RC-molecule, full overlap `o_min = L−1`, source-faithful equal-support reading, sample-uniform (B): PROVED iff

- **Artifact:** `AssemblyP1/FullOverlapMoleculeML.lean`
- **Branch:** `issue260-fulloverlap-molecule-ml` @ `532ef64`; merged `c34ee44`/`70e78db`
- **Statement:** Truth is exact-ML sample-uniform maximal IFF normalized
  molecule-count vector unique; criterion = coordinatewise dominance on `supp(A)`.
- **Equal-support essential:** `AATT→AAAT` refutes the broad reading;
  `W1 AAATAT→AAAAAT` is the non-uniqueness witness.
- **Axioms:** `{propext, Classical.choice, Quot.sound}`

### #257 (PARTIAL) — exact support-domain rigidity theorem landed; Graver structural iff NOT merged

- **Merged artifact:** `AssemblyP1/ExactRigidityCriterion.lean`
- **Branch:** `research/257-rigid-read-graphs`; merged `c28aec7`/`b0ce311`
- **Merged statement:** Exact support-domain rigidity theorem for positive
  circulations on the oriented `L`-mer support graph.
- **NOT merged:** `AssemblyP1/GraverRigidity.lean` (Graver structural iff) —
  this file is untracked on the agent working directory and has NOT been merged
  to main. The Graver criterion (`A` rigid IFF no Graver element `g ∈ Gr(M)`
  satisfies `g ≥ 1 − A` coordinatewise) remains OPEN.
- **Axioms (merged):** `{propext, Classical.choice, Quot.sound}`

### #261 (PARTIAL) — count-vector and exact binomial partial results

- **Artifact:** `AssemblyP1/GeneralBidirectedFlowML.lean` (partial)
- **Commit:** `02406aa` (current main HEAD)
- **Status:** Count-vector and exact binomial partial results integrated.
  General §6.2 bidirected flow classification remains OPEN.

### Population maximality without repeats: PROVED

- `PopulationGibbs.truth_is_population_maximizer`; equality iff normalized spectra
  agree. Population-level only; does NOT settle finite sampling.

---

## REFUTED — specific conjectures, NOT classifications

### Historical molecule-flow full-overlap BRIDGING SUFFICIENCY: REFUTED

- Merged PR #142 literal Shomorony §6.4 W1/W2 strict exact/binomial
  counterexamples at MB09 full-overlap §6.2.
- **W1:** `S=AAATAT`, `D=AAAAAT` (`G=6`, `L=3`): exact ratio 3, binomial ratio 5.
- **W2:** `S=ATATACAC`, `D=ATACACAC` (`G=8`, `L=3`): exact ratio 3/2, binomial ratio 9/5.
- This refutes a sufficiency claim only; it does not classify any genome set or
  overlap floor.

### #259 recovered WIP's fixed-x iff continuous KKT: FALSE for integer flows

- **Witness:** `S=AAABBB`, `G=N=6`, `x=[3,1,2,1]`.
- Continuous KKT optimality is **sufficient**, but **NOT necessary**, for maximizing a differentiable concave likelihood over a discrete integer-feasible subset of its continuous convex relaxation. At an interior point, the stationary-gradient condition suffices; with active box boundaries, the correct KKT inequality/multiplier conditions suffice. The stated AAABBB discrete winner violates stationarity on a feasible real direction, so necessity fails.
- **Status:** REFUTED as a classification criterion. The exact integer witness is
  recorded on the issue board.

---

## OPEN — explicitly unresolved

### #258 (fixed-x sample classification)

- **PR:** #151, signed head `ce011d5` (parent `32ef867`) on branch `agent/board-255-matrix-b6aa4ea0dce8-20261010`
- **Has:** Local kernel-checkable AAABBB 4 numerical candidate likelihoods.
- **Does NOT yet prove:** Exhaustion/global truth winner.
- **Still needs:** Final CI.
- **Status:** OPEN. All dependent results remain open.

### #259 (MB09 §6.1 fixed-external-N product-binomial)

- **(A)** at fixed `x` and **(B)** for every realizable complete-support `x`.
- **Status:** OPEN. No binomial-specific classification (extra `(1−d(w)/N)^{n−x(w)}`
  factors, zero-count coordinates, boundary 0/1 probabilities) is established.
- **Note:** The recovered WIP's continuous KKT iff is FALSE (see REFUTED above).

### #261 (general MB09 §6.2 bidirected flows at arbitrary `o_min ≤ L−1`)

- **All sub-axes OPEN:** arbitrary overlap floor, transitive reduction, vertex
  lower bound 1, orientation/RC classes, integer vs half-integral flows, flows
  not spelling one circular genome, candidate-set choice, truth admissibility,
  likelihood (exact vs fixed-N binomial), and length universe.
- **Status:** OPEN, explicitly unresolved.

### #262 (full-overlap edge irreducibility)

- **Distinction:** Full-overlap edge irreducibility must be distinguished from
  conditional source-faithful flow transfer.
- **Status:** OPEN.

### #263 (separable convex discrete Graver criterion)

- **Status:** IN PROGRESS. Separable convex discrete Graver criterion.

### #264 (integer-kernel conformal Graver decomposition)

- **Status:** OPEN. A separate agent is formalizing a finite conformal Graver
  basis obstruction and decomposition, distinct from the already-merged
  bounded zero-sum-delta rigidity iff in #257.

---

## AXIS MATRIX (PROVED / REFUTED / OPEN)

| Axis | Status | Detail |
|---|---|---|
| Oriented vs RC molecule types | PROVED (landed scopes) | Oriented + same-length + exact multinomial + sample-uniform PROVED (#256); RC + full-overlap + fixed-length + exact multinomial + sample-uniform PROVED (#260); oriented arbitrary-overlap and RC arbitrary-overlap OPEN (#261) |
| Exact multinomial vs fixed-N binomial | PROVED (exact) / OPEN (binomial) | Exact multinomial PROVED in the two landed scopes; fixed-N binomial (MB09 §6.1) OPEN (#259) |
| Same vs variable length | PROVED (same) / OPEN (variable) | Same-length PROVED where landed; variable length OPEN (fenced to #261) |
| Spelled genomes vs MB09 §6.2 bidirected flows / overlap floor | PROVED (full-overlap) / OPEN (arbitrary) | Equal-support full-overlap RC molecule-spectrum ML PROVED (#260); unrestricted source-faithful MB09 §6.2 nonspelled flow candidate domain and arbitrary overlap floor OPEN (#261); historical bridging sufficiency at full overlap REFUTED (W1/W2, PR #142) |
| Truth candidacy | PROVED (landed scopes) / OPEN (extended) | Truth genuinely admissible over spelled candidate universes PROVED in the landed scopes; extended candidate sets OPEN (#261) |
| Literal historical read-string `I_s` vs project placement `I_s` | PROVED (placement) / REFUTED (literal) / OPEN (remaining) | Project-placement reading PROVED (#256 iff needs no `I_s`); literal historical `I_s` full-overlap bridging sufficiency REFUTED (W1/W2); remaining historical-referent questions OPEN |

---

## Source-fidelity audit summary

The manuscript (`paper/`) and repository docs have been audited against the
original Medvedev-Brudno 2009 source:

| Audit point | Status |
|---|---|
| §6.1 true joint multinomial vs approximate product-binomial pseudo-likelihood | Correctly distinguished in paper Def. 1.2 and Appendix A.5 |
| §6.2 signed bidirected flow vs actual circular genomes | Correctly distinguished in paper §2.3, §4, and Appendix D |
| Infinite graph capacities vs external N probability bound | Correctly distinguished: §6.2 has `u = ∞` on overlap edges; §6.1 binomial uses external `N` |
| Terminal arcs high cost vs forbidden | Correctly stated: supersource/sink edges have "prohibitively large costs", not forbidden |
| RC classes | Correctly distinguished: oriented reads vs molecule classes throughout |
| Literal source read-string `I_s` vs placement coverage | Correctly distinguished: `I_s^match` (historical) vs `I_s` (placement-based) in paper §2.2, §4.3 |

---

## #255 umbrella status

**#255 remains OPEN.** Scoped claims on the #258, #259, #261, #262, #263, and #264
fronts are unresolved; no conjecture is promoted to fact. #255 closes only when
every scoped claim is proved or refuted to the issue's evidence standard
(audited proof, direct Lean theorem where feasible, green CI/merge) and this
matrix is updated to match.
