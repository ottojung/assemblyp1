# Issue #261: ML maximality in general bidirected flow domains

Child of #255; extends #260 from full overlap to genuine MB09 §6.2 bidirected
overlap graphs at arbitrary `o_min ≤ L − 1`.

## Source audit

Primary source: Medvedev & Brudno, *Maximum Likelihood Genome Assembly*,
J. Comput. Biol. 16(8) (2009) 1101–1116 (PMC3154397), §3.1–§3.4, §5.2, §6.1–§6.2,
as quoted in `docs/section62-mb09-bidirected-graph-audit.md`.

The §6.2 feasibility object (Variant F of `docs/ml-formalization-contract.md`) is
encoded in `AssemblyP1/Section62BidirectedFlow.lean`: vertices are observed read
molecule classes (§3.1, §4.1), edges are all proper bidirected overlaps of length
`≥ o_min` (§3.3, §6.2), transitive edge reduction removes overlaps spelled by two
shorter overlaps (§6.2), each vertex has lower bound 1 (§6.2), edge lower bounds
are 0 and upper bounds infinite (§6.2), and the signed-incidence balance
`pos(f)(v) − neg(f)(v) = 0` holds after the supersource/supersink conversion
(§3.4, §6.2).

The §6.1 objective is the product of separable binomial marginals with external
genome size `N` (§6.1). The exact multinomial objective (Variant E) is the
specialization to fixed per-class probabilities `d_i / N`.

## The new phenomenon at arbitrary overlap

At full overlap (`o_min = L − 1`) every edge overlap is exactly `L − 1`, so a
flow that visits `k` reads spells a genome of length exactly `k`: the length is
fixed by the throughput. At arbitrary `o_min ≤ L − 1` an edge may carry any
overlap length in `[o_min, L − 1]`, so a flow that visits `k` reads with overlap
lengths `o_1, …, o_k` spells a genome of length `∑ (L − o_j)`, which is **not**
determined by the throughput. The candidate genome length `N` is therefore a
*variable*, and the exact-multinomial likelihood comparison between a candidate
(counts `d`, length `N`) and the truth (counts `A`, length `G`) acquires a
length factor.

## Candidate classes and maximality conditions

### Class 1: Variable-length exact-multinomial (Variant E)

- **Candidates**: count vectors `d` with variable length `N` (flows, not
  necessarily spelled circuits or circular genomes).
- **Truth**: admitted (the truth is a candidate).
- **Likelihood**: exact multinomial `∏ᵢ (dᵢ/N)^(xᵢ)`.
- **Length universe**: variable `N ≥ ∑ d`.
- **Maximality condition** (`varLengthCriterion`): the truth is sample-uniformly
  maximal **iff** `∀ i ∈ supp A : Bᵢ·G ≤ Aᵢ·N` (the density bound). This is
  necessary and sufficient. At `N = G` it reduces to coordinatewise dominance
  (`fixedLengthRecovery`), recovering #260's Proposition 3.2.
- **Witnesses**: `stretch_beats` (AATATT beats AATT on `e_{AT}`), `dilution_witness`.

### Class 2: Flow-domain binomial with external N = G (Variant A)

- **Candidates**: §6.2 feasible flows with throughput `B`, external `N = G` fixed.
- **Truth**: admitted.
- **Likelihood**: §6.1 separable binomial `∏ᵢ C(n, xᵢ) (Bᵢ/N)^(xᵢ) (1−Bᵢ/N)^(n−xᵢ)`.
- **Length universe**: fixed `N = G`.
- **Maximality condition** (`flow_dominance_criterion`): the truth is
  sample-uniformly maximal **iff** no admissible flow throughput `B` has
  `Bᵢ > Aᵢ` for some `i ∈ supp A` (coordinatewise dominance on the truth's
  support). This is necessary and sufficient.
- **Failure at `o_min < L − 1`**: the `AAATT` instance at `o_min = 1` has
  non-spelling flow maximizers that beat the truth (ratio `256/81`), verified by
  `scripts/verify_issue261_general_bidirected_flow_ml.py`.

### Class 3: Integer flows vs half-integral relaxation

- **Candidates**: integer §6.2 flows vs half-integral (LP relaxation) flows.
- **Truth**: admitted.
- **Likelihood**: §6.1 separable binomial.
- **Length universe**: fixed `N = G`.
- **Maximality condition**: the integer flow constraint is **binding**. The
  half-integral optimum can strictly beat every integral maximizer. Witness:
  `AAATT` at `o_min = 1`, `N = 5`, `x = (AAA:2, AAT:1, TAA:1)`. The AAA binomial
  factor `d²(5−d)²` is maximized at `d = 2, 3` (value 36) among integers but at
  `d = 5/2` (value 625/16) among half-integers, so the half-integral flow
  `h = (5/2, 1, 1)` beats the integral maximizers by `625/576` (`half_integral_gap`).

### Class 4: Flows that do NOT spell one circular genome

- **Candidates**: §6.2 feasible flows that are not necessarily spelled by a
  single circular genome (non-spelled flows).
- **Truth**: admitted.
- **Likelihood**: §6.1 separable binomial.
- **Length universe**: fixed `N = G`.
- **Maximality condition**: no tractable structural criterion is known. The
  `AAATT` instance at `o_min = 1` exhibits non-spelling flow maximizers that
  beat the truth, so the truth is not maximal in this class. The
  `Section62BridgingCounterexample` module kernel-checks the literal §6.2
  feasibility of both the truth and the competitor.
- **Status**: OPEN. The non-spelled-flow phenomenon is a genuine obstruction at
  `o_min < L − 1` with no known necessary-and-sufficient condition.

### Class 5: Rescaling ties at variable length

- **Candidates**: count vectors with variable length.
- **Truth**: admitted.
- **Likelihood**: exact multinomial.
- **Length universe**: variable.
- **Maximality condition**: uniqueness of the normalized spectrum is
  **impossible** at variable length. The `k`-fold cover `S^k` has spectrum
  `k·A` and length `k·G`, so its normalized spectrum equals the truth's and it
  ties on every sample (`rescaling_tie`). This is a phenomenon with no
  full-overlap analogue.

## Remaining-open matrix

| Axis | Status |
|---|---|
| Variable-length exact-multinomial criterion | **RESOLVED** (`varLengthCriterion`) |
| Flow-domain binomial criterion (external N=G) | **RESOLVED** (`flow_dominance_criterion`) |
| Half-integral relaxation gap | **RESOLVED** (`half_integral_gap`) |
| Rescaling ties at variable length | **RESOLVED** (`rescaling_tie`) |
| Non-spelled-flow maximality criterion | **OPEN** |
| Transitive reduction interaction with ML | **OPEN** |
| Orientation/RC class interaction | **OPEN** |
| Sample realizability at arbitrary overlap | **OPEN** |

## Artifacts

- `AssemblyP1/GeneralBidirectedFlowML.lean`: kernel-checked abstract theorems.
- `scripts/verify_issue261_general_bidirected_flow_ml.py`: independent exact
  recomputation (all checks pass).
- `scratch261/Audit.lean`: axiom audit (only propext, Classical.choice, Quot.sound).
