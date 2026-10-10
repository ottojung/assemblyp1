# Issue #261: ML maximality in general bidirected flow domains

Child of #255; extends #260 from full overlap to genuine MB09 §6.2 bidirected
overlap graphs at arbitrary `o_min ≤ L − 1`.

## Source audit

Primary source: Medvedev & Brudno, *Maximum Likelihood Genome Assembly*,
J. Comput. Biol. 16(8) (2009) 1101–1116 (PMC3154397), §3.1–§3.4, §5.2, §6.1–§6.2,
as quoted in `docs/section62-mb09-bidirected-graph-audit.md` and read directly
from the PMC full text on 2026-10-10.

The §6.2 feasibility object (Variant F of `docs/ml-formalization-contract.md`) is
encoded in `AssemblyP1/Section62BidirectedFlow.lean`: vertices are observed read
molecule classes (§3.1, §4.1), edges are all proper bidirected overlaps of length
`≥ o_min` (§3.3, §6.2), transitive edge reduction removes overlaps spelled by two
shorter overlaps (§6.2), each vertex has lower bound 1 (§6.2), edge lower bounds
are 0 and upper bounds infinite (§6.2), and the signed-incidence balance
`pos(f)(v) − neg(f)(v) = 0` holds after the supersource/supersink conversion
(§3.4, §6.2).

**The §6.1 objective has two displays (primary-source correction).** §6.1 first
writes the exact *global read-count multinomial* in the candidate's own length
`N(D)` with the constraint `∑ᵢ dᵢ = N(D)`, then states that this is not separable
and approximates it by the *product of per-class binomials* with the **external**
genome size `N` (known from experiment). §6.2's convex-flow algorithm optimizes
the **binomial approximation**, not the exact multinomial. Keeping these two
objectives distinct is part of correctness; the earlier draft conflated them.

## The new phenomenon at arbitrary overlap

At full overlap (`o_min = L − 1`) every edge overlap is exactly `L − 1`, so a
flow that visits `k` reads spells a genome of length exactly `k`: the length is
fixed by the throughput. At arbitrary `o_min ≤ L − 1` an edge may carry any
overlap length in `[o_min, L − 1]`, so a flow that visits `k` reads with overlap
lengths `o_1, …, o_k` spells a genome of length `∑ (L − o_j)`, which is **not**
determined by the throughput. For the *exact multinomial* objective the candidate
length `N` is therefore a variable and the comparison acquires a length factor.

## Candidate classes and maximality conditions

### Class 1: Variable-length exact multinomial (the §6.1 first display)

- **Candidates**: count vectors `d` with variable length `N` (flows, not
  necessarily spelled circuits or circular genomes). The §6.1 exact multinomial
  additionally requires `∑ᵢ dᵢ = N`; `varLengthCriterion` is stated without that
  constraint, so it is a criterion at the count-vector layer.
- **Truth**: admitted.
- **Likelihood**: exact multinomial `∏ᵢ (dᵢ/N)^(xᵢ)` (the §6.1 first display).
- **Length universe**: variable `N`.
- **Maximality condition** (`varLengthCriterion`): the truth is sample-uniformly
  maximal for this objective **iff** `∀ i ∈ supp A : Bᵢ·G ≤ Aᵢ·N` (the density
  bound). This is necessary and sufficient for the stated objective. At `N = G` it
  reduces to coordinatewise dominance (`fixedLengthRecovery`), recovering #260's
  Proposition 3.2. Under the genome constraint `∑ᵢ dᵢ = N`, summing the density
  bound forces equality, i.e. `B = (N/G)·A` (the rescaling class of Class 5).
- **Source status**: **project-defined objective**. This is the §6.1 *exact*
  multinomial, which §6.2 does **not** optimize. It is a well-defined and
  kernel-checked mathematical result, but it is not by itself a claim about the
  §6.2 algorithm's optimum.
- **Witnesses**: `stretch_beats` (AATATT beats AATT on `e_{AT}`), `dilution_witness`.

### Class 2: Fixed-external-`N` multinomial product (NOT the §6.1 binomial)

- **Candidates**: throughput vectors `B` (count vectors), external `N = G` fixed.
- **Truth**: admitted.
- **Likelihood**: the exact multinomial with a *common external* length `N = G`
  substituted for candidate and truth; after cancelling the candidate-independent
  `n!/∏xᵢ!` and the common `N⁻ⁿ` the comparison is `∏ᵢ Bᵢ^xⁱ ≤ ∏ᵢ Aᵢ^xⁱ`.
- **Length universe**: fixed `N = G`.
- **Maximality condition** (`flow_dominance_criterion`): the truth is
  sample-uniformly maximal for this product objective over a class of throughput
  vectors **iff** no candidate `B` in the class has `Bᵢ > Aᵢ` for some
  `i ∈ supp A` (coordinatewise dominance). Necessary and sufficient **for this
  product objective**.
- **Source status**: **project-defined, correctly labelled.** This product is
  **not** the §6.1 separable binomial: the binomial retains a per-class
  `(1 − dᵢ/N)^(n−xᵢ)` factor that does not cancel.
- **Refutation of the §6.1 binomial as coordinatewise** (kernel-checked):
  `binomial_not_coordinatewise` exhibits truth `A = (1, 2)`, candidate `B = (1, 1)`,
  external `N = 3`, sample `x = (2, 1)`, where `B ≤ A` coordinatewise yet the
  separable-binomial core `binomCore` satisfies `binomCore B x 3 = 8 > 4 =
  binomCore A x 3`. So coordinatewise dominance is **not sufficient** for the
  §6.1 binomial, and `flow_dominance_criterion` must not be cited as its criterion.

### Class 2′: The genuine §6.1 separable binomial (OPEN)

- **Candidates**: §6.2 feasible flows with throughput `B`, external `N = G`.
- **Truth**: admitted.
- **Likelihood**: §6.1 separable binomial
  `∏ᵢ C(n, xᵢ) (Bᵢ/N)^(xᵢ) (1 − Bᵢ/N)^(n−xᵢ)`.
- **Length universe**: fixed `N = G`.
- **Maximality condition**: **OPEN.** Coordinatewise dominance is necessary
  (concentrated samples) but not sufficient (`binomial_not_coordinatewise`). A
  necessary-and-sufficient condition at the count-vector layer is the
  homogeneous linear-log condition derived in the note below, but its
  specialization to the §6.2 feasible flow set (including vertex lower bound `1`
  and the non-spelled-flow phenomenon) is not established here.
- **Partial implication (count-vector layer).** Taking logarithms of the
  candidate/truth binomial ratio gives, for `uᵢ = log(Bᵢ/Aᵢ) ≤ 0` and
  `vᵢ = log((N−Bᵢ)/(N−Aᵢ)) ≥ 0`, the condition
  `n·∑ᵢ vᵢ + ∑ᵢ xᵢ (uᵢ − vᵢ) ≤ 0` for all supported `x` with `∑xᵢ = n`; by
  homogeneity the extremal samples `x = eᵢ` suffice, so the condition is
  `∀ i ∈ supp A : uᵢ + ∑_{j≠i} vⱼ ≤ 0`. This is *project-derived*, not a source
  fact, and is not claimed as the §6.2 flow-level criterion.
- **Flow-level refutation of maximality in a concrete instance**: the `AAATT`
  instance at `o_min = 1` has non-spelled flow maximizers that beat the truth
  (ratio `256/81`); see Class 4 and
  `AssemblyP1.Section62NonSpelledFlow` (`nonspelled_se62_flow_domain_countermodel`,
  `half_integral_strictly_better`), independently recomputed by
  `scripts/verify_issue261_general_bidirected_flow_ml.py` and
  `scripts/verify_se62_nonspelled_flow_domain.py`.

### Class 3: Integer flows vs half-integral relaxation

- **Candidates**: integer §6.2 flows vs half-integral (LP relaxation) flows.
- **Truth**: admitted.
- **Likelihood**: §6.1 separable binomial, fixed `N = G`.
- **Length universe**: fixed `N = G`.
- **Status**: **RESOLVED at the flow level** by `AssemblyP1.Section62NonSpelledFlow`
  (`half_integral_strictly_better`, kernel-checked): the integer flow constraint is
  binding. The new module contributes the exact arithmetic of the `AAA` factor:
  `d²(5−d)²` is `36` at `d = 2, 3` but `625/16` at `d = 5/2`, giving the ratio
  `625/576` (`half_integral_gap`, `half_integral_beats_integral`). This arithmetic
  alone is **not** a feasibility proof; the flow-level feasibility is the cited
  kernel-checked result.

### Class 4: Flows that do NOT spell one circular genome

- **Candidates**: §6.2 feasible flows that are not necessarily spelled by a
  single circular genome (non-spelled flows).
- **Truth**: admitted.
- **Likelihood**: §6.1 separable binomial, fixed `N = G`.
- **Length universe**: fixed `N = G`.
- **Maximality condition**: no tractable structural criterion is known. The
  `AAATT` instance at `o_min = 1` exhibits non-spelling flow maximizers that beat
  the truth (ratio `256/81`). `AssemblyP1.Section62NonSpelledFlow` kernel-checks
  the literal §6.2 feasibility of the truth and the competitors and that the
  maximizer set `{(2,1,1), (3,1,1)}` consists of non-sequence spectra.
- **Status**: **OPEN** at the level of a general criterion; the finite obstruction
  is kernel-checked. No necessary-and-sufficient condition is known.

### Class 5: Rescaling ties at variable length

- **Candidates**: count vectors with variable length.
- **Truth**: admitted.
- **Likelihood**: exact multinomial.
- **Length universe**: variable.
- **Maximality condition**: uniqueness of the normalized spectrum is
  **impossible** at variable length. The `k`-fold cover `S^k` has spectrum `k·A`
  and length `k·G`, so its normalized spectrum equals the truth's and it ties on
  every sample (`rescaling_tie`). No full-overlap analogue.

## Remaining-open matrix

| Axis | Status |
|---|---|
| Variable-length exact-multinomial criterion (§6.1 exact display) | **RESOLVED** (`varLengthCriterion`), project-defined objective |
| Fixed-external-`N` multinomial-product criterion | **RESOLVED** (`flow_dominance_criterion`), correctly labelled |
| Genuine §6.1 separable-binomial count-vector criterion | **OPEN** (`binomial_not_coordinatewise` rules out coordinatewise; linear-log form derived, not proved at flow level) |
| §6.1 binomial over the §6.2 feasible flow set | **OPEN** |
| Half-integral relaxation gap | **RESOLVED** (flow level: `Section62NonSpelledFlow`; arithmetic: `half_integral_gap`) |
| Rescaling ties at variable length | **RESOLVED** (`rescaling_tie`) |
| Non-spelled-flow maximality criterion | **OPEN** (finite obstruction kernel-checked) |
| Transitive reduction interaction with ML | **OPEN** |
| Orientation/RC class interaction | **OPEN** |
| Sample realizability at arbitrary overlap | **OPEN** |

## Artifacts

- `AssemblyP1/GeneralBidirectedFlowML.lean`: kernel-checked abstract theorems,
  including the §6.1-binomial counterexample `binomial_not_coordinatewise`.
- `scripts/verify_issue261_general_bidirected_flow_ml.py`: independent exact
  recomputation (all checks pass), including the binomial counterexample.
- `scratch261/Audit.lean`: axiom audit (only propext, Classical.choice, Quot.sound).
