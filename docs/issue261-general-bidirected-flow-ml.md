# Issue #261: ML maximality in general bidirected flow domains

Child of #255; extends #260 from full overlap to genuine MB09 §6.2 bidirected
overlap graphs at arbitrary `o_min ≤ L − 1`.

## Source audit

Primary source: Medvedev & Brudno, *Maximum Likelihood Genome Assembly*,
J. Comput. Biol. 16(8) (2009) 1101–1116 (PMC3154397), §3.1–§3.4, §5.2, §6.1–§6.2,
as quoted in `docs/section62-mb09-bidirected-graph-audit.md` and read directly
from the PMC full text on 2026-10-10.

A project implementation of parts of the §6.2 feasibility object (Variant F
of `docs/ml-formalization-contract.md`) is provided in
`AssemblyP1/Section62BidirectedFlow.lean`. **It is not yet an established
source-faithful equivalence**, owing to the reduction, throughput, terminal and
spelling-flow adapter gaps detailed below. In the intended historical model,
vertices are observed read
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

### Class 2′: Genuine §6.1 product-binomial likelihood (count-vector theorem derived; flow-level OPEN)

- **Source model**: The §6.1 approximation is the product of binomials over all
  read-molecule classes (including classes with observed count zero). Its
  *external* denominator `N=G` is fixed from the true genome. This does
  **not** impose candidate genome length `G`, nor does it bound an otherwise
  unbounded flow's throughput by itself.
- **Probability domain**: for each candidate throughput `d_j`, require
  `0 ≤ d_j ≤ N` before assigning a binomial probability. §6.2 graph edge
  capacities are infinite; the reconciliation of that graph domain with the
  binomial probability domain (restriction or extended cost) remains **OPEN**.
- **Exact factorization** (mathematical identity; Lean theorem **OPEN**):
  for the full class universe `T`, let `n=∑_{j∈T}x_j` and
  `K(d;x)=∏_{j∈T} d_j^{x_j}(N-d_j)^{n-x_j}`.
  For each `i∈T`, define
  `q_i(d)=d_i·∏_{j∈T,j≠i}(N-d_j)`.
  Then **`K(d;x)=∏_{i∈T}q_i(d)^{x_i}`** exactly, including
  integer endpoints with `0^0=1`. The omitted binomial coefficients and
  the common `N` powers do not depend on `d`.
- **Exactly fixed read count `n), observed support fixed**:
  take the set `I={i:x_i>0}` to be the *same* set of observed read types
  for all samples compared, put `m=|I|` and assume `n≥m≥1`.
  A supported observation has `x_i≥1` for each `i∈I`,
  `x_j=0` outside `I`, and total `n`.
  Let `P_A=∏_{i∈I}q_i(A)`, `P_B=∏_{i∈I}q_i(B)` and `t=n-m`.
  If the true spectrum has `q_i(A)>0` on `I`, **B never strictly beats A
  for any such observation iff**
  `∀i∈I: P_B·q_i(B)^t ≤ P_A·q_i(A)^t`.
  Proof: distribute one count to every `i∈I`, then concentrate the remaining
  `t` observations at the type with greatest `q_i(B)/q_i(A)`.
  If any candidate `q_i(B)=0`, its likelihood is zero for every
  positive-full-support observation, and these inequalities still hold.
  This is an exact `m`-check equivalence for a **fixed candidate B**;
  quantifying over a source-faithful feasible-flow universe is a further step.
- **Uniformly over every `n≥m)**: for a fixed candidate B, non-defeat is
  equivalent to `P_B=0` **or**
  `∀i∈I: q_i(B)≤q_i(A)`. Unlike the interior-only version,
  this correctly handles zero-likelihood candidate boundaries.
- **Neither direction of coordinatewise dominance on the original `d_i`
  is valid as a general binomial criterion**:
  `binomial_not_coordinatewise` shows it is **not sufficient**
  (`A=(1,2)`, `B=(1,1)`, `N=3`, `x=(2,1)`, core 8 versus 4).
  It is **not necessary** even for genuine circular spellings of different
  lengths: `S=ACA` has length 3 and molecule counts `A=(1,1,1)`
  on `{AA,AC,CA}` at read length 2; `D=ACAACA` has
  `B=(2,2,2)`. Under the fixed external `N=3`, the candidate/truth
  product-binomial ratio is `2^(−n)<1` for every nonempty observation
  on those classes, although every candidate throughput is greater.
  This is a **pairwise** counterexample, not a theorem that S globally
  maximizes likelihood over all admissible flows. A source-model Lean
  adapter for this example remains open.
- **Flow-level structural characterization (program, not yet a proof)**:
  For the *actual* source-faithful finite integer-flow fiber, the fixed-n
  criterion reduces sample-uniform ML to the `m` extreme observations.
  On a correctly bounded split-vertex flow representation, the negative
  log-binomial cost for each extreme is separable convex. Standard Graver
  optimality theory would then give a finite structural certificate via
  absence of a feasible improving Graver augmentation. The **bidirected
  flow-to-matrix**, transitive reduction, terminal treatment, probability
  boundaries and valid throughput adapter are **not formalized here**.
  Pure likelihood maximization must also be distinguished from the
  terminal-penalized algorithm's optimization problem.
- **Counterexample already formalized**: the `AAATT` instance at
  `o_min=1` has nonspelled optimizing flows that beat truth by `256/81`
  under the project's existing flow predicate; see Class 4. Its fidelity
  to every detail of the original reduced graph remains to be audited.

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
| Genuine §6.1 separable-binomial count-vector criterion | **Mathematically derived**: exact q-factorization; fixed-n extreme-sample iff and boundary-complete all-n iff. Lean general theorem **OPEN** |
| §6.1 binomial over the §6.2 feasible flow set | **OPEN** |
| Half-integral relaxation gap | **RESOLVED** (flow level: `Section62NonSpelledFlow`; arithmetic: `half_integral_gap`) |
| Rescaling ties at variable length | **RESOLVED** (`rescaling_tie`) |
| Non-spelled-flow maximality criterion | **OPEN** (finite obstruction kernel-checked) |
| Transitive reduction interaction with ML | **OPEN** |
| Orientation/RC class interaction | **OPEN** |
| Sample realizability at arbitrary overlap | **OPEN** |

## Source-faithfulness and remaining proof blockers (explicit)

The existing abstract count-vector theorems are useful and kernel-checked, but
**they do not, by themselves, solve the full MB09 §6.2 flow classification**.

1. **Transitive reduction.** `isReducibleB` requires both two-leg proper
   overlap lengths to be smaller than the direct overlap `l<L`, while imposing
   `l1+l2-L=l`; these inequalities cannot hold simultaneously. Hence the
   literal predicate cannot delete any proper overlap. The alternative
   `isReducibleLongerB` only checks that each leg is longer; it does *not*
   require equal spelled sequence, signed-endpoint compatibility, or even
   that both legs survive the overlap threshold. With `L=4`,
   `AAAC→ACCA→CAAA` using overlaps 2 and 2 spells `AAACCAAA`,
   whereas direct `AAAC→CAAA` at overlap 1 spells `AAACAAA`.
   Blindly reducing the latter edge changes the language of spelled molecules.
   Myers (2005) and the MB09 §6.2 citation require spelling-preserving
   transitive reduction, not either current approximation.
2. **Flow attached to spelling.** The project predicate `SpelledFeasible62`
   checks a spelling alongside a feasible flow, but does not prove equality
   `f = Spelling.flow sp` or `d = Spelling.visits sp`; the flow admissibility
   conjunct is checked against the unreduced edge graph even when the spelling
   checks a reduced graph. Do not infer that `d` is the spectrum of `sp`
   without the missing alignment theorem.
3. **Signed bidirected throughput.** The current `throughput` counts
   departures using the stored `sx` end of edges. A general bidirected
   traversal may use the reversed orientation; show its equality to the
   split-vertex visit count under all allowed traversals, or explicitly
   restrict the candidate domain.
4. **Terminal modeling.** The zero-terminal `Feasible62` circuit subdomain
   is not all augmented flows: MB09 uses expensive supersource/sink arcs
   rather than forbidding them. The *pure binomial ML* objective and the
   *binomial-plus-terminal-penalty* solver objective are different.
5. **Probability feasibility.** Original §6.2 edge upper bounds are
   infinite, but the §6.1 binomial is probabilistic only when `0≤d_i≤N`.
   An explicit restriction or extended-cost convention is required.
6. **Fixed observed support vs missing types.** The fixed-n extremal theorem
   varies read multiplicities while holding the set `I` of *observed types*
   and hence the constructed overlap graph fixed. Omitting a true-positive
   molecule changes that graph and may remove the truth's flow. It needs
   separate classification.
7. **Integer optimization adapter.** A useful future endpoint is a
   precise integer matrix for the faithfully reduced signed bidirected
   graph, explicit throughput and terminal variables, then a verified
   Graver augmentation optimality theorem for each fixed-support extreme
   sample. Any constraints requiring candidates to be spelled by a
   *single primitive genome* must be treated separately from all flows.

Source reading: [Medvedev–Brudno 2009, §§6.1–6.2](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/);
[Myers 2005 string-graph reduction](https://pubmed.ncbi.nlm.nih.gov/16204131/).

## Artifacts

- `AssemblyP1/GeneralBidirectedFlowML.lean`: kernel-checked abstract theorems,
  including the §6.1-binomial counterexample `binomial_not_coordinatewise`.
- `scripts/verify_issue261_general_bidirected_flow_ml.py`: independent exact
  recomputation (all checks pass), including the binomial counterexample.
- `scratch261/Audit.lean`: axiom audit (only propext, Classical.choice, Quot.sound).
