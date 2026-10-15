# AssemblyP1 umbrella #255 — research framework

_Status: 2026-10-14. Integration front (agent 4ba67d3247d8): child-issue
map refreshed against current board states, the exact landed scopes of
merged PRs #163/#165/#166/#167/#174/#179/#182/#193, the exact iid
finite-ML classification posted on the issue 2026-10-13, and the
population-to-finite bridge posted 2026-10-14. Coordination
front: agent 96b26e582cdf (rebased by agents 491a5de6e543, 3a1a51f8aef9,
and 4ba67d3247d8; superseded by this rebase onto `main` @ `157ad34`).
This document organizes the classification axes of the #255 research
program. It is a framework, not a result: every scoped claim below is
labeled with its epistemic class, and every unproved claim remains OPEN.
The companion status record is `docs/remaining-open-matrix-255.md`._

## 1. Core question

For a circular truth genome `S` of length `G`, read length `L`, and an
observed read multiset with counts `x`: **exactly when is `S` a finite-sample
maximum-likelihood (ML) maximizer?** Uniqueness of the maximizer is
secondary to maximality (the issue text freezes this order).

Two quantifier regimes must be kept separate; structure alone need not
decide (A):

- **(A) Fixed sample.** For one observed count vector `x`, decide whether
  the likelihood of the truth dominates (or ties) the likelihood of every
  admissible competing candidate.
- **(B) Every admissible sample.** Decide whether the truth dominates for
  EVERY admissible finite sample (sample-uniform maximality). This is a
  strictly stronger requirement; a criterion for (B) yields (A) by
  instantiation, not conversely.

## 2. Frozen classification axes

The program freezes six axes. A fully specified sub-problem is one cell of
this product; a classification is valid only inside its cell.

### Axis 1 — Molecule type: oriented vs reverse-complement (RC)

Reads as oriented `L`-mer strings versus reads as unoriented molecule
classes (each read string identified with its reverse complement). The
support sets, candidate universes, and likelihoods differ; results do not
transfer across the axis without proof.

### Axis 2 — Likelihood: exact multinomial vs fixed-N product-binomial

- **Exact multinomial (project-defined exact objective).** The joint
  read-count distribution under uniform sampling; kernel-checked landings
  use this objective.
- **Fixed-external-N product-binomial (MB09 §6.1).** The approximate
  pseudo-likelihood with per-type binomial marginals, including the extra
  `(1 − d(w)/N)^{n−x(w)}` factors, zero-count coordinates, and boundary
  probabilities 0/1. MB09 §6.1 motivates this replacement asymptotically;
  it licenses no finite-sample claim (see the primary-source record in the
  matrix).

### Axis 3 — Length: same-length vs variable-length

All candidate genomes of the same length `G` as the truth, versus a
candidate universe over multiple genome lengths.

### Axis 4 — Candidate domain: spelled genomes vs MB09 §6.2 bidirected flows, and the overlap floor

- **Spelled genomes.** Candidates are circular genomes whose read
  spectrum (or molecule-count vector) is compared to the truth's.
- **MB09 §6.2 bidirected flows.** Candidates are balanced circulations on a
  signed bidirected overlap graph, with an overlap floor `o_min ≤ L−1`.
  Full overlap (`o_min = L−1`) is a distinct, settled cell; arbitrary
  `o_min` is open. Sub-axes: transitive reduction, vertex lower bound 1,
  orientation/RC classes, integer vs half-integral flows, and flows that
  do not spell one circular genome.

### Axis 5 — Truth candidacy

Whether the truth itself is an admissible candidate in the domain under
consideration (e.g., does the truth's spectrum/flow satisfy the domain's
constraints?). Landed scopes prove truth candidacy inside their cells;
extended candidate sets must re-establish it.

### Axis 6 — Information predicate: literal historical read-string `I_s` vs project placement `I_s`

The historical Shomorony-style read-string matching predicate `I_s^match`
versus the project's placement-coverage predicate `I_s`. The #256 iff needs
no `I_s`; the literal historical reading's full-overlap bridging
sufficiency is refuted (W1/W2). Remaining historical-referent questions
stay OPEN.

## 3. Anchors (known, with scope)

- **Population maximality: PROVED (kernel-checked), unconditional for all
  circular genomes.** `population_maximizer_unrestricted`: the truth
  maximizes the exact population likelihood over ALL circular candidate
  genomes, with no repeat, P2, primitivity, bridging, or
  information-feasibility assumptions (merged PR #154; #273 CLOSED). Repeats bear only on
  *uniqueness*: `PopulationGibbs.truth_is_population_maximizer` gives
  equality iff normalized spectra agree, and the uniqueness refinement
  needs P2/primitivity conditions (#274 CLOSED). Population-level only;
  does NOT settle finite sampling.
- **Oriented same-length graph rigidity suffices: PROVED (kernel-checked).**
  Support-domain rigidity of the oriented `L`-mer circulation graph
  implies sample-uniform exact-ML maximality in that cell (#256).
- **Historical molecule-flow full-overlap bridging sufficiency:
  REFUTED.** Literal W1 (`AAATAT→AAAAAT`, exact ratio 3, binomial ratio
  5) and W2 (`ATATACAC→ATACACAC`, exact ratio 3/2, binomial ratio 9/5)
  refute the bridging claim at MB09 full-overlap §6.2 (merged PR #142, merge commit `49b2903`).
  This refutes a sufficiency claim only; it classifies no genome set or
  overlap floor.
- **#259 fixed-N product-binomial scoped landings: PROVED (kernel-checked),
  partial scope.** q factorization `∏ q_i(B)^{x_i}` (PR #163); all-count
  effectiveWeight coordinatewise iff over arbitrary nonnegative count
  vectors (PR #165); explicit strict integer witness (PR #166); positive
  same-support covered-sample iff for oriented spectra (PR #167). These do
  NOT settle the general §6.2 claim, #259(A), or #259(B) over the full
  candidate universe — see the matrix for exact scopes.
- **Exact iid finite-ML classification on the all-true-starts-sampled
  domain: PROVED (elementary), posted 2026-10-13, not kernel-checked.**
  Candidate `D` is never strictly better than truth for any full-start-covered
  finite sample IFF some true type has `q_j = 0` OR `q_i ≤ p_i` for every
  true type; same-support normalized forces `p = q`. Distinct from the
  §6.1 surrogate (which the same sample `AAATT`/`AAATA` separates:
  product-binomial ratio `65536/50625 > 1`, exact iid tie) and from the
  source-historical matched `I_s` domain. The fixed-`x` problem (A) remains
  halfspace inequalities; all broader conjectures remain OPEN.
- **Population-to-finite bridge (exact multinomial): PROVED (elementary),
  2026-10-14, not kernel-checked.** `∑_w x(w)·log p_D(w) =
  n·∑_w p̂(w)·log p_D(w)` with `p̂(w) = x(w)/n`; hence for fixed `x` the
  truth maximizes the exact finite-sample likelihood IFF it is the
  KL-projection `D_KL(p̂‖p_S) ≤ D_KL(p̂‖p_D)` for every candidate. A 2-type
  witness (`p_S=(1/2,1/2)`, `p_D=(1/4,3/4)`, `p̂=(1/4,3/4)`) separates
  population maximality (Gibbs) from finite-sample maximality. This is a
  unifying lens and a restatement of the fixed-`x` (A) comparison, not a
  classification; it closes no child and does not touch the §6.1 surrogate
  or §6.2 flows.

## 4. Child-issue map (states board-verified 2026-10-14; owners as last recorded)

| Issue | Cell / question | Regime | State | Owner |
|---|---|---|---|---|
| #256 | oriented, same-length, exact multinomial | (B) | CLOSED — kernel-checked iff landed | — |
| #257 | oriented read-graph rigidity criterion; Graver structural iff | structural | PARTIAL — `ExactRigidityCriterion.lean`, `GraverRigidity.lean` merged; broader taxonomy OPEN | agent 75fc272a3a01 |
| #258 | oriented, same-length, exact multinomial, fixed `x` | (A) | CLOSED — `FixedXExactML.lean` merged (PR #159) | — |
| #259 | MB09 §6.1 fixed-external-N product-binomial | (A)+(B) | PARTIAL — q factorization (#163), all-count effectiveWeight coordinatewise iff (#165), strict integer witness (#166), positive same-support covered-sample iff (#167) kernel-checked and merged; full-coverage surrogate classification claim posted 2026-10-13 (OPEN, not kernel-checked); full (A)/(B) classification OPEN | agent a569f93c31a7 |
| #260 | RC, full-overlap, exact multinomial, source-faithful equal-support | (B) | CLOSED — kernel-checked iff landed | — |
| #261 | general MB09 §6.2 bidirected flows, arbitrary `o_min` | (A)+(B) | OPEN — partial count-vector/exact-binomial results merged; kernel-checked spelled binomial counterexample with hidden window landed (PRs #179/#182); Observation-7 characterization active, not kernel-checked; general classification OPEN | agent 30239e162137 |
| #262 | full-overlap edge irreducibility; lift counterexamples to arbitrary overlap | structural | OPEN — active | agent b5fe60dfd915 |
| #263 | separable-convex discrete Graver optimality certificate | structural | OPEN — active | agent fbf2e43e7998 |
| #264 | integer-lattice Graver basis obstruction/decomposition | structural | CLOSED — kernel-checked | — |
| #265 | whitepaper/presentations: finite-read inference and ML guarantees thread | editorial | OPEN — PR #189 merged (theorem-level visibility); ML optimality framed as entrance per user hierarchy correction | agent fd6665d5acb6 |
| #266 | conditional identifiability from Not-So-Greedy information-feasibility | conditional inference | OPEN — conditional posterior structure posted 2026-10-13; Lean formalization active | agent 2318a363d938 |
| #267 | reconcile finite ML counterexamples with Bayes optimality / conditional feasibility | conditional inference | OPEN — three-facts reconciliation structure posted 2026-10-13; build on merged FiniteBayesDecision | agent d5f48efb876a |
| #268 | whitepaper: foreground Bayes-optimal ML and the 2016 comparison | editorial | OPEN — PR #189 redundancy check; coordinate #265 | agent ffd9d61d8644 |
| #269 | Lean: finite Bayes/MAP optimality; monotone prior-average success | conditional inference (kernel) | PARTIAL — generic MAP decision optimality (PR #174) and exact iid `n→n+1` MAP success monotonicity (PR #193) kernel-landed; assembly-specific orbit-pmf endpoint OPEN | agent 39611d5caebc |
| #270 | Lean: finite-read recovery bounds from population identifiability (Hellinger) | conditional inference (kernel) | OPEN — Bhattacharyya affinity certificate strategy posted 2026-10-13 | agent 1875e2e258f2 |
| #271 | compare exact boundaries of conditional Bayes and ordinary finite ML | conditional inference | OPEN — clean decision boundary posted 2026-10-13 | agent 2434b45008b9 |
| #272 | weakest side information for certain finite Bayesian recovery | conditional inference | PARTIAL — `certain_iff_proper` coloring theorem landed (PR #164); full classification OPEN | agent 1a88c454e30b |
| #273 | unconditional population ML maximizer for all circular genomes | population | CLOSED — `population_maximizer_unrestricted` merged (PR #154) | — |
| #274 | population likelihood support-inclusion semantics | population | CLOSED — merged (PR #156) | — |
| #276 | reframe paper around comparable information/recovery guarantees | editorial | CLOSED — delivered 2026-10-12 | — |

Adjacent (outside the #255 ML-classification core): #254 (programmers'
talk; merged, CLOSED on board 2026-10-14), #280 (signed-commit policy).

## 5. Epistemic policy

- Conjectures remain **OPEN** until proved or refuted to the issue's
  evidence standard (audited proof, direct Lean theorem where feasible,
  green CI/merge). No conjecture is promoted to fact by agreement or by
  surviving falsification attempts.
- Every scoped claim states its cell (Axes 1–6) and regime (A)/(B) before
  its epistemic class.
- The remaining-open matrix is updated only when a scoped claim is
  proved, refuted, or explicitly re-scoped with evidence.
- #255 closes only when every scoped claim in its child map is proved or
  refuted and the matrix matches the landed artifacts.

## 6. Coordination protocol

The umbrella coordination front (this agent) maintains this framework and
the matrix; it does not duplicate live child fronts. Child fronts own
their cells; the umbrella records their states, flags stale entries, and
ensures every OPEN cell has exactly one named owner. Re-scoping a cell
(merging, splitting, or closing a child) is recorded here with the
evidence link.
