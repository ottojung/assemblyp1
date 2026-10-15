# AssemblyP1 umbrella #255 — research framework

_Status: 2026-10-15. Integration front (agent e05c947b4ab8): child-issue
map refreshed against current board states and the exact landed scopes of
merged PRs through #234 (current `origin/main` @ `b4071f5`), superseding the
2026-10-14 refresh at `157ad34` (PR #196). Board states re-verified
2026-10-15 via `antonina board show`: #262, #266, #267, and #270 have since
CLOSED, and #281, #284, #300 are #255-relevant children not previously
listed here. The exact iid finite-ML classification posted on the issue
2026-10-13 and the population-to-finite bridge posted 2026-10-14 are
recorded with their scope. Coordination front: agent 96b26e582cdf (rebased
by agents 491a5de6e543, 3a1a51f8aef9, 4ba67d3247d8, and e05c947b4ab8).
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
  domain: PROVED (elementary), posted 2026-10-13, not kernel-checked as
  stated; a related envelope theorem is kernel-checked but scoped.**
  Candidate `D` is never strictly better than truth for any full-start-covered
  finite sample IFF some true type has `q_j = 0` OR `q_i ≤ p_i` for every
  true type; same-support normalized forces `p = q`. Distinct from the
  §6.1 surrogate (which the same sample `AAATT`/`AAATA` separates:
  product-binomial ratio `65536/50625 > 1`, exact iid tie) and from the
  source-historical matched `I_s` domain. The fixed-`x` problem (A) remains
  halfspace inequalities; all broader conjectures remain OPEN. A kernel
  partial artifact exists on main: `AssemblyP1/FiniteSampleIidEnvelope.lean`
  (`truth_maximizer_iff_envelope_le_one`, added via PR #172, merge `4d4970c`;
  compiled by the library glob but not imported by the root aggregator) states
  the MAP envelope iff for a fixed surplus total `m`, not the pointwise
  all-sample criterion above — see the matrix's exact-iid section.
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
- **Short finite-read ML counterexamples, variable length: PROVED
  (kernel-checked).** `AssemblyP1/ShortFiniteMLCounterexamples.lean`
  (PR #229, merged `67e1de7`, independently reviewed): in the variable-length
  exact ordered-read/multinomial model, truths `AT` (`G=2,L=1`), `AAT`
  (`G=3,L=2`), `AAAT` (`G=4,L=3`) each satisfy the full `InformationFeasible`
  predicate, while spelled competitors `AAT`, `AAAT`, `AAAAT` are strictly
  better with ratios `32/27`, `81/64`, `4096/3125`. The `L=1`/`L=2` witnesses
  have vacuous repeat clauses (`BridgesCopy` forces `e+2 ≤ L`). Board #300
  remains OPEN pending closure; this is a refutation of a sufficiency reading,
  not a classification.
- **#281 finite-read exponential error decay: PROVED (kernel-checked),
  scoped.** `NonmonotonicityWitness281.lean` (PR #208, exact-ML success is
  non-monotone in `n`), `PrimitiveP2FiniteClass.lean` (PR #214, finite
  primitive-P2 candidate class and `(L−1)`-window cap),
  `PrimitiveP2UniformSeparation.lean` (PR #234, uniform exponential exact-ML
  error bound for primitive-P2 genomes). Board #281 OPEN; the genome-level
  finite corollary and paper recentering remain.
- **#261 spelled-circuit to §6.2 feasible-flow adapters: PROVED
  (kernel-checked), scoped.** `Section62BinomialCriterion.lean` (PR #201),
  `Section62FlowCountVectorAdapter.lean` (PR #212), and
  `Section62SpelledFlowAdapter.lean` (PR #233) connect spelled circuits to
  §6.2 feasible flows. They do NOT classify the general §6.2 flow domain.
- **#271 conditional-Bayes vs ordinary finite-ML separation: PROVED
  (kernel-checked).** `ConditionalVsOrdinaryMLSeparation.lean` and
  `W1W2SeparationCompatibility.lean` (PR #232): the two recovery notions are
  logically incomparable; conditional certainty needs the truth-dependent
  event, and the W1/W2 (A)-side adapter stays open by design.
- **#269 orbit adapter and Bayes-value monotonicity: PROVED (kernel-checked).**
  `GenomeOrbitAdapter.lean` (PR #200: oriented orbit read pmf, normalization,
  rotation invariance, prior-on-orbits MAP success monotonicity) and
  `BayesValueMonotonicity.lean` (PR #231: `V_{n+1} ≥ V_n`). RC-orbit and
  source-historical endpoints are deliberately not claimed.

## 4. Child-issue map (board states re-verified 2026-10-15; owners as last recorded)

| Issue | Cell / question | Regime | State | Owner |
|---|---|---|---|---|
| #256 | oriented, same-length, exact multinomial | (B) | CLOSED — kernel-checked iff landed | — |
| #257 | oriented read-graph rigidity criterion; Graver structural iff; finite decider | structural | PARTIAL — `ExactRigidityCriterion.lean`, `GraverRigidity.lean`, `FiniteRigidityDecider.lean` (PR #209, merged `2fa1b93`) landed; broader read-graph taxonomy OPEN | — |
| #258 | oriented, same-length, exact multinomial, fixed `x` | (A) | CLOSED — `FixedXExactML.lean` merged (PR #159) | — |
| #259 | MB09 §6.1 fixed-external-N product-binomial | (A)+(B) | PARTIAL — q factorization (#163), all-count effectiveWeight coordinatewise iff (#165), strict integer witness (#166), positive same-support covered-sample iff (#167), covered-binomial weight iff (`CoveredBinomialWeightsIff.lean`, PR #211, merged `298682b`), circular binomial-vs-iid inversion (PR #224, merged `aedf1b9`) kernel-checked; full (A)/(B) classification OPEN | — |
| #260 | RC, full-overlap, exact multinomial, source-faithful equal-support | (B) | CLOSED — kernel-checked iff landed | — |
| #261 | general MB09 §6.2 bidirected flows, arbitrary `o_min` | (A)+(B) | OPEN — spelled binomial counterexample (#179/#182), binomial criterion (`Section62BinomialCriterion.lean`, PR #201), flow-count adapter (PR #212), spelled-circuit→§6.2 adapter (PR #233) landed; general classification OPEN | — |
| #262 | full-overlap edge irreducibility; lift counterexamples to arbitrary overlap | structural | CLOSED — `Section62FullOverlapLift.lean` (PR #202, merged `4492b65`); independent review `3e3657c` | — |
| #263 | separable-convex discrete Graver optimality certificate | structural | OPEN — active | — |
| #264 | integer-lattice Graver basis obstruction/decomposition | structural | CLOSED — kernel-checked | — |
| #265 | whitepaper/presentations: finite-read inference and ML guarantees thread | editorial | OPEN (delivered) — PR #189 visibility; scoped finite-family sample-complexity note (`docs/sample-complexity-265.md`, merge `069f64e`); rebalanced decks (`22a6233`); pending #254/#268 review | — |
| #266 | conditional identifiability from Not-So-Greedy information-feasibility | conditional inference | PARTIAL (board CLOSED) — `ConditionalIdentifiability.lean` (PR #198 merged `a3dd8a0`; PR #203 merged `235114d`) kernel-checked; residual instance/multiset-preserving NSG source adapter OPEN per author handoff | — |
| #267 | reconcile finite ML counterexamples with Bayes optimality / conditional feasibility | conditional inference | CLOSED — `MapDecisionExamples.lean` + 3 notes (merge `157ad34`), mechanical fixes (`6a4d9e9`), fail-closed audit (`5c8a103`); review commit `6a4d9e9` | — |
| #268 | whitepaper: foreground Bayes-optimal ML and the 2016 comparison | editorial | OPEN (delivered) — paper refocus (`e7e3d20`/`b47eb04`), MB09 verbatim fidelity check (merge `cac6347`); #265 mirror pending | — |
| #269 | Lean: finite Bayes/MAP optimality; monotone prior-average success | conditional inference (kernel) | OPEN — generic MAP (#174), iid `n→n+1` monotonicity (#193), oriented orbit adapter (`GenomeOrbitAdapter.lean`, PR #200), Bayes value `V_{n+1} ≥ V_n` (PR #231) kernel-landed; RC-orbit/source endpoint deliberately not claimed | — |
| #270 | Lean: finite-read recovery bounds from population identifiability (Hellinger) | conditional inference (kernel) | CLOSED — `FiniteReadRecovery*.lean` (PRs #199/#205/#207) merged; board CLOSED | — |
| #271 | compare conditional Bayes and ordinary finite ML | conditional inference | PARTIAL — separation and genome adapter landed; integration PR #274 proves ML-soundness is a SUFFICIENT (not necessary) refinement for conditional certainty to imply ordinary ML; the general source-defined implication remains OPEN | — |
| #272 | weakest side information for certain finite Bayesian recovery | conditional inference | PARTIAL — coloring and side-information order landed; integration PR #274 proves the source-property/truth-only weakest-promise iff; the fully read-dependent source promise family remains OPEN | — |
| #273 | unconditional population ML maximizer for all circular genomes | population | CLOSED — `population_maximizer_unrestricted` merged (PR #154) | — |
| #274 | population likelihood support-inclusion semantics | population | CLOSED — merged (PR #156) | — |
| #276 | reframe paper around comparable information/recovery guarantees | editorial | CLOSED — delivered 2026-10-12 | — |
| #281 | finite primitive-P2 candidate class, uniform exact-ML recovery and tightness | kernel/editorial | PARTIAL — finite class and uniform error bound landed; integration PR #274 proves the length cap is tight at K=1 for every alphabet q>=2; tightness for K>1 and remaining editorial integration OPEN | — |
| #284 | correct section-6.2 reduction; circular read-occurrence and RC observed-class fidelity | structural/source | PARTIAL — signed integration PR #274 kernel-proves ideal two-hop reduction iff, oriented circular read counts and observed RC molecule-class counts (including palindromes); full Myers practical algorithm, unobserved RC universe and general flow realization remain OPEN | — |
| #300 | Lean short finite-read ML counterexamples (true lengths 2,3,4) | (A)/variable-length | OPEN (needs closure) — `ShortFiniteMLCounterexamples.lean` (PR #229, merged `67e1de7`), independently reviewed | — |

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
