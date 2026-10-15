# AssemblyP1 umbrella #255 — remaining-open matrix

_Status: 2026-10-14. Integration front (agent 4ba67d3247d8; orchestrator
agent 4f59729f6003 for PR #196): rebased onto `main` @ `157ad34` (current
main head at integration time; merged PRs #193/#194 and #267) and
refreshed with the exact landed scopes of merged PRs #163/#165/#166/#167, the exact
iid finite-ML classification posted on the issue 2026-10-13, the
kernel-checked spelled binomial counterexample of PRs #179/#182, the finite
Bayes/MAP decision theorem of PR #174 plus the landed iid MAP monotonicity
of PR #193, the population-to-finite bridge observation, and current board
child-issue statuses (board-verified 2026-10-14 via `antonina board show`).
Observed integration range for audit: base `157ad34` = exact PR base at
integration time; the signed PR #196 head this line ships is recorded on the
PR page and in `git log`; observed 2026-10-14.
Coordination front: agent 96b26e582cdf (rebased by agents 491a5de6e543,
3a1a51f8aef9, and 4ba67d3247d8; superseded by this rebase).
This matrix is a proposed, reviewable status record for the #255 research
umbrella, not a declaration that the remaining proofs are finished. It is
updated only when a scoped claim is proved, refuted, or explicitly
re-scoped with evidence. Conjectures remain OPEN until proved or
refuted. The classification-axis organization lives in
`docs/research-framework-255.md`._

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

### #258 (CLOSED) — exact multinomial, oriented same-length, fixed observation `x` (A): PROVED certificate

- **Artifact:** `AssemblyP1/FixedXExactML.lean`
- **PR:** #159, merged `080b1b3829e015b6499486363167665c21a55bc1`
- **Statement:** `fixedX_classification_iff` is the exact product-inequality
  certificate over positive balanced, mass-`G`, truth-support spectra.
  `feasibleSpectrum_iff_258` exhausts the four possible AAABBB spectra;
  `fixedX_four_chamber_iff_258` gives all three exact integer-product chamber
  comparisons, with explicit unique-win, top-tie, and strict-loss samples.
  `feasibleSpectrum_realizable_258` constructs circular genomes for all four.
- **Verification:** all three exact-head CI workflows green (Lean compile,
  kernel replay, full axiom audit); independent check of all 64 binary
  length-six genomes via `scripts/verify_fixedx_258.py`.
- **Additional:** PR #161 merged as `a8200738db63001b299058b07600b39791a8c7e1`
  preserving `scripts/verify_feasible_spectrum_ml_255.py` (974 exact-rational
  (truth,sample) cases at G=5,6,L=2; 158 out-of-spelled-class
  higher-likelihood cases recorded).
- **Scope:** fixed-`x` same-length oriented spectra; not fixed-N
  product-binomial, RC molecule flows, variable genome length, or
  arbitrary-overlap graph reconstruction. Positive maximizer is over
  *spectra*, not unique genome strings when cyclic rotations tie.

### #264 (CLOSED) — integer-lattice Graver basis obstruction/decomposition

- **Artifact:** `AssemblyP1/GraverRigidity.lean`, imported and audited on main.
- **Proof:** conformal extraction of a Graver element by l1 strong induction;
  oriented fixed-support circulation rigidity iff absence of a feasible
  unit Graver augmentation, plus `graver_decomposition` for #263.
- **Not implied:** full finite-basis enumeration or convex optimization
  certificate in #263, still OPEN.

### #257 (PARTIAL) — support rigidity and Graver structural iff LANDED; broader taxonomy OPEN

- **Merged artifacts:** `AssemblyP1/ExactRigidityCriterion.lean`,
  `AssemblyP1/GraverRigidity.lean`, and `AssemblyP1/GraverRigidityAudit.lean`.
- **Graver theorem:** `rigid_iff_forall_graver_not_feasible` and the
  equivalent coordinate-box obstruction `rigid_iff_forall_graver_not_inbox`
  are proved in Lean for a finite oriented support-edge set, positive balanced
  **integer** circulations with **fixed total**. `graver_decomposition`
  supplies a conformal integer-kernel decomposition.
- **Still OPEN:** broader read-graph structural classification outside this
  positive, same-length, oriented integer-circulation universe; no transfer
  to general bidirected, half-integral, or arbitrary-overlap flow candidates;
  and no finite algorithm/test unless global Graver-set finiteness (Dickson/
  Gordan) is established.

### Population maximality: PROVED — unconditional for all circular genomes; repeats bear only on uniqueness

- **Unrestricted maximality (no repeat condition):**
  `AssemblyP1.PopulationUniqueness.population_maximizer_unrestricted`: for any
  true circular genome `S` and any candidate `D` under the exact population
  objective, `ell_S(D) ≤ ell_S(S)` (Gibbs/KL inequality); no P2, primitivity,
  bridging, information-feasibility, or no-repeat assumptions; no fixed
  candidate length. Tie iff distributions agree
  (`population_tie_iff_distribution_eq_unrestricted`, plus the
  periodic-read-distribution and periodic-population-likelihood tie
  corollaries). (#273 CLOSED; PR #154, merged `60821ac`, stacked on PR #158
  base `d3b7fb3` which included the merged #156 support-inclusion repair;
  exact-head CI all green before merge — Lean build, Documents, Slides and
  Pages; kernel replay under the corrected `PopLogLik` prints axioms
  `{propext, Classical.choice, Quot.sound}` for all four endpoints.)
- **Uniqueness is repeat-dependent:** `PopulationGibbs.truth_is_population_maximizer`;
  equality iff normalized spectra agree; the uniqueness refinement needs
  P2/primitivity conditions. (#274 CLOSED: support-inclusion semantics fixed,
  merged PR #156.)
- Population-level only; does NOT settle finite sampling.

### #269 partial foundation — finite Bayes/MAP decision optimality: LANDED (issue still OPEN)

- **Artifact:** `AssemblyP1/FiniteBayesDecision.lean`
- **PR:** #174, merged `950ea4f`. The board issue #269 remains **OPEN**: only the
  generic foundation landed; the assembly-specific endpoint is unresolved
  (see the #269 section below).
- **Statement:** `chooseMAP_optimal` (finite MAP maximizes zero-one prior-averaged
  decision success over a finite candidate family), randomized-policy
  dominance, and marginal-refinement monotonicity (`chooseMAP_success_monotone_under_refinement`).
- **Scope:** generic finite-decision Bayes/MAP optimality only. It is the
  entrance/rationale for likelihood study, NOT an assembly-specific
  recovery theorem, and does NOT settle #269's assembly-specific endpoint
  (genome-orbit prior, exact iid read model, `n→n+1` normalization bridge),
  #266, #267, or #270. The paper's core contribution remains the
  assembly-specific classification, not ML-optimality supremacy (user
  hierarchy correction recorded on #265/#268, 2026-10-13).

### Spelled binomial counterexample with hidden window (PRs #179/#182): LANDED

- **Artifacts:** `AssemblyP1/Section62NonSpelledFlow.lean` and
  `docs/spelled-binomial-counterexample-261.md`
- **PRs:** #179 merged `a849ea0` (research note), #182 merged `95bc479`
  (kernel certificates).
- **Statement:** for truth `S=AAATT` (`G=5`, `L=3`), observed starts
  `{0,0,1,4}` (molecule counts `x={AAA:2,AAT:1,TAA:1}`), the spelled
  candidate `D=AAATA` has FULL molecule spectrum `d_D={AAA:2,AAT:1,ATA:1,TAA:1}`
  where `ATA` is an unobserved graph vertex. Kernel-checked:
  `spelledCandidate261_binomial_ratio` / `spelledCandidate261_binomial_better`
  (fixed-N product-binomial candidate/truth ratio `65536/50625 > 1`),
  `spelledCandidate261_iid_tie` (exact iid multinomial ratio exactly `1` on
  the same sample), `spelled_candidate_reversal_with_bridging`,
  `spelledCandidate261_circuit_edges_survive`, and
  `spelledCandidate261_circuit_signed`.
- **Significance:** a same-length source-style finite SAMPLE where bridged
  truth loses under the MB09 §6.1 product-binomial surrogate while the exact
  iid objective ties — the cleanest landed illustration that the surrogate
  and the exact objective are distinct models. NOT a counterexample to the
  positive R7 slice (candidates whose complete window spectrum is supported
  on observed vertices); the general §6.2 flow classification remains OPEN.

### #259 (PARTIAL) — fixed-N product-binomial effective weights and witnesses: LANDED

- **Effective weights / q factorization (PR #163, merged `386c470`):**
  `AssemblyP1/FixedNBinomialEffectiveWeights.lean` — `product_factor` and
  `effectiveProduct_eq_binomialNumerator` prove the candidate-dependent
  integer numerator of the product-binomial objective is exactly
  `∏ q_i(B)^{x_i}` with `q_i(B) = B_i ∏_{j≠i} (N−B_j)` (the effective
  weight), over `ℕ` including zero counts with the `0^0 = 1` convention.
  `binomialNumerator_le_iff_effectiveProduct_le` connects numerator order
  to score order.
- **All-count effectiveWeight coordinatewise iff (PR #165, merged `908754f`):**
  `all_observations_order_iff_pointwise` and
  `every_observation_effectiveProduct_le_iff` give the exact criterion:
  `(∀ x : E → ℕ, effectiveProduct N B x ≤ effectiveProduct N A x) ↔
  ∀ i, effectiveWeight N B i ≤ effectiveWeight N A i`, over ALL nonnegative
  observation count vectors on one fixed modeled read-type universe.
- **Constructive strict witness (PR #166, merged `ec52da3`):**
  `AssemblyP1/FixedNConstructiveWitness.lean` — explicit integer
  `(A, B, G, N, x)` with `T = Σ B_i(N−B_i)`, `n = NT`,
  `x_i = B_i(T + (N−G)(N−B_i))`, `sum x = n`, `0 < x_i < n`, strict
  log-ratio `logScore(A;x) − logScore(B;x) < 0`, and `G·x_i ≥ A_i`
  (type-count coverage budget). No KKT necessity asserted.
- **Positive same-support covered-sample iff (PR #167, merged `9002ef6`):**
  `AssemblyP1/FiniteStartCoverage.lean` — `coverage_of_type_budget`
  constructively realizes any type-wise budget exceeding true start
  multiplicities as a start-covering sample;
  `uniform_covered_maximizer_iff_spectrum_rigid` and
  `uniform_normalized_score_iff_rigidity` prove: for oriented positive
  same-support interior read-type spectra of total `G` with `G ≤ N`, truth
  maximizes the fixed-N product-binomial (normalized) score for EVERY
  start-covered sample iff the candidate class has no spectrum distinct
  from truth.
- **Exact scope — NOT covered:** these results do NOT establish the general
  §6.2 bidirected-flow claim, the #259(A) fixed-`x` classification, or the
  #259(B) sample-uniform iff over the full candidate universe (arbitrary
  bidirected flows, RC molecule classes, or variable genome length). The
  q factorization is an algebraic identity for the §6.1 surrogate
  pseudo-likelihood; the coordinatewise iff ranges over arbitrary
  nonnegative count vectors without genome-start coverage; the
  covered-sample iff is scoped to oriented positive same-support spectra.
- **Status:** These are scoped partial results. The full #259(A) fixed-x
  classification and #259(B) sample-uniform iff for the product-binomial
  remain OPEN; no complete classification is claimed.
- **Axioms:** `{propext, Classical.choice, Quot.sound}` (kernel-checked).

### #272 (PARTIAL) — finite side-information coloring: LANDED

- **Artifact:** `AssemblyP1/FiniteSideInformationColoring.lean` +
  `AssemblyP1/FiniteSideInformationColoringAudit.lean`
- **Results:** `certain_iff_proper` (truthful deterministic side label
  achieves pointwise certainty iff it is a proper coloring of the
  confusability graph); four-candidate two-observation model with two
  incomparable minimum-cardinality two-label side channels
  (`labelA_certain`, `labelB_certain`, `labelA_not_refines_labelB`,
  `labelB_not_refines_labelA`, `no_common_coarsest`).
- **Status:** Support-only abstraction; the bridge to a specific genome
  assembly reconstruction theorem supplying the auxiliary label is OPEN.
- **Axioms:** `{propext, Classical.choice, Quot.sound}` (kernel-checked).

### Section 62 (PARTIAL) — spelling-preserving reduction candidate: LANDED

- **Artifacts:** `AssemblyP1/Section62SpellingReductionCandidate.lean`,
  `AssemblyP1/Section62GlobalSpellingPreservation.lean`,
  `AssemblyP1/Section62ReductionVacuityAudit.lean`
- **Results:** `spellDirect_length`, `spellPath_length`,
  `spellDirect_full_overlap`, `spellPath_eq_spellDirect`,
  `fullOverlap_not_reducible`, `fullOverlap_survives`,
  `replacement_overlaps_longer`, `regression_rc_involution`.
- **Status:** Partial spelling-preserving overlap-reduction candidate;
  NOT a source-faithful proof of Myers transitive reduction. Equivalence
  to the cited algorithm, bidirected reverse-complement semantics,
  global walk-language preservation, and Observation 7 remain OPEN.
  Does NOT lift any §6.2 genome flow witness or likelihood inequality.

---

## Mathematical proofs (human-readable; NOT kernel-checked, NOT merged)

### Exact iid finite-ML classification on the all-true-starts-sampled domain: PROVED (elementary), posted 2026-10-13

- **Source:** Antonina #255 board comment, research-assistant @
  2026-10-13T23:07:10.986Z. Epistemic class: mathematical proof
  (finite products + power-unboundedness). Kernel-check feasible but NOT
  yet performed; not merged to main.
- **Setting:** truth oriented spectrum `A` on support `T = {i : A_i > 0}`,
  true pmf `p_i = A_i/|S| > 0`; candidate genome `D` with exact iid pmf
  `q_i = spec_L(D)_i/|D|`. Admissible full-start-covered observed count
  vectors are exactly `x_i ≥ A_i` for `i ∈ T` and `x_j = 0` for `j ∉ T`
  (realizable: sample each true start once, then arbitrary extra copies at
  a representative start of each type).
- **Statement (necessary and sufficient):** candidate `D` is never strictly
  better than truth `S` for ANY such finite sample IFF
  **[∃ j ∈ T: q_j = 0]** (D's exact likelihood is identically 0) **OR
  [q_i ≤ p_i for EVERY i ∈ T]**.
- **Proof:** Sufficiency is a product inequality over observed types; the
  zero-support case is immediate. For necessity, assume `q_i > 0` for all
  `i ∈ T` and `q_i > p_i` for some type `i`; take `x = A + k·δ_i`. The
  candidate/truth likelihood ratio
  `R_k = (∏_{j∈T} (q_j/p_j)^{A_j})·(q_i/p_i)^k → ∞`, giving a strict
  finite-sample counterexample with complete true-start coverage. All
  multinomial coefficients cancel for fixed `x`.
- **Same-support normalized corollary:** with candidate/truth SAME
  probability support and no extras, `q_i ≤ p_i` for all `i` together with
  normalization (both sums 1) forces `p = q`: exact ML is universally
  maximal on this all-covered domain IFF normalized-spectrum
  IDENTIFIABILITY holds (ties possible). With candidate extra unobserved
  read types, strict `q_i < p_i` for all true types is possible, so
  spectral-rigidity necessity does NOT hold unrestrictedly.
- **Explicit distinctions (required, recorded 2026-10-13):**
  1. **Objective:** exact iid multinomial — NOT the MB09 §6.1 fixed-N
     product-binomial surrogate of #259. The landed `S=AAATT` vs `D=AAATA`
     witness shows the models diverge on one and the same sample
     (product-binomial ratio `65536/50625 > 1`, exact iid ratio exactly `1`;
     see PRs #179/#182 above).
  2. **Domain:** all-true-starts-sampled (full-start coverage) — NOT the
     source-historical matched read-string `I_s` domain. No claim is made
     that all `I_s`-admissible samples equal full-start-covered samples.
  3. **Regime:** a (B)-flavored statement at a precisely stated stronger
     cover domain. The FIXED-`x` problem (A) remains a set of candidate-score
     halfspace inequalities; this result does not classify (A).
- **Parallel claim for the §6.1 surrogate (OPEN, not kernel-checked):**
  posted on #259 2026-10-13T23:28:50Z — for full-coverage samples
  `x = A + y`, `y ≥ 0` on `supp(A)`, with surrogate effective weights
  `a_i = q_i(A)`, `b_i = q_i(B)`: `∀ y, F_B(A+y) ≤ F_A(A+y)` IFF
  `[∃ i ∈ S: b_i = 0] OR [∀ i ∈ S: b_i ≤ a_i]`. Structurally identical to
  the exact iid theorem but for the pseudo-likelihood; not proved in Lean,
  and not a general §6.2 flow result. The same post records that the
  `AAATT` fixed-x witness branch (agent a569f93c31a7) duplicates the merged
  PR #182 counterexample — no independent new #259 classification.
- **Status:** recorded as a landed elementary mathematical proof with
  explicit scope. It does NOT close #255, #259, or any child issue; all
  broader conjectures remain OPEN.

### Population-to-finite bridge (exact multinomial): PROVED (elementary), note posted 2026-10-14

- **Source:** `docs/population-finite-gap-255.md` (agent 91e0bcccb63a,
  reviewed and scoped by agent 4ba67d3247d8). Epistemic class: mathematical
  observation (finite sums + Gibbs inequality). Kernel-check feasible but NOT
  performed; the proposed `AssemblyP1/PopulationFiniteGap.lean` draft is
  **not landed** (it does not currently compile) and is explicitly not
  claimed here.
- **Setting:** a fixed finite read-type universe `W`, exact multinomial
  objective for one observed count vector `x` with total `n = ∑_w x(w) > 0`,
  empirical distribution `p̂(w) = x(w)/n`, truth read distribution `p_S`,
  candidate read distribution `p_D` (both positive on `W`).
- **Bridge identity (elementary):** `∑_w x(w)·log p_D(w) =
  n·∑_w p̂(w)·log p_D(w)`. The candidate-independent multinomial coefficient
  is dropped. Hence for fixed `x` the truth maximizes the exact finite-sample
  log-likelihood over candidates IFF `D_KL(p̂ ‖ p_S) ≤ D_KL(p̂ ‖ p_D)` for
  every candidate `D` — i.e. the truth is the KL-projection of the empirical
  distribution onto the candidate set.
- **Separation:** population maximality (Gibbs, PROVED above) does NOT imply
  finite-sample maximality. Witness: `p_S = (1/2,1/2)`, `p_D = (1/4,3/4)`,
  `p̂ = (1/4,3/4)` (`n = 4`): population `ℓpop_S(S) = log(1/2) ≈ −0.693 >
  ℓpop_S(D) ≈ −0.837`, but empirical `∑ p̂ log p_D ≈ −0.562 > ∑ p̂ log p_S =
  log(1/2)`. The gap is between the true distribution (population) and the
  empirical distribution (finite sample); the #274 support-inclusion repair
  does not change it.
- **Honest scope:** the "KL-projection condition" is a *restatement* of the
  fixed-`x` comparison, not a classification: it is exactly the (A)-regime
  halfspace-inequality condition already recorded for #258/#259(A). It
  provides a unifying lens (finite ML = empirical-population ML) and explains
  why the (B)-regime conditions of #256/#167 are needed; it does NOT classify
  (A) or (B), does not touch the §6.1 surrogate or §6.2 flows, and closes no
  child issue. The `n → ∞` law-of-large-numbers closure of the gap is
  standard and is not claimed as a new result.

---

## REFUTED — specific conjectures, NOT classifications

### Historical molecule-flow full-overlap BRIDGING SUFFICIENCY: REFUTED

- Merged PR #142 (merge commit `49b2903`, merged 2026-10-10) literal Shomorony §6.4 W1/W2 strict exact/binomial
  counterexamples at MB09 full-overlap §6.2.
- **W1:** `S=AAATAT`, `D=AAAAAT` (`G=6`, `L=3`): exact ratio 3, binomial ratio 5.
- **W2:** `S=ATATACAC`, `D=ATACACAC` (`G=8`, `L=3`): exact ratio 3/2, binomial ratio 9/5.
- This refutes a sufficiency claim only; it does not classify any genome set or
  overlap floor.

### #259 recovered WIP's fixed-x iff continuous KKT: FALSE for integer flows

- **Witness:** `S=AAABBB`, `G=N=6`, `x=[3,1,2,1]`.
- Continuous KKT optimality is **sufficient**, but **NOT necessary**, for
  maximizing a differentiable concave likelihood over a discrete
  integer-feasible subset of its continuous convex relaxation. The stated
  AAABBB discrete winner violates stationarity on a feasible real direction,
  so necessity fails.
- **Status:** REFUTED as a classification criterion. The exact integer witness
  is recorded on the issue board.

---

## OPEN — explicitly unresolved

### #259 (MB09 §6.1 fixed-external-N product-binomial)

- **(A)** at fixed `x` and **(B)** for every realizable complete-support `x`.
- **Owner:** agent a569f93c31a7 (active since 2026-10-13T22:05); prior
  owners agent c1ffc5ad4930 and agent 8270b79a96d7 (failed with an upstream
  endpoint outage).
- **Status:** PARTIAL results landed (see LANDED above); full (A)/(B) classification OPEN.
- **Landed (PRs #163 `#386c470`, #165 `#908754f`, #166 `#ec52da3`, #167
  `#9002ef6`, merged 2026-10-11/12):** q factorization
  (`∏ q_i(B)^{x_i}`); all-count effectiveWeight coordinatewise iff; explicit
  strict integer witness; start-coverage realization; positive same-support
  covered-sample iff — all kernel-checked in
  `FixedNBinomialEffectiveWeights.lean`, `FixedNConstructiveWitness.lean`,
  `FiniteStartCoverage.lean`.
- **New claim (OPEN, not kernel-checked; posted 2026-10-13T23:28:50Z):**
  full-coverage zero/new-support classification for the surrogate —
  `∀ y ≥ 0` on `supp(A)`, `F_B(A+y) ≤ F_A(A+y)` IFF
  `[∃ i ∈ S: b_i = 0] OR [∀ i ∈ S: b_i ≤ a_i]` with `a_i = q_i(A)`,
  `b_i = q_i(B)`. The exact iid analogue is PROVED (see the mathematical
  proofs section above); the surrogate version awaits kernel-checking. A
  concurrent interior equal-support necessity route (auxiliary comparison
  at `x = B`, strict Bernoulli maximizer) was posted 2026-10-13T22:22Z and
  likewise remains OPEN.
- **Dedup audit (2026-10-13T23:26Z):** agent a569f93c31a7's branch
  `agent/a569f93c31a7-issue259-binomial-maximality` (head `1b7e6ee`,
  `FixedNBinomialAAATTClassification.lean`) reproduces the EXACT merged PR
  #182 witness (`S=AAATT`, `n=4`, ratio `65536/50625`); no independent new
  #259 classification, no PR created, branch preserved remotely only.
- **Still OPEN:** the complete #259(A) fixed-x classification and #259(B)
  sample-uniform iff for the product-binomial over the full candidate
  universe (including arbitrary bidirected flows, RC molecules, and
  variable genome length). The landed covered-sample iff does NOT prove the
  general §6.2 claim.
- **Note:** The recovered WIP's continuous KKT iff is FALSE (see REFUTED above).
- **Primary-source record (MB09 §6.1, page 11):** the original Medvedev–Brudno
  2009 PDF literally states: "However, as the number of trials goes to
  infinity, the X_i random variables become independent." (verified directly
  against <https://www.cs.toronto.edu/~brudno/medvedev_MLA.pdf>, page 11,
  §6.1). The sentence licenses NO finite-sample claim: for fixed category
  probabilities, `Cov(X_i,X_j) = −n·p_i·p_j` and the standardized correlation
  is independent of `n`; only normalized frequencies decorrelate as `n→∞`.
  The product-of-binomials objective is a deliberate approximate
  pseudo-likelihood, not the exact joint likelihood. #259 (A)/(B) remains OPEN.

### #261 (general MB09 §6.2 bidirected flows at arbitrary `o_min ≤ L−1`)

- **Owner:** agent 30239e162137 (since 2026-10-12T02:49); Observation-7
  front active under agent 569edc7b2026 (since 2026-10-13T21:11).
- **Partial (merged):** `AssemblyP1/GeneralBidirectedFlowML.lean` carries
  count-vector and exact-binomial partial results (`varLengthCriterion`,
  `dilution`, `fixedLengthRecovery`, `densityDominance`,
  `flow_dominance_criterion`, `binomial_not_coordinatewise`,
  `half_integral_gap`, stretch/dilution witnesses), integrated at `02406aa`.
- **Landed (PRs #179 `#a849ea0`, #182 `#95bc479`):** kernel-checked spelled
  binomial counterexample with hidden window (`Section62NonSpelledFlow.lean`,
  `docs/spelled-binomial-counterexample-261.md`): `S=AAATT` vs spelled
  `D=AAATA`, product-binomial ratio `65536/50625 > 1`, exact iid tie,
  surviving reduced circuit edges, signed seams. Scoped to one concrete
  same-length witness; NOT a general flow classification.
- **Active (not kernel-checked):** Observation-7 characterization — exact
  cyclic-start partition identity `C_D(c) = V(c) + Σ` skipped-internal-window
  indicators, so observed-vertex count equality holds IFF every skipped
  internal window class is unobserved; a proof strategy that surviving
  reduced edges skip no observed read class (two-hop detour contradiction
  via `isReducibleSpellingB`) was posted 2026-10-13T21:05Z and remains a
  strategy, not a theorem. An earlier total-mass obstruction was corrected
  (2026-10-13T20:00Z): it requires the graph vertices to cover ALL
  genomic L-window classes, which §6.2 observed read vertices need not.
- **OPEN sub-axes:** arbitrary overlap floor, transitive reduction, vertex
  lower bound 1, orientation/RC classes, integer vs half-integral flows,
  flows not spelling one circular genome, candidate-set choice, truth
  admissibility, likelihood (exact vs fixed-N binomial), length universe.
- **Status:** OPEN, explicitly unresolved. General §6.2 bidirected flow
  classification remains OPEN.

### #262 (full-overlap edge irreducibility; lift counterexamples to arbitrary overlap)

- **Owner:** agent b5fe60dfd915 (since 2026-10-12T02:49).
- **Distinction:** Full-overlap edge irreducibility must be distinguished from
  conditional source-faithful flow transfer.
- **Status:** OPEN. Lean formalization of the embedding/lift in progress.

### #263 (separable convex discrete Graver criterion)

- **Owner:** agent fbf2e43e7998 (since 2026-10-12T02:57).
- **Status:** OPEN. Separable convex discrete Graver superadditivity over an
  integer affine fiber with box constraints; conditional on the #264
  conformal decomposition. Connects #257 rigidity certificates to
  #259/#261 likelihood maximizers; must not duplicate the #257 integer-kernel
  proof or the #261 likelihood analysis.

### #265 (whitepaper/presentations: finite-read inference and ML guarantees)

- **Owner:** agent fd6665d5acb6 (since 2026-10-12T02:45); active
  continuation agent 8edd83345a62 (since 2026-10-13T23:23).
- **Status:** OPEN. Editorial integration: make the statistical
  interpretation of genome reconstruction a central organizing thread of the
  whitepaper and presentations. Coordinates with #254, #255, #247, #269/#270.
- **Update (2026-10-13):** PR #189 (`9ca5c8f`) merged — paper now gives
  theorem-level visibility to MAP/ML correctness motivation, Graver
  rigidity iff, effective-weight all-count iff, and signed graph
  spelling preservation/mismatch. User hierarchy correction recorded:
  Bayes-optimal ML is the ENTRANCE/rationale, NOT the overarching result;
  the paper's core is the assembly-specific classification, positive
  rigidity, negative finite witnesses, and population identifiability.
  Reconcile #265/#268 against the current paper before closing either.

### #266 (conditional identifiability from Not-So-Greedy information-feasibility)

- **Owner:** agent 2318a363d938 (since 2026-10-12T02:45); active
  continuation agent 24528d33253c (since 2026-10-13T23:23).
- **Status:** OPEN. Prove what conditioning on `F(g,r)` implies: (1)
  uniqueness of the feasible fibre given fixed observed `r`; (2) conditional
  recovery `P([G]=[A(r)] | R=r, E) = 1` under any positive prior and any
  valid generative finite-read likelihood. Exact source-faithful
  read-STRING definitions; not an ordinary-ML-uniqueness claim.
- **Update (2026-10-13):** conditional-posterior structure posted —
  conditioning on truth-dependent `E(g,r)` restricts posterior support to
  `{g : π(g)P(r|g) > 0 ∧ E(g,r)}`; a Not-So-Greedy deterministic
  reconstruction guarantee for every feasible `g` forces this set to one
  genome orbit, giving conditional posterior 1. This is a conditional
  theorem, NOT unconditional sample-wise ML maximality; the `E` predicate
  must be the literal 2016 matched-string predicate, with the adapter
  explicit.
- **Update (2026-10-14):** PR #198 merged as `a3dd8a0` adds
  `AssemblyP1/ConditionalIdentifiability.lean` (abstract decoder/feasible-
  fibre, conditional posterior, constrained MAP, no-better-rule corollary,
  latent-placement weighted-mass adapter, historically scoped endpoint) plus
  `docs/issue266-conditional-identifiability.md`, the ledger row, and this
  entry. The previously OPEN read-instance gap is closed: the 2016 manuscript
  explicitly deduplicates read instances before assembly (§3.2, p. 12), and
  the new §7 adapter (`exists_finset_decoder`, `nsg_instance_iff_finset`,
  `historicalEvent_dedup`, `historical_feasible_fibre_unique_of_instance_decoder`)
  is kernel-checked; `SourceRegime` makes the `2 ≤ L ≤ S.len` regime explicit.
  The external `hNSG` guarantee remains the trust boundary (the algorithm is
  not formalized).

### #267 (reconcile finite ML counterexamples with Bayes optimality and conditional feasibility)

- **Owner:** agent d5f48efb876a (since 2026-10-12T02:45); active
  continuation agent bb09fddb7948 (since 2026-10-13T23:12).
- **Status:** OPEN. Rigorous source-faithful comparison of (a)
  Not-So-Greedy's guarantee, (b) exact finite-sample ML failures, (c)
  Bayes/MAP optimality. Cover finite-candidate Bayes/MAP optimality,
  conditioning on the event `E`, and small rigorous examples.
- **Update (2026-10-13):** three-facts reconciliation structure posted —
  (1) unconditional MAP maximizes prior-average success but can be wrong
  on individual `x`; (2) ordinary finite ML can rank a nonfeasible
  competitor above truth; (3) conditional posterior given `E` is supported
  only on feasible positive-weight hypotheses. Explicit finite toy
  (`p_g=0.1`, `p_h=0.2`, `E(g,x)=true`, `E(h,x)=false`) separates the
  regimes. Build on merged `FiniteBayesDecision.lean`; do not repeat the
  generic MAP proof.

### #268 (whitepaper: foreground Bayes-optimal ML and the nontrivial 2016 comparison)

- **Owner:** agent ffd9d61d8644 (since 2026-10-12T02:57); active
  continuation agent 7a974f0a0947 (since 2026-10-13T23:12).
- **Status:** OPEN. Editorial; compare with #265/#266/#267/#276.
- **Update (2026-10-13):** PR #189 already foregrounds ML/MAP optimality
  as entrance; if remaining work is redundant to PR #189, report
  redundancy and propose only concrete remaining edits. Close only after
  current paper, slides/claims matrix, and bibliography acceptance are
  confirmed and all missing parts landed.

### #269 (Lean: finite Bayes/MAP optimality and monotone prior-average success)

- **Owner:** agent 39611d5caebc (active since 2026-10-14T03:16); earlier
  fronts agent cc005eba36e4 (from 2026-10-12) and continuation agent
  5b4c0d4fd983 (2026-10-13, landed PR #193).
- **Status:** OPEN. Kernel-check that MAP maximizes prior-averaged success
  against every policy for every `n` (incl. `n=0` and tie handling) over a
  finite candidate family; connect to a concrete AssemblyP1 read model.
  Prior attempt failed on an infinite genome type; `Finset.exists_max_image`
  is the confirmed Lean 4.34 API for the maximizing witness.
- **Update (2026-10-13):** the generic core is LANDED (PR #174,
  `FiniteBayesDecision.lean`, see LANDED above).
- **Update (2026-10-14):** the `n→n+1` normalization bridge is LANDED.
  PR #193 (merged `6d28a41`) adds `AssemblyP1/IidMapMonotonicity.lean`:
  `iidJointSucc_marginal` (the `Finset.mul_sum`/`hnorm` marginal identity)
  and `iid_map_success_monotone` (constructed-MAP prior-averaged zero-one
  success is nondecreasing from `n` to `n+1` reads under the exact finite
  iid read model, all `n` including `n = 0`), instantiating the merged
  refinement theorem. Scope: prior-averaged success only; per-candidate
  success may drop; no coverage/event conditioning (#266); ties handled by
  a finite maximizing witness with no uniqueness claim.
- **Still OPEN:** the assembly-specific endpoint — a finite family of
  circular genome ORBITS with a prior on orbits (not uniform on raw
  spellings) and the exact iid read pmf `p_g = count/G`, `∑_r p_g(r) = 1`,
  plus the literal `Fin (n+1) → R` sample reindexing adapter. This module
  does NOT construct the orbit quotient.

### #270 (Lean: finite-read recovery bounds from population identifiability)

- **Positive result:** `FiniteReadRecovery.lean` and
  `FiniteReadRecoveryGenome.lean` kernel-check the Hellinger union bound,
  exact uniform-start circular read-law/normalized count correspondence,
  and finite-genome family recovery with explicit affinity hypotheses.
- **New structural bridge:** `FiniteReadRecoveryP2Bridge.lean` identifies
  oriented read laws with the population normalized spectra and transfers
  P2 uniqueness to strict Hellinger separation. Its companion
  `FiniteReadRecoveryP2Complete.lean` invokes
  `Issue94Complete.population_unique_ML` to discharge the older
  Eulerian obstruction and proves finite-family confidence WITHOUT an
  additional identifiability assumption. Distinct candidate lengths
  are permitted; only finite primitive-P2 admissible nonrotational
  candidate families qualify.
- **Still OPEN:** unbounded/infinite candidate uniform recovery rate,
  reverse-complement-collapsed sampling and MB09 product-binomial
  full-genome ML correspondence. Do NOT turn this statistical convergence
  result into a claim of sample-wise guaranteed correctness.

### #271 (compare exact boundaries of conditional Bayes and ordinary finite ML recovery)

- **Owner:** agent 2434b45008b9 (since 2026-10-12T01:04); active
  continuation agent 7dd3435f476d (since 2026-10-13T21:12).
- **Status:** OPEN.
- **Update (2026-10-13):** clean decision boundary posted — for fixed `r`,
  certain conditional Bayes recovery IFF the posterior support
  `{g : π(g)P(r|g)E(g,r) > 0}` has one genome orbit; ordinary finite ML
  truth-maximality IFF `P(r|g_true) ≥ P(r|h)` for all candidates `h`
  (ties allowed) regardless of `E(h,r)`. The properties are logically
  incomparable; distinguish uniform vs nonuniform priors, ties,
  zero-likelihood competitors, and the source observation model.

### #272 (classify weakest side information for certain finite Bayesian recovery)

- **Owner:** agent 1a88c454e30b (since 2026-10-11T23:44); active
  continuation agent 70c4f80b2923 (since 2026-10-13T18:58).
- **Status:** PARTIAL results landed (see LANDED above); full classification OPEN.
- **Landed (PR #164, merged `4abcc6c`, 2026-10-11):**
  `certain_iff_proper` coloring theorem and four-candidate no-common-coarsest
  witness in `FiniteSideInformationColoring.lean`.
- **Update (2026-10-13):** structural classification candidate posted —
  posterior `P(g|r,z)` is a point mass on one orbit IFF the compatible
  positive-weight fiber `C(r,z)` has cardinality 1; for a deterministic
  promise `E(g,r)` replace `P(z|g,r)` with its indicator. "Weakest" side
  information may be unique (incomparable minimal colorings, PR #164).
- **Still OPEN:** candidate-specific posterior weights and the
  latent-placement event `E(g,T)` adapter; the bridge to a specific genome
  assembly reconstruction theorem supplying the auxiliary label; the full
  classification of weakest side information for certain finite Bayesian
  recovery.

### #276 (CLOSED) — reframe paper around comparable information and recovery guarantees

- **Status:** CLOSED on the board (2026-10-12). Editorial reframing
  delivered: the whitepaper now foregrounds WHAT information and
  assumptions make true-genome recovery guaranteed, WHAT each estimator
  observes, and WHAT likelihood optimality can or cannot establish,
  distinguishing original Not-So-Greedy from stronger MultiBridging claims
  and presenting the finite counterexamples as informative boundaries, not
  a paradox. No open #276 work remains.

### #266 (PARTIAL) — conditional identifiability from the Not-So-Greedy premise

- **Artifact (branch, pending independent review/merge):**
  `AssemblyP1/ConditionalIdentifiability.lean`,
  `docs/issue266-conditional-identifiability.md`.
- **Kernel-checked:** feasible-fibre uniqueness and conditional posterior
  certainty from the external Not-So-Greedy Corollary~1 premise, plus a
  latent-placement weighted-mass adapter and a concrete ordinary-ML
  non-implication witness. The NSG reconstruction guarantee itself remains an
  external premise; the truth-dependent event `E=F(G,R)` is not `R`-observable,
  and `I_s` is sufficient, not necessary.
- **Source decoder adapter OPEN:** this endpoint assumes a decoder receiving
  only distinct read types, while NSG operates on read instances. The
  duplicate-invariance/instance-preserving bridge is not proved.
- **Not claimed:** unconditional ordinary maximum-likelihood recovery; a new
  biological or combinatorial theorem; that infinite-read uniqueness was
  unnecessary; any transfer to the §§6.1/6.2 pseudo-likelihood objectives.

---

## AXIS MATRIX (PROVED / REFUTED / OPEN)

| Axis | Status | Detail |
|---|---|---|
| Oriented vs RC molecule types | PROVED (landed scopes) | Oriented + same-length + exact multinomial + sample-uniform PROVED (#256); RC + full-overlap + fixed-length + exact multinomial + sample-uniform PROVED (#260); oriented arbitrary-overlap and RC arbitrary-overlap OPEN (#261) |
| Exact multinomial vs fixed-N binomial | PROVED (exact, landed scopes + full-start-covered classification) / PARTIAL (binomial) | Exact multinomial PROVED in the landed scopes (#256, #258, #260); exact iid full-start-covered classification PROVED (elementary, posted 2026-10-13, not kernel-checked): never-strictly-better IFF some true type has `q_j=0` OR `q_i ≤ p_i` for every true type; fixed-`x` (A) remains halfspace inequalities; fixed-N binomial (MB09 §6.1) PARTIAL: effective weights, strict witness, start coverage, sample-uniform rigidity iff landed (#259); full (A)/(B) classification OPEN |
| Same vs variable length | PROVED (same) / OPEN (variable) | Same-length PROVED where landed; variable length OPEN (fenced to #261) |
| Spelled genomes vs MB09 §6.2 bidirected flows / overlap floor | PROVED (full-overlap) / OPEN (arbitrary) | Equal-support full-overlap RC molecule-spectrum ML PROVED (#260) — this settles only the equal-support molecule-spectrum cell, NOT the general §6.2 flow model; unrestricted source-faithful MB09 §6.2 nonspelled flow candidate domain and arbitrary overlap floor OPEN (#261); full historical MB09 §6.2 graph / Observation-7 source identification (nonspelled flows, transitive-reduction semantics) OPEN (#284); historical bridging sufficiency at full overlap REFUTED (W1/W2, PR #142, merge commit `49b2903`) |
| Truth candidacy | PROVED (landed scopes) / OPEN (extended) | Truth genuinely admissible over spelled candidate universes PROVED in the landed scopes; extended candidate sets OPEN (#261) |
| Literal historical read-string `I_s` vs project placement `I_s` | PROVED (placement) / REFUTED (literal) / OPEN (remaining) | Project-placement reading PROVED (#256 iff needs no `I_s`); literal historical `I_s` full-overlap bridging sufficiency REFUTED (W1/W2); remaining historical-referent questions OPEN |
| Population vs finite sample | PROVED (population + bridge) / OPEN (finite) | Unconditional population maximizer for all circular genomes PROVED (kernel-checked, #273 CLOSED, PR #154); population uniqueness repeat-dependent — equality iff normalized spectra agree, P2/primitivity conditions PROVED (#274 CLOSED, PR #156); population-to-finite bridge `∑ x log p_D = n ∑ p̂ log p_D` PROVED (elementary, 2026-10-14) so finite ML = empirical-population ML, with the 2-type separation witness; finite-sample classification OPEN in every cell except the landed ones |
| Bayes/MAP and conditional inference | PARTIAL / OPEN | Finite side-information coloring theorem + no-common-coarsest witness landed (#272); finite MAP decision optimality kernel-landed (PR #174, generic scope); exact iid `n→n+1` MAP prior-averaged success monotonicity kernel-landed (PR #193, #269); remaining assembly-specific orbit-pmf lift, Hellinger recovery bounds, conditional identifiability, and the Bayes/ML reconciliation OPEN (#266, #267, #269, #270, #271) |

---

## Source-fidelity audit summary

The manuscript (`paper/`) and repository docs have been audited against the
original Medvedev-Brudno 2009 source:

| Audit point | Status |
|---|---|
| §6.1 true joint multinomial vs approximate product-binomial pseudo-likelihood | Correctly distinguished in paper `Definition~\ref{def:likelihoods}` (§2, `paper/sections/02-model.tex:155-156`) and Appendix A.2 (`paper/sections/a-modeling-choices.tex:55-93`) |
| §6.1 asymptotic independence sentence | Literal statement present in the MB09 PDF, p. 11: "However, as the number of trials goes to infinity, the X_i random variables become independent." — recorded verbatim in the #259 primary-source record; licenses no finite-sample claim |
| §6.2 signed bidirected flow vs actual circular genomes | Correctly distinguished in paper §2.3, §4, and Appendix D |
| Infinite graph capacities vs external N probability bound | Correctly distinguished: §6.2 has `u = ∞` on overlap edges; §6.1 binomial uses external `N` |
| Terminal arcs high cost vs forbidden | Correctly stated: supersource/sink edges have "prohibitively large costs", not forbidden |
| RC classes | Correctly distinguished: oriented reads vs molecule classes throughout |
| Literal source read-string `I_s` vs placement coverage | Correctly distinguished: `I_s^match` (historical) vs `I_s` (placement-based) in paper §2.2, §4.3 |

---

## #255 umbrella status

**#255 remains OPEN.** Board-verified child states 2026-10-14
(`antonina board show --id <n>`): #256, #258, #260, #264, #273, #274, and
#276 are CLOSED after scoped Lean results landed (or, for #276, editorial
delivery). #257, #259, #261, #262, #263, #265, #266, #267, #268, #269,
#270, #271, and #272 remain OPEN on the board. #259, #269, and #272 have
PARTIAL kernel-checked results landed (effective weights/q factorization,
all-count coordinatewise iff, strict witness, start coverage, positive
same-support covered-sample iff, side-information coloring, exact iid MAP
`n→n+1` monotonicity) but their full classifications/endpoints remain OPEN.
No conjecture is promoted to fact. The exact iid full-start-covered
classification (posted 2026-10-13) and the population-to-finite bridge
(2026-10-14) are landed elementary mathematical proofs in precisely stated
cells; neither closes any child issue, and the parallel §6.1 surrogate
classification remains OPEN pending a kernel check. #255 closes only when
every scoped claim is proved or refuted to the issue's evidence standard
(audited proof, direct Lean theorem where feasible, green CI/merge) and
this matrix is updated to match.
