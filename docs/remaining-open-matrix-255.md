# AssemblyP1 umbrella #255 — remaining-open matrix

## Addendum — 2026-10-24 (order-audit reachability + per-axis OPEN audit, unmerged)

* **Verified this run (isolated fresh clone, no shared-checkout edits).**
  `origin/main` HEAD is `234f348`. All three recent #255 artifacts are
  reachable on origin and form the ancestry chain
  `48447f5 -> 5b55129 -> origin/main 234f348` (`merge-base --is-ancestor`
  yes for both links): `5b55129` (4 fixed-x objective-equivalence iff
  lemmas, `MaximizerOrderTransform`), `48447f5` (order-audit module
  `MaximizerOrderTransformAudit` + root import + exact-rational verifier
  `scripts/verify_255_order_transform.py`), `7a8d326` (matrix addendum
  recording `5b55129` pending-integration status). All three remain
  **unmerged / pending-integration**; none is on `main`, and none closes
  any child front. No Lean cell owned by #257/#259/#261 is duplicated here.
* **Honest per-axis status after this audit (nothing promoted to fact):**
  fixed-x (A) has kernel-checked objective-equivalence lemmas only
  (monotone rewording preserves argmax; antitone swaps max/min) — truth
  maximality at fixed x stays OPEN; sample-uniform (B) exact-iid
  full-start-covered cell PROVED (PR #251), all other (B) cells OPEN;
  exact multinomial PROVED only in landed scopes (#256/#258/#260 + PR
  #251), fixed-N binomial PARTIAL (#259 landed weights/witnesses, full
  (A)/(B) OPEN); same length PROVED in landed scopes, variable length
  OPEN (fenced to #261, short counterexamples landed #300); spelled
  genomes vs §6.2 bidirected flows / overlap floor OPEN except
  full-overlap + reduced-circuit occurrence cells; truth candidacy PROVED
  in landed scopes, extended candidate sets OPEN; literal historical
  read-string `I_s` bridging sufficiency REFUTED (W1/W2), project
  placement `I_s` PROVED where landed, remaining historical-referent
  questions and the (A)-side adapter OPEN (#271). Cross-checked by
  `scripts/verify_255_matrix_axes.py`.
* **#255 stays OPEN.** This is a documentation/verification increment only.

## Addendum — 2026-10-21 (L3 uniqueness transport: does NOT hold, kernel-checked)

* **New kernel-checked increment on the L3 axis.**  The merged L3 transport
  (`AssemblyP1.Section62PhysicalOrbitObjective`, PR #353) reduces *maximality*
  (ties admitted) of a physical orbit flow to maximality of its physical visit
  vector, for any score that is a function of the visit vector.  The #255
  umbrella asks for the transport of the exact ML objective *or its argmax /
  uniqueness*.  The uniqueness half is now settled, and it does **not** hold:
  `AssemblyP1.Section62PhysicalOrbitObjectiveUniqueness` (+ audit) proves
  * `physUniqueMaximal_image_of_flow` — uniqueness transports **forward**:
    a unique flow maximizer has a unique visit-vector maximizer;
  * `physUniqueMaximal_of_injective` /
    `physUniqueMaximal_iff_of_injective` — uniqueness transports **backward
    only under injectivity** of the visit map on the candidate set at the truth;
  * `MixedLoop.physVisitVec_twoRep_eq` — on the minimal length-`1`
    mixed-sign self-loop witness (`mixedLoop` on `Tagged Bool`), two orbit IDs
    representing the *same* physical edge give two distinct orbit flows the
    *same* physical visit vector, so the visit map is not injective;
  * `MixedLoop.physUniqueMaximal_not_transported` — on that witness the visit
    vector is the unique image maximizer while the flow is not a unique
    maximizer, for every score that is a function of the visit vector
    (including the exact oriented ML objective).
  Axioms `⊆ {propext, Classical.choice, Quot.sound}`; no
  `sorry`/`admit`/`axiom`/`native_decide`.  Scoped note:
  `docs/issue261-physical-orbit-objective-uniqueness-255.md`.
* **Still genuinely OPEN:** L1 remains the source-graph correspondence (owned
  by live #284/#261); the spelled-genome identification and the general §6.2
  classification remain OPEN.  Uniqueness of the *flow* maximizer is **not**
  recovered by the physical-orbit objective transport without an injectivity
  hypothesis; this increment delimits the L3 transport, it does not close it.

## Addendum — 2026-10-19 (dihedral orbit quotient, #269)

* **#269 dihedral item CLOSED (conditional + obstruction).**  The last open #269
  item — the dihedral (rotation + reverse-complement) orbit quotient — is
  kernel-checked in `AssemblyP1/DihedralOrbitQuotient.lean` (+
  `AssemblyP1/DihedralOrbitQuotientAudit.lean`), `docs/dihedral-orbit-quotient-269.md`,
  and `scripts/verify_269_dihedral_orbit_quotient.py`.  Under the explicit
  RC-invariance hypothesis `RCInvariant c` on the raw oriented read pmf, the
  merged MAP/ML/monotonicity/certificate results lift to the dihedral quotient
  (`readPmf_dihedral_map_success_monotone`,
  `readPmf_uniform_dihedral_prior_ML`, `readPmf_dihedral_certificate`); the
  strand-symmetrized read law gives the same results unconditionally
  (`sym_dihedral_map_success_monotone`, `sym_uniform_dihedral_prior_ML`).  The
  hypothesis is **necessary**, with a precise kernel-checked obstruction: the
  length-3 binary genome `001` has `p(00) = 1/3` while its reverse complement has
  `p(00) = 0` (`Obstruction.readPmf_not_rcInvariant`), so no function on dihedral
  classes pulls back to the raw read pmf (`Obstruction.no_dihedral_descent`).
  Axioms `⊆ {propext, Classical.choice, Quot.sound}`; no
  `sorry`/`admit`/`axiom`/`native_decide`.  This does **not** change any §6.1/§6.2
  flow status, #266 event-conditional inference, or per-truth monotonicity
  (still refuted by `GenomeOrbitAdapter.PerTruthDrop.perTruth_true_drops`).
* **Still genuinely open on the #255 umbrella:** the same items as the
  2026-10-18 addendum (source-faithful physical RC bidirected graph
  correspondence, flow-objective transport, general §6.2 classification,
  exact Myers fidelity).  Nothing here closes those.

## Addendum — verified 2026-10-17 (avoid duplicate research)

The dated matrix below is a **historical 2026-10-16 snapshot**, not an
authoritative list of currently absent Lean theorems. Always cross-check
`origin/main` and the exact GitHub PR merge statuses before assigning work.

* **Already proved:** PR #265 merged the unconditional, repository-specific
  Observation 7 signed-circuit statement in
  `Section62GlobalSkippedBridge.observation7_reduced_signed_circuit_range_count`,
  with the local `Section62SkippedWindowFactor` and idealized Myers
  `Section62MyersIdealTransitivity` source spelling lemmas on main.
  No new agent should reprove these.
* **Already proved:** PR #300 separately counted positive/negative signed
  half-incidences invariant under edge reversal; PR #307 merged a **stronger**
  physical tagged-edge reversal-quotient and one-physical-visit vs
  two-inherited-departures `ATAT` counterexample. Duplicate PR #306 was closed
  without merge.
* **Already proved:** PR #312 generalized the p,q long-bridge rigidity
  classification; PR #310 proved the scoped finite Bayes/MAP certificate.
  These are not pending research tasks.
* **Integrated since the older snapshot:** signed aggregate PR #313 is
  **MERGED** at `23881843a37d9e2a50d07c23b519058f3baddf51`,
  incorporating bounded experimental #304 RC-overlap/three palindrome orbits,
  #305 interior-matching finite convex surrogate (not exact source ML on
  zero-probability endpoints), and the independent exact-rational #309
  verifier/doc. Original PRs #295 and #304 are superseded by this signed
  integration; #305 is GitHub-marked merged. The #309 workflow YAML edit
  was intentionally **not** included because the GitHub OAuth credential
  lacks workflow-write scope, but its verifier was independently run and
  its script and documentation were preserved byte-for-byte.
  PR #311 was closed as a tree-identical no-op. Probe PR #242 remains
  intentionally unmerged.

* **Genuinely open:** a source-faithful edge-indexed physical RC bidirected
  graph correspondence (including parallel overlaps and practical transitive
  reduction); transport of signed balance, physical incidence *visit counts*,
  vertex bounds, and ML objective into that source graph; sufficiently strong
  contig/single-genome realization hypotheses; exact extended-real ML
  support/Graver optimizer equivalence (not the finite affine surrogate).

Model execution/liveness as of this check: both host OpenCode Console
providers (OpenCode and OpenCode Go) reject requests due **expired API keys**,
so Antonina's managed agents cannot execute until credentials are renewed.
Their saved task prompts are not evidence of running workers. Manual signed
GitHub integration remains possible.

## Addendum — 2026-10-18 (reversal-orbit transport, #255/#261 front)

* **Stale premises corrected.** The docs-only gap note is **already merged**:
  PR #301 (`docs/section62-reversal-orbit-correspondence-gap-255.md`, head
  `ba3e6bc`, base `f338cdf`) is `state=closed, merged=true` — it is not open.
  PR #315 ("directed double-cover signed-incidence balance", head `21264cf`)
  is also merged. Current `origin/main` at this check is
  `230eca1cbe0bdb4c1a4375b7a13b3dabc679d379`.
* **Newly kernel-checked (branch
  `agent/b5e5c7634f3b-issue255-reversal-orbit-transport`, not yet merged):**
  `AssemblyP1.Section62ReversalOrbitTransport` **refutes the first disjunct of
  the pinned L2 flow-transport discipline**. The legacy `throughput` counts an
  oriented edge as departing the class of its stored `sx` end; for a self-loop
  its reverse-complement representation departs the *same* class, so
  `throughput_pair_selfloop` gives
  `throughput cls f [e, reverseEdge e] v = f e + f (reverseEdge e)`, and any
  reversal-symmetric flow (`f e = f (reverseEdge e)`) has **even** inherited
  departure throughput (`throughput_pair_selfloop_symm`). The unit mixed-sign
  loop orbit has physical visit count **one**
  (`mixed_physical_visit_one`), so
  `no_revsymm_flow_realizes_unit_loop` proves no reversal-symmetric oriented
  flow realizes it. The `f e = f (rev e)` symmetrization therefore does **not**
  leave the physical feasible set unchanged; the correct route is the
  quotient-orbit flow of `Section62PhysicalEdgeOrbit`. Axioms
  `⊆ {propext, Quot.sound}`; no `sorry`/`admit`/`axiom`/`native_decide`.
  Minimal witness: the length-`1` `mixedLoop` on `Tagged Bool`, not `ATAT`.
  Independent verifier `scripts/verify_261_reversal_orbit_transport.py`
  (86 exact-integer assertions, exit 0).
* **Still genuinely OPEN on this front:** the quotient model is not identified
  with MB09's physical RC overlap multigraph (edge multiplicity,
  transitive-reduction contract). Only the incidence-level transport is settled.

## Addendum — 2026-10-19 (physical edge-orbit ML-objective transport, #255/#261 L3)

* **Landed (kernel-checked, this increment):** the L3 remainder — transport of
  the exact §6.2 ML objective to physical orbit totals — at the level of the
  objective argument and the maximality reduction.
  `AssemblyP1.Section62PhysicalOrbitObjective` (+
  `AssemblyP1.Section62PhysicalOrbitObjectiveAudit`) defines the physical
  visit-count / read-copy vector `physVisitVec` (`= physPosTotal`, the objective
  argument), proves representative-invariance (`physVisitVec_reverse`),
  additivity (`physVisitVec_add`), transports the §6.2 vertex lower bound
  (`PhysVertexBound`, `physVertexBound_reverse`), and transports the
  flow-to-count-vector reduction `physMaximal_image_iff` /
  `physMaximal_reverse_iff`. On the length-`1` mixed-sign self-loop witness the
  physical visit count is `1` versus the induced oriented departure throughput
  `2` (`Witness.mixed_physical_ne_departure`), so the transport is not vacuous.
  Axioms `⊆ {propext, Quot.sound}`; no `sorry`/`admit`/`axiom`/`native_decide`.
  Scoped note: `docs/issue261-physical-orbit-objective.md`.
* **Still genuinely OPEN:** L1 only — the quotient edge set is not identified
  with MB09's physical RC overlap multigraph (edge multiplicity,
  transitive-reduction contract), and no physical orbit flow is identified with
  a single circular spelled genome.

---

### Historical 2026-10-16 matrix follows


_Status: 2026-10-16, reconciled by agent b629762217b2 against current
`origin/main` @ `c581d11` (GitHub PR #287 merge; `git ls-remote
https://github.com/ottojung/assemblyp1 refs/heads/main`). This supersedes
the 2026-10-15 refresh at `b4071f5` (agent e05c947b4ab8, commit `9abb4e1`)
and the 2026-10-14 refresh at `157ad34` (PR #196).

**Reconciliation of the stale matrix-refresh branch.** The branch
`agent/e05c947b4ab8/issue255-matrix-refresh` @ `9abb4e1` was left
`needs-integration`; it is now an **ancestor of `origin/main`** (landed via
merge `92f9d87`, then advanced by PR #196 `ee2ac8b`, PR #259 `fb51592`,
and the PR #274 doc commit `27869e5`). Nothing on that branch is
unmerged; this update is on top of it.

**Post-#274 landings now on `origin/main` (previously unrecorded here).**
GitHub PRs: #251 exact iid full-start-covered pointwise classification
(merge `13411a6`; **this is the #255 axis-(B) item that the previous
revisions recorded as OPEN**); #277 `RigidityBridge` for #257 (merge
`cf54277`); #263 §8.1 bouquet rigidity for #257 (merge `18f01c3`); #253
candidate-specific latent-start feasibility for #271 (merge `b6dfee1`);
#256 exact-iid-vs-§6.1 power monotonicity for #259 (merge `d40a18e`); #279
fixed-n full-coverage extreme-sample iff for §6.1 (merge `ad3582b`); #278
unobserved-molecule-type adjudication for §6.1 (merge `e30401b`); #261
target-D posterior/MAP equivalence for #269 (merge `58be9d2`); #244 side
information `Is`-vs-unambiguous ordering for #272 (merge `41e5aec`); #258
and #268 uniform exponential exact-ML error rate for #281 (merges
`70c21b8`/`eaf5d38`); #280 strong-law/KL limit for #265 (merge `53f8c4d`);
#282 generic anchored-window spelling identity and word-level RC law for
#284 (merge `c581d11`); #252 window alignment for #284 (merge `0b87b58`);
#281 GitHub PR for board #263 penalized-ML distinction (merge `e57e81f`).
See "Post-#274 child-front landings" below.

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
- **Status:** The idealized two-hop reduction and global walk-language
  preservation are kernel-checked (Section62GlobalSpellingPreservation and
  Section62MyersIdealTransitivity). The oriented circular read-occurrence
  equality and observed reverse-complement class-count lift are also
  kernel-checked in integration PR #274. Exact equivalence to the full
  approximate Myers algorithm, the full unobserved section-6.1 class universe,
  and arbitrary feasible-flow realizability remain OPEN. These scopes must
  not be conflated.

### #284 (OPEN) — global circular read occurrences: PROVED in signed integration PR #274

- **Already on main:** Section62GlobalCircularCorrespondence,
  Section62CircularWindowAdapter, Section62FullSpectrumIndexing,
  Section62FullSpectrumUnseenFactor, and the periodic seam lemmas.
- **Kernel-checked in signed integration PR #274:** the genuine reduced
  signed-circuit circular-window alignment, no-skipped-observed-window
  theorem, exact oriented read-word occurrence equality (including G<L),
  observed reverse-complement molecule-class count identity (palindromes
  counted once), and the ideal Myers same-spelling two-hop iff.
- **Still OPEN:** full equivalence to Myers's practical approximate-overlap
  algorithm; the complete unobserved section-6.1 RC class universe versus
  the source's literal 4^k indexing; general feasible-flow-to-genome
  realization. The issue remains OPEN despite the new scoped theorems.


### #262 (CLOSED) — full-overlap lift to arbitrary overlap threshold: LANDED

- **Artifact:** `AssemblyP1/Section62FullOverlapLift.lean`
- **PR:** #202, merged `4492b65`; independent review at exact head `3e3657c`
  (module imported into the root replay/audit). Lifts the full-overlap
  counterexample to arbitrary `o_min`; board #262 CLOSED.

### #259 (PARTIAL) — covered-binomial weight iff and circular inversion: LANDED

- **Artifact:** `AssemblyP1/CoveredBinomialWeightsIff.lean` (PR #211, merged
  `298682b`; `covered_product_le_iff_zero_or_pointwise`,
  `covered_effectiveProduct_le_iff`,
  `covered_ambient_start_samples_effectiveProduct_le_iff`, plus
  new-support/non-vacuity witnesses; `scripts/verify_covered_binomial_weights_259.py`)
  and `AssemblyP1/Section62BinomialRealGenomeInversion.lean` (PR #224).
- **Scope:** the fixed-`N` product-binomial covered-sample classification on a
  fixed modeled read-type universe; does NOT classify the general §6.2 flow
  domain or the exact iid objective.

### #259 (PARTIAL) — fixed-`x` (axis A) product-binomial criterion: LANDED

- **Artifact:** `AssemblyP1/FixedXProductBinomialMaximality.lean` +
  `AssemblyP1/FixedXProductBinomialMaximalityAudit.lean`,
  `docs/fixedx-product-binomial-maximality-259.md`,
  `scripts/verify_fixedx_product_binomial_259.py`.
- **Kernel-checked:** at a fixed observation `x` (`n = ∑ x`) the MB09 §6.1
  product-binomial objective is **separable**,
  `F_B(x) = ∏_e B e ^ (x e) (N - B e) ^ (n - x e)`
  (`fixedX_eq_separable`); the exact necessary-and-sufficient fixed-`x`
  criterion is the product inequality (`fixedX_le_iff`), with coordinatewise
  (`fixedX_le_of_coordwise`) and pointwise effective-weight
  (`fixedX_le_of_effectiveWeight_le`) sufficient strengthenings; a
  concentrated-sample iff (`fixedX_concentrated_iff`); and a full-class
  fixed-`x` classification on the smallest instance `Fin 2`, `N = 4`,
  `x = (2,2)` (`fixedX_fin2_full_class`).
- **Axis-A-to-axis-B bridge:** `sampleUniform_iff_pointwise` shows the
  sample-uniform maximality of `robust_iff_unique` is exactly the pointwise
  special case of the fixed-`x` criterion.
- **Strict separation:** `fixedX_weaker_than_pointwise` exhibits positive
  equal-total `A = (2,2)`, `B = (3,1)` over `Fin 2`, `N = 4`, with `A` winning
  at the covered sample `x = (2,2)` while `q_0(B) = 9 > 4 = q_0(A)`.  Hence
  pointwise effective-weight domination is sufficient but **not necessary** for
  fixed-`x` maximality: fixed-`x` maximality is strictly weaker than
  sample-uniform maximality.
- **Axioms:** `{propext, Classical.choice, Quot.sound}` (kernel-checked).
- **Residual OPEN:** a full-class fixed-`x` maximizer classification when the
  empirical frequency `x_e N / n` is non-integral (the integer program's
  maximizer need not be the real-relaxation MLE); variable genome length; the
  §6.2 bidirected-flow domain (`#260`/`#261`).  This entry does not close any
  of those.

### #266 (CLOSED on board; PARTIAL scope) — conditional identifiability from the NSG premise: LANDED

- **Artifacts:** `AssemblyP1/ConditionalIdentifiability.lean` (PR #198 merged
  `a3dd8a0`; PR #203 merged `235114d` adds the read-instance/dedup source
  adapter), `docs/issue266-conditional-identifiability.md`, and a
  `paper/sections/b-epistemic-ledger.tex` row.
- **Kernel-checked:** feasible-fibre uniqueness and conditional posterior
  certainty from the external Not-So-Greedy Corollary 1 premise, plus a
  latent-placement weighted-mass adapter and an ordinary-ML non-implication
  witness. The NSG reconstruction guarantee remains an external premise.
- **Residual OPEN:** the author handoff records that the
  `Finset`-of-distinct-read-types decoder premise is stronger than NSG's
  `N`-read-instance guarantee, so a duplicate-invariance adapter remains
  open. Recorded as PARTIAL, not a full closure.

### #267 (CLOSED) — finite ML vs Bayes-optimality reconciliation: LANDED

- **Artifacts:** `docs/bayes-optimality-conditional-feasibility-267.md`,
  `docs/audit-267-finite-ml-vs-conditional-bayes.md`,
  `docs/recommendations-265-254-267.md`, `AssemblyP1/MapDecisionExamples.lean`,
  `scripts/audit-267-independent-checks.py` (35/35).
- **Merges:** `157ad34` (PR #196 branch base), mechanical review fixes F1–F6
  `6a4d9e9`, audit fail-closed `5c8a103`; board review commit `6a4d9e9`.
  Three-facts reconciliation: unconditional MAP optimality (reused, not
  reproved), ordinary finite ML can rank a nonfeasible competitor above the
  feasible truth (W1–W6), and conditioning on `E=F(G,R)` is a different
  experiment. Board #267 CLOSED.

### #270 (CLOSED) — finite-read recovery bounds from population identifiability: LANDED

- **Artifacts:** `AssemblyP1/FiniteReadRecovery.lean` (PR #199, merged
  `3b6fc7c`), `AssemblyP1/FiniteReadRecoveryGenome.lean` (PR #205, merged
  `a42a53e`), `AssemblyP1/FiniteReadRecoveryP2Bridge.lean` and
  `AssemblyP1/FiniteReadRecoveryP2Complete.lean` (PR #207, merged `41bc335`).
- **Statement:** Hellinger/Bhattacharyya union bound, exact uniform-start
  circular read-law correspondence, finite-genome family recovery with
  explicit affinity hypotheses, and the primitive-P2 identifiability bridge.
- **Scope:** statistical convergence, NOT sample-wise guaranteed correctness;
  unbounded candidate uniform rates remain outside the closed scope. Board
  #270 CLOSED.

### Exact iid full-start-covered pointwise classification: LANDED (kernel-checked, GitHub PR #251)

- **Artifact:** `AssemblyP1/FiniteSampleIidEnvelope.lean` (extends PR #172
  `4d4970c`), audit `AssemblyP1/FiniteSampleIidEnvelopeAudit.lean`.
- **PR / merge:** GitHub PR #251, content commit `d3eb0a3`, merge
  `13411a620389d409306f93853086f6d3278898b0` (2026-10-15). Both new root
   imports are present at head: `AssemblyP1.lean:292` (`import
   AssemblyP1.FiniteSampleIidEnvelope`) and `:293`
   (`import AssemblyP1.FiniteSampleIidEnvelopeAudit`).
- **Statement:** `truth_maximizer_forall_covered_iff`
  (`AssemblyP1/FiniteSampleIidEnvelope.lean:197`) proves, for true oriented
  support `E`, positive true spectrum `A` (`A i > 0`), true iid probabilities
  `p i > 0`, and candidate `q i ≥ 0`:
  `(∀ x, FullStartCovered A x → ∏ q^x ≤ ∏ p^x) ↔ (∃ j, q j = 0) ∨ (∀ i, q i ≤ p i)`,
  where `FullStartCovered A x := ∀ i, A i ≤ x i`
  (`AssemblyP1/FiniteSampleIidEnvelope.lean:175`). This is exactly the
  pointwise all-full-start-covered sample criterion that earlier revisions of
  this matrix recorded as an OPEN axis-(B) item; it is now the `m`-free
  generalization of the fixed-surplus envelope
  `truth_maximizer_iff_envelope_le_one` (same file, `:144`).
- **Axioms:** `{propext, Classical.choice, Quot.sound}` (recorded at the
  `#print axioms` audit in `FiniteSampleIidEnvelopeAudit.lean`); no
  `sorry`/`admit`/new `axiom`.
- **Scope:** EXACT iid multinomial on the true oriented support. It does NOT
  cover the MB09 §6.1 fixed-`N` product-binomial surrogate (board #259), the
  general §6.2 bidirected-flow domain (board #261), or the source-historical
  matched read-string `I_s` domain. It is a #255 umbrella axis-(B) item and
  does not by itself close any child board issue.

---

## Post-#274 child-front landings (2026-10-16, head `c581d11`)

These are kernel-checked and/or CI-verified results merged to `origin/main`
at or after the PR #274 integration (`149b85d`) and after the previous
revision of this matrix was written. Each row states the **resolved scoped
sub-claim** and the **residual OPEN scope** for its board child issue; none is
a full classification.

| Board child | Resolved sub-claim now on main | Exact artifact / lemma (file:line) | Merge | Residual OPEN scope |
|---|---|---|---|---|
| #257 | Exact finite bouquet/8.1 rigidity criterion for the explicit `(m1,m2,f)` bridge graph and a real-vs-integer feasibility gap witness | `AssemblyP1/RigidityBridge.lean` (`bridge_nonrigid_iff` `:295`, `bridgeA_rigid_iff_trivial` `:208`); `AssemblyP1/RigidityBouquet.lean` (`bouquet_nonrigid_iff` `:405`, `len233_mult211_real_integer_gap` `:530`) | `cf54277` (GitHub PR #277), `18f01c3` (GitHub PR #263) | Broader read-graph structural classification outside the positive same-length oriented integer-circulation universe; no general bidirected/half-integral/arbitrary-overlap transfer (#257 still OPEN) |
| #259 | Exact-iid-vs-§6.1 ranking inversion for all `n` and sharpness of the covered-weight iff disjuncts | `AssemblyP1/Section62BinomialPowerMonotonicity.lean` (`ranking_inversion_all_n` `:117`, `exact_prefers_A_all_n` `:96`, `surrogate_prefers_B_all_n` `:107`); `AssemblyP1/CoveredBinomialWeightsIffSharpness.lean` (`iff_needs_zero_disjunct` `:40`, `iff_needs_pointwise_disjunct` `:68`) | `d40a18e` (GitHub PR #256) | Full #259 (A)/(B) product-binomial classification over the full candidate universe still OPEN |
| #259 | Exact fixed-`n` full-coverage **extreme-sample** iff for §6.1 count vectors (`|I|` explicit concentration samples suffice) | `AssemblyP1/Section62FiniteNExtremeSamples.lean` (`binomial_fixed_n_extreme_iff` `:195`, `surplus_sum_of_fullcoverage` `:136`) | `ad3582b` (GitHub PR #279) | General `∀ y ≥ 0` full-coverage surrogate classification still OPEN |
| #261 | Unobserved-molecule-type adjudication: the §6.1 count-vector criterion must range over the full modeled universe; observed-support-only dominance is insufficient | `AssemblyP1/Section62BinomialSupportAdjudication.lean` (`criterion_is_full_support` `:137`, `observedOnly_insufficient` `:247`, `flow_genome_gap` `:167`) | `e30401b` (GitHub PR #278) | General §6.2 bidirected-flow classification OPEN |
| #261 | Spelled-throughput image identity refuted: an explicit feasible signed flow whose throughput vector is not a spelled visit set | `AssemblyP1/Section62SpelledFlowImageRefutation.lean` (`exists_feasible_not_spelled` `:229`, `image_ne_spelledVisitSet` `:217`) | `149b85d` (GitHub PR #274) | Full §6.2 flow classification OPEN |
| #271 | Candidate-specific latent-start feasibility adapter (replaces an external support oracle) and conditional-Bayes-implies-B separation; target-D posterior/MAP equivalence with zero-mass handling for #269 | `AssemblyP1/ConditionalVsMLGenomeAdapter271.lean` (`p_nonneg` `:126`, `p_sum_one` `:132`); `AssemblyP1/ConditionalBayesEImpliesB271.lean` (`condCertain_imp_MLMax_of_MLsound` `:137`, `genome_E_not_MLsound` `:321`); `AssemblyP1/PosteriorMAPEquivalence.lean` (`iid_map_posterior_max` `:106`, `zeroMass_all_joint_max` `:78`) | `b6dfee1` (GitHub PR #253), `58be9d2` (GitHub PR #261) | No genome-level conditional-recovery claim; W1/W2 (A)-side adapter stays open (#271 still OPEN) |
| #272 | `Is`-vs-unambiguous ordering classification: read-only sufficiency iff implication-of-unambiguity; truth-dependent and singleton promises incomparable | `AssemblyP1/FiniteSideInformationOrdering.lean` (`sufficient_readonly_iff_imp_unambiguous` `:91`, `truthdependent_sufficient_incomparable` `:146`, `ordering_verdict` `:272`) | `41e5aec` (GitHub PR #244) | Candidate-specific posterior weights and latent-placement `E(g,T)` adapter; bridge to a genome reconstruction theorem (#272 still OPEN) |
| #281 | Explicit uniform exponential exact-ML error rate (`primitiveP2_ML_confidence_explicit`, `all_primitiveP2_ML_confidence`) surfaced in the paper and both decks | `AssemblyP1/PrimitiveP2UniformSeparation.lean` (`primitiveP2_ML_confidence_explicit` `:340`, `primitiveP2_exponential_error_bound` `:317`); `paper/sections/01-introduction.tex`; `slides/{biologists,programmers}.md` | `70c21b8` (GitHub PR #258), `eaf5d38` (GitHub PR #268) | Genome-level finite corollary and paper recentering still OPEN (#281 still OPEN) |
| #265 | Strong-law / KL-limit statement for finite identifiable families + CI script | `scripts/verify_strong_consistency_265.py`; `paper/sections/05-population.tex`; `docs/presentation-arc-265.md` | `53f8c4d` (GitHub PR #280), `b9f0f47` (CI wiring, GitHub PR #284) | #265/#268 editorial review pass still OPEN |
| #265 | Chernoff refinement of the finite-family recovery bound: `Σ_D exp(-n C(p_S,p_D)) ≤ \|C_S\| exp(-n C_*)`, `C_* ≥ ln(1/ρ_*)`; `C_*` is the exact finite-family exact-ML error exponent (classical Chernoff/Sanov, EXTERNAL); the bound stays loose at finite `n` (~3.7× exact at `n=16`, ratio `≈√n`) | `paper/sections/03-open-question.tex` (`prop:chernoff-refinement`, `rem:chernoff-sharp`); `docs/chernoff-exponent-finite-recovery-265.md`; `scripts/verify_chernoff_finite_recovery_265.py`; both decks' speaker notes | pending (branch `agent/df84a657ae4a-issue265-chernoff-exponent`) | Tight/minimax finite-`n` bound and the unrestricted-universe uniform sample size remain OPEN |
| #284 | Generic anchored-window spelling identity and word-level reverse-complement class-count law | `AssemblyP1/Section62GenericAnchorSpelling.lean` (`generic_anchors_window_eq_sources` `:70`, `generic_circular_spelling_anchors` `:99`); `AssemblyP1/Section62RcWordLaw.lean` (`classWordCount_eq_rc_class_count` `:72`) | `c581d11` (GitHub PR #282), `0b87b58` (GitHub PR #252) | Exact Myers practical-algorithm fidelity and full unobserved RC class universe still OPEN (#284 still OPEN) |
| #263 | Conditional separable-convex Graver optimality certificate (file added by GitHub PR #249) plus the penalized-solver-cost vs pure-ML distinction | `AssemblyP1/SeparableConvexGraver.lean` (`graver_optimal_iff_no_improving` `:324`, `negLog_discConvOn` `:500`) | `9fa5a41` (GitHub PR #249), `e57e81f` (GitHub PR #281) | Full separable-convex discrete Graver certificate conditional on #264 still OPEN (#263 still OPEN) |

---

## Mathematical proofs (human-readable; kernel status per entry)

One entry here (the exact iid full-start-covered classification) has since
been **kernel-checked** and is cross-referenced to the LANDED section; the
rest remain human-readable only, as labeled per entry.

### Exact iid finite-ML classification on the all-true-starts-sampled domain: NOW KERNEL-CHECKED (was elementary-only), posted 2026-10-13

- **Source:** Antonina #255 board comment, research-assistant @
  2026-10-13T23:07:10.986Z. Originally recorded as an elementary mathematical
  proof (finite products + power-unboundedness), **not** kernel-checked.
- **Status change (reconciled 2026-10-16).** The pointwise all-sample
  statement is now a kernel-checked theorem on `origin/main`:
  `AssemblyP1.FiniteSampleIidEnvelope.truth_maximizer_forall_covered_iff`
  (`AssemblyP1/FiniteSampleIidEnvelope.lean:197`), landed by GitHub PR #251
  (content `d3eb0a3`, merge `13411a6`). It is **root-imported** at
  `AssemblyP1.lean:292–:293` (both the module and its
  `#print axioms` audit `FiniteSampleIidEnvelopeAudit.lean`), and the file is
  additionally compiled by the CI library glob (`lakefile.lean`
  `globs := #[.andSubmodules \`AssemblyP1]`). Axioms
  `{propext, Classical.choice, Quot.sound}`. See the LANDED section above for
  the exact statement and scope. The earlier revision of this matrix wrongly
  recorded this item as OPEN and the artifact as "NOT imported by the root
  aggregator ... and no doc references it"; both statements were true at
  `b4071f5` but are false at `c581d11`.
- **Kernel predecessor artifact (still present):**
  `AssemblyP1/FiniteSampleIidEnvelope.lean` also proves
  `truth_maximizer_iff_envelope_le_one` (PR #172, merge `4d4970c`): for a
  fixed finite read-type universe `E`, baseline counts `a` positive on the
  true support, surplus `y` with fixed total `m`, ratios `r_i=q_i/p_i` and
  `rmax=max_i r_i`, truth is a MAP maximizer for every `x=a+y` with `∑y=m`
  IFF the scalar envelope `(πQ/πP)·∏ r_i^{a_i}·rmax^m ≤ 1` (support holes
  give 0). `truth_maximizer_forall_covered_iff` is the `m`-free
  generalization over every full-start-covered `x ≥ A`.
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
- **Status:** the pointwise classification is now kernel-checked (PR #251;
  see the LANDED section above) and no longer elementary-only. The §6.1
  surrogate parallel claim remains OPEN (next bullet). It does NOT close
  #255, #259, or any child issue; all broader conjectures remain OPEN.

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
- **Status:** PARTIAL results landed (see LANDED above).  Axis **A** (fixed
  `x`) now has a kernel-checked necessary-and-sufficient criterion plus the
  strict separation from axis B (see the `#259 (PARTIAL) — fixed-`x` (axis A)`
  entry above).  The full-class fixed-`x` classification at non-integral
  empirical frequency, and the full axis-B candidate universe, remain OPEN.
- **Landed (PRs #163 `#386c470`, #165 `#908754f`, #166 `#ec52da3`, #167
  `#9002ef6`, merged 2026-10-11/12):** q factorization
  (`∏ q_i(B)^{x_i}`); all-count effectiveWeight coordinatewise iff; explicit
  strict integer witness; start-coverage realization; positive same-support
  covered-sample iff — all kernel-checked in
  `FixedNBinomialEffectiveWeights.lean`, `FixedNConstructiveWitness.lean`,
  `FiniteStartCoverage.lean`.
- **Additional landed (PR #211 `298682b`, PR #224 `aedf1b9`):**
  `CoveredBinomialWeightsIff.lean` proves a genuine necessary-and-sufficient
  covered-sample weight criterion on a fixed modeled read-type universe
  (`covered_product_le_iff_zero_or_pointwise`,
  `covered_ambient_start_samples_effectiveProduct_le_iff`, new-support and
  non-vacuity witnesses; checked by
  `scripts/verify_covered_binomial_weights_259.py`), and
  `Section62BinomialRealGenomeInversion.lean` exhibits a length-100 genome pair
  where the exact objective prefers `A` while the fixed-N surrogate prefers
  `B`. Neither classifies the general §6.2 flow domain.
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
- **Axis A landed (kernel-checked):** the fixed-`x` criterion
  (`AssemblyP1/FixedXProductBinomialMaximality.lean`,
  `docs/fixedx-product-binomial-maximality-259.md`,
  `scripts/verify_fixedx_product_binomial_259.py`): separability, the exact
  product criterion, coordinatewise/pointwise sufficient inequalities, the
  concentrated-sample iff, the smallest-instance full-class classification, and
  the strict separation from sample-uniform maximality.  See the LANDED entry
  above.
- **Still OPEN:** a full-class #259(A) fixed-`x` maximizer classification when
  the empirical frequency `x_e N / n` is non-integral, and the #259(B)
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
- **Landed adapters (PRs #201 `72dca8a`, #212 `a426670`, #233 `99e8527`):**
  `Section62BinomialCriterion.lean` (uniform binomial criterion and
  `qFac` factorization), `Section62FlowCountVectorAdapter.lean`
  (`feasible_flow_maximal_image_iff`, subset/count-vector monotonicity), and
  `Section62SpelledFlowAdapter.lean` (`spelling_flow_feasible`,
  `throughput_eq_visits`, `balCore_eq_zero`, `weighted_dedup`). These connect
  spelled circuits to §6.2 feasible flows but do NOT classify the general
  flow domain.
- **New kernel-checked scope (integration PR #274):** the exact circular
  occurrence equality for every observed oriented read word of a genuine
  reduced signed circuit, plus its observed RC molecule-class corollary.
  This replaces the old no-skipped-window proof strategy, now discharged.
  It does not identify all feasible flow throughputs with spelled genomes.
- **New kernel-checked scope (2026-10-18, branch
  `agent/b5e5c7634f3b-issue255-reversal-orbit-transport`):** reversal-orbit
  **incidence transport** is settled at the negative end —
  `AssemblyP1.Section62ReversalOrbitTransport` proves the legacy departure
  `throughput` is even on every reversal-symmetric oriented flow over a
  self-loop orbit, so the `f e = f (rev e)` symmetrization cannot represent the
  unit physical mixed-sign loop flow (physical visit count one). The
  quotient-orbit flow (`physPos`/`physNeg`, merged #307) is the correct route.
  The source-graph/objective transport (L1 and the L3 remainder) stays OPEN.
- **OPEN sub-axes:** arbitrary overlap floor, transitive reduction, vertex
  lower bound 1, orientation/RC classes, integer vs half-integral flows,
  flows not spelling one circular genome, candidate-set choice, truth
  admissibility, likelihood (exact vs fixed-N binomial), length universe.
- **Status:** OPEN, explicitly unresolved. General §6.2 bidirected flow
  classification remains OPEN.

### #262 (CLOSED) — full-overlap edge irreducibility; lift counterexamples to arbitrary overlap

- **Status:** CLOSED. `AssemblyP1/Section62FullOverlapLift.lean` (PR #202,
  merged `4492b65`) lifts the full-overlap §6.2 ML counterexample to arbitrary
  `o_min`; independent review at exact head `3e3657c` (module imported into the
  root replay/audit). See the LANDED section above.

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
- **Update (2026-10-15):** a scoped finite-family sample-complexity bound
  landed (`docs/sample-complexity-265.md`, merge `069f64e`,
  `scripts/verify_sample_complexity_265.py`) and the decks were rebalanced to
  a positive operational arc (`22a6233`). Board #265 remains OPEN pending the
  #254/#268 review pass; the general non-equal-length ML characterization
  stays with #261/#284, not here.
- **Update (2026-10-16):** the strong-law/KL limit statement landed in the
  paper and both decks (`53f8c4d`) with `scripts/verify_strong_consistency_265.py`
  wired into CI (`b9f0f47`), and both decks were re-centered on the #268
  two-question narrative (Question A conditional / Question B unconditional) by
  agent `68d129da714f`; see `docs/deck-arc-consistency-265.md`. Paper,
  claims-matrix (`tab:claims`), and bibliography acceptance re-checked there
  (all `\ref`/`\cite` resolve; build 0 undefined).
- **Update (2026-10-17):** the whitepaper now cites the newly merged
  kernel-checked **necessary-and-sufficient** finite Bayes/MAP optimality
  certificate (paper `rem:bayes-certificate`;
  `AssemblyP1/BayesOptimalityCertificate.lean`, PR #310): the converse to
  `thm:bayes-optimal` (`pointwiseMAP_iff_bayesOptimal`), the tie witness
  (`TieWitness.both_optimal`), forced choice at a strict maximizer, and the
  conditional-posterior-one boundary (`posterior_eq_one_iff_singleton_support`).
  `tab:claims` row 2 and `docs/verification.md` were updated to cite it. This
  closes the item-3 "limits/ties" citation gap; the genuinely open items are
  unchanged: the general (non-equal-length) finite-ML characterization and a
  sharp uniform sample size over the unrestricted genome universe.

### #266 (board CLOSED; PARTIAL scope) — conditional identifiability from Not-So-Greedy information-feasibility

- **Status:** board CLOSED 2026-10-14; recorded here as PARTIAL, not a full
  scientific closure. PR #198 merged as `a3dd8a0` adds
  `AssemblyP1/ConditionalIdentifiability.lean` (abstract decoder/feasible-
  fibre, conditional posterior, constrained MAP, no-better-rule corollary,
  latent-placement weighted-mass adapter, historically scoped endpoint) plus
  `docs/issue266-conditional-identifiability.md` and a ledger row. PR #203
  merged as `235114d` adds the §7 read-instance/dedup adapter
  (`exists_finset_decoder`, `nsg_instance_iff_finset`, `historicalEvent_dedup`,
  `historical_feasible_fibre_unique_of_instance_decoder`); `SourceRegime` makes
  the `2 ≤ L ≤ S.len` regime explicit.
- **Kernel-checked:** feasible-fibre uniqueness and conditional posterior
  certainty from the external Not-So-Greedy Corollary 1 premise. The external
  `hNSG` guarantee remains the trust boundary (the algorithm is not
  formalized).
- **Residual OPEN (per author handoff):** the `Finset`-of-distinct-read-types
  decoder premise used by `historical_feasible_fibre_unique` is stronger than
  NSG Corollary 1, which consumes `N` read instances and adjusts edge
  multiplicities; an instance/multiset-preserving adapter (or duplicate-
  invariance theorem) remains to be proved. Not claimed: unconditional
  ordinary maximum-likelihood recovery; any transfer to the §§6.1/6.2
  pseudo-likelihood objectives.

### #267 (CLOSED) — reconcile finite ML counterexamples with Bayes optimality and conditional feasibility

- **Status:** CLOSED. Merged `157ad34` (PR #196 branch base) adds
  `AssemblyP1/MapDecisionExamples.lean`, `docs/bayes-optimality-conditional-feasibility-267.md`,
  `docs/audit-267-finite-ml-vs-conditional-bayes.md`,
  `docs/recommendations-265-254-267.md`, and
  `scripts/audit-267-independent-checks.py` (35/35); mechanical review fixes
  F1–F6 at `6a4d9e9`; fail-closed audit at `5c8a103`; board review commit
  `6a4d9e9`. Three coexisting facts: (1) unconditional MAP maximizes
  prior-average success but can err on an individual `x` (reused from
  `FiniteBayesDecision`, not reproved); (2) ordinary finite ML can rank a
  nonfeasible competitor above the feasible truth (W1–W6); (3) conditioning on
  `E=F(G,R)` is a different experiment with effective prior `π(g|E)` and joint
  likelihood `π(g)P_g(R)1_F(g,R)`. See the LANDED section above.

### #268 (whitepaper: foreground Bayes-optimal ML and the nontrivial 2016 comparison)

- **Owner:** agent ffd9d61d8644 (since 2026-10-12T02:57); active
  continuation agent 7a974f0a0947 (since 2026-10-13T23:12).
- **Status:** OPEN. Editorial; compare with #265/#266/#267/#276.
- **Update (2026-10-13):** PR #189 already foregrounds ML/MAP optimality
  as entrance; if remaining work is redundant to PR #189, report
  redundancy and propose only concrete remaining edits. Close only after
  current paper, slides/claims matrix, and bibliography acceptance are
  confirmed and all missing parts landed.
- **Update (2026-10-15):** paper refocus delivered (`e7e3d20`, `b47eb04`),
  followed by the #268 fidelity check (`cac6347`, MB09 verbatim quote,
  Bayes prior-averaged scope, `#273`/`#274` likelihood convention). Board #268
  remains OPEN pending the #265 mirror in the decks and claims-matrix
  acceptance.
- **Update (2026-10-16):** the pending #265 mirror is now in place: both decks
  name the two questions (Question A conditional / Question B unconditional)
  and the claims matrix (`tab:claims` row 1 vs row 3) and bibliography were
  re-checked for consistency (agent `68d129da714f`,
  `docs/deck-arc-consistency-265.md`). The remaining #268 question is whether
  the human reviewer accepts the centered wording; no further deck/claims-matrix
  gap is recorded.

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
- **Update (2026-10-15):** the oriented assembly-specific endpoint is
  LANDED. `AssemblyP1/GenomeOrbitAdapter.lean` (PR #200, merged `3c639dc`)
  constructs the oriented orbit quotient with the exact iid read pmf
  `p_g = count/G` (`readPmf_sum_one`, `readPmf_rotWord`, `orbitReadPmf`,
  `quotient_likelihood_well_defined_iff`, `orbit_map_success_monotone`,
  `uniform_orbit_prior_ML`) and records the raw-spelling-vs-orbit prior
  distinction (`spellingPushforward_eq_uniform_iff_constant_orbitSize`).
  `AssemblyP1/BayesValueMonotonicity.lean` (PR #231, merged `967db37`) proves
  `bayesValue_succ_ge` / `bayesValue_mono` (`V_{n+1} ≥ V_n`).
- **Update (2026-10-16):** the §6.2 feasible-flow non-equivalence is LANDED as a
  Lean separation theorem. `AssemblyP1/Section62FlowGenomeSeparation.lean` (+
  `Section62FlowGenomeSeparationAudit.lean`) reuses
  `AssemblyP1/Section62FlowCountVectorAdapter` (`throughputVec_congr`,
  `maximal_image_iff`) to show every §6.2 objective factors through the
  molecule-class throughput, then exhibits the reverse-complement pair `S0 = 00`,
  `S1 = 11` with equal §6.2 visit vector but different exact oriented likelihood,
  refuting `exactLikelihood = φ ∘ classCount` and hence
  `section62_flow_objective_ne_genome_likelihood`. Verifier
  `scripts/verify_269_flow_genome_separation.py`; see
  `docs/section62-flow-genome-separation-269.md`. It does not touch #261's
  throughput-image classification.
- **Update (2026-10-17):** the necessary-and-sufficient finite Bayes/MAP
  optimality certificate is LANDED.
  `AssemblyP1/BayesOptimalityCertificate.lean` (+
  `AssemblyP1/BayesOptimalityCertificateAudit.lean`) closes the **necessary**
  half of target B: a deterministic policy is Bayes-optimal iff it is pointwise
  MAP (`pointwiseMAP_iff_bayesOptimal`), with the strict-loss and tie witnesses
  `StrictLossWitness.strict_loss`/`TieWitness.both_optimal`. It also proves the
  conditional-posterior-one boundary `posterior_eq_one_iff_singleton_support`
  and its rotation-class instantiation
  `orbit_posterior_eq_one_iff_singleton_support`. Verifier
  `scripts/verify_269_bayes_optimality_certificate.py`; see
  `docs/bayes-map-optimality-certificate-269.md`. The prior-averaged scope is
  checked against the merged `PerTruthDrop` (`16/25 < 4/5` while the
  prior-average rises `13/20 → 139/200`). It does not touch #266's
  event-conditional theorem, #261's throughput-image classification, or the
  merged A/C/D/E endpoints (PRs #174/#193/#200/#231/#261).
- **Still OPEN:** the reverse-complement-orbit quotient (the adapter proves
  rotation invariance only; RC invariance is deliberately not claimed) and any
  source-historical endpoint. Board #269 remains OPEN.

### #270 (CLOSED) — Lean: finite-read recovery bounds from population identifiability

- **Status:** CLOSED (board). PRs #199 (`3b6fc7c`), #205 (`a42a53e`), and
  #207 (`41bc335`) merged.
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
- **Outside the closed scope (recorded, not claimed):** unbounded/infinite
  candidate uniform recovery rate, reverse-complement-collapsed sampling, and
  MB09 product-binomial full-genome ML correspondence. This is a statistical
  convergence result, NOT sample-wise guaranteed correctness.

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
- **Update (2026-10-15):** the abstract separation is LANDED.
  `AssemblyP1/ConditionalVsOrdinaryMLSeparation.lean` and
  `AssemblyP1/W1W2SeparationCompatibility.lean` (PR #232, merged `4c90973`,
  `AxiomAudit271.lean`) kernel-check the incomparability on a finite model and
  reuse the W1/W2 (A)-side counterexamples. Board #271 remains OPEN: no
  genome-level conditional-recovery claim is made (the witness is an explicit
  abstract toy), and the W1/W2 (A)-side adapter stays open by design.

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
- **Additional landed (PR #195 `b0a6e9f`, PR #204 `c312cbb`, PR #262 `654ed0c`):**
  `FiniteBayesianSideInformation.lean` (independent reviews of the ordering
  blocker and the normalized positive-support incomparability) and
  `FiniteSideInformationOrder.lean` (the `Stronger` preorder on side channels,
  `sufficient_of_stronger`, `sufficient_and`, `false_strongest`, and
  incomparable minimal channels), plus `FiniteSideInformationSourcePromise.lean`
  (truth-only source-property family: weakest exists iff every read is already
  unambiguous).
- **Additional landed (literal read-string adapter, #272):**
  `FiniteSideInformationReadStringAdapter.lean` + audit.  Defines the adapter
  `isPromiseReadString` (observation = distinct read-string set, promise =
  `HistoricalInformationFeasibleLiteral` marginalised over compatible
  placements), proves it is read-dependent (outside both `AdmReadOnly` and
  `AdmTruthOnly`), applies `weakest_admissible_iff_union` to the read-dependent
  `I_s` family (`weakest_readStringIS_iff_sufficient`,
  `weakest_readStringIS_of_fibreUnique`), and kernel-checks the `I_s` necessity
  obstructions (general coverage/triple/interleaved projection lemmas and the
  unbridged-triple witnesses `ABXABYABZ` / `ABXABZABY`).  See
  [`issue272-read-string-adapter.md`](issue272-read-string-adapter.md).
- **Additional landed (read-only decoder certainty, target 3, 2026-10-18):**
  `FiniteReadOnlyDecoderCertainty.lean` + audit.  Some read-only decoder reaches
  posterior one at `r` iff the supported truth-fibre of `r` is a single nonempty
  orbit class (`exists_readOnly_decoder_certain_iff_support_singleton`), which is
  exactly the weakest read-only promise `Unambiguous`
  (`readOnly_certain_set_eq_weakest`); "inferable from the read iff read-only" is
  formalized by `admReadOnly_iff_factorable` / `truthDependent_not_factorable`;
  and the bounded target-4 distinction "minimum sufficient promise always exists,
  weakest need not" by `minimum_exists_unique` / `minimum_without_weakest`.  See
  [`issue272-readonly-decoder-certainty.md`](issue272-readonly-decoder-certainty.md).
- **Additional landed (`I_s` vs `Unambiguous` ordering, 2026-10-19):**
  `FiniteReadStringIsVsUnambiguous.lean` + audit.  On a length-`4`,
  read-length-`2` read-realizable model the merged literal read-string adapter
  `isPromiseReadString` is **incomparable** with `Unambiguous`
  (`isPromiseRS_unambiguous_incomparable`): direction 1 (`I_s ⇒ Unambiguous`) is
  refuted because `ABAB` is `I_s`-promising at `Y = {AB, BA}` while the
  different-orbit `AABB` also realizes `Y`; direction 2 (`Unambiguous ⇒ I_s`) is
  refuted because `Y = {AA, BB}` is `Unambiguous` while the realizer `BBAA` is
  not `I_s`-promising.  The two promises constrain the read-realizable fibre and
  the `I_s`-feasible fibre respectively.  See
  [`issue272-read-string-is-vs-unambiguous.md`](issue272-read-string-is-vs-unambiguous.md).
- **Still OPEN:** the bridge to a specific genome assembly reconstruction
  theorem supplying the auxiliary label; the decoder-level certainty endpoint
  (external Not-So-Greedy guarantee remains an attributed premise); `I_s`
  necessity for the *particular* 2016 decoder; the full classification of
  weakest side information for certain finite Bayesian recovery.

### #276 (CLOSED) — reframe paper around comparable information and recovery guarantees

- **Status:** CLOSED on the board (2026-10-12). Editorial reframing
  delivered: the whitepaper now foregrounds WHAT information and
  assumptions make true-genome recovery guaranteed, WHAT each estimator
  observes, and WHAT likelihood optimality can or cannot establish,
  distinguishing original Not-So-Greedy from stronger MultiBridging claims
  and presenting the finite counterexamples as informative boundaries, not
  a paradox. No open #276 work remains.

### #281 (exponential ML error decay and finite primitive-P2 class)

- **Status:** OPEN. Landed (see LANDED above): `NonmonotonicityWitness281.lean`
  (PR #208), `PrimitiveP2FiniteClass.lean` (PR #214),
  `PrimitiveP2UniformSeparation.lean` (PR #234). A prior review of PR #199
  (`FiniteReadRecovery.lean`, merged for #270) is recorded on #281.
- **Still OPEN:** the genome-level finite corollary (bounded genome lengths)
  and the paper recentering around identifiability; the general
  non-equal-length ML characterization is NOT owned here.

### #284 (correct §6.2 transitive reduction; prove spelling fidelity)

- **Status:** OPEN at the source-model boundary, despite substantial
  kernel-checked advances in integration PR #274: idealized Myers
  two-hop reduction iff, signed global walk-language preservation,
  full oriented circular read-occurrence identity, and observed RC
  molecule-class counting including palindromes.
- **Still OPEN:** exact Myers practical algorithm correspondence,
  the full unobserved section-6.1 class universe and 4^k ambiguity,
  and characterization of which general feasible balanced flows spell
  a single circular genome.


### #300 (short finite-read ML counterexamples, true lengths 2, 3, 4)

- **Status:** OPEN (needs closure). Landed (see LANDED above):
  `AssemblyP1/ShortFiniteMLCounterexamples.lean` + `AxiomAudit300.lean` +
  `docs/source-notes/short-finite-ml-counterexamples-300.md` (PR #229, merged
  `67e1de7`), independently reviewed APPROVE.
- **Remaining:** close the board issue; no minimality is claimed and no
  classification follows from the witnesses.

---

## Reconciliation at head `c581d11` (2026-10-16)

This section is the reviewable index requested for umbrella #255: it maps
each **frozen axis** to the **board child issues** that own it, states which
sub-claims are now supported by a kernel-checked artifact or a CI test at
`origin/main` @ `c581d11`, and separates the two flag categories explicitly.

### Frozen axes → child issues → current evidence

| Frozen axis | Board children | Kernel-checked / test support at `c581d11` | Genuinely OPEN at `c581d11` |
|---|---|---|---|
| Oriented vs reverse-complement molecule types | #256 (CLOSED), #260 (CLOSED), #261 (OPEN) | `RobustSameLengthIff.lean` (`robust_iff_unique_spectrum`), `FullOverlapMoleculeML.lean` (`robust_maximality_iff_unique`), `Section62RcWordLaw.lean` (`classWordCount_eq_rc_class_count`) | arbitrary-overlap oriented and RC flows (#261) |
| Exact multinomial vs fixed-`N` binomial | #256/#258/#260 (CLOSED), #259 (OPEN), #261 (OPEN) | exact iid full-start-covered classification `FiniteSampleIidEnvelope.truth_maximizer_forall_covered_iff` (PR #251); `FixedXExactML.lean` (#258); `FixedNBinomialEffectiveWeights.lean`, `CoveredBinomialWeightsIff.lean`, `Section62FiniteNExtremeSamples.lean` (`binomial_fixed_n_extreme_iff`), `Section62BinomialSupportAdjudication.lean` (#259 partial) | full #259 (A)/(B) product-binomial classification; the §6.1 **surrogate** full-coverage `∀y` classification (see flag F-a) |
| Same vs variable length | #258/#260 (CLOSED), #261 (OPEN), #300 (OPEN) | same-length iffs (#256/#260); `ShortFiniteMLCounterexamples.lean` + `AxiomAudit300.lean` (PR #229) | general variable-length classification (#261); #300 board closure |
| Spelled genomes vs MB09 §6.2 bidirected flows / overlap floor | #260/#262 (CLOSED), #261/#284 (OPEN) | `Section62FullOverlapLift.lean` (#262); spelled-circuit flow adapters `Section62FlowCountVectorAdapter.lean`/`Section62SpelledFlowAdapter.lean`; `Section62SpelledFlowImageRefutation.lean` (`exists_feasible_not_spelled`); `Section62GenericAnchorSpelling.lean` (`generic_circular_spelling_anchors`) | arbitrary feasible-flow realization, full unobserved RC class universe, exact Myers practical-algorithm fidelity (#261/#284) |
| Truth candidacy | #256/#260 (CLOSED), #261 (OPEN) | truth admissibility proved in the landed scopes | extended candidate sets (#261) |
| Literal historical read-string `I_s` vs project placement `I_s` | #256 (CLOSED), #271 (OPEN) | project-placement reading proved (#256 needs no `I_s`); W1/W2 literal historical bridging sufficiency REFUTED (`HistoricalCoverageSameLengthWitnesses.lean`, PR #142 `49b2903`) | remaining historical-referent questions; W1/W2 (A)-side adapter (#271) |
| Population vs finite sample | #273/#274 (CLOSED), #255 axis-(B) | `PopulationMaximizerUnrestricted.lean` (`AssemblyP1.PopulationUniqueness.population_maximizer_unrestricted`), `PopulationGibbs.lean`; exact iid finite classification PR #251 | finite-sample classification outside the landed cells; population-to-finite bridge is elementary-only (see flag F-b) |
| Finite-read reliability / sample complexity | #281 (OPEN), #265 (OPEN) | `PrimitiveP2FiniteClass.lean`, `PrimitiveP2UniformSeparation.lean` (`primitiveP2_ML_confidence_explicit`), `NonmonotonicityWitness281.lean`; `scripts/verify_strong_consistency_265.py` | genome-level finite corollary (#281); #265/#268 editorial pass |
| Bayes/MAP and conditional inference | #266/#267/#270 (CLOSED), #269/#271/#272 (OPEN) | `FiniteBayesDecision.lean`, `IidMapMonotonicity.lean`, `GenomeOrbitAdapter.lean`, `BayesValueMonotonicity.lean`, `PosteriorMAPEquivalence.lean`, `ConditionalVsOrdinaryMLSeparation.lean`, `FiniteSideInformationColoring.lean`, `FiniteSideInformationOrdering.lean` | RC-orbit quotient and genome-level conditional recovery (#269/#271); latent-placement adapter (#272); duplicate-invariance adapter (#266 residual) |

### Flag F-a — RESOLVED scoped claim that lacks a kernel-checked artifact

- The **§6.1 surrogate full-coverage `∀y` classification** (`∀ y ≥ 0` on
  `supp(A)`: `F_B(A+y) ≤ F_A(A+y)` iff `[∃ i: b_i = 0] ∨ [∀ i: b_i ≤ a_i]`,
  with `a_i = q_i(A)`, `b_i = q_i(B)`) is recorded as PROVED only as an
  **elementary** post (Antonina #259, 2026-10-13T23:28:50Z) and is **not
  kernel-checked** at `c581d11`. The closest kernel artifacts are the
  *fixed-`n` extreme-sample* iff `Section62FiniteNExtremeSamples.lean`
  (`binomial_fixed_n_extreme_iff` `:195`, GitHub PR #279) and the
  *covered-sample weight* iff `CoveredBinomialWeightsIff.lean`
  (`covered_product_le_iff_zero_or_pointwise`), neither of which is the
  general `∀y` surrogate statement. Marked OPEN, not resolved.

### Flag F-b — RESOLVED claim that lacks a kernel-checked artifact

- The **population-to-finite bridge** (`∑_w x(w)·log p_D(w) = n·∑_w p̂(w)·log p_D(w)`,
  hence fixed-`x` finite ML = empirical KL projection) is a PROVED
  **elementary** observation (`docs/population-finite-gap-255.md`). It is
  **not kernel-checked**: the proposed `AssemblyP1/PopulationFiniteGap.lean`
  is **absent** at `c581d11` (verified: no such file). It restates the
  (A)-regime comparison and is not claimed to classify anything.

### Genuinely OPEN at `c581d11` (board state, `antonina board show`)

Board-OPEN child issues: **#257, #259, #261, #263, #265, #268, #269, #271,
#272, #281, #284, #300**. Board-CLOSED child issues: #247, #254, #256, #258,
#260, #262, #264, #266, #267, #270, #273, #274, #276, #277, #282. Every OPEN
child carries only scoped partial results (see the table above); no full
classification in any of them is claimed. Conjectures remain OPEN.

---

## AXIS MATRIX (PROVED / REFUTED / OPEN)

| Axis | Status | Detail |
|---|---|---|
| Oriented vs RC molecule types | PROVED (landed scopes) | Oriented + same-length + exact multinomial + sample-uniform PROVED (#256); RC + full-overlap + fixed-length + exact multinomial + sample-uniform PROVED (#260); oriented arbitrary-overlap and RC arbitrary-overlap OPEN (#261) |
| Exact multinomial vs fixed-N binomial | PROVED (exact, landed scopes) / PARTIAL (binomial) | Exact multinomial PROVED in the landed scopes (#256, #258, #260); short variable-length exact counterexamples kernel-landed (#300, PR #229); **exact iid full-start-covered pointwise classification now KERNEL-CHECKED** (`FiniteSampleIidEnvelope.truth_maximizer_forall_covered_iff`, GitHub PR #251, merge `13411a6`, root-imported at `AssemblyP1.lean:292`; the earlier revision wrongly recorded this as OPEN/un-imported); fixed-`x` (A) remains halfspace inequalities; fixed-N binomial (MB09 §6.1) PARTIAL: effective weights, strict witness, start coverage, covered-sample weight iff (#211), fixed-`n` extreme-sample iff (#279), sample-uniform rigidity iff landed (#259); full (A)/(B) classification OPEN; the §6.1 surrogate full-coverage `∀y` classification is elementary-only (flag F-a) |
| Same vs variable length | PROVED (same) / OPEN (variable) | Same-length PROVED where landed; variable-length sufficiency REFUTED by short exact counterexamples (#300); general variable-length classification OPEN (fenced to #261) |
| Spelled genomes vs MB09 §6.2 bidirected flows / overlap floor | PROVED (full-overlap and reduced-circuit occurrences) / OPEN (arbitrary flows) | Full-overlap RC molecule-spectrum ML proved (#260); spelled-circuit flow adapters landed (#201/#212/#233); signed integration PR #274 kernel-proves circular oriented read occurrences and observed RC class counts for genuine reduced circuits, but also refutes the general spelled-throughput image identity (#247). Arbitrary feasible-flow realization, full unobserved RC classes, and exact Myers practical-algorithm fidelity remain OPEN (#261/#284). |
| Truth candidacy | PROVED (landed scopes) / OPEN (extended) | Truth genuinely admissible over spelled candidate universes PROVED in the landed scopes; extended candidate sets OPEN (#261) |
| Literal historical read-string `I_s` vs project placement `I_s` | PROVED (placement) / REFUTED (literal) / OPEN (remaining) | Project-placement reading PROVED (#256 iff needs no `I_s`); literal historical `I_s` full-overlap bridging sufficiency REFUTED (W1/W2); remaining historical-referent questions OPEN |
| Population vs finite sample | PROVED (population + bridge) / OPEN (finite) | Unconditional population maximizer for all circular genomes PROVED (kernel-checked, #273 CLOSED, PR #154); population uniqueness repeat-dependent — equality iff normalized spectra agree, P2/primitivity conditions PROVED (#274 CLOSED, PR #156); population-to-finite bridge `∑ x log p_D = n ∑ p̂ log p_D` PROVED (elementary, 2026-10-14) so finite ML = empirical-population ML, with the 2-type separation witness; finite-sample classification OPEN in every cell except the landed ones |
| Finite-read reliability / sample complexity (#281) | PROVED (scoped) / OPEN (full) | Finite primitive-P2 candidate class (`PrimitiveP2FiniteClass.lean`, PR #214), non-monotonicity of exact-ML success (PR #208), and uniform exponential exact-ML separation (PR #234) kernel-landed; scoped sample-complexity bound (#265, merge `069f64e`); genome-level finite corollary OPEN (#281) |
| Bayes/MAP and conditional inference | PARTIAL / OPEN | Finite side-information coloring (#164) and side-information order (#195/#204) landed (#272); finite MAP decision optimality kernel-landed (PR #174, generic scope); exact iid `n→n+1` MAP prior-averaged success monotonicity (PR #193) and oriented orbit adapter + Bayes value `V_{n+1} ≥ V_n` (#200/#231) kernel-landed; conditional-vs-ordinary separation (#232) kernel-landed; #266 (board CLOSED; residual instance adapter OPEN), #267 (CLOSED), and #270 (CLOSED) landed; RC-orbit quotient and genome-level conditional recovery remain OPEN (#269, #271) |

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

**#255 remains OPEN.** Board-verified child states **2026-10-16** at
`origin/main` @ `c581d11` (`antonina board show --id <n>`): #247, #254, #256,
#258, #260, #262, #264, #266, #267, #270, #273, #274, #276, #277, and #282
are CLOSED after scoped Lean results landed (or, for #254/#276, editorial
delivery). #257, #259, #261, #263, #265, #268, #269, #271, #272, #281, #284,
and #300 remain OPEN on the board. Several OPEN children carry PARTIAL
kernel-checked results (effective weights/q factorization, all-count
coordinatewise iff, strict witness, start coverage, covered-sample weight
iff, fixed-`n` extreme-sample iff, side-information coloring/order, orbit
adapter, posterior/MAP equivalence, Bayes value monotonicity, finite
primitive-P2 class and uniform separation, spelled-flow adapters,
conditional-vs-ordinary separation, global-circular correspondence,
anchored-window spelling and word-level RC law) but their full
classifications/endpoints remain OPEN.
No conjecture is promoted to fact. **Corrected at this reconciliation:** the
exact iid full-start-covered pointwise classification (posted 2026-10-13) is
**now kernel-checked** — `FiniteSampleIidEnvelope.truth_maximizer_forall_covered_iff`
(GitHub PR #251, merge `13411a6`, root-imported at `AssemblyP1.lean:292`) — and
is no longer an OPEN axis-(B) item; the earlier revision of this matrix
recorded it as OPEN with the artifact "NOT imported by the root aggregator",
which was already false at `c581d11`. The population-to-finite bridge
(2026-10-14) remains an elementary proof in a precisely stated cell and is
**not** kernel-checked (`AssemblyP1/PopulationFiniteGap.lean` is absent; flag
F-b). The §6.1 surrogate full-coverage `∀y` classification remains
elementary-only (flag F-a). Neither flag closes any child issue. #255 closes
only when every scoped claim is proved or refuted to the issue's evidence
standard (audited proof, direct Lean theorem where feasible, green CI/merge)
and this matrix is updated to match.
