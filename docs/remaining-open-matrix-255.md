# AssemblyP1 umbrella #255 — remaining-open matrix

_Status: 2026-10-12. Source-fidelity / whitepaper-theorem-matrix integration
front. Verified base: `main` @ `a8200738db63001b299058b07600b39791a8c7e1`
(PR #161 merged after all exact-head CI checks passed).
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

### #257 (PARTIAL) — support rigidity and Graver structural iff LANDED; broader taxonomy OPEN

- **Merged artifacts:** `AssemblyP1/ExactRigidityCriterion.lean`,
  `AssemblyP1/GraverRigidity.lean`, and `AssemblyP1/GraverRigidityAudit.lean`.
- **Graver theorem:** `rigid_iff_forall_graver_not_feasible` and the
  equivalent coordinate-box obstruction `rigid_iff_forall_graver_not_inbox`
  are proved in Lean for a finite oriented support-edge set, positive balanced
  **integer** circulations with **fixed total**. `graver_decomposition`
  supplies a conformal integer-kernel decomposition.
- The module was integrated to main via the already-merged Graver work;
  the previous statement that it was *untracked and not merged* is obsolete.
- **Still OPEN:** broader read-graph structural classification outside this
  positive, same-length, oriented integer-circulation universe; no transfer
  to general bidirected, half-integral, or arbitrary-overlap flow candidates.

### #258 (CLOSED) — exact multinomial, oriented same-length, fixed observation x

- **Artifact:** imported `AssemblyP1/FixedXExactML.lean`.
- **PR:** #159, merged `080b1b3829e015b6499486363167665c21a55bc1`.
- **Statement:** `fixedX_classification_iff` is the exact product-inequality
  certificate over positive balanced, mass-G, *truth-support* spectra.
  `feasibleSpectrum_iff_258` exhausts the four possible AAABBB spectra;
  `fixedX_four_chamber_iff_258` gives all three exact integer-product chamber
  comparisons, with explicit unique-win, top-tie, and strict-loss samples.
  `feasibleSpectrum_realizable_258` constructs circular genomes for all four.
- **Verification:** all three exact-head CI workflows green, including Lean
  compilation, kernel replay and full axiom audit; independently checked all
  64 binary length-six genomes with `scripts/verify_fixedx_258.py`.
- **Additional:** PR #161 merged as `a8200738db63001b299058b07600b39791a8c7e1`
  preserving `scripts/verify_feasible_spectrum_ml_255.py` from obsolete PR #151.
  This exact-rational script passed 974 (truth,sample) cases with G=5,6,L=2
  and recorded 158 out-of-spelled-class higher-likelihood cases.
- **Scope:** fixed-x same-length oriented spectra; not fixed-N product-binomial,
  RC molecule flows, variable genome length, or arbitrary-overlap graph
  reconstruction. Positive maximizer is over *spectra*, not unique genome
  strings when cyclic rotations tie.

### #264 (CLOSED) — integer-lattice Graver basis obstruction/decomposition

- **Artifact:** `AssemblyP1/GraverRigidity.lean`, imported and audited on main.
- **Proof:** conformal extraction of a Graver element by l1 strong induction;
  direct oriented fixed-support circulation rigidity iff absence of a feasible
  unit Graver augmentation, plus `graver_decomposition` for #263.
- **Not implied:** full finite-basis enumeration or convex optimization
  certificate in #263, still OPEN.

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

### #259 (MB09 §6.1 fixed-external-N product-binomial)

- **(A)** at fixed `x` and **(B)** for every realizable complete-support `x`.
- **Status:** OPEN. No binomial-specific classification (extra `(1−d(w)/N)^{n−x(w)}`
  factors, zero-count coordinates, boundary 0/1 probabilities) is established.
- **Note:** The recovered WIP's continuous KKT iff is FALSE (see REFUTED above).
- **Primary-source record (MB09 §6.1, page 11):** the original Medvedev–Brudno
  2009 PDF literally states: "However, as the number of trials goes to
  infinity, the X_i random variables become independent." (verified directly
  against <https://www.cs.toronto.edu/~brudno/medvedev_MLA.pdf>, page 11,
  §6.1; the sentence sits between "When taken together, their joint
  distribution is exactly the multinomial distribution" and "Because the
  number of trials (sampled k-molecules) is typically large, we can
  approximate the multinomial distribution as the product of the individual
  binomial distributions of each X_i."). Three things are explicitly separate:
  - **(a) Literal asymptotic statement:** the quotation is what the authors
    wrote, as an asymptotic motivation for replacing the exact multinomial by
    the product of binomial marginals. It is a source fact about the paper's
    wording, now recorded verbatim with page.
  - **(b) No finite-sample license:** the sentence licenses NO finite-sample
    claim. For a multinomial with fixed category probabilities `p_i`,
    `Cov(X_i,X_j) = −n·p_i·p_j` and the standardized correlation
    `−sqrt(p_i·p_j/((1−p_i)(1−p_j)))` is independent of `n`; only the
    normalized frequencies `X_i/n` have covariance `−p_i·p_j/n → 0`. The
    product-of-binomials objective is therefore a deliberate approximate
    pseudo-likelihood — not the exact joint likelihood, and not a generally
    asymptotically exact factorization — and no finite-`n` maximality
    classification for (A) or (B) follows from it.
  - **(c) Status unchanged:** #259 (A)/(B) remains OPEN; the landed
    exact-multinomial scopes (#256, #260), the refuted bridging/KKT claims,
    and every other OPEN entry are unaffected. No status is flipped by this
    source-fidelity correction.

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
- **Not claimed:** unconditional ordinary maximum-likelihood recovery; a new
  biological or combinatorial theorem; that infinite-read uniqueness was
  unnecessary; any transfer to the §§6.1/6.2 pseudo-likelihood objectives.

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
| §6.1 asymptotic independence sentence | Literal statement present in the MB09 PDF, p. 11: "However, as the number of trials goes to infinity, the X_i random variables become independent." — recorded verbatim in the #259 primary-source record; licenses no finite-sample claim |
| §6.2 signed bidirected flow vs actual circular genomes | Correctly distinguished in paper §2.3, §4, and Appendix D |
| Infinite graph capacities vs external N probability bound | Correctly distinguished: §6.2 has `u = ∞` on overlap edges; §6.1 binomial uses external `N` |
| Terminal arcs high cost vs forbidden | Correctly stated: supersource/sink edges have "prohibitively large costs", not forbidden |
| RC classes | Correctly distinguished: oriented reads vs molecule classes throughout |
| Literal source read-string `I_s` vs placement coverage | Correctly distinguished: `I_s^match` (historical) vs `I_s` (placement-based) in paper §2.2, §4.3 |

---

## #255 umbrella status

**#255 remains OPEN.** #258 and #264 are CLOSED after scoped Lean results
landed; #259, #261, #262 and #263, plus the broader #257 taxonomy, remain
unresolved; no conjecture is promoted to fact. #255 closes only when
every scoped claim is proved or refuted to the issue's evidence standard
(audited proof, direct Lean theorem where feasible, green CI/merge) and this
matrix is updated to match.
