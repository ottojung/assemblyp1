# Whitepaper refocus note (board #268)

Authoring note for the #268 whitepaper main-text refocus. This records which
sections changed, what each change is meant to accomplish, the exact evidence
level of every headline it touches, and the open questions left for human
review.

## Provenance

- Base: `origin/main` at `cbc54bf07f1ba5c8a1df4f495285b7b3d014b2ad`.
- Branch: `agent-0252d4b354b2-issue268-refocus`.
- Scope: whitepaper prose only. No Lean proof, source code, or theorem
  statement was weakened or restated.

## Changed sections

### `paper/sections/02-model.tex`

Added the paragraph *"Uniform start sampling is not uniform read-type
probability"* immediately after Definition `def:likelihoods` (exact
multinomial and fixed-`N` binomial). It separates two uniformities that the
required narrative distinguishes: uniform sampling over start positions versus
the induced read-type probabilities `d_w/|D|`, which are generally nonuniform.
It also notes the other ways nonuniform read-type probabilities can arise
(nonuniform start sampling, position-dependent coverage, a different read-type
convention) and states that all exact-likelihood statements in the paper use
uniform start sampling unless stated otherwise. This is prose clarification of
the existing model; it introduces no new claim.

### `paper/sections/03-open-question.tex`

1. **Theorem `thm:bayes-optimal` restated more explicitly.** The statement now
   names the equivalence classes as cyclic-rotation classes, names zero-one
   loss, states that a uniform prior on the *equivalence classes* makes MAP and
   ML coincide, and records that the conclusion holds at every finite sample
   size `n` for iid reads. This matches the kernel-checked endpoint
   `AssemblyP1.FiniteBayesDecision` (see `FiniteBayesDecision.lean`:
   `pointwise_MAP_optimal`, `pointwise_MAP_optimal_randomized`,
   `finite_iid_MAP_optimal`, `chooseMAP_success_monotone_under_refinement`).
   No hypothesis was added or dropped relative to the merged endpoint.

2. **New paragraph "Rotation classes and the choice of prior."** Explains that
   the prior is over rotation classes rather than literal spellings, that a
   uniform prior over spellings would weight classes by orbit size (an artifact
   of the representation, cf. `rem:cyclic`), and that this is a modeling choice
   under which ML is the prior-average optimum. It explicitly disclaims
   optimality for a fixed truth or under other priors/losses.

3. **New subsection "A worked example, and five claims that must not be
   conflated"** (`sec:five-claims`), placed after the Bayes rationale and
   before the finite/population conclusions. It contains:
   - Example `ex:worked-bayes`: a two-candidate, two-observation direct
     computation in which MAP/ML is prior-average optimal (`5/8`) yet fails on a
     positive-probability sample. Labeled an elementary direct computation, not
     a new theorem.
   - Table `tab:claims`: the five notions (conditional reconstruction, prior
     average Bayes optimality, pointwise finite-sample failure, identifiability,
     limiting consistency) with scope/quantifier, hypotheses, conclusion, and
     evidence. The evidence column uses the proof-to-claim labels required by
     the issue: the 2016 reconstruction premise is an imported published
     premise (`shomorony2016`), not a Lean proof; the kernel-checked endpoints
     are named explicitly.

## Evidence levels (proof-to-claim policy)

| Headline | Label |
| --- | --- |
| Bayes/MAP prior-average optimality | (i) kernel-checked `FiniteBayesDecision`; classical textbook `berger1985` |
| Conditional reconstruction (Question A) | (iv) published 2016 reconstruction premise + (i) kernel-checked conditional/ordinary separation |
| Pointwise finite-sample failure `W_1,W_2` | (i) kernel-checked certificates |
| Identifiability (population/rigidity) | (i) kernel-checked population and rigidity theorems |
| Limiting consistency | (i) kernel-checked `FiniteReadRecovery` + explicit sample-size corollary |
| Worked example `ex:worked-bayes` | direct computation, not a new theorem |
| Rotation-class prior discussion | modeling choice, not a theorem |

No conditional derivation whose key historical algorithm premise is imported is
labeled "Lean-proved": the Question A row names the published premise
explicitly.

## Validation

- PDF build: `latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex`
  exit `0`, 48 pages, 0 undefined references, no new overfull boxes.
- Research-docs CI scripts: `check-research-docs.py`,
  `verify_historical_coverage_audit.py`, `verify_247c_historical_witnesses.py`,
  `verify_261_binomial_extreme_samples.py`, `verify_261_spelled_flow_adapter.py`,
  `verify_261_spelled_flow_maximality.py`,
  `verify_covered_binomial_weights_259.py`, `verify_281_window_cap.py 3 11 4`,
  and `verify_sample_complexity_265.py` all exit `0`.

## Follow-up verification (2026-10-26)

- Verified repository identity at `https://github.com/ottojung/assemblyp1.git`;
  fetched `origin/main` at `234f3480d7589c8fc4e056c91dda91343fe64ece` and the
  published ready branch at `ce15e3daaf41c6c5577b073f8ea0cdd2ecaa201f`.
- The ready commit is signed (`git verify-commit`: Good signature) and descends
  from the recorded main. Its diff against main is exactly the two prose files
  `paper/sections/01-introduction.tex` (+8) and
  `paper/sections/03-open-question.tex` (+3/-1); the changes are limited to the
  Bayes-average versus pointwise motivation and the R-only/conditioning caveat.
- `sh paper/build.sh` in `paper/` exited 0; latexmk reported the existing PDF is
  up to date. `check-research-docs.py` and the eight targeted historical,
  binomial, window-cap, and sample-complexity verification scripts all passed.
- At verification time the branch was not an ancestor of `origin/main`, and
  the public PR listing showed no PR for this ready branch. `gh` is unavailable;
  unauthenticated GitHub API accepts reads but rejects comment creation with
  HTTP 401 (and prior PR operations returned 403). Thus this review could not
  create an integration PR or post a board comment. Compare URL:
  <https://github.com/ottojung/assemblyp1/compare/main...agent/m207b4xxQBSjv47yF8Z6FF-issue268-ready>.
- Reusable #265 slide narrative: introduce finite-n uniform-prior MAP/ML as a
  prior-average benchmark, then state the two questions early. Conditional
  feasible-fiber reconstruction follows from the strong reconstruction premise;
  original-unrestricted likelihood given only truth-feasibility remains the
  substantive pointwise comparison. Preserve evidence labels and distinguish
  source-faithful observation models.

## Open questions for human review

1. The claim matrix `tab:claims` is prose-level synthesis; the row-1 evidence is
   a published premise plus a kernel-checked *separation* statement, not a Lean
   proof of the reconstruction theorem itself. Confirm this is the intended
   reading of the proof-to-claim policy.
2. `ex:worked-bayes` is intentionally abstract (no assembly instance). If a
   concrete assembly instance is preferred, the natural one is the `AABB/ABAB`
   identifiability failure plus the `W_1` strict failure; both are already in the
   text, so the abstract example was kept short.
3. The paragraph on the choice of prior states a sufficient modeling rationale
   for the uniform-over-rotation-classes prior. Whether to also discuss
   nonuniform priors that nevertheless share the ML argmax on a restricted
   observation family (noted in the existing text after `thm:bayes-optimal`) is
   a presentation choice.
