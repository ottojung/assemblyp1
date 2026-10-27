# #265 status reconciliation (2026-10-27)

Owner: agent-XWuMFrLyO8sdaX32ulshT4-indicate
Repository: `https://github.com/ottojung/assemblyp1` (fresh clone; `origin/main`
was `3decc39b4f8b5e187dc3df1b8c56720b4615045a`)
Purpose: reconcile live work and project theorem scopes before further
manuscript/deck integration. This is a review note, not a new statistical
theorem or a replacement for the open matrix.

## Live identity and work state

GitHub reuses a number between an issue and a pull request after an issue is
converted. The API's `/issues/265`, `/issues/269`, and `/issues/281` now resolve
to closed, merged PR records about unrelated tasks. Do not use those endpoint
numbers alone to infer the status of the statistical work. The active linked
integration item is PR [#406](https://github.com/ottojung/assemblyp1/pull/406),
open at `ffb44ef2648aa3e4f21ef7cf3edffef1a946a95e`, base `3decc39`. Its diff is
four files: early paper introduction, programmer deck, exact-rational verifier,
and a focused source note. `origin/main` does not contain that change yet.

The newest #265-linked comment identifies the #268 conditional-inference
distinction as already included in PR #406. It requires keeping the
truth-dependent feasible-fiber experiment distinct from ordinary R-only ML:
the 2016 reconstruction premise is external, and the singleton conditional
posterior corollary is paper-level, not a Lean theorem. No parallel paper
rewrite should duplicate these changes.

## Verified claim-to-source map on current main

| Statistical claim | Current source / exact endpoint | Scope and epistemic status |
| --- | --- | --- |
| Uniform random circular starts induce `p_G(w)=spec_L(G)(w)/|G|`; ordered iid data likelihood is `prod_i p_G(R_i)` | `AssemblyP1/FiniteReadRecoveryGenome.lean`; paper `05-population.tex` finite-recovery adapter | Oriented, error-free reads; rotations induce the same law. Do not identify with MB09's approximations. |
| Finite MAP is optimal under a finite prior and zero-one loss; uniform prior gives ML | `AssemblyP1/FiniteBayesDecision.lean`: `chooseMAP_optimal`, `chooseMAP_optimal_randomized`; paper `thm:bayes-optimal` | Prior-average only. A fixed truth or different loss/prior is not covered by this slogan. Ties require a consistent MAP choice. |
| Prior-average iid MAP success is nondecreasing with one extra read | `AssemblyP1/IidMapMonotonicity.lean`: `iid_map_success_monotone`; generalized decision refinement in `FiniteBayesDecision` | Ignore the extra read. Not a pointwise/per-truth claim. |
| Per-truth exact ML success can decrease: `AAC` vs `AAAC`, `L=2`, strict-success `2/3` at `n=1`, `4/9` at `n=2` | `AssemblyP1/NonmonotonicityWitness281.lean`: `success_not_monotone`; `05-population.tex` `prop:nonmonotone` | Checked with strict-win tie handling; no positive-probability ties for `n>=1`. This is a different quantity from prior-average optimal success. |
| Finite iid likelihood error decays for a finite distinguishable family | `AssemblyP1/FiniteReadRecovery.lean`: `eventProb_wrong_le_exp`, `eventProb_wrong_le_exp_of_identifiable`; genome adapters and the primitive-P2 explicit result are separate modules | Error events count ties as errors; zero support is division-free. Abstract finite-family or explicit primitive-P2 conditions matter. Not a claim of monotone per-truth success. |
| Population exact log-likelihood is maximized at the truth, equality iff laws agree | `AssemblyP1/PopulationUniqueness.lean`: `population_maximizer_unrestricted`, `population_tie_iff_distribution_eq_unrestricted`; paper `lem:gibbs` | Kernel-checked unrestricted population maximality. Equality only identifies a law, not necessarily a genome. |
| Population uniqueness up to rotation for primitive-P2 candidates | `PopulationUniqueness.population_unique_ML_up_to_rotation` | Hypotheses include primitive/P2 oriented candidates; the Lean statement carries `EulerianCycleObstruction`. Do not report generic unrestricted structural identifiability. |
| Strong consistency from SLLN + KL for a finite identifiable family | Paper `05-population.tex`, `prop:strong-consistency` | Standard statistics, explicitly paper-level/not Lean-proved. Infinite reads mean a limit; this proposition itself gives no finite `n`. Separate kernel-checked Hellinger bound supplies scoped rates. |
| Exact fixed-sample classification / structural theorem | `docs/remaining-open-matrix-255.md` current addenda and source modules it cites | Distinguish oriented exact multinomial (#258/#251), RC full-overlap (#260), §6.1 product-binomial (#259), and §6.2 flow/objective transport (#261). The matrix leaves broader cells open. |

## Model boundaries that must remain visible

1. The AAC/AAAC illustration uses circular, oriented, error-free `L=2`
   reads with independent uniform starting positions and exact iid likelihood.
   It is a finite-sample witness, not a defect in ML and not a result about a
   different objective.
2. MB09 §6.1 is a fixed-`N` product-binomial approximation; §6.2 is a flow
   likelihood over its modeled graph/domain. Neither should be silently
   substituted for exact product likelihood over genome read laws.
3. Theorem statements in Lean are not automatically source-faithful MB09
   classifications. The current matrix explicitly leaves source graph
   correspondence, general §6.2 candidate classification, and some RC and
   variable-length axes unresolved.
4. `I_s`/historical coverage and bridging, placement-based project predicates,
   and truth-dependent feasible-fiber conditioning are distinct predicates or
   experiments. The 2016 reconstruction guarantee remains an external source
   premise rather than a Lean-proved AssemblyP1 theorem.
5. Neither a limiting consistency theorem nor an exponential asymptotic rate
   alone answers an unrestricted finite-sample “how many reads for 99%?”
   question. Use a finite-family bound only with its explicit candidate set,
   read model, affinity/separation assumptions, and tie convention.

## Exact review state and validation in this invocation

- Verified `git ls-remote`: `main=3decc39...`, PR #406 head
  `ffb44ef...`, #399 head `337fb3a...`, #405 head `a024033...`.
- GitHub PR API: #406 is open, unmerged, mergeable, base `3decc39...`; no
  requested reviewers. The #265-linked checkpoint at 04:47 UTC reported zero
  submitted reviews and a `signed-commits` failure due to unsigned earlier
  commits (tip signature alone does not clear that check). Recheck exact-head
  CI/reviews before integration.
- Ran `python3 scripts/check-research-docs.py`: PASS.
- Audited PR #406's four-path diff and compared its figure note from the exact
  PR ref. No overlap-safe source edit was identified; no source or manuscript
  changes were made here.
- GitHub REST read endpoints were available through `webfetch`; `gh` is not
  installed. This runtime has no usable authenticated API write path for
  posting the requested Antonina checkpoint. This document is the durable
  local handoff; the board update remains to be posted by an invocation with
  board write access.

## Next

Review the open PR #406 at its exact current head and resolve its full commit
signature gate; check whether PR #399/#405 have since merged and refresh the
#255 matrix from current `main`. Once #406 is integrated, continue only on a
specific unowned acceptance gap (including the maintained biologist deck if
not already updated), while preserving the #254 audience and theorem/model
scope distinctions above. Keep statistical classification questions open
where the source-faithful candidate domain remains unresolved.
