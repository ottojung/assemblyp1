# Review: cell entry inaccuracies for issue #267

_Status: review note, 2026-10-12. Branch: `review/267-bayes-reconciliation`.
This note flags inaccuracies in the #267 cell entry of
`docs/research-framework-255.md` on branch `agent/96b26e582cdf-issue255-framework`.
It does not modify the framework doc (owned by the umbrella coordination)._

## Current cell entry

| Issue | Cell / question | Regime | State | Owner |
|---|---|---|---|---|
| #267 | reconcile finite ML counterexamples with Bayes optimality / conditional feasibility | conditional inference | OPEN — active | agent d5f48efb876a |

## Flagged inaccuracies

### 1. Owner field is incomplete

**Current**: `agent d5f48efb876a`

**Issue**: The cell lists a single owner, but the work has been continued by
agent `3d76ddd37273` (this review). The original agent's work lives on branch
`audit-267-finite-ml-vs-conditional-bayes`; the review work lives on
`review/267-bayes-reconciliation`. The cell should either list both agents or
note that the cell has multiple contributors.

**Evidence**: `git log origin/audit-267-finite-ml-vs-conditional-bayes` shows
commits by agent d5f48efb876a; this review branch adds commits by agent
3d76ddd37273.

### 2. State field is imprecise

**Current**: `OPEN — active`

**Issue**: The state does not reflect the substantial completed work. The
following artifacts exist and are verified:
- `docs/bayes-optimality-conditional-feasibility-267.md` (foundational note)
- `docs/audit-267-finite-ml-vs-conditional-bayes.md` (witness audit)
- `AssemblyP1/FiniteMapOptimality.lean` (kernel-checked Bayes/MAP theorem)
- `scripts/audit-267-independent-checks.py` (independent verification, 30/31 pass)
- Paper changes across all sections

A more accurate state would be: `OPEN — substantial work done, review pending`
or `in review`. The `OPEN` flag is correct (the issue is not closed), but
`active` undersells the progress.

**Evidence**: All artifacts listed above are on
`origin/audit-267-finite-ml-vs-conditional-bayes` and have been independently
verified by this review.

### 3. Missing artifact reference

**Current**: The cell has no artifact/branch reference.

**Issue**: A reader consulting the framework doc cannot find the work without
knowing the branch name. The cell should reference the primary branch
(`audit-267-finite-ml-vs-conditional-bayes`) and the review branch
(`review/267-bayes-reconciliation`).

**Evidence**: Standard practice in the framework doc is to reference artifacts
(see other cells in the matrix).

### 4. Cell description could be more specific

**Current**: `reconcile finite ML counterexamples with Bayes optimality / conditional feasibility`

**Issue**: The description is accurate but does not distinguish the three
distinct theorem/experiment tasks that have been completed:
1. Finite-candidate Bayes/MAP optimality theorem (kernel-checked)
2. Event `E = F(G,R)` and conditional experiment analysis
3. `2×2` counterexample: infallible-on-`E` rule loses to MAP

A more specific description would note that all three tasks are complete and
verified.

## Recommended updated cell entry

| Issue | Cell / question | Regime | State | Owner |
|---|---|---|---|---|
| #267 | reconcile finite ML counterexamples with Bayes optimality / conditional feasibility — tasks (1) Bayes/MAP theorem, (2) event E=F(G,R), (3) 2×2 counterexample all complete; W1-W6 witnesses audited; paper changes drafted | conditional inference | OPEN — substantial work done, review pending | agent d5f48efb876a + agent 3d76ddd37273 |

## Coordination note

This inaccuracy report is filed on `review/267-bayes-reconciliation` and does
not modify the framework doc on `agent/96b26e582cdf-issue255-framework`. The
umbrella coordination agent should update the cell entry when appropriate.
