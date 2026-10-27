# Issue #268 current-state reconciliation

## Verified repository state

- Project remote: `https://github.com/ottojung/assemblyp1.git`.
- Current `origin/main`: `3decc39b4f8b5e187dc3df1b8c56720b4615045a`.
- The #268 manuscript milestone is present on current main: the Bayes/MAP
  theorem, both questions, the source-scoped Not-So-Greedy guarantee, and the
  uniform-start distinction are already in `paper/sections/03-open-question.tex`
  and `paper/sections/02-model.tex`. Current main includes prior #268/ #265
  claim-labeling and singleton-result changes.
- A further ready branch exists at
  `origin/agent/m207b4xxQBSjv47yF8Z6FF-issue268-ready`, commit
  `54aa90cb`; it descends from `ce15e3da` and contains the manuscript edits
  `7f091e62` plus a verification note. `7f091e62` is **not** an ancestor of
  current main. It clarifies Bayes-average versus pointwise motivation and the
  truth-dependent event caveat. No PR or merge was independently verified.
- The prior handoff's audit commit `3378697142088a2e4d3a51c38a70179e7644ff9f`
  is present on `origin/agent/issue268-claim-audit-27FfIFGKIMwR6GpfJ13uOX-doubly`,
  not current main. It correctly records the Lean boundary: the abstract
  conditional implications are kernel checked, while historical decoder
  correctness remains an external 2016 premise.

## Checks and limitations

The repository identity and refs above were verified with Git against `origin`.
`gh issue view 268 --repo ottojung/assemblyp1 --comments` was attempted but
failed because `gh` is unavailable. The local `/workspace/board-log.json` has
no issue-268 comment entries, so newest board comments and prior handoffs could
not be independently reconciled. The ready-branch prose records successful
paper and documentation checks, but those checks were not rerun during this
state-only reconciliation. No independent review, PR integration, or merge
state was verified.

## Handoff

The main-branch baseline already covers most narrative requirements, and the
remaining ready-branch changes are small but not merged. Reconcile the current
issue and #265 comments; then have the integration owner review and merge the
ready branch (or port its two prose edits) if still desired, run the paper
build and document CI on the resulting main-based change, and obtain independent
review. Keep #268 open until those board acceptance gates are verified.
