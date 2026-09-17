# assemblyp1 scheduled-work itinerary

## Scope

This is the entry point for recurring scheduled work on:

<https://github.com/ottojung/assemblyp1>

Before acting, read and obey:

- `AGENTS.md` in this repository;
- `docs/research-orchestration.md` for the research graph and reconciliation protocol;
- `docs/skills/research-orchestrator.md` for broad or multi-worker research;
- `docs/skills/scheduled.md` in this repository;
- <https://github.com/ottojung/lubko/blob/main/docs/SKILL.md> when Lubko is the execution platform.

## Work selection

Prefer, in order:

1. recover abandoned issue-tracked work that has useful partial progress;
2. continue an already-open assemblyp1 PR that needs implementation, verification, reconciliation, or review;
3. select an actionable open issue on the current research frontier;
4. if no issue exists, advance the earliest unresolved item in `docs/formalization-plan.md`, first creating a focused GitHub issue so the work has durable coordination state.

When an issue is too broad for one worker, decompose it into narrow research packets/issues and keep their dependencies explicit. Favor source-model formalization and validation before speculative proof attempts unless a concrete counterexample/proof opportunity is already well defined. Maintain positive and negative tracks in parallel when both can materially reduce uncertainty.

## Branching and review

- Work on an isolated branch, normally `agent/<short-topic>`.
- Open a draft PR to `main` early for substantial work.
- Do not merge a scheduled agent's PR into `main` merely to keep the schedule moving; `main` is the human review boundary unless a later authoritative intent record changes that policy.
- It is fine for multiple independent research PRs to coexist when they do not conflict.
- Reconcile overlapping research outputs before treating either branch as a dependency of later proof work.

## Completion

For issue-tracked scheduled work, mark the orchestrator status `completed` when:

- the intended scoped research/formalization change is committed and pushed;
- all delegated packets for this scoped cycle are terminal and their results reconciled;
- `lake build` succeeds on the exact proposed head when Lean code changed;
- repository CI is green or any remaining CI blocker is documented as external;
- the PR/issue contains enough explanation, evidence classification, and citations for a reviewer to judge source fidelity and mathematical status;
- no known correctness blocker is being hidden.

A completed scheduled item may remain as an open PR awaiting human review. The recurring task should then choose another actionable item on a future invocation.
