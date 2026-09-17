# assemblyp1 scheduled-work itinerary

## Scope

This is the entry point for recurring scheduled work on:

<https://github.com/ottojung/assemblyp1>

Before acting, read and obey:

- `AGENTS.md` in this repository;
- `docs/skills/scheduled.md` in this repository;
- <https://github.com/ottojung/lubko/blob/main/docs/SKILL.md> when Lubko is the execution platform.

## Work selection

Prefer, in order:

1. recover abandoned issue-tracked work that has useful partial progress;
2. continue an already-open assemblyp1 PR that needs implementation, verification, or review;
3. select an actionable open issue;
4. if no issue exists, advance the earliest unresolved item in `docs/formalization-plan.md`, first creating a focused GitHub issue so the work has durable coordination state.

Favor source-model formalization and validation before speculative proof attempts unless a concrete counterexample/proof opportunity is already well defined.

## Branching and review

- Work on an isolated branch, normally `agent/<short-topic>`.
- Open a draft PR to `main` early for substantial work.
- Do not merge a scheduled agent's PR into `main` merely to keep the schedule moving; `main` is the human review boundary unless a later authoritative intent record changes that policy.
- It is fine for multiple independent research PRs to coexist when they do not conflict.

## Completion

For issue-tracked scheduled work, mark the orchestrator status `completed` when:

- the intended scoped research/formalization change is committed and pushed;
- `lake build` succeeds on the exact proposed head;
- repository CI is green or any remaining CI blocker is documented as external;
- the PR contains enough explanation and citations for a reviewer to judge source fidelity;
- no known correctness blocker is being hidden.

A completed scheduled item may remain as an open PR awaiting human review. The recurring task should then choose another actionable item on a future invocation.
