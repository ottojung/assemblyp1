# Scheduled research orchestrator

This guide is adapted from Lubko's reusable scheduled-orchestrator protocol. It defines the durable coordination mechanics for recurring ChatGPT invocations working on assemblyp1. Project-specific work selection and completion policy live in [`docs/skills/itinerary-assemblyp1.md`](itinerary-assemblyp1.md); research decomposition and reconciliation live in `docs/research-orchestration.md` and `docs/skills/research-orchestrator.md`.

Canonical Lubko references:

- <https://github.com/ottojung/lubko/blob/main/docs/SKILL.md>
- <https://github.com/ottojung/lubko/blob/main/docs/skills/scheduled.md>

When operating through Lubko, obey those canonical instructions as well as this repository's `AGENTS.md`.

## Disposable invocations, durable state

A scheduled invocation may disappear at any time. Conversation state must never be the only record of ongoing work. Durable state belongs in the target issue, branch/PR, commits, repository documentation, and any Lubko job/agent handles used to execute work.

## Issue ownership

When scheduled work is tracked by a GitHub issue, maintain one durable status comment containing the marker:

```text
<!-- assemblyp1-orchestrator-status -->
```

The status should make these facts unambiguous:

- `state`: `working` or `completed`;
- `owner`: a fresh short identifier for the current invocation;
- useful recovery resources: branch, PR, Lubko agent/job IDs, worktree/cwd, and other durable handles.

Do not put credentials or unnecessary logs in the comment.

When an orchestrator has delegated subjobs, the canonical status must also list the currently active AssemblyP1 delegated-agent handles/resources well enough for another scheduled invocation to account for them. Remove or mark workers terminal as soon as their status is known. Before launching a new delegated agent, reconcile this durable worker state with observable Lubko job status and obey the repository-wide concurrency cap from the AssemblyP1 itinerary/intent records.

If multiple marked comments exist because of a race, the most recently updated marked comment is canonical. Immediately after claiming or inheriting work, re-read it; if another owner won the race, yield.

While retaining ownership, refresh the canonical status at least once every five minutes. A `working` status with no update for ten minutes may be treated as abandoned and inherited according to the project itinerary. Before every refresh, re-read ownership and yield if another invocation has taken over.

## Recovery

On every scheduled run, assume an earlier invocation may have been interrupted. Recover from observable state:

- issue and canonical status comment;
- branches, commits, and open PRs;
- CI status;
- Lubko jobs, managed agents, worktrees, and logs when present;
- the formalization plan, research graph, and intent records.

Preserve useful partial work. Never rely on remembered agent IDs, branches, or completion state without checking them.

## Research discipline

A scheduled agent must continue doing useful work rather than merely reporting that work exists. However, formalization fidelity is a completion condition, not an inconvenience: when a source definition is unclear, record the ambiguity and cite it rather than silently choosing a convenient theorem.

For broad or multi-worker research, apply `docs/skills/research-orchestrator.md`: create narrow work packets, keep epistemic classes explicit, run genuinely independent tracks in parallel when useful, reconcile exact propositions before integration, and preserve useful negative results. Scheduled recurrence is a transport/lifecycle mechanism; it does not replace the research protocol.

Push work branches early, open a draft PR early for substantial changes, keep recovery state current, and verify the exact proposed head with `lake build` and repository CI.
