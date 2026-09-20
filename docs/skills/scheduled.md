# Scheduled research orchestrator

This guide is adapted from Lubko's reusable scheduled-orchestrator protocol. It defines the durable coordination mechanics for recurring ChatGPT invocations working on assemblyp1. Project-specific work selection and completion policy live in [`docs/skills/itinerary-assemblyp1.md`](itinerary-assemblyp1.md); research decomposition and reconciliation live in `docs/research-orchestration.md` and `docs/skills/research-orchestrator.md`.

Canonical Lubko references:

- <https://github.com/ottojung/lubko/blob/main/docs/SKILL.md>
- <https://github.com/ottojung/lubko/blob/main/docs/skills/scheduled.md>

Every scheduled AssemblyP1 run operates through Lubko for worker-pool discovery even if its eventual local task is tiny. Read and obey the canonical Lubko instructions as well as this repository's `AGENTS.md`.

## Lightweight startup: inspect and opportunistically fill the Lubko pool

Every scheduled run should take a quick live snapshot of the AssemblyP1 Lubko pool near startup. This is infrastructure support for the research run, **not a blocking gate and not the main task**.

1. Through Lubko's Supabase transport, run `lubko-agent list --running --json` on `phoebe-dev` and poll that root job to terminal when the transport allows it.
2. Identify running AssemblyP1 agents. New agents are identified by a title beginning `AssemblyP1:`. For legacy sessions created before this rule, also count a running agent whose cwd clearly belongs to AssemblyP1 (for example `/workspace/assemblyp1-...`).
3. Reconcile that snapshot with any agent handles mentioned in durable status. Live Lubko state is authoritative for whether an agent is actually running; durable comments provide recovery context.
4. Compute an approximate number of clearly free slots under the repository-wide cap of five.
5. If useful slots are available, generate materially different packets from the whole live frontier and launch a **small batch** into clearly free capacity. Do not limit packet generation to open issues/PRs.
6. Create new agents with titles of the form `AssemblyP1: <short packet name>`. A created-but-idle agent does not count toward saturation; start it with a substantive prompt.
7. Do **not** re-list after every launch. Re-count after a batch, before a later launch wave, or when there is specific reason to suspect the shared count changed materially. If a race temporarily overfills the pool, stop only this invocation's own excess newly launched agents when that can be determined safely.
8. If live recounting or polling becomes unavailable, uncertain, or blocked, **stop launching additional agents whose capacity cannot be established, record the uncertainty briefly, and continue useful research/reconciliation/local work that does not risk exceeding the cap**. Pool bookkeeping failure must not terminate the research run.
9. Saturation is a soft operational target. Prefer keeping useful capacity occupied, but never let agent-management plumbing consume the run or displace higher-value mathematical work.

The purpose of this check is to keep parallel research healthy with low overhead. It is not a proof obligation that must be fully discharged before useful research can proceed.

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
- the **research/repository progress that matters**;
- only those recovery handles needed for another invocation to continue safely.

Do not put credentials, routine pool counts, launch/recount narration, root-job chatter, or other orchestration plumbing in the comment unless it is materially needed to recover blocked work.

When an orchestrator has delegated subjobs, mention workers only when their identity/result/recovery handle matters to the research state. A report whose main accomplishment is that workers were launched, counted, or verified running is not useful progress reporting. Before a new launch wave, reconcile durable worker state with observable Lubko status as practical and obey the repository-wide cap.

If multiple marked comments exist because of a race, the most recently updated marked comment is canonical. Immediately after claiming or inheriting work, re-read it; if another owner won the race, yield.

While retaining ownership, refresh the canonical status at least once every five minutes. A `working` status with no update for ten minutes may be treated as abandoned and inherited according to the project itinerary. Before every refresh, re-read ownership and yield if another invocation has taken over.

## Recovery

On every scheduled run, assume an earlier invocation may have been interrupted. Recover from observable state:

- issue and canonical status comment;
- branches, commits, and open PRs;
- CI status;
- Lubko jobs, managed agents, worktrees, and logs when present;
- the formalization plan, research graph, and intent records.

Preserve useful partial work. Never rely on remembered agent IDs, branches, completion state, or a remembered Lubko blocker without checking them again in the current run.

## Research discipline

A scheduled agent must continue doing useful work rather than merely reporting that work exists. However, formalization fidelity is a completion condition, not an inconvenience: when a source definition is unclear, record the ambiguity and cite it rather than silently choosing a convenient theorem.

For broad or multi-worker research, apply `docs/skills/research-orchestrator.md`: create narrow work packets, keep epistemic classes explicit, run genuinely independent tracks in parallel when useful, reconcile exact propositions before integration, and preserve useful negative results. Scheduled recurrence is a transport/lifecycle mechanism; it does not replace the research protocol.

Push work branches early, open a draft PR early for substantial changes, keep recovery state current, and verify the exact proposed head with `lake build` and repository CI.
