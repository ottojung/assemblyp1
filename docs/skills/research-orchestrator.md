# Research orchestrator

Use this skill when the task is broader than one already-specified lemma or source lookup. The orchestrator owns prioritization, decomposition, synchronization, reconciliation, verification, and integration.

## Read first

Before dispatching work, read:

1. `AGENTS.md`;
2. `docs/open-problem.md`;
3. the locked literature ground truth identified by the intent records;
4. `docs/research-orchestration.md`;
5. `docs/skills/exploration.md`;
6. relevant issues, active PRs, and source papers.

Consult `docs/formalization-plan.md` only when the work actually concerns formalization. Do not use remembered repository state when live state is available.

## Orchestrator procedure

### Recover the graph and portfolio

Recover existing issues, active PRs, worker status, failed approaches, and unresolved ambiguities before starting new work.

Maintain two views:

- the durable dependency graph of questions/results, often represented by issues; and
- a live portfolio of materially different research approaches, including temporary packets that may not yet have issues.

The issue graph is durable memory. The portfolio is the larger search surface from which agents are allocated. The portfolio is for allocating effort, not judging truth.

### Establish or generate the frontier

Once the initial source-faithful statement is sufficiently pinned down, treat mathematical exploration rather than intermediate formalization as the default research mode. If one blocking question is clearly dominant, state it precisely. Otherwise generate several genuinely different candidate approaches or scaffold questions and use `exploration.md` to compare them.

Do not force a predetermined proof/counterexample split or reuse a static roadmap merely because it already exists.

### Build packets, not vague prompts

Each delegated packet must specify an objective, permitted assumptions, non-goals, required evidence, deliverable, stop conditions, and handoff format. A worker must be able to fail usefully.

Prefer sharply different packets, targeted independent replications, or cheap evaluators over several workers all asked to "solve" the same thing.

### Keep the shared Lubko pool near useful saturation

When Lubko is available, the orchestrator should normally **delegate broad substantive exploration rather than perform it all itself**. Across all concurrent AssemblyP1 orchestrators, aim to keep the shared pool close to **5 useful active agents** whenever the live frontier supports that many independent packets.

Use the scheduled skill's lightweight live pool snapshot when practical. New AssemblyP1 agents must use an `AssemblyP1:` title prefix. Launch only into clearly free shared capacity; do not turn per-agent recounting into the research task. Do not interpret the target as "five per orchestrator."

If useful capacity is idle, broaden the frontier rather than assuming the current open issue/PR is the only work available. Generate materially different packets from the published target and live portfolio and launch a sensible batch when capacity is clearly available. Agent packets do not require pre-existing GitHub issues; promote them into durable issues/docs/PRs only when their question, result, obstruction, dependency, or recovery state deserves persistence.

The orchestrator's comparative advantage is coordination: choose and diversify packets, steer agents, stop unproductive duplication, compare exact propositions and evidence, reconcile results, and decide the next wave. Direct work is appropriate for tiny deterministic operations, inherently serial coordination, cheap spot checks, and final review/reconciliation.

Do not create agents merely to satisfy a quota, and do not send several agents near-identical vague prompts. Pool utilization is secondary to making and integrating research progress.

AssemblyP1 imposes a hard **repository-wide** cap: **no more than 5 delegated agents may be actively working in parallel across all concurrent orchestrators**. Before launching a new `lubko-agent`, inspect durable worker/status state and account for already-active AssemblyP1 agents. If five are active, keep additional packets queued in the shared portfolio/frontier and launch them only after a slot is durably known to be free.

This project-specific limit overrides Lubko's generic "use as many agents as useful" guidance.

### Keep write surfaces isolated

Each write-capable worker gets its own branch/worktree. Research-only workers may return issue comments or source notes without a code branch. Open draft PRs early when a branch contains durable work worth reviewing.

### Evaluate before escalating effort

For each promising approach, ask for the cheapest evaluator that can materially change its priority:

- primary-source check;
- small hand example;
- bounded exact computation;
- counterexample attempt;
- Lean micro-lemma/typecheck;
- independent derivation;
- assumption-strength comparison.

Use evaluator failures as inputs to the next version of the approach. Revise, weaken, split, combine, block, or retire routes rather than repeatedly retrying them unchanged.

### Track claims explicitly

For every important worker output, record whether it is a source fact, modeling decision, conjecture, computational result, mathematical proof, or kernel-checked result. Record assumptions separately from conclusions.

Portfolio rank, worker confidence, and agent consensus do not change epistemic class.

### Reconcile before integration

After overlapping work completes, compare exact propositions. Normalize notation and inspect quantifiers, candidate genome class, genome equivalence, fixed-versus-variable length, latent placements, observed multiplicities, and probability model.

When outputs conflict, classify whether:

- one worker is mistaken;
- assumptions differ;
- source conventions differ;
- evidence strength differs;
- the issue has forked into distinct valid questions.

Never resolve a conflict by vote.

### Evolve the survivors

Do not simply assign more agents to the same successful-looking route. Improve promising approaches by mutating assumptions, changing representation, combining compatible insights, extracting structural lemmas from computation, or turning verifier failures into corrected statements.

Record parent/descendant relationships when the history is useful.

### Turn results into a better frontier

The orchestrator's most important output is not a prose summary; it is a better next research state.

Preserve stable discoveries in notes/issues, turn unresolved structural ideas into focused issues, turn suspicious lemmas into cheap evaluator packets, generate scaffold problems when they would reveal structure, and retire routes whose failures are now understood.

Do not promote stable definitions or lemmas to Lean by default. Substantial formalization is reserved for pinning down the initial published statement and verifying a plausible complete proof or counterexample. Tiny Lean experiments may be used as bounded evaluators without creating a formalization queue.

### Verify and review

Independently check primary-source claims, rerun important searches, inspect Lean assumptions, run `lake build`, check CI, and review PR diffs. The agent that produced a result is not its independent reviewer.

The orchestrator itself owns final PR review and integration judgment; do not delegate those responsibilities to `lubko-agent`.

## Research ledger format

A concise issue/PR handoff may contain:

```text
Question:
Result:
Epistemic class:
Assumptions:
Evidence:
Evaluator feedback:
Failed/ruled-out approaches:
Portfolio status:
Dependencies unblocked:
Recommended next packet:
```

Use this as a guide, not bureaucracy.

## When to stop or redirect a branch

Stop or redirect when:

- it assumes something unavailable in the published model;
- source ambiguity invalidates its premise;
- an evaluator falsifies its key step;
- it duplicates another branch without independent-value justification;
- effort is growing without improved evidence or discrimination;
- a different representation or scaffold now has clearly higher information value;
- the work has reached a stable handoff better served by another role.

Preserve useful negative results before stopping.

## Completion

A research-orchestration cycle is complete when it has materially improved the durable research state: for example by reconciling results, establishing or refuting a claim, improving the model/source interpretation, integrating trustworthy work, or otherwise shrinking uncertainty.

Launching workers, filling the pool, or merely collecting worker summaries is not by itself completion.
