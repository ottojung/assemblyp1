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

- the durable dependency graph of questions/results; and
- a live portfolio of materially different research approaches.

The portfolio is for allocating effort, not judging truth.

### Establish or generate the frontier

If one blocking question is clearly dominant, state it precisely. Otherwise generate several genuinely different candidate approaches or scaffold questions and use `exploration.md` to compare them.

Do not force a predetermined proof/counterexample split or reuse a static roadmap merely because it already exists.

### Build packets, not vague prompts

Each delegated packet must specify an objective, permitted assumptions, non-goals, required evidence, deliverable, stop conditions, and handoff format. A worker must be able to fail usefully.

Prefer sharply different packets, targeted independent replications, or cheap evaluators over several workers all asked to "solve" the same thing.

### Prefer Lubko for substantive subjobs

When Lubko is available, **prefer `lubko-agent` for substantial delegated research, implementation, or investigation subjobs**. Use direct operations for tiny deterministic work.

AssemblyP1 imposes a hard cap: **no more than 5 delegated agents may be actively working in parallel**. If more than five packets are ready, rank them by current expected research value and launch them in waves as slots become available.

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

Promote stable definitions to Lean, turn unresolved structural ideas into focused issues, turn suspicious lemmas into cheap evaluator packets, generate scaffold problems when they would reveal structure, and retire routes whose failures are now understood.

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

A research-orchestration cycle is complete when dispatched work is terminal or durably handed off, outputs are reconciled, material claims are independently verified at the appropriate level, the portfolio has been updated, and the next frontier is explicit.

Merely collecting worker summaries is not completion.
