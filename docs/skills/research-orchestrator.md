# Research orchestrator

Use this skill when the task is broader than one already-specified lemma or one already-specified source lookup. The orchestrator owns decomposition, synchronization, reconciliation, verification, and integration.

## Read first

Before dispatching work, read:

1. `AGENTS.md`;
2. `docs/open-problem.md`;
3. `docs/formalization-plan.md`;
4. `docs/research-orchestration.md`;
5. the relevant issues, active PRs, and source papers.

Do not use remembered repository state when live state is available.

## Orchestrator procedure

### Establish the current frontier

Write down the smallest currently blocking question. State its exact dependence on the published open problem. If the question contains an unresolved source ambiguity, resolve or isolate that ambiguity before proof work builds on it.

### Build packets, not vague prompts

Each delegated packet must specify an objective, permitted assumptions, non-goals, required evidence, deliverable, stop conditions, and handoff format. A worker must be able to fail usefully.

Prefer several sharply different packets to several workers all asked to "solve" the same thing. Useful parallelism includes independent source transcription, proof versus counterexample search, theorem mathematics versus Lean API design, and search implementation versus completeness/symmetry analysis.

### Keep write surfaces isolated

Each write-capable worker gets its own branch/worktree. Research-only workers may return issue comments or source notes without a code branch. Open draft PRs early when a branch contains durable work worth reviewing.

### Track claims explicitly

For every important worker output, record whether it is a source fact, modeling decision, conjecture, computational result, mathematical proof, or kernel-checked result. Record assumptions separately from conclusions.

Do not let downstream workers cite "agent X found Y" when the durable evidence is a paper passage, executable experiment, or Lean theorem; point them to the actual evidence.

### Reconcile before integration

After parallel work completes, compare the exact propositions. Normalize notation and inspect quantifiers, candidate genome class, genome equivalence, fixed-versus-variable length, latent placements, observed multiplicities, and probability model. These distinctions are especially likely to create false agreement in assemblyp1.

When outputs conflict, classify the conflict:

- one worker is mistaken;
- the workers used different assumptions;
- the sources genuinely use different conventions;
- the issue has forked into two valid but distinct questions.

Never resolve a conflict by vote.

### Turn results into a smaller frontier

The orchestrator's most important output is not a summary; it is a better next research graph. Promote stable definitions to Lean, split large proof obligations into lemmas, turn suspicious lemmas into finite-search targets, and create focused issues for unresolved dependencies.

### Verify and review

Independently check primary-source claims, rerun important searches, inspect Lean assumptions, run `lake build`, check CI, and review PR diffs. The agent that produced a result is not its independent reviewer.

## Research ledger format

A concise issue/PR handoff should contain:

```text
Question:
Result:
Epistemic class:
Assumptions:
Evidence:
Failed/ruled-out approaches:
Open ambiguities:
Dependencies unblocked:
Recommended next packet:
```

Use this structure as a guide, not as bureaucracy. Omit empty fields when they add no information.

## When to stop a branch

Stop or redirect a worker when:

- it is proving a theorem under assumptions unavailable in the published model;
- a source ambiguity invalidates its premise;
- a small counterexample falsifies the key lemma;
- it is duplicating another branch without independent-value justification;
- the search space has exploded and no completeness or pruning argument is emerging;
- the work has reached a stable handoff point better served by a different role.

Preserve useful negative results before stopping.

## Completion

A research-orchestration cycle is complete when all dispatched work is terminal, its outputs are reconciled, durable artifacts have been updated, important claims are independently verified at the appropriate level, and the next frontier is explicit. Merely collecting worker summaries is not completion.
