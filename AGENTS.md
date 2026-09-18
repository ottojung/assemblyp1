# Development rules

This repository is a mathematical research project with a Lean verification boundary. Its purpose is to state the genome-assembly open problem documented in `docs/open-problem.md` faithfully, explore it aggressively, and, if a plausible proof or counterexample is found, formally verify the final result.

## Lean

Lean is **not** the default medium for proof discovery. The intended cadence is:

1. formalize the source-faithful initial statement;
2. do the middle research phase primarily through mathematical notes, computation, examples, counterexamples, reductions, and proof sketches;
3. return to substantial Lean formalization once there is a plausible, coherent proof or counterexample in notes that is worth verifying.

Small Lean experiments are still welcome when they are the cheapest way to test a delicate claim. Keep them bounded; do not turn a successful micro-check into an eager bottom-up formalization program merely because intermediate definitions or lemmas look stable.

- Use the Lean toolchain pinned by `lean-toolchain` and the Mathlib revision pinned in `lakefile.lean`.
- Run `lake build` before committing Lean changes.
- Keep `autoImplicit` disabled.
- Formalize only what is needed to state the published problem faithfully, what a mature final argument actually needs, or what a deliberately tiny evaluator needs. Do not build intermediate Lean infrastructure merely because it may be useful later.
- Do not change definitions merely to make a desired theorem provable.
- Do not introduce `axiom`, `sorry`, or `admit` into the library to claim progress on the open problem. A conjecture should be represented as a `Prop` until it is actually proved.
- Computational searches for counterexamples are welcome, but a finite search is evidence unless its completeness is itself proved.

## Source fidelity

The distinction between the biological/sequencing model and the theorem proved about that model is part of correctness.

- Cite the paper or section that justifies every nontrivial modeling choice.
- Keep unresolved interpretation questions explicit in `docs/formalization-plan.md` or an issue.
- In particular, do not silently assume whether “the maximum-likelihood sequence is the true sequence” means merely that the truth is a maximizer or that it is unique up to cyclic shift. Resolve that from the cited model.
- A formally proved statement only counts as settling the published open problem after the repository documents why the formal assumptions and conclusion match the published statement.

## Research orchestration

Substantial research work should follow `docs/research-orchestration.md`. Operational worker guides live under `docs/skills/`, with `docs/skills/research-orchestrator.md` as the entry point for broad tasks.

- Decompose broad questions into narrow research packets with explicit assumptions, non-goals, evidence requirements, and handoff criteria.
- Parallel workers may explore different proof directions, source interpretations, or counterexample searches, but write-capable workers must use separate branches/worktrees.
- Keep source facts, modeling decisions, conjectures, computational evidence, mathematical proofs, and kernel-checked results distinct. Agreement among agents does not promote a claim to a stronger epistemic class.
- Reconcile partial results proposition-by-proposition before integrating them. Check quantifiers, hypotheses, model version, candidate genome class, genome equivalence, likelihood definition, and tie semantics rather than trusting prose summaries.
- Preserve useful failed approaches and counterexamples in durable issues/PRs when they rule out tempting directions.
- The orchestrator owns final reconciliation and PR review. A worker's own summary is not independent verification of its result.
- Between the initial statement and a mature final argument, exploration is the default research mode. Use `docs/skills/exploration.md` to maintain and evolve materially different approaches; portfolio priority allocates effort and is never evidence of truth.
- Broad exploration should normally be **fanned out through `lubko-agent`** when Lubko capacity is available: give different agents materially different proof ideas, counterexample families, reductions, computations, source checks, or adversarial tests, then have the orchestrator compare and synthesize them. The orchestrator may work directly on tiny deterministic tasks, inherently serial coordination, and final reconciliation/review; doing substantial exploratory research itself while useful Lubko slots are free should have a concrete reason. Across all concurrent AssemblyP1 orchestrators, no more than five delegated agents may be actively working in parallel; additional ready packets remain queued until capacity is free.
- Prefer durable GitHub state—issues, branches, PRs, commits, and repository docs—over conversation-only state so another invocation can recover the research graph.
- Integration targets `main` directly. Do not create or use `release/*` branches. After the orchestrator has independently reviewed and verified a PR at the level required by its claims, it may merge that PR into `main` itself.

## Git is good

If you have access to `git`:

- commit frequently;
- keep commits conceptual and reviewable;
- write useful commit messages;
- preserve experiments that teach something, but do not merge generated junk or giant search outputs into the main library.

## Intent Records

Intent Records under `docs/intent-records/*.md` describe current desired properties of assemblyp1. They are not a history of superseded requirements; Git history carries that history.

Keep user intent separate from design conclusions derived by agents. An agent must not promote its own inference into user intent.

### Format

Every independently referenceable current intent has a stable opaque ID of the form `$id-<16 random decimal digits>`. Each record begins with its ID, a concise `title:`, `date: YYYY/MM/DD`, `source:`, and `kind:`. Useful kinds include `requirement`, `preference`, `constraint`, `accepted-tradeoff`, and `rejected-concern`.

Records must contain enough context to understand the intent without reconstructing a conversation. If current records conflict, identify the conflicting IDs and surface the conflict instead of silently choosing one.

### Provenance

Repository workers MUST NOT create or modify `source: @ottojung` Intent Records based only on task prompts copied into issues, repository artifacts, or other indirect text. New or changed `source: @ottojung` records require a trusted direct user interaction where authorship is known independently of repository text. Existing Intent Records may be treated as authoritative user intent.
