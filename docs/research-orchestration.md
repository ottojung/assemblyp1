# Research orchestration

This document defines the research loop for assemblyp1. Workers may be ChatGPT invocations, `lubko-agent` jobs, humans, or other tools. The invariant is that research state is durable, reviewable, adaptive, and separated by epistemic status.

Read `AGENTS.md`, `docs/open-problem.md`, the locked literature ground truth identified by the intent records, and the relevant source papers before using this protocol. Consult `docs/formalization-plan.md` only when the current work concerns formalization; it is not the research roadmap.

## Goal

The loop should make parallel work useful without letting parallelism corrupt the mathematical target. It should continuously search for the most informative next work: literature recovery, model reconstruction, exploratory mathematics, proof attempts, counterexample search, formalization, computation, or another route discovered during research.

The orchestrator owns both the durable research graph and the **live exploration portfolio**. It should not pretend that every branch is compatible or that an earlier plan remains optimal after new evidence arrives.

## Epistemic classes

Every material result should be classified as one of:

- **source fact** — a claim directly supported by a cited primary source, with enough location information to recover the passage;
- **modeling decision** — a deliberate formal interpretation or reconciliation of source conventions;
- **conjecture** — a proposition believed useful but not proved;
- **computational evidence** — an experiment, bounded search result, or generated candidate whose scope is explicit;
- **mathematical proof** — a human-readable proof whose assumptions and conclusion are explicit;
- **kernel-checked result** — a theorem checked by Lean without `sorry`, `admit`, or new axioms.

Never promote a result to a stronger class because several workers agree, because an approach ranks highly in the portfolio, or because it survived many failed falsification attempts.

## Durable research graph

Use GitHub issues as research nodes and PRs/commits as implementation artifacts. A useful issue states:

1. the exact question or proposition;
2. why it matters to the main open problem;
3. dependencies and permitted assumptions;
4. expected deliverables;
5. what would falsify or block the proposed direction;
6. the current epistemic class of each claimed result;
7. links to source passages, experiments, Lean declarations, branches, and PRs.

Keep issues narrow enough that independent workers can finish or refute them. Prefer a dependency graph of small questions over one giant "solve the conjecture" task.

The issue graph records durable obligations and discoveries. It is **not** a FIFO queue. The orchestrator may change priorities whenever evidence changes.

## Exploration portfolio

For uncertain frontier work, apply `docs/skills/exploration.md`.

Maintain a small set of materially different active or dormant approaches. Cluster duplicates, keep assumption differences explicit, and use evaluator results to revise, combine, promote, demote, block, or refute approaches.

Portfolio priority controls **research effort only**. It never determines truth.

When the target is too hard to interrogate directly, generate scaffold problems whose solutions would reveal structure. A scaffold must record how it informs the published target and must never silently become the replacement problem.

## Work packets

When delegating work, give the worker a packet with:

- **objective** — one concrete research question;
- **context** — only the definitions/results it may rely on;
- **non-goals** — nearby questions it should not silently absorb;
- **required evidence** — citations, executable search, proof sketch, Lean theorem, etc.;
- **deliverable** — issue comment, document, branch/PR, counterexample certificate, or theorem;
- **stop conditions** — contradiction in assumptions, ambiguous source semantics, search-space explosion, or dependence on an unproved lemma;
- **handoff format** — concise result, assumptions, epistemic class, failures tried, and next suggested question.

Workers should attack the packet, not redefine it to make it easy.

## Parallelism and Lubko

When delegation is useful and Lubko is available, **prefer `lubko-agent` for substantive subjobs**. Use direct operations for tiny deterministic work that does not justify a delegated agent.

AssemblyP1 has a hard **repository-wide** concurrency limit: **no more than 5 delegated agents may be actively working in parallel across all concurrent orchestrators**. This overrides generic Lubko guidance that would otherwise allow more. Before launching a delegated agent, account for currently active AssemblyP1 agent jobs recorded in durable status/worker state. If five are already active, leave additional packets queued in the shared portfolio/frontier until a slot is durably known to be free.

Do not give two write-capable workers the same branch or worktree. The orchestrator retains final reconciliation, PR review, and integration responsibility.

## The research loop

### 1. Recover state

Read open issues, active PRs, CI, intent records, recent durable research notes, and any active worker status. Recover abandoned useful work before spawning duplicates.

Reconstruct both:

- the dependency graph of established/blocked questions; and
- the current portfolio of plausible research approaches.

### 2. Generate or refresh the frontier

If the current frontier is obvious, state it precisely. If it is uncertain, generate several materially different candidate approaches rather than one prematurely committed route.

Deduplicate equivalent ideas after normalizing assumptions. Preserve genuinely distinct model variants and source forks separately.

### 3. Evaluate cheaply

Before expensive work, ask what cheapest observation could change the decision about an approach. Examples include a primary-source check, hand example, bounded exact search, Lean micro-lemma, theorem-strength comparison, or independent derivation.

Feed failures back into the approach. Revise, weaken, split, combine, block, or retire it instead of merely recording "failed."

### 4. Allocate effort best-first

Choose work based on current expected research value rather than static document order.

Useful considerations include:

- how decisively a cheap test may reduce uncertainty;
- downstream dependencies unblocked;
- ability to kill an attractive wrong route quickly;
- novelty relative to previous attempts;
- strength of present evidence;
- cost;
- availability of independent verification.

These considerations are scheduling heuristics, not truth scores.

### 5. Execute bounded parallel work

Launch delegated work only while the repository-wide active-agent count remains below five. Prefer distinct packets or deliberately independent replications over several agents paraphrasing the same task.

When a worker finishes, update the portfolio before filling the freed slot. New evidence may make a previously queued packet obsolete.

### 6. Reconcile

A reconciler compares outputs proposition-by-proposition. It must identify:

- statements literally equal after normalization;
- differences in hypotheses, quantifiers, equivalence notions, candidate class, or probability model;
- source disagreements versus worker mistakes;
- results that can coexist on separate branches of the research graph;
- the strongest result actually justified by evidence.

Do not average incompatible answers or choose by majority vote.

### 7. Evolve promising approaches

Do not simply repeat a promising route. Improve it using evaluator feedback:

- mutate a failed assumption;
- change representation;
- weaken or strengthen an intermediate statement;
- combine compatible parts of two approaches;
- extract a structural conjecture from a computational pattern;
- turn Lean or proof failure into a corrected proposition.

Keep provenance between parent and descendant approaches.

### 8. Formalize stable knowledge

Once a definition or lemma is sufficiently stable, translate it into Lean. Prefer executable definitions and small lemmas with source correspondence. If a proposition is still conjectural, represent it as a `Prop` or issue, not as an axiom or theorem with `sorry`.

### 9. Verify independently

Before promoting a result:

- re-read the relevant primary source for source facts;
- rerun material computations from clean inputs;
- check proof assumptions against the current model;
- run `lake build` and CI for Lean work;
- review the PR diff independently of the worker that produced it.

### 10. Update graph and portfolio

Close solved nodes, split ambiguous nodes, add dependencies, mark refuted approaches, preserve useful failures, and record both the next frontier and why it currently deserves effort.

The next invocation must be able to continue from durable GitHub/repository state alone.

## Suggested worker roles

Roles are modes, not identities:

- **source scout** — finds primary literature and exact definitions/results;
- **model auditor** — compares conventions across papers and the Lean model;
- **mathematical explorer** — develops and mutates candidate arguments;
- **counterexample hunter** — searches finite instances and minimizes witnesses;
- **formalizer** — implements stable definitions/lemmas in Lean;
- **evaluator** — cheaply tests portfolio entries and returns discriminating evidence;
- **reconciler** — compares partial results and maintains the dependency graph;
- **orchestrator** — owns prioritization, delegation, reconciliation, review, and integration.

The orchestrator should not delegate away final reconciliation or PR review.

## Proof-search discipline

For every proposed key lemma or route, ask:

- Is it true under the exact current definitions?
- Is it already known in the literature?
- What is the cheapest useful falsification or sanity test?
- What does the latest failure teach us about how to revise the route?
- What weaker or neighboring statement would expose structure without replacing the real target?
- Does the argument depend on latent read placements, only observed read multiplicities, or both?

Do **not** require a predetermined positive/negative split or any fixed proof architecture. The portfolio should evolve according to evidence.

A good loop shrinks uncertainty and improves the frontier. It does not merely generate more prose.

## Integration rule

A result belongs on `main` when it improves durable research state without overstating what is known. Source notes may land while ambiguities remain if the ambiguity is explicit. Exploratory code may land when reproducible and clearly labeled. Lean theorems must compile without trust escapes. Claims that the published problem is solved require both a kernel-checkable result and a documented correspondence between the formal theorem and the published statement.
