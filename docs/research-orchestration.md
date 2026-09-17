# Research orchestration

This document defines the research loop for assemblyp1. It is deliberately executor-agnostic: the workers may be ChatGPT invocations, Lubko agents, humans, or other tools. The invariant is that research state is durable, reviewable, and separated by epistemic status.

Read `AGENTS.md`, `docs/open-problem.md`, `docs/formalization-plan.md`, and the relevant source papers before using this protocol.

## Goal

The loop should make parallel work useful without letting parallelism corrupt the mathematical target. It should distribute literature search, model reconstruction, exploratory mathematics, counterexample search, and Lean formalization; reconcile partial results; and continuously turn trustworthy discoveries into smaller formal obligations.

The orchestrator is responsible for the research graph, not for pretending that every branch is compatible.

## Epistemic classes

Every material result should be classified as one of:

- **source fact** — a claim directly supported by a cited primary source, with enough location information to recover the passage;
- **modeling decision** — a deliberate formal interpretation or reconciliation of source conventions;
- **conjecture** — a proposition believed useful but not proved;
- **computational evidence** — an experiment, bounded search result, or generated candidate whose scope is explicit;
- **mathematical proof** — a human-readable proof whose assumptions and conclusion are explicit;
- **kernel-checked result** — a theorem checked by Lean without `sorry`, `admit`, or new axioms.

Never promote a result to a stronger class merely because several workers agree with it.

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

## Work packets

When delegating work, give the worker a packet with:

- **objective** — one concrete research question;
- **context** — only the definitions/results it may rely on;
- **non-goals** — nearby questions it should not silently absorb;
- **required evidence** — citations, executable search, proof sketch, Lean theorem, etc.;
- **deliverable** — issue comment, document, branch/PR, counterexample certificate, or theorem;
- **stop conditions** — contradiction in assumptions, ambiguous source semantics, search-space explosion, or dependence on an unproved lemma;
- **handoff format** — concise result, assumptions, confidence/epistemic class, failures tried, and next suggested question.

Workers should attack the packet, not redefine it to make it easy.

## The research loop

### 1. Recover state

Read the open issues, active PRs, CI, formalization plan, and recent durable research notes. Recover abandoned useful work before spawning duplicates.

### 2. Choose the frontier

Select questions that unblock the greatest number of downstream nodes. Early in the project, source/model ambiguity dominates. Later, prefer small lemmas that cut multiple proof branches or small finite searches that can decisively kill a conjectural step.

### 3. Decompose

Turn the frontier question into independent or deliberately competing packets. Good parallel decompositions include:

- two workers independently transcribing a difficult source definition;
- literature search versus direct theorem derivation;
- positive proof attempt versus counterexample search;
- mathematical lemma proof versus Lean API/formalization design;
- brute-force exploration versus symmetry reduction/completeness proof.

Do not give two write-capable workers the same branch or worktree.

### 4. Execute in parallel

Workers may explore aggressively, but must preserve assumptions and negative results. Failed approaches are useful when they rule out a tempting path or expose a missing hypothesis.

### 5. Reconcile

A reconciler compares outputs proposition-by-proposition. It must identify:

- statements that are literally the same after normalization;
- statements that differ in hypotheses, quantifiers, equivalence notions, candidate class, or probability model;
- source disagreements versus worker mistakes;
- results that can coexist on separate branches of the research graph;
- the strongest result actually justified by the evidence.

Do not average incompatible answers. Preserve unresolved forks explicitly.

### 6. Formalize the stable frontier

Once a definition or lemma is sufficiently stable, translate it into Lean. Prefer executable definitions and small lemmas with source correspondence. If a proposition is still conjectural, represent it as a `Prop` or issue, not as an axiom or a theorem with `sorry`.

### 7. Verify independently

Before promoting a result:

- re-read the relevant primary source for source facts;
- rerun bounded searches from clean inputs;
- check proof assumptions against the current model;
- run `lake build` and CI for Lean work;
- review the PR diff independently of the worker that produced it.

### 8. Update the graph

Close solved nodes, split ambiguous nodes, add newly discovered dependencies, and record the next frontier. The next invocation must be able to continue from GitHub/repository state alone.

## Suggested worker roles

Roles are modes, not identities. One worker may take several roles on separate packets.

- **source scout** — finds primary literature and exact definitions/results;
- **model auditor** — compares conventions across papers and the Lean model;
- **mathematical explorer** — derives lemmas and proof decompositions on paper;
- **counterexample hunter** — searches finite instances and minimizes witnesses;
- **formalizer** — implements stable definitions/lemmas in Lean;
- **reconciler** — compares partial results and maintains the dependency graph;
- **orchestrator** — chooses the frontier, delegates, verifies, reviews, and integrates.

The orchestrator should not delegate away final reconciliation or PR review.

## Proof-search discipline

Maintain both positive and negative tracks until one is genuinely ruled out. For every proposed key lemma, ask:

- Is it true under the exact current definitions?
- Is it already known in the literature?
- Can a small finite instance falsify it?
- What weaker statement would still advance the main theorem?
- What stronger hypothesis would make it easy, and is that hypothesis actually available?
- Does the lemma depend on latent read placements, only observed read multiplicities, or both?

A good loop shrinks uncertainty. It does not merely generate more prose.

## Integration rule

A result belongs on `main` when it improves the durable research state without overstating what is known. Source notes may land while ambiguities remain if the ambiguity is explicit. Exploratory code may land when it is reproducible and clearly labeled. Lean theorems must compile without trust escapes. Claims that the published problem is solved require both a kernel-checkable result and a documented correspondence between the formal theorem and the published statement.
