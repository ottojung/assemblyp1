# AssemblyP1 scheduled-work itinerary

## Scope

This is the **sole entry point** for scheduled ChatGPT tasks that advance the AssemblyP1 repository itself.

Target repository:

<https://github.com/ottojung/assemblyp1>

Before acting, study and obey:

- `AGENTS.md`;
- `docs/open-problem.md`;
- `docs/formalization-plan.md`;
- `docs/research-orchestration.md`;
- `docs/skills/scheduled.md`;
- `docs/skills/research-orchestrator.md` when the selected work is broad or benefits from multiple workers;
- the narrower skill under `docs/skills/` appropriate to the selected packet.

When Lubko is the execution platform, also obey its canonical execution skill:

<https://github.com/ottojung/lubko/blob/main/docs/SKILL.md>

`docs/skills/scheduled.md` owns reusable scheduled-orchestrator mechanics. `docs/research-orchestration.md` owns the generic research graph, delegation, epistemic-status, and reconciliation protocol. This itinerary contains only AssemblyP1-specific work selection, integration, and completion policy; do not restate those shared mechanics here.

**Never stop or disable the recurring scheduled task merely because one research direction fails or one item is blocked.** Preserve useful negative results and recovery state, then continue with another actionable node on the research frontier. A failed conjectural lemma, a counterexample, or a source ambiguity is research progress when recorded precisely.

The mathematical target is the published open problem, not a theorem chosen for convenience. Source/model ambiguity blocks dependent proof claims but does not block unrelated useful work.

## Work selection

Apply `docs/skills/scheduled.md` and `docs/research-orchestration.md`, with these AssemblyP1-specific choices.

Prefer work in this order:

1. **Recover abandoned issue-tracked work** that has useful partial results, an existing branch/PR, unfinished formalization, or unreconciled worker output.
2. **Advance an existing open AssemblyP1 PR** that needs implementation, source-fidelity verification, Lean repair, reconciliation, or review preparation.
3. **Select an actionable open issue on the current research frontier** whose dependencies are satisfied and which is not actively owned under the scheduled-work protocol.
4. **If no suitable issue exists, create one for the earliest actionable unresolved item in `docs/formalization-plan.md`** or for a concrete dependency exposed by current research.

Within equally actionable work, prefer nodes that reduce uncertainty or unblock several downstream nodes. In the current early phase, prioritize source-model recovery and validation before large speculative proof attempts.

Good scheduled packets include:

- resolving one precise source-model ambiguity with primary citations;
- formalizing one stable definition or small family of closely related definitions;
- proving one reusable mathematical/Lean lemma;
- independently checking a central conjectural lemma;
- running and documenting a bounded counterexample search with exact scope;
- minimizing and formalizing a discovered witness;
- reconciling two overlapping or conflicting research outputs;
- adding small examples that validate Lean definitions against the source papers.

Do not select a giant task such as “solve the conjecture” when it can be decomposed into narrower nodes with explicit dependencies.

For central uncertain lemmas, maintain positive and negative pressure: pair proof search with literature or counterexample search when doing so can cheaply falsify a bad direction.

If the selected issue has a genuine external or upstream blocker, record enough durable state for later recovery, update its dependencies, and choose other actionable work. A blocked node is not a reason to terminate the recurring orchestrator.

## Research integration

AssemblyP1 does **not** use Lubko's `release/*` integration scheme. Research branches and PRs integrate directly toward `main`, but `main` remains the human review boundary.

- Each write-capable packet uses an isolated branch/worktree, normally `agent/<short-topic>`.
- Start new work from current `main` unless the packet explicitly depends on an unmerged research branch; in that case record the dependency and avoid pretending the dependent result is already part of the stable project model.
- Open a draft PR to `main` early once there is durable work worth recovering or reviewing.
- Scheduled orchestrators **must not merge their own research/task PRs into `main`** merely to keep the loop moving. Human promotion into `main` is the integration boundary unless an authoritative intent record changes this policy.
- Multiple independent research PRs may coexist. Do not serialize independent proof, literature, and counterexample work unnecessarily.
- When two PRs overlap mathematically, reconcile their exact propositions and assumption surfaces before treating either as a dependency of later work.
- If a PR changes a source-sensitive definition, theorem statement, likelihood model, repeat/bridging predicate, candidate-genome class, or equivalence relation, downstream work must explicitly identify which version it assumes until the change is integrated.
- Before declaring a packet complete, reconcile its branch with current `main` when necessary to establish that the exact proposed head still builds and its documentation remains coherent. Never overwrite concurrent work to achieve this.
- Preserve useful failed approaches, counterexamples, and source ambiguities in durable issues/docs even when no code from that branch should merge.

A scheduled invocation may prepare several independent PRs over time. It should not create an artificial omnibus branch that hides which results depend on which assumptions.

## Verification and review

Verification must match the epistemic claim being made.

For source/model work:

- cite primary sources precisely enough to recover the relevant definition/result;
- distinguish quoted/source-supported facts from the agent's interpretation;
- record unresolved convention mismatches instead of silently choosing one.

For computation:

- record the exact finite search space, pruning/symmetry assumptions, and whether completeness was proved;
- preserve explicit witnesses/certificates for discovered counterexamples;
- never promote “no counterexample found” into a proof.

For Lean work:

- run `lake build` on the exact proposed head;
- require repository CI to pass, including warning-as-error and axiom audit;
- do not introduce `sorry`, `admit`, or new axioms to claim progress;
- separately review that the formal definitions/statements still correspond to the intended source mathematics.

The orchestrator owns final reconciliation and PR review. A worker's own summary or green tests are evidence, not independent verification.

## Completion

A scheduled AssemblyP1 work item is complete when:

- its scoped research question has reached a terminal useful state: proved, refuted, source-resolved, formally implemented, or explicitly blocked with durable evidence;
- all delegated packets for that item are terminal and their outputs have been reconciled;
- every material claim is labeled at the strongest epistemic level actually supported by its evidence;
- useful results, including negative results, are preserved in issues, docs, commits, or a PR;
- the proposed branch is reconciled with relevant current repository state;
- `lake build` succeeds on the exact proposed head when Lean code changed;
- repository CI is green, or any remaining failure is clearly demonstrated to be external and unrelated to the proposed work;
- no unresolved source-fidelity, mathematical-correctness, or review blocker is hidden;
- the next research frontier or downstream dependencies are explicit.

Completion does **not** require the PR to be merged into `main`. A reviewed, green, ready-for-human-review PR may remain open while future scheduled invocations select other independent actionable work.

After those conditions hold, complete the shared scheduled-orchestrator bookkeeping according to `docs/skills/scheduled.md` and continue the recurring task on future invocations.
