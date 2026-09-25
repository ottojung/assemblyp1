# AssemblyP1 scheduled-work itinerary

## Scope

This is the **sole entry point** for scheduled ChatGPT tasks that advance the AssemblyP1 repository itself.

Target repository:

<https://github.com/ottojung/assemblyp1>

Before acting, study and obey:

- `AGENTS.md`;
- `docs/open-problem.md`;
- `docs/research-orchestration.md`;
- `docs/skills/scheduled.md`;
- `docs/skills/research-orchestrator.md` when the selected work is broad or benefits from multiple workers;
- `docs/skills/exploration.md` whenever the best next direction is uncertain or several approaches deserve comparison;
- the narrower skill under `docs/skills/` appropriate to the selected packet;
- **on every scheduled run, read and obey Lubko's canonical execution skill:** <https://github.com/ottojung/lubko/blob/main/docs/SKILL.md>. The lightweight pool check in `docs/skills/scheduled.md` uses Lubko, but it must not dominate or block the research run.

Consult `docs/formalization-plan.md` when the current work concerns formalization. It defines the project's formalization cadence: pin down the initial statement, explore primarily outside Lean, then formalize a mature final proof/counterexample. It is **not** the research strategy or a fallback work queue.

AssemblyP1's preferred execution target is `lubko://marceline-dev`. Lubko's canonical skill is the operational authority for reaching it: follow the Supabase job transport, `lubko-agent` lifecycle when available, polling/liveness, and execution-safety rules rather than improvising a direct shell connection. `marceline-dev` has Git and Guix available. Before Lean work, follow `docs/skills/lean-on-marceline-dev.md` and verify that the exact repository-pinned toolchain is available; do not treat an arbitrary Guix Lean version as project verification. Do not silently make `marceline-dev` primary again for new work; use it only for explicit recovery/diagnosis of pre-migration state or a separately justified fallback. AssemblyP1-specific rules in this itinerary still govern research selection, the repository-wide five-agent cap, and direct integration into `main`.

`docs/skills/scheduled.md` owns reusable scheduled-orchestrator mechanics. `docs/research-orchestration.md` owns the generic research graph, delegation, epistemic-status, and reconciliation protocol. This itinerary contains only AssemblyP1-specific work selection, integration, and completion policy; do not restate those shared mechanics here.

**The scheduled ChatGPT task must never be paused, stopped, or disabled. There will always be useful work to do until the published open problem is faithfully settled, whether by advancing the current frontier, recovering or reconciling prior work, testing assumptions, improving the formal model, investigating literature, or discovering a better research direction.**

Never stop or disable the recurring scheduled task merely because one research direction fails or one item is blocked. Preserve useful negative results and recovery state, then continue with another way to advance the research frontier. A failed conjectural lemma, a counterexample, a source ambiguity, or evidence that a proposed method is unproductive is research progress when recorded precisely.

The ultimate goal is to settle the published open problem faithfully. The orchestrator should continuously choose work by how much it can advance that goal, not by mechanically consuming a predetermined checklist or methodology.

## Work selection

Near startup, perform the lightweight Lubko pool snapshot from `docs/skills/scheduled.md` and opportunistically launch a useful batch when capacity is clearly available. Then proceed with the research run; pool bookkeeping is not a gate on issue work, PR repair, proof search, CI diagnosis, or local exploration.

Apply `docs/skills/scheduled.md` and `docs/research-orchestration.md`, with these AssemblyP1-specific choices.

Prefer existing durable work before inventing duplicate work for the orchestrator's own coordination/recovery attention:

1. **Recover abandoned issue-tracked work** that has useful partial results, an existing branch/PR, unfinished formalization, or unreconciled worker output.
2. **Advance an existing open AssemblyP1 PR** when doing so can move the research toward a trustworthy integrated result.
3. **Select an actionable open issue on the current research frontier** whose dependencies are satisfied and which is not actively owned under the scheduled-work protocol.

This ordering does **not** mean all delegated agents must work on the first open issue or PR. Open issues are durable research nodes, not the boundary of allowed exploration. Give an existing node only the worker capacity it can use independently and productively; fill remaining free agent slots from the broader live frontier.

Exploratory agent packets may begin without an issue. When a packet produces a question, result, dependency, obstruction, or recovery state that should survive across invocations, promote it into an issue, document, branch/PR, or other durable repository state.

If existing durable work does not consume all useful research capacity, **derive additional frontier packets from the current state of the problem**. Do not fall back to a fixed plan. Reconstruct the frontier from the published target, intent records, literature ground truth, current formal definitions, established lemmas, computational evidence, failed approaches, unresolved ambiguities, and recently completed work.

The orchestrator has discretion over what kind of question is most valuable. Depending on the current state, progress may come from literature recovery, model clarification, proving or refuting a lemma in notes, discovering a new reduction, constructing or excluding examples, computational exploration, validating correspondence with the source problem, repairing an earlier assumption, or a method not anticipated by this repository. Substantial formalization is normally reserved for the initial statement or a mature final result. These are examples, not a prescribed menu, ordering, or proof strategy.

When the frontier is genuinely uncertain, maintain a shared portfolio of distinct approaches and allocate effort best-first according to current evidence and expected information value. Portfolio priority is only a scheduling device; it must never be treated as evidence that an approach is mathematically correct.

When choosing among plausible frontier questions, use research judgment. Useful considerations include whether a result would remove a major uncertainty, unlock several dependent questions, decisively test a central assumption, expose a flaw in the current model, simplify the target, or convert informal understanding into independently checkable knowledge. Do not optimize for producing commits, Lean code, or completed checklist items when another kind of work would advance the mathematical problem more.

The orchestrator may decompose a broad frontier question into multiple independent or competing packets when that is useful. Prefer narrow leaf packets with explicit ownership over claiming a broad umbrella issue exclusively; concurrent scheduled orchestrators should be able to choose other unowned frontier leaves. It may also abandon, mutate, combine, or redirect a methodology when evaluator feedback suggests a better route. Repository documents must not be treated as authority for a proof method merely because they were written earlier.

For broad exploration, aim for **near-saturation of the shared Lubko pool** when useful work exists. The repository-wide maximum is **5 actively working delegated agents across all concurrent orchestrators**. Use `lubko-agent list --running --json` on `marceline-dev` for a live snapshot when practical; do not infer the count only from GitHub issue comments. Launch into clearly free capacity in small batches, refresh periodically or before another wave, and keep the research run moving if pool telemetry becomes temporarily unavailable.

Do not manufacture filler work or duplicate active packets to hit five. Instead, if the selected issue/PR cannot use all available slots independently, generate materially different packets from the wider research frontier and run those alongside it. When an agent finishes, fails, stalls, or is stopped, reconcile its output and refill the slot promptly when another useful packet exists.

The orchestrator should concentrate on packet choice, steering, comparison, reconciliation, and the next wave. Tiny deterministic work, inherently serial coordination, and final review can remain direct.

If the selected issue has a genuine external or upstream blocker, record enough durable state for later recovery, update its dependencies, and choose other useful work. A blocked node is not a reason to terminate the recurring orchestrator.

## Research integration

AssemblyP1 integrates directly into `main`. **Do not create or use `release/*` branches.**

- Each write-capable packet uses an isolated branch/worktree, normally `agent/<short-topic>`.
- Start new work from current `main` unless the packet explicitly depends on an unmerged research branch; in that case record the dependency and avoid pretending the dependent result is already part of the stable project model.
- Open a draft PR to `main` early once there is durable work worth recovering or reviewing.
- After independently reviewing the PR diff and completing the verification required by its epistemic claims, a scheduled orchestrator may merge the PR into `main` itself. There is no human-only merge boundary.
- Multiple independent research PRs may coexist. Do not serialize independent work unnecessarily.
- When two PRs overlap mathematically, reconcile their exact propositions and assumption surfaces before treating either as a dependency of later work.
- If a PR changes a source-sensitive definition, theorem statement, likelihood model, repeat/bridging predicate, candidate-genome class, or equivalence relation, downstream work must explicitly identify which version it assumes until the change is integrated.
- Before declaring a packet complete, reconcile its branch with current `main` when necessary to establish that the exact proposed head still builds and its documentation remains coherent. Never overwrite concurrent work to achieve this.
- Preserve useful failed approaches, counterexamples, source ambiguities, and methodological dead ends in durable issues/docs when they change what future workers should try.

A scheduled invocation may prepare several independent PRs over time. It should not create an artificial omnibus branch that hides which results depend on which assumptions.

## Lean on Marceline Dev

Before running Lean on `marceline-dev`, follow [`lean-on-marceline-dev.md`](lean-on-marceline-dev.md). In particular, use the existing `/home/lubko/.elan/bin` installation instead of creating a per-worktree toolchain.

## Verification and review

Verification must match the epistemic claim being made.

For source/model work:

- cite primary sources precisely enough to recover the relevant definition/result;
- distinguish quoted/source-supported facts from the agent's interpretation;
- record unresolved convention mismatches instead of silently choosing one.

For computation:

- record the exact scope, assumptions, and limitations of the computation;
- preserve reproducible evidence for material discoveries;
- do not promote computational evidence into a proof unless the required completeness argument is itself established.

For Lean work, when the initial-statement or mature-final-result threshold justifies doing it:

- run `lake build` on the exact proposed head;
- require repository CI to pass, including warning-as-error and axiom audit;
- do not introduce `sorry`, `admit`, or new axioms to claim progress;
- separately review that the formal definitions/statements still correspond to the intended source mathematics.

The orchestrator owns final reconciliation and PR review. A worker's own summary or green tests are evidence, not independent verification.

## Completion

A scheduled AssemblyP1 work item is complete when:

- its scoped research question has reached a terminal useful state such as resolved, refuted, formally implemented, source-resolved, or explicitly blocked with durable evidence;
- all delegated packets for that item are terminal and their outputs have been reconciled;
- every material claim is labeled at the strongest epistemic level actually supported by its evidence;
- useful results, including negative results and failed approaches that affect future strategy, are preserved durably;
- the proposed branch is reconciled with relevant current repository state;
- `lake build` succeeds on the exact proposed head when Lean code changed;
- repository CI is green, or any remaining failure is clearly demonstrated to be external and unrelated to the proposed work;
- no unresolved source-fidelity, mathematical-correctness, or review blocker is hidden;
- the current research state makes clear what is known, what remains uncertain, and how another orchestrator can continue making progress.

Completion does not mechanically require a merge when there is a concrete reason to leave a PR open, but a reviewed and verified PR may be merged directly into `main` by the orchestrator; it need not wait for separate human promotion.

After those conditions hold, complete the shared scheduled-orchestrator bookkeeping according to `docs/skills/scheduled.md` and continue the recurring task on future invocations.
