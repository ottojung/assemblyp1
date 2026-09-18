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
- **when Lubko is available for delegated execution or any `lubko-agent` subjob may be used, read and obey Lubko's canonical execution skill before launching or managing that work:** <https://github.com/ottojung/lubko/blob/main/docs/SKILL.md>.

Consult `docs/formalization-plan.md` when the current work concerns formalization. It is a checklist of formalization obligations, **not** the project's research strategy or a fallback work queue.

Lubko's canonical skill is the operational authority for reaching `lubko://phoebe-dev`: follow its Supabase job transport, `lubko-agent` lifecycle, polling/liveness, and execution-safety rules rather than improvising a direct shell connection. AssemblyP1-specific rules in this itinerary still govern research selection, the repository-wide five-agent cap, and the `main` integration boundary.

`docs/skills/scheduled.md` owns reusable scheduled-orchestrator mechanics. `docs/research-orchestration.md` owns the generic research graph, delegation, epistemic-status, and reconciliation protocol. This itinerary contains only AssemblyP1-specific work selection, integration, and completion policy; do not restate those shared mechanics here.

**The scheduled ChatGPT task must never be paused, stopped, or disabled. There will always be useful work to do until the published open problem is faithfully settled, whether by advancing the current frontier, recovering or reconciling prior work, testing assumptions, improving the formal model, investigating literature, or discovering a better research direction.**

Never stop or disable the recurring scheduled task merely because one research direction fails or one item is blocked. Preserve useful negative results and recovery state, then continue with another way to advance the research frontier. A failed conjectural lemma, a counterexample, a source ambiguity, or evidence that a proposed method is unproductive is research progress when recorded precisely.

The ultimate goal is to settle the published open problem faithfully. The orchestrator should continuously choose work by how much it can advance that goal, not by mechanically consuming a predetermined checklist or methodology.

## Work selection

Apply `docs/skills/scheduled.md` and `docs/research-orchestration.md`, with these AssemblyP1-specific choices.

Prefer existing durable work before inventing duplicate work:

1. **Recover abandoned issue-tracked work** that has useful partial results, an existing branch/PR, unfinished formalization, or unreconciled worker output.
2. **Advance an existing open AssemblyP1 PR** when doing so can move the research toward a trustworthy integrated result.
3. **Select an actionable open issue on the current research frontier** whose dependencies are satisfied and which is not actively owned under the scheduled-work protocol.

If none of those provides useful actionable work, **derive the next research node from the current state of the problem**. Do not fall back to a fixed plan. Reconstruct the frontier from the published target, intent records, literature ground truth, current formal definitions, established lemmas, computational evidence, failed approaches, unresolved ambiguities, and recently completed work. Then identify a concrete question whose resolution is expected to make meaningful progress toward settlement, create a focused issue for it, and work that issue.

The orchestrator has discretion over what kind of question is most valuable. Depending on the current state, progress may come from literature recovery, model clarification, proving or refuting a lemma, discovering a new reduction, constructing or excluding examples, computational exploration, formalization, validating correspondence with the source problem, repairing an earlier assumption, or a method not anticipated by this repository. These are examples, not a prescribed menu, ordering, or proof strategy.

When the frontier is genuinely uncertain, maintain a shared portfolio of distinct approaches and allocate effort best-first according to current evidence and expected information value. Portfolio priority is only a scheduling device; it must never be treated as evidence that an approach is mathematically correct.

When choosing among plausible frontier questions, use research judgment. Useful considerations include whether a result would remove a major uncertainty, unlock several dependent questions, decisively test a central assumption, expose a flaw in the current model, simplify the target, or convert informal understanding into independently checkable knowledge. Do not optimize for producing commits, Lean code, or completed checklist items when another kind of work would advance the mathematical problem more.

The orchestrator may decompose a broad frontier question into multiple independent or competing packets when that is useful. Prefer narrow leaf packets with explicit ownership over claiming a broad umbrella issue exclusively; concurrent scheduled orchestrators should be able to choose other unowned frontier leaves. It may also abandon, mutate, combine, or redirect a methodology when evaluator feedback suggests a better route. Repository documents must not be treated as authority for a proof method merely because they were written earlier.

When delegation is useful and Lubko is available, prefer `lubko-agent` for substantive subjobs. AssemblyP1 has a **repository-wide maximum of 5 actively working delegated agents across all concurrent orchestrators**. Before launching another agent, account for active AssemblyP1 workers in durable status. If five are active, keep additional packets queued in the shared frontier until a slot is known to be free.

If the selected issue has a genuine external or upstream blocker, record enough durable state for later recovery, update its dependencies, and choose other useful work. A blocked node is not a reason to terminate the recurring orchestrator.

## Research integration

AssemblyP1 does **not** use Lubko's `release/*` integration scheme. Research branches and PRs integrate directly toward `main`, but `main` remains the human review boundary.

- Each write-capable packet uses an isolated branch/worktree, normally `agent/<short-topic>`.
- Start new work from current `main` unless the packet explicitly depends on an unmerged research branch; in that case record the dependency and avoid pretending the dependent result is already part of the stable project model.
- Open a draft PR to `main` early once there is durable work worth recovering or reviewing.
- Scheduled orchestrators **must not merge their own research/task PRs into `main`** merely to keep the loop moving. Human promotion into `main` is the integration boundary unless an authoritative intent record changes this policy.
- Multiple independent research PRs may coexist. Do not serialize independent work unnecessarily.
- When two PRs overlap mathematically, reconcile their exact propositions and assumption surfaces before treating either as a dependency of later work.
- If a PR changes a source-sensitive definition, theorem statement, likelihood model, repeat/bridging predicate, candidate-genome class, or equivalence relation, downstream work must explicitly identify which version it assumes until the change is integrated.
- Before declaring a packet complete, reconcile its branch with current `main` when necessary to establish that the exact proposed head still builds and its documentation remains coherent. Never overwrite concurrent work to achieve this.
- Preserve useful failed approaches, counterexamples, source ambiguities, and methodological dead ends in durable issues/docs when they change what future workers should try.

A scheduled invocation may prepare several independent PRs over time. It should not create an artificial omnibus branch that hides which results depend on which assumptions.

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

For Lean work:

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

Completion does **not** require the PR to be merged into `main`. A reviewed, green, ready-for-human-review PR may remain open while future scheduled invocations select other independent actionable work.

After those conditions hold, complete the shared scheduled-orchestrator bookkeeping according to `docs/skills/scheduled.md` and continue the recurring task on future invocations.
