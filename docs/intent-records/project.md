$id-2083587146518535
title: Formalize the published assembly open problem in Lean
date: 2026/09/17
source: @ottojung
kind: requirement

The purpose of this repository is to formalize the published open problem about whether the relevant bridging conditions guarantee that the maximum-likelihood assembly is the true genome, and to provide a foundation for trying to settle it.

---

$id-6292990609556170
title: Use Lean for the initial statement and final verification
date: 2026/09/17
source: @ottojung
kind: requirement

The repository should contain a Lean project, but formalization should not be the default medium for the middle research phase. Use Lean first to pin down the published open problem faithfully. Then prioritize mathematical exploration in notes, computation, examples, counterexamples, reductions, and proof sketches. Return to substantial Lean formalization when there is a plausible, coherent final proof or counterexample worth verifying. Small Lean experiments may still be used as bounded evaluators when they are the cheapest way to test a specific claim.

---

$id-5292271620912949
title: Seed the repository with agent and scheduled-work infrastructure
date: 2026/09/17
source: @ottojung
kind: requirement

Initialize the repository with reusable agent instructions, intent records, scheduling/orchestration guidance, and basic project infrastructure adapted from the user's existing Lubko project so that future agents can continue the work coherently.

---

$id-5953330995835449
title: Preserve the published problem rather than an agent-invented substitute
date: 2026/09/17
source: @ottojung
kind: constraint

The mathematical target is the open problem actually stated in the accepted literature. Modeling choices and theorem statements must be traced to those papers; an attractive theorem invented by an agent is not a substitute for the published question.

---

$id-1179785159633342
title: Start with setup and formalization rather than claiming a solution
date: 2026/09/17
source: @ottojung
kind: preference

The initial repository should be seeded and made ready for research. The first work is to formalize the open problem accurately; the bootstrap should not pretend the conjecture has already been proved or refuted.

---

$id-8841362759042187
title: Orchestrate research and proof work through cooperating agents
date: 2026/09/17
source: @ottojung
kind: requirement

The repository should provide AI-facing research skills, instructions, and guides for an agentic loop that can distribute literature research, mathematical exploration, counterexample search, proof work, computation, and bounded formal checks across multiple workers, then reconcile partial results, guide subsequent search, and integrate trustworthy progress into the project. The workflow should preserve durable state and make disagreements, assumptions, and evidence explicit rather than merely aggregating agent summaries.

---

$id-4318762045197832
title: Follow the locked literature ground-truth document
date: 2026/09/17
source: @ottojung
kind: requirement

The authoritative literature ground truth for this project is the following locked document:

<https://github.com/ottojung/assemblyp1/blob/99c158c59aa374ea3898ec4658b6eec52fbad342/docs/literature-status.md>

The project must follow that document when determining what formal statement is being investigated. The authoritative literature ground truth must not change.

---

$id-7412038659146728
title: Keep proof-discovery strategy adaptive
date: 2026/09/17
source: @ottojung
kind: constraint

Repository plans and agent instructions must not prescribe a proof or counterexample methodology in advance merely because it seems plausible now. The orchestrator should choose and revise methods from the live research state, evidence, and opportunities it discovers, always with the ultimate goal of faithfully settling the published conjecture. Formalization checklists may record representation work that remains to be done, but they must not become a surrogate research roadmap or force the orchestrator to follow a predetermined sequence, positive/negative split, search technique, or proof architecture.

---

$id-6502748193614207
title: Keep the shared Lubko pool near five useful active agents
date: 2026/09/17
source: @ottojung
kind: constraint

Across all concurrent AssemblyP1 orchestrators, no more than five delegated agents may be actively working in parallel at once, and the system should normally stay close to that shared cap whenever there are useful non-overlapping research packets available. Five is a saturation target, not a quota: do not create filler work or duplicate active packets merely to occupy slots. When capacity is free, orchestrators should broaden the search across materially different proof ideas, counterexample families, reductions, computations, source checks, adversarial evaluations, or scaffold questions, then steer, compare, reconcile, and synthesize the workers' results.

---

$id-3574186209471538
title: Allow orchestrators to merge directly into main
date: 2026/09/18
source: @ottojung
kind: requirement

AssemblyP1 must not use release branches or a human-only merge boundary. Research and implementation PRs should target `main` directly, and orchestrators may merge validated PRs into `main` themselves after completing the required independent review and verification.

---

$id-4827061539048172
title: Let agents explore beyond the open issue list
date: 2026/09/18
source: @ottojung
kind: requirement

GitHub issues are durable coordination and recovery nodes, not the universe of work that agents are allowed to do. Delegated agents may pursue useful temporary packets directly from the live research frontier without a pre-existing issue. An existing issue or PR should receive only as many agents as can work on it independently without stepping on each other; remaining useful agent capacity should explore other frontier directions. When an exploratory packet produces a question, result, dependency, obstruction, or recovery state worth carrying across runs, preserve it in an issue, document, branch/PR, or other durable repository state.

---

$id-7314082651974063
title: Keep pool saturation lightweight and subordinate to research
date: 2026/09/18
source: @ottojung
kind: requirement

Scheduled AssemblyP1 orchestrators should actively inspect the live Lubko agent pool and use clearly free capacity for useful independent packets, with five active delegated agents as the shared utilization target and hard maximum. Pool management must remain lightweight infrastructure: use a startup snapshot and small launch batches, refresh periodically or before another wave rather than after every individual launch, and never make successful saturation verification a prerequisite for substantive research. If Lubko recounting, polling, or launch verification becomes uncertain or blocked, stop launching additional uncertain agents, record the uncertainty briefly when useful for recovery, and continue safe mathematical/repository work.


---

$id-9018427365142097
title: Preserve the original intuition with an infinite-data theorem after negative settlement
date: 2026/09/20
source: @ottojung
kind: requirement

If the source-faithful initial versions of the bridging-to-maximum-likelihood claim, including the materially live source disambiguations, are all convincingly settled negatively, the project should not stop at the negative result. It should then formulate and prove an appropriate infinite-data or population-level positive analogue that preserves the attractive core intuition connecting sufficient repeat resolution with maximum-likelihood recovery.

Do not freeze the exact statement, likelihood formula, limiting formalism, or auxiliary hypotheses in this intent record. Those details should be chosen from the mathematical understanding available after the initial variants are settled, rather than committing the project now to a conjecture that may later turn out to be poorly formulated.

---

$id-3186075429146831
title: Produce publication artifacts through CI
date: 2026/09/21
source: @ottojung
kind: requirement

The repository's human-facing publication artifacts, including the white-paper PDF and Beamer presentation PDF, should normally be built by GitHub CI and exposed as CI artifacts. Their availability should not depend on a maintainer manually building or uploading them from a workstation.

This intent specifies the delivery invariant, not a workflow frequency or trigger policy. CI configuration may choose appropriate triggers and may evolve as the repository changes, provided the canonical PDFs remain reproducibly buildable and obtainable from GitHub CI.


---

$id-2748391057614286
title: Prefer Marceline Dev for AssemblyP1 execution
date: 2026/09/25
source: @ottojung
kind: preference

AssemblyP1 should prefer `lubko://marceline-dev` rather than `lubko://phoebe-dev` for delegated research, orchestration, and Lean execution. The managed-agent CLI should come from a pinned older Lubko checkout that still contains `lubko-agent`, exposed through a small wrapper such as `$HOME/.local/bin/lubko-agent` that runs `uv run --project /workspace/our-lubko-with-agent lubko-agent "$@"`. Matching Phoebe's exact Lean version is not required; use a suitable Lean available on Marceline for evaluator and verification work.
