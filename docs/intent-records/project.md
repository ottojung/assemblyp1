$id-2083587146518535
title: Formalize the published assembly open problem in Lean
date: 2026/09/17
source: @ottojung
kind: requirement

The purpose of this repository is to formalize the published open problem about whether the relevant bridging conditions guarantee that the maximum-likelihood assembly is the true genome, and to provide a foundation for trying to settle it.

---

$id-6292990609556170
title: Use a Lean project as the formal research substrate
date: 2026/09/17
source: @ottojung
kind: requirement

The repository should contain a Lean project and use formalization as the durable representation of the mathematical problem and any eventual proof or counterexample.

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

The repository should provide AI-facing research skills, instructions, and guides for an agentic loop that can distribute literature research, mathematical exploration, counterexample search, lemma formalization, and proof work across multiple workers, then reconcile partial results, guide subsequent search, and integrate trustworthy progress into the formal project. The workflow should preserve durable state and make disagreements, assumptions, and evidence explicit rather than merely aggregating agent summaries.

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
