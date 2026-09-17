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
title: Establish the literature ground truth for the formal statement
date: 2026/09/17
source: @ottojung
kind: requirement

The literature work must lock down the ground truth of the exact mathematical statement that the accepted literature leaves open. Before a proof or counterexample is treated as addressing the published problem, the repository should establish from primary sources the intended model, hypotheses, optimization objective, admissible competitors, equivalence and tie semantics, and other statement-defining conventions. Genuine source ambiguity should be recorded explicitly and investigated rather than resolved for convenience. Incremental or provisional formalizations are useful research artifacts, but no convenient interpretation should become the canonical target without literature-grounded justification.
