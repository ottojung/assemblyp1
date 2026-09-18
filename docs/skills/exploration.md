# Adaptive exploration

Use this skill when the research frontier is uncertain and several materially different approaches, lemmas, model interpretations, experiments, or reductions could plausibly advance the published open problem.

The purpose is to manage **search effort**, not to decide mathematical truth. Portfolio priority never upgrades a claim's epistemic status. This is the project's default mode after the initial statement is pinned down and before a mature proof or counterexample is ready for final formal verification.

## Maintain an approach portfolio

Keep a small live portfolio of distinct research states. An entry may be a hypothesis, proof architecture, candidate lemma family, counterexample family, reduction, source interpretation to test, computational encoding, or other concrete route.

For each entry record only what is useful:

- exact idea or question;
- assumptions and model version;
- current evidence and epistemic class;
- cheapest useful evaluator or falsification test;
- expected downstream leverage;
- important failures already observed;
- next mutation, combination, or refinement worth trying.

Cluster or deduplicate entries that are equivalent after normalizing assumptions. Preserve genuinely different assumption surfaces as separate entries.

## Generate diversity before convergence

When the frontier is unclear, generate several **meaningfully different** approaches rather than many paraphrases of one idea. Diversity can come from different representations, reductions, source interpretations, proof invariants, search variables, or abstraction levels.

Do not force a positive/negative split, a fixed number of approaches, or any particular family. The live problem state determines useful diversity.

## Evaluate cheaply and continuously

Before spending substantial effort, run the cheapest evaluator that can change the decision about an approach. Depending on the claim, evaluators may include:

- primary-source checks;
- tiny hand-worked examples;
- bounded exact computation;
- counterexample search;
- a deliberately tiny Lean typecheck or micro-lemma when it is cheaper than resolving the question informally;
- theorem-strength/assumption comparison;
- dimensional or invariance sanity checks;
- independent derivation.

Evaluator failure is feedback. Feed the exact failure back into the approach and either revise it, weaken it, split it, or retire it.

Tests and scores are evidence about **where to search next**, not evidence that the conjecture is true. Do not escalate a successful evaluator into broad Lean formalization unless the initial statement or a mature final argument actually requires it.

## Best-first allocation

Allocate workers to the currently highest-value frontier entries rather than processing a static queue.

Useful scheduling considerations include:

- probability that a cheap test will decisively resolve uncertainty;
- downstream nodes unblocked if successful;
- ability to kill an attractive but wrong direction quickly;
- novelty relative to work already attempted;
- strength and reliability of current evidence;
- expected cost;
- availability of an independent verification route.

Do not encode these as a rigid numerical formula unless doing so is genuinely useful. The orchestrator may revise priorities whenever new evidence arrives.

## Evolve promising approaches

A promising route should not merely be repeated. Improve it by:

- mutating a failed assumption;
- weakening or strengthening an intermediate statement;
- changing representation;
- combining compatible parts of two approaches;
- extracting the obstruction exposed by a failed proof;
- turning a computational pattern into a structural conjecture;
- turning a Lean failure into a corrected mathematical statement.

Retain provenance so that a descendant approach records what changed and why.

## Generate scaffold problems

When the target is too hard to interrogate directly, deliberately create easier neighboring problems whose answers may expose structure. Examples include restricted parameter regimes, toy models, minimal repeat structures, alternate but source-compatible formulations, or local lemmas.

A scaffold problem is an **instrument**, not a replacement target. Record how solving or refuting it is expected to inform the published problem. Retire scaffolds that stop providing information.

## Portfolio lifecycle

An approach may be:

- **active** — worth current effort;
- **dormant** — plausible but lower priority or waiting on a dependency;
- **refuted** — falsified under its stated assumptions;
- **subsumed** — replaced by a stronger or cleaner approach;
- **blocked** — cannot progress until a named dependency is resolved.

Do not delete refuted or blocked approaches when their failure is informative. Preserve the smallest useful obstruction and link it from later descendants.

## Parallel workers and Lubko

Broad exploration should normally use Lubko as a **fan-out engine**, not as an occasional fallback. When multiple materially different approaches, evaluators, counterexample families, reductions, or interpretations are worth testing and worker slots are available, dispatch several narrow `lubko-agent` packets in parallel and let their results compete or complement one another.

Use the orchestrator primarily to generate/diversify packets, steer workers, notice duplication, compare exact claims, and synthesize the next frontier. Do not spend the whole cycle doing substantive exploratory mathematics directly while useful Lubko slots sit idle unless there is a concrete reason the work is better kept local or serial.

Prefer diversity over replication by default. Independent replication is useful when a claim is important or suspicious, but several agents should not receive vague near-identical "solve it" prompts.

AssemblyP1 has a project-specific concurrency limit: **no more than 5 agents may be actively working in parallel**. This overrides Lubko's generic advice to use as many agents as useful. If more than five packets are ready, keep the remainder in the portfolio/frontier and launch them in later waves as slots free up.

The cap applies to actively working delegated agents, not to dormant issues, completed agents, or queued portfolio entries.

## Handoff

A useful exploration handoff is concise:

```text
Portfolio changes:
Evaluators run:
Approaches promoted for more effort:
Approaches revised/subsumed/refuted:
New scaffold questions:
Best current frontier:
Why it is next:
```

The orchestrator should leave the portfolio in a state another invocation can recover from durable repository/GitHub state.
