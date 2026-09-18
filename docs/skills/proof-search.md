# Proof search

Use this skill when the mathematical statement is stable enough to attack but the proof is not known.

## Start from the exact proposition

Write the target with all quantifiers and hypotheses. Name which hypotheses come from the published model, which are previously proved lemmas, and which are temporary exploratory assumptions.

Do not begin from an informal slogan such as "bridging should imply ML." State which bridging predicate, which likelihood, which candidate class, and which genome equivalence are in force.

## Maintain a proof-approach portfolio

Do not commit immediately to one proof architecture. Maintain a small set of materially different approaches and apply `exploration.md`.

An approach may be:

- a lemma decomposition;
- a representation change;
- a reduction to an adjacent theorem;
- an invariant;
- a likelihood comparison scheme;
- a graph/string transformation;
- a contradiction strategy;
- a scaffold problem designed to reveal structure.

Cluster equivalent ideas. Keep approaches separate when their assumptions or target variants differ.

Portfolio priority determines where to spend effort, not whether an approach is mathematically correct.

## Build local lemma DAGs when useful

Within a promising approach, work backward from the target and forward from available structure. A lemma DAG is one representation of a proof route, not the mandatory global research plan.

For each central candidate lemma record:

- exact statement;
- dependencies;
- why it advances that approach;
- current epistemic status;
- cheapest plausible evaluator/falsification test;
- useful weaker or neighboring variants.

Prefer lemmas that are independently meaningful or discriminate between multiple approaches.

## Use cheap evaluators early

Before investing deeply in a central lemma or architecture:

- test tiny finite instances when feasible;
- search for degenerate/equality cases;
- inspect hidden assumptions such as fixed candidate length or stronger bridging;
- negate the conclusion and look for a minimal witness;
- compare with known source results;
- try a small Lean formulation/typecheck when it can expose missing conditions;
- ask an independent worker to derive or attack the same key step.

A failed evaluator should change the next attempt. Do not simply retry the same proof with more prose.

## Evolve failed and promising routes

Use failures constructively:

- identify the exact obstruction;
- weaken or strengthen an intermediate lemma;
- change representation;
- split one route into distinct assumption cases;
- combine compatible insights from different approaches;
- extract a structural conjecture from computational evidence;
- turn a Lean failure into a corrected mathematical statement.

Record what changed between parent and descendant routes when useful.

## Generate scaffold problems

When the full theorem is too opaque, create easier neighboring problems that may expose structure: restricted parameter regimes, simpler repeat configurations, toy likelihood models, or local lemmas.

A scaffold must state why its resolution informs the published target. Solving a scaffold does not count as solving the open problem, and a scaffold should be abandoned when it stops yielding information.

## Equality and uniqueness

Keep weak and strong conclusions separate:

1. truth is an ML maximizer;
2. every ML tie is genome-equivalent to truth.

A proof of (1) does not imply (2). When deriving inequalities, track equality conditions from the beginning.

## Lean interaction

Once a lemma has a stable mathematical idea—or when a tiny Lean experiment is the cheapest useful evaluator—use Lean early.

Lean failures often expose missing side conditions or overstrong statements. Conversely, do not spend large formalization effort on an approach that has not earned that effort through evidence or leverage.

If a proof attempt fails, preserve the exact obstruction. "Could not prove" is weak; a precise failure can become the next portfolio entry or evaluator.

## Parallel delegation

When several proof packets are worth exploring and Lubko is available, prefer `lubko-agent` for substantive subjobs. Follow the AssemblyP1-wide cap of **at most 5 actively working delegated agents in parallel**.

Use parallelism for genuinely distinct routes, independent checks, or targeted evaluators—not five near-identical attempts at the same vague prompt.

## Handoff

Return:

```text
Target:
Active proof approaches:
Approach/evaluator results:
Established lemmas and evidence class:
Central unresolved steps:
Scaffold problems and what they teach:
Failed/subsumed routes:
Equality/uniqueness issues:
Best next proof/search packet and why:
```
