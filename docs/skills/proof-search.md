# Proof search

Use this skill when the mathematical statement is stable enough to attack but the proof is not known.

## Start from the exact proposition

Write the target with all quantifiers and hypotheses. Name which hypotheses come from the published model, which are previously proved lemmas, and which are temporary exploratory assumptions.

Do not begin from an informal slogan such as "bridging should imply ML." State which bridging predicate, which likelihood, which candidate class, and which genome equivalence are in force.

## Build a lemma DAG

Work backward from the target and forward from available structure. Turn the proof into a directed acyclic graph of candidate lemmas rather than a linear narrative.

For each candidate lemma record:

- exact statement;
- dependencies;
- why it advances the target;
- whether it is source-known, conjectural, computationally tested, proved on paper, or Lean-checked;
- easiest plausible falsification test;
- useful weaker variants.

Prefer lemmas that are independently meaningful and reusable across several proof branches.

## Run adversarial checks early

Before investing in a central lemma:

- test tiny finite instances when feasible;
- search for degenerate cases and equality cases;
- inspect whether the lemma secretly assumes fixed candidate length, unique reads, or a stronger bridging condition;
- negate the conclusion and ask what a minimal counterexample would have to look like;
- compare with known combinatorics-on-words or assembly results in the literature.

A cheap falsification is progress.

## Positive proof strategies

For the assemblyp1 target, promising families of arguments may include:

- reconstructing structural constraints on any candidate that explains all observed reads;
- translating bridging into constraints on repeat multiplicities or admissible graph traversals;
- expressing likelihood ratios between a candidate and the truth and factoring them into local/count terms;
- proving that a candidate with different repeat structure must lose likelihood or violate an observed read constraint;
- reducing global comparison to a finite family of graph/string transformations whose likelihood effect can be analyzed.

These are research directions, not assumptions. Discard them if the formal model does not support them.

## Equality and uniqueness

Keep the weak and strong conclusions separate:

1. truth is an ML maximizer;
2. every ML tie is genome-equivalent to truth.

A proof of (1) does not imply (2). When deriving inequalities, track equality conditions from the beginning rather than trying to reconstruct them after the main proof.

## Lean interaction

Once a lemma has a stable mathematical proof idea, hand it to formalization early. Lean failures often expose missing side conditions or overly strong statements. Conversely, do not spend large amounts of Lean effort on a speculative lemma that has not survived small-case testing or mathematical scrutiny.

If a proof attempt fails, preserve the exact obstruction. "Could not prove" is weak; "the induction loses the bridging witness because the reduced genome does not preserve condition X" is a reusable negative result.

## Handoff

Return:

```text
Target:
Lemma DAG:
Established lemmas and evidence class:
Central unproved lemmas:
Counterexample checks performed:
Failed approaches and why:
Equality/uniqueness issues:
Best next proof or search packet:
```
