# Formalization plan

This document defines **when** AssemblyP1 should use Lean. It is not the research roadmap and it is deliberately much smaller than a conventional bottom-up formalization plan.

## Principle

AssemblyP1 is exploration-first.

Lean has two primary jobs:

1. **Formalize the initial published statement faithfully.**
2. **Formalize the final result once there is a plausible, coherent proof or counterexample in mathematical notes.**

The project should not eagerly formalize intermediate objects, definitions, invariance lemmas, or proof infrastructure merely because they appear stable or might be useful later. During discovery, ordinary mathematical notes, executable experiments, literature work, toy examples, reductions, and proof sketches are the default media.

## Phase A — pin down the initial statement

Formalize only enough source-faithful structure to make the target proposition precise and typecheckable.

The initial statement must expose every distinction that materially changes the published question, including where relevant:

- the circular/error-free sequencing model;
- observed read multiplicity;
- admissible candidate-genome universe;
- exact versus approximate maximum-likelihood variants left unresolved by the literature;
- bridging/repeat hypotheses used by the published question;
- genome equivalence and maximizer-versus-uniqueness conclusions.

When the literature genuinely leaves a choice unresolved, preserve parallel statement variants or explicit parameters. Do not resolve ambiguity by choosing whichever formulation is easiest to formalize.

This phase is complete when the repository has a defensible formal target, or explicit family of target variants, whose correspondence to the accepted literature is documented. It does **not** require a reusable formal library of every intermediate biological or combinatorial notion.

## Exploration phase — default research mode

After the initial statement is sufficiently pinned down, stop expanding Lean infrastructure by default.

Research should proceed primarily through:

- mathematical notes and proof sketches;
- examples and counterexamples;
- exact or bounded computation;
- structural conjectures and reductions;
- literature connections and adjacent theorems;
- competing proof architectures;
- adversarial checking of assumptions and equality cases.

Stable intermediate facts should normally be preserved in notes/issues. They do not automatically earn a Lean implementation.

If an intermediate formalization branch or PR already exists, bring it to a coherent and useful stopping point rather than expanding its scope merely to make the formalization feel complete. Preserve what it established, then merge, close, or park it according to its actual value.

## Phase B — formalize a mature result

Return to substantial Lean development once there is a **plausible complete notes proof or counterexample**: an argument whose main structure is understood, whose essential lemmas are identified, and which has survived serious informal and adversarial checking.

Then:

- formalize the exact target variant being settled;
- formalize only the definitions and lemmas actually required by that argument;
- use Lean failures to repair the notes proof when they expose a genuine gap;
- run the full repository verification and axiom audit;
- maintain a prose correspondence argument showing that the verified theorem really addresses the published problem.

If formalization reveals that the notes proof has a substantive gap, return to exploration rather than compensating by building large speculative formal infrastructure.

## Exception — tiny Lean evaluators

A small Lean experiment is appropriate when it is the cheapest way to answer a concrete question such as:

- whether a proposed lemma is well-typed under the current model;
- whether an apparently obvious finite or invariance fact needs an extra hypothesis;
- whether a key reduction matches the exact target statement.

Keep these experiments tightly bounded. Their purpose is to inform exploration, not to create a permanent bottom-up formalization queue.

## Source fidelity

At both formalization boundaries, do not weaken or strengthen the published statement merely because a different theorem is easier to encode or prove.
