# Formalization

Use this skill to translate a stable piece of the mathematical model or proof into Lean while preserving the published semantics.

## Before coding

Identify:

- the source definition or theorem being formalized;
- the exact mathematical object and its invariants;
- whether the object belongs to the sequencing process, the observable data, the candidate-genome model, or the proof layer;
- the equivalence relation involved;
- any still-unresolved source ambiguity.

Do not encode an unresolved ambiguity merely because Lean requires a definition. Isolate it behind a parameter/interface or return it to the research graph.

## Design rules

Prefer representations that make the source mathematics transparent before optimizing the API. Small explicit definitions are better than clever abstractions whose biological meaning is difficult to audit.

For circular genomes, keep positions and cyclic indexing explicit enough that source examples can be checked. Avoid quotienting early unless quotienting materially simplifies later proofs without hiding distinctions needed by repeats or read placements.

Distinguish latent sequencing information from observed data. A sampled start position may witness that an occurrence was bridged; the ML objective should depend only on the observable read data if that is what the source model specifies.

Preserve multiplicity when the probability model uses multiplicity. A set of distinct reads is not interchangeable with a multiset/count vector merely because an assembly-graph algorithm later deduplicates reads.

## Development loop

On `phoebe-dev`, first follow [`lean-on-phoebe-dev.md`](lean-on-phoebe-dev.md) so the host Elan installation is on `PATH` and worktrees do not grow duplicate toolchains.

1. Add the smallest definition or theorem interface justified by the source.
2. Encode one or more hand-checkable examples.
3. Prove elementary invariance/normalization lemmas before larger theorems.
4. Use temporary `example` declarations or scratch experiments while exploring, but do not commit `sorry`, `admit`, or new axioms into the library.
5. Run `lake build` frequently.
6. Keep declarations small enough that failed proof attempts reveal which mathematical fact is missing.

## Statement fidelity review

Before calling a formalization complete, compare Lean and prose dimension-by-dimension:

- quantifiers;
- finite/nonempty assumptions;
- circular versus linear topology;
- fixed versus candidate-dependent genome length;
- alphabet assumptions;
- orientation/reverse complement treatment;
- read sampling and errors;
- multiplicity;
- repeat occurrence/maximality definitions;
- bridging witness semantics;
- likelihood normalization;
- candidate class;
- equality/equivalence and tie semantics.

A proof of a nearby stronger or weaker theorem does not settle the target unless the relationship is itself proved and documented.

## Lemma boundaries

When formalizing proof work, prefer lemmas with one conceptual job and reusable statements. If a theorem requires a long proof because several source/model facts are entangled, split it along mathematical dependencies, not merely file size.

Name intermediate results by what they establish, not by the current proof step number.

## Handoff

A formalization PR should explain:

```text
Source/model statement represented:
Lean declarations added/changed:
Correspondence argument:
Examples/tests:
Assumptions intentionally left abstract:
Known mismatches or unresolved questions:
Downstream lemmas now possible:
```

Green CI proves that Lean accepted the code; it does not by itself prove source fidelity. That correspondence must remain reviewable in prose.
