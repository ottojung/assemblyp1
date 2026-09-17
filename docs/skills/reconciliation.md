# Reconciliation

Use this skill after two or more research packets have produced overlapping, competing, or dependent results. Reconciliation is a technical task: compare propositions and evidence, not personalities or prose quality.

## Normalize each result

For every output extract:

- exact claim;
- quantifiers;
- hypotheses;
- definitions/version of the model used;
- epistemic class;
- evidence location;
- known caveats;
- downstream claims that depend on it.

Rewrite notation into a common vocabulary before comparing claims.

## Compare assumption surfaces

In assemblyp1, explicitly compare:

- circular versus linear genome;
- known/fixed genome length versus candidate-dependent length;
- strand orientation and reverse-complement treatment;
- read length/error assumptions;
- latent read starts versus observed read strings;
- multiplicity versus deduplicated reads;
- repeat maximality and occurrence conventions;
- exact bridging predicate;
- exact likelihood versus an approximation/transformed objective;
- admissible candidate genomes;
- cyclic shift/equivalence semantics;
- maximizer versus unique-maximizer conclusion.

Many apparent contradictions disappear once these are aligned; many apparent agreements disappear too.

## Conflict classes

Classify a disagreement as one of:

1. **notation only** — same proposition after normalization;
2. **strength difference** — one result strictly strengthens/weakens another;
3. **assumption mismatch** — conclusions are not directly comparable;
4. **source convention mismatch** — two cited sources genuinely define different models;
5. **evidence mismatch** — e.g. computation versus proof of the same claim;
6. **substantive contradiction** — same proposition, same assumptions, incompatible conclusions;
7. **worker error** — one derivation/search/transcription is demonstrably wrong.

Do not collapse classes 3 or 4 into class 7 merely to simplify the project.

## Resolve systematically

For substantive contradictions:

1. reproduce both evidence trails;
2. reduce to the smallest proposition on which they disagree;
3. test a hand-checkable finite instance if possible;
4. re-read source text when source semantics are involved;
5. ask for an independent derivation or Lean check when appropriate;
6. preserve the unresolved fork if evidence is still insufficient.

The reconciler may reject a worker result, but should record why in a durable place if downstream work might otherwise repeat it.

## Merge the research graph

After reconciliation:

- deduplicate equivalent issue nodes;
- add implication/dependency edges exposed by stronger/weaker results;
- mark refuted conjectural nodes and link their witnesses;
- promote proved lemmas to formalization tasks;
- split source ambiguities into explicit model forks;
- update downstream nodes whose assumptions changed.

Do not rewrite history to make the path look linear. Git and closed issues may retain dead ends; current docs should describe the live model and live frontier.

## Promotion rules

A result may be promoted only to the strongest status its evidence supports:

- cited text -> source fact about what the source says;
- executable bounded search -> computational evidence for that bound or a concrete witness;
- mathematical derivation -> mathematical proof, subject to assumption review;
- Lean theorem -> kernel-checked result about the formal definitions;
- Lean theorem + documented source correspondence -> candidate result about the published problem.

The last transition is especially important. Lean can prove the wrong formal statement perfectly.

## Handoff

Return:

```text
Results compared:
Normalized propositions:
Assumption differences:
Conflict classification:
Resolution/evidence:
Claims accepted and epistemic class:
Claims rejected/refuted:
Research graph changes:
Next frontier:
```
