# Formalization plan

This document records formalization obligations that are currently visible from the published problem and the repository's source analysis. It is **not** the project's research strategy, not a priority queue, and not a prescribed route to a proof or counterexample.

The ordering below is organizational only. The research orchestrator may formalize objects in a different order, interleave formalization with mathematical discovery, postpone work whose semantics are unstable, or introduce different intermediate abstractions when that better serves the ultimate goal. Any formalization must still preserve source fidelity.

## 1. Recover the exact paper model

- [ ] Formalize the Shomorony et al. circular, error-free, fixed-read-length sampling model.
- [ ] Read the cited Medvedev–Brudno maximum-likelihood formulation and transcribe its admissible candidate sequences and objective exactly.
- [ ] Determine from the literature whether the open question asks for an ML maximizer result, uniqueness up to cyclic shift, or another precise statement.
- [ ] Record any mismatch between the source papers' modeling conventions rather than silently reconciling it.

## 2. Strings and circular genomes

- [ ] Define the string/genome objects needed by the source-faithful model.
- [ ] Define circular indexing and the relevant genome equivalence.
- [ ] Prove the basic equivalence/invariance facts required by later statements.
- [ ] Define fixed-length circular reads/windows and occurrence multiplicity as required by the model.

## 3. Sequencing observations and likelihood

- [ ] Represent the observed sequencing data with the multiplicity information required by the source model.
- [ ] Define the probability/likelihood of an observation under an admissible candidate genome exactly as required by the literature-grounded model.
- [ ] Prove normalization, invariance, and other elementary facts that later arguments actually need.
- [ ] Formalize the maximum-likelihood and tie/uniqueness semantics established by the literature work.

## 4. Repeats and bridging

- [ ] Formalize repeat occurrences and the repeat classes actually used by the paper.
- [ ] Formalize the source-faithful bridging predicates.
- [ ] Formalize triple-repeat and interleaving conditions where required.
- [ ] Formalize coverage and the complete hypothesis of the published question.

## 5. Validate the transcription

- [ ] Encode source examples or other hand-checkable instances useful for validating the definitions.
- [ ] Check that the Lean definitions classify those instances consistently with the source mathematics.
- [ ] Maintain a prose correspondence argument from the formal hypotheses/conclusion to the literature-grounded statement.

## Boundary of this document

This checklist ends at the boundary between **representing the problem faithfully** and **deciding how to solve it**.

It intentionally does not prescribe how to prove or refute the conjecture. Proof discovery belongs to the live research graph and the orchestration process in `docs/research-orchestration.md`. Agents and orchestrators should choose, revise, combine, or abandon methods in response to evidence. A proof, counterexample, reduction, computation, structural classification, imported theorem, or other sound route may be appropriate; this document does not privilege any of them in advance.

Do not weaken or strengthen the published statement merely because a particular method becomes easier.
