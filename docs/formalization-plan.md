# Formalization plan

The order here is intentional: first make the statement faithful, then try to prove or refute it.

## 1. Recover the exact paper model

- [ ] Formalize the Shomorony et al. circular, error-free, fixed-read-length sampling model.
- [ ] Read the cited Medvedev–Brudno maximum-likelihood formulation and transcribe its admissible candidate sequences and objective exactly.
- [ ] Decide, with a citation, whether the open question asks for an ML maximizer result or uniqueness up to cyclic shift.
- [ ] Record any mismatch between the two papers' modeling conventions rather than silently reconciling it.

## 2. Strings and circular genomes

- [ ] Define a finite alphabet and finite strings.
- [ ] Define nonempty circular genomes and cyclic indexing.
- [ ] Define cyclic-shift equivalence and prove it is an equivalence relation.
- [ ] Define length-`L` circular reads/windows and occurrence multiplicity.

## 3. Sequencing observations and likelihood

- [ ] Represent an observed collection of reads with multiplicity.
- [ ] Define the probability/likelihood of an observation under a candidate genome exactly as required by the source model.
- [ ] Prove elementary normalization and invariance facts needed by the objective.
- [ ] Formalize maximum-likelihood and tie/uniqueness semantics.

## 4. Repeats and bridging

- [ ] Formalize repeat occurrences and the repeat classes actually used by the paper.
- [ ] Formalize bridged repeat copies.
- [ ] Formalize all-bridged triple repeats.
- [ ] Formalize interleaved repeats and the required bridging condition.
- [ ] Formalize coverage and the full information-feasibility predicate.

## 5. Validate the transcription

- [ ] Encode small examples from the paper or supplementary material.
- [ ] Prove that the Lean definitions classify those examples as the paper says.
- [ ] Write a prose correspondence argument from every theorem hypothesis/conclusion to the cited source definitions.

## 6. Attack the open problem

Develop both tracks in parallel where useful:

- positive track: derive likelihood inequalities from coverage and bridging structure;
- negative track: enumerate small finite genomes/read multisets looking for a counterexample, then prove any discovered instance inside Lean.

Do not weaken or strengthen the published statement merely because one track becomes easier.
