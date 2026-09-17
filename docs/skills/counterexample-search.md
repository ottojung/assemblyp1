# Counterexample search

Use this skill to attack conjectures, candidate lemmas, or modeling interpretations by exhaustive or heuristic finite search.

## Principle

A computation may discover a witness, refute a universally quantified statement on one valid instance, or provide bounded evidence. It is not automatically a proof of completeness. Keep those roles separate.

## Specify the search space first

Record:

- alphabet and alphabet size;
- circular genome lengths considered;
- read length and sample size;
- whether reads are represented as sequences, multisets, or count vectors;
- candidate genome lengths/classes;
- equivalence reductions such as cyclic rotation or symbol renaming;
- exact bridging/coverage predicate;
- exact likelihood/objective being compared;
- all pruning rules and why they preserve completeness.

Do not let implementation convenience silently narrow the mathematical statement.

## Search modes

### Exhaustive refutation

Use when the finite space is small enough or symmetry reduction is strong enough. Enumerate canonical representatives, verify the hypotheses exactly, and test the conclusion.

### Targeted search

Use structural clues from failed proofs to bias toward likely witnesses: repeated motifs, minimal interleavings, triple repeats, rare/overrepresented read multiplicities, candidate genomes with altered repeat counts, or equality cases in proposed inequalities.

Targeted failure is evidence only within the searched family.

### Solver-assisted search

SAT/SMT/ILP or custom constraint search may encode larger instances. Preserve the generated instance and enough information to recheck it independently without trusting the solver's prose output.

## Symmetry reduction

Exploit only proved-safe symmetries. Common possibilities include cyclic rotation of a circular genome and alphabet renaming. Reverse complement is a symmetry only if the current source model's equivalence makes it one.

Document the canonicalization rule. If completeness depends on it, prove or separately validate that every instance has a representative in the reduced space.

## Witness minimization

When a counterexample is found, minimize it aggressively while preserving the relevant hypotheses and failure:

1. genome length;
2. alphabet size;
3. read length;
4. number of sampled reads;
5. number/complexity of repeats;
6. multiplicities in the observation.

Small witnesses are easier to understand and formalize.

## Certificates

A useful witness should be emitted as explicit finite data, not just a log line. Include:

- true circular genome;
- sampled read multiset/count vector and, if needed for bridging, latent start positions;
- candidate genome(s);
- verification of coverage and every bridging condition;
- exact likelihood values or an exact inequality certificate;
- equivalence check showing why the candidate is genuinely distinct when uniqueness is at issue.

Prefer integers/rationals and exact combinatorics over floating-point comparisons.

## From computation to Lean

A found witness can settle a universal conjecture negatively only after its conditions are mathematically verified. The preferred end state is a small Lean theorem constructing the instance and proving the hypotheses plus failed conclusion.

For a bounded no-counterexample result, formalize the enumeration only when the bound itself matters to the research. Otherwise record it as computational evidence and move on.

## Failure analysis

If no witness is found, report the exact bounds, runtime/search strategy, and which families were covered. Then ask whether the result suggests:

- increasing bounds;
- proving a structural lemma explaining the absence;
- improving symmetry reduction;
- attacking a narrower candidate lemma;
- changing the search variable from genomes to graph/count structures.

"No counterexample found" must never be paraphrased as "the conjecture appears true" without the bounds attached.
