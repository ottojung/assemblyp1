# Maximum-likelihood conclusion and tie semantics

## Question

Shomorony et al. (2016) ask whether bridging conditions can guarantee that “the maximum-likelihood sequence is the true sequence.” This note records what the primary sources do and do not justify about the conclusion when the likelihood has multiple maximizers.

This note is independent of the separate unresolved question of which Medvedev–Brudno likelihood/feasible-set layer the 2016 sentence intends.

## Primary-source evidence

### Shomorony et al. (2016)

The accepted paper's Discussion first contrasts information-feasible reconstruction with optimization formulations. It says that Theorem 1 guarantees reconstruction of the true sequence but gives no guarantee that this sequence is the solution of an optimization-based formulation. It then calls the Medvedev–Brudno maximum-likelihood formulation a candidate for the “correct” formulation and asks whether bridging conditions can guarantee that “the maximum-likelihood sequence is the true sequence.”

Source: Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse, “Information-optimal genome assembly via sparse read-overlap graphs,” *Bioinformatics* 32(17), 2016, i494–i502, DOI `10.1093/bioinformatics/btw450`, Discussion.

The relevant passage does **not** define a tie-breaking rule, say that the likelihood optimum is unique, quantify over every optimum, or state an equivalence relation under which uniqueness is intended. The singular phrase “the maximum-likelihood sequence” therefore cannot by itself distinguish a selected maximizer from a unique maximizer.

The earlier author-hosted preprint (`nsgIlan.pdf`, "Optimal Sequence Assembly via Sparse Read-Overlap Graphs", 2016-01-23) does **not** contain the accepted open-question sentence at all: its Discussion poses a different question, and its only "likelihood" content is the appended Bresler same-likelihood theorem. It likewise adds no tie convention, so it does not resolve this distinction either. See `../source-notes/shomorony-open-question-referent.md` §3.4. Searches of the accepted article and version material for optimizer-selection or uniqueness language did not produce a source statement resolving the distinction.

### Medvedev and Brudno (2009)

Section 6.1 defines the global read-count likelihood for a circular candidate genome `D` and says: “we attempt to assemble the genome with the maximum global read-count likelihood.” The abstract similarly describes a framework for assembling the genome that is the “most likely source of the reads.”

Source: Paul Medvedev and Michael Brudno, “Maximum Likelihood Genome Assembly,” *Journal of Computational Biology* 16(8), 2009, 1101–1116, DOI `10.1089/cmb.2009.0047`, abstract and §6.1.

The paper defines optimization of the likelihood but does not, in the relevant formulation, provide a tie-breaking rule or a theorem that the optimizer is unique. Its algorithmic language therefore does not supply the missing semantics in Shomorony et al.'s later sentence.

## Source-faithful conclusion

The primary literature inspected here does **not resolve** whether the 2016 open question asks only for the truth to attain the maximum likelihood or for all maximum-likelihood solutions to represent the truth (equivalently, uniqueness modulo whatever genome equivalence the final source-faithful model adopts).

Accordingly, AssemblyP1 must preserve at least two distinct theorem schemas until stronger source evidence appears:

1. **truth-is-a-maximizer:** the true genome attains maximum likelihood among admissible competitors;
2. **all-maximizers-are-truth:** every admissible genome attaining maximum likelihood is equivalent to the true genome.

When the candidate class is nonempty and the likelihood maximum is attained, schema 2 is the operational uniqueness guarantee relevant to an unspecified ML assembler: any returned optimum is correct. It is strictly stronger in meaning than schema 1 whenever a non-equivalent tied optimum can exist.

Calling schema 2 “unique maximizer up to equivalence” is a modeling normalization, not wording supplied by the papers. The final equivalence relation (at minimum cyclic shift in the Shomorony circular model, with any additional source-supported identifications handled separately) must itself be justified before this schema can be identified with the published question.

## Formalization consequence

Lean may safely formalize and investigate both schemas in parallel. A proof of truth-is-a-maximizer is mathematically useful but must **not** be advertised as settling the stronger interpretation of the published open problem. Conversely, a counterexample consisting only of a non-equivalent tied maximizer refutes the all-maximizers-are-truth schema but does not refute truth-is-a-maximizer.

This ambiguity should remain explicit in downstream theorem names, issue dependencies, and correspondence claims. It must not be resolved by choosing whichever statement is easier to prove.

## Epistemic status

- The quoted/paraphrased statements about what the papers say are **source facts** from the primary papers cited above.
- The conclusion that the inspected sources leave tie semantics unresolved is a **source-analysis result**.
- The two-schema organization is a **modeling organization decision** designed to prevent an unsupported strengthening or weakening of the published question.
