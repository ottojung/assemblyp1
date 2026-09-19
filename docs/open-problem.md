# Open problem: bridging conditions and maximum-likelihood assembly

## Published source

Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, and David N. C. Tse, “Information-optimal genome assembly via sparse read-overlap graphs,” *Bioinformatics* 32(17), 2016, i494–i502. DOI: [10.1093/bioinformatics/btw450](https://doi.org/10.1093/bioinformatics/btw450).

Near the end of the paper the authors state:

> “Understanding whether bridging conditions can be used to guarantee that the maximum-likelihood sequence is the true sequence is currently an open question.”

The maximum-likelihood formulation they refer to is attributed to Medvedev and Brudno (2009). The exact definitions from that formulation must be incorporated before this repository claims to contain the final formal statement.

The primary-source resolution of the objective, candidate class, length convention, circular equivalence, sampling model, and tie semantics is recorded in [`docs/source-notes/ml-objective-candidate-class-resolution.md`](source-notes/ml-objective-candidate-class-resolution.md), including the source-version fork between the accepted article and the author-hosted early preprint. The accepted 2016 main text has been independently re-retrieved and verified, and the exact `§6.1` (exact multinomial) → binomial approximation → `§6.2` (read-overlap biflow) relation recorded, in [`docs/source-notes/ml-accepted-text-source-verification.md`](source-notes/ml-accepted-text-source-verification.md).

## Assembly model used by Shomorony et al.

The paper works, for exposition, with a circular sequence `s` of length `G`. A sequencing experiment produces `N` error-free reads of common length `L`; reads are drawn independently and uniformly from the `G` possible length-`L` substrings of `s`, with circular indexing.

The paper builds on information-feasibility conditions involving repeats. Its set `I_s` requires, in addition to coverage, that:

1. every triple repeat is all-bridged; and
2. every pair of interleaved repeats is bridged in the required sense.

A repeat copy is bridged when a read extends beyond that copy on both sides. These conditions are sufficient for the paper's Not-So-Greedy construction to recover the true circular sequence up to cyclic shift.

## What must be formalized before attacking the conjecture

The bootstrap Lean files deliberately expose only an abstract `AssemblyModel`. A faithful theorem statement still requires extracting and reconciling at least:

- finite circular strings and equality up to cyclic shift;
- fixed-length read sampling with multiplicity;
- coverage;
- repeats, maximal repeats if required by the paper's definitions, triple repeats, interleaving, and the exact bridging predicates;
- the information-feasible condition actually intended in the open-question sentence;
- the Medvedev–Brudno maximum-likelihood objective, including what candidate genome lengths are allowed and how ties are treated;
- the exact conclusion meant by “the maximum-likelihood sequence is the true sequence.”

Two candidate conclusion schemas currently live in `AssemblyP1/Model.lean`: truth is an ML maximizer, and truth is the unique ML maximizer up to genome equivalence. Neither is yet designated as the published conjecture.

## What would count as settlement

A positive settlement is a Lean proof of a formally justified version of the published implication. A negative settlement is a mathematically valid counterexample satisfying the faithfully formalized bridging hypotheses while violating the faithfully formalized maximum-likelihood conclusion.

A computationally discovered counterexample is useful, but the final repository should contain a kernel-checkable proof that the finite instance has the required properties.
