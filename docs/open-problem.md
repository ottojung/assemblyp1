# Open problem: bridging conditions and maximum-likelihood assembly

## Published source

Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, and David N. C. Tse, “Information-optimal genome assembly via sparse read-overlap graphs,” *Bioinformatics* 32(17), 2016, i494–i502. DOI: [10.1093/bioinformatics/btw450](https://doi.org/10.1093/bioinformatics/btw450).

Near the end of the paper the authors state:

> “Understanding whether bridging conditions can be used to guarantee that the maximum-likelihood sequence is the true sequence is currently an open question.”

The maximum-likelihood formulation they refer to is attributed to Medvedev and Brudno (2009). The exact definitions from that formulation must be incorporated before this repository claims to contain the final formal statement.

A primary-source trace of what the phrase “the maximum-likelihood formulation of the AP (Medvedev and Brudno, 2009)” does and does not denote is recorded in [`docs/source-notes/shomorony-mb-formulation-provenance.md`](source-notes/shomorony-mb-formulation-provenance.md); it separates the source facts from the reading and keeps the candidate-universe choice explicit. An independent reconciliation of the four candidate referents, the witness-sufficiency question, and the existing notes is [`docs/source-notes/mb-formulation-referent-reconciliation.md`](source-notes/mb-formulation-referent-reconciliation.md). The accepted text selects none of them; the repository must keep the referent, the candidate class, and the tie semantics explicit rather than silently choosing. A focused source-fidelity result on the conclusion's equivalence semantics is [`docs/source-notes/equivalence-and-tie-wellposedness.md`](source-notes/equivalence-and-tie-wellposedness.md): it proves that the exact likelihood is always cyclic-shift invariant, so the stronger “every maximizer is the truth” schema *requires* cyclic shift in the genome equivalence, and that reverse-complement equivalence is forced exactly when Medvedev–Brudno's reverse-complement-collapsed read types are used. The read-type space and the genome equivalence are therefore one coupled unresolved choice rather than two independent ones; equivalence conventions can only change tie-based conclusions. A consolidated determination of the conclusion semantics — maximizer-vs-uniqueness, cyclic-shift/reverse-complement equivalence, candidate length, and ties — with the residual ambiguity marked, is [`docs/source-notes/conclusion-semantics-determination.md`](source-notes/conclusion-semantics-determination.md).

## Assembly model used by Shomorony et al.

The paper works, for exposition, with a circular sequence `s` of length `G`. A sequencing experiment produces `N` error-free reads of common length `L`; reads are drawn independently and uniformly from the `G` possible length-`L` substrings of `s`, with circular indexing.

The paper builds on information-feasibility conditions involving repeats. Its set `I_s` requires, in addition to coverage, that:

1. every triple repeat is all-bridged; and
2. every pair of interleaved repeats is bridged in the required sense.

A repeat copy is bridged when a read extends beyond that copy on both sides. These conditions are sufficient for the paper's Not-So-Greedy construction to recover the true circular sequence up to cyclic shift.

## Formalization status and the remaining source boundary

The repository is no longer only a bootstrap `AssemblyModel`. It now kernel-checks substantial project mathematics, including finite counterexample certificates, normalized-spectrum arithmetic, abstract positive-circulation rigidity, a circular-word/spectrum adapter, and the primitive/periodic repeat-theory reduction used by the oriented same-length rigidity argument. These formal results deliberately use small source-independent abstractions where that gives a cleaner verification boundary.

That progress does **not** by itself settle which theorem the 2016 sentence denotes. A source-faithful final statement still requires reconciling the historical choices that remain material, especially:

- the exact Medvedev–Brudno candidate object/universe referred to by Shomorony et al.;
- oriented read strings versus reverse-complement-collapsed read types;
- whether candidate genome length is constrained or merely appears as an externally supplied likelihood parameter;
- maximizer versus uniqueness semantics and the corresponding genome equivalence;
- the exact bridge from Shomorony's information-feasibility condition to the hypotheses consumed by a particular formal theorem.

For the current positive oriented theorem, the project keeps the source-supported implication from `I_s` to the required no-long-triple-repeat condition explicit rather than silently redefining `I_s`. Likewise, upgrading equality of complete spectra to genome uniqueness up to rotation uses the external Bresler–Bresler–Tse complete-spectrum theorem unless and until that theorem is separately formalized.

Two candidate conclusion schemas live in `AssemblyP1/Model.lean`: truth is an ML maximizer, and truth is the unique ML maximizer up to genome equivalence. Neither is designated as *the* published conjecture while the source ambiguity above remains unresolved.

## What would count as settlement

A positive settlement is a Lean proof of a formally justified version of the published implication. A negative settlement is a mathematically valid counterexample satisfying the faithfully formalized bridging hypotheses while violating the faithfully formalized maximum-likelihood conclusion.

A computationally discovered counterexample is useful, but the final repository should contain a kernel-checkable proof that the finite instance has the required properties.
