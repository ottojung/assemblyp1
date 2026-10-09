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

For the current positive oriented theorem, the project keeps the source-supported implication from `I_s` to the required no-long-triple-repeat condition explicit rather than silently redefining `I_s`. Upgrading equality of complete spectra to genome uniqueness up to rotation still uses the external Bresler–Bresler–Tse complete-spectrum theorem on the **finite** same-length slice; the **population** theorem, by contrast, now discharges that step internally in the kernel (`AssemblyP1.Issue94Complete.population_unique_ML`, no external premise, axioms only `propext`, `Classical.choice`, `Quot.sound`). The finite corollary and the population endpoint must therefore not be conflated.

Two candidate conclusion schemas live in `AssemblyP1/Model.lean`: truth is an ML maximizer, and truth is the unique ML maximizer up to genome equivalence. Neither is designated as *the* published conjecture while the source ambiguity above remains unresolved.

## Finite-sample landscape

The finite (finite-sample) reading of the sentence has been classified
interpretation-by-interpretation in
[`docs/source-notes/interpretation-matrix-217.md`](source-notes/interpretation-matrix-217.md),
which is the row-by-row record behind issue #217. Its summary: every
interpretation of the finite question that is both determinate and
source-supported is resolved — eleven negative rows (nine kernel-checked,
sharing eight witness modules, and two exact-arithmetic reproductions) and four
positive rows, of which three are kernel-checked — the
oriented/same-length/genuine-§6.2 slice carries a kernel-checked maximizer
theorem plus kernel-checked rotation-uniqueness conditional on the external BBT
input, and the oriented **variable-length** slice is refuted in infinite
families (`AssemblyP1/OrientedVariableLengthSe62.lean`, the #210
classification, with the amplification mechanism kernel-checked at `M = 1, 2`).
**No determinate source-supported row remains open.** The last determinate row to
close was the same-length §6.2 question under the per-occurrence strengthening
`d_D(w) ≥ x(w)`, which Medvedev–Brudno §6.2 does not state: it is refuted by
`ATATACAC → ATACACAC` (exact ratio `3/2`, binomial `9/5`), kernel-checked in
`AssemblyP1/PerOccurrenceSameLengthCounterexample.lean`; see
[`docs/peroccurrence-samelength-dna-counterexample-212.md`](peroccurrence-samelength-dna-counterexample-212.md).
The residue outside the resolved set is one row under a different paper's
doubled-strand **concatenation** convention (R16), now open in *both*
directions — the known `AAATAT → AAAAAT` witness is kernel-checked
*inadmissible* under the length-`2G` remap (`doubled_not_information_feasible`),
and no beat is known — and one non-determinate row, the unspecified general
principle (R17); neither is a determinate source-supported reading of the 2016
sentence, and the resolved claim is not extended to either. A third non-source entry (R18) records the
disclosed two-disjoint-circles duplex model `(S, rc(S))`: circle-by-circle `I_s`
is exactly equivalent to `I_s(S)`, while duplex-as-a-whole is ill-defined and
strictly stronger, and when orientation is unobserved its normalized class
likelihood equals the Medvedev–Brudno molecule distribution. One further leaf
artifact is **resolved as redundant and is not a matrix row**: #216's general
sample-multiplicity `Part 6` formalization (uncommitted, no committed or board
result, and it does not compile) is **superseded by #210**, whose result is
already kernel-checked in `AssemblyP1/OrientedVariableLengthSe62.lean`; the
implication lattice claims no general amplification theorem.
#219's same-length complete-spectrum fibre-count is now **integrated**: its note
and exact-arithmetic audit are in the repository, and its Lean divisor-sum core
`AssemblyP1/FibreCountArithmetic.lean` (Möbius inversion, totient
rearrangement) is kernel-checked, with the BEST/Matrix-Tree graph content
external. It is a population counting result, not a matrix row. The positive
same-length *rotation-uniqueness* half
stays conditional on the external complete-spectrum input; only the population
theorem is now kernel-checked without it.
The referent question itself is untouched. The **final source-gap count** for the
2016 finite question is **7 unresolved items** (the canonical register
`docs/source-notes/finite-interpretation-universe-audit.md` §6, items 1–6 and 8;
item 7, the repository-provenance gap, was closed); the three bearing directly on
the matrix claim are the likelihood referent, the uninspected publisher
supplement, and the strand/equivalence convention. None is a matrix row, and none
is used to decide one; the enumeration is in
[`docs/source-notes/interpretation-matrix-217.md`](source-notes/interpretation-matrix-217.md)
§3.1.

## What would count as settlement

A positive settlement is a Lean proof of a formally justified version of the published implication. A negative settlement is a mathematically valid counterexample satisfying the faithfully formalized bridging hypotheses while violating the faithfully formalized maximum-likelihood conclusion.

A computationally discovered counterexample is useful, but the final repository should contain a kernel-checkable proof that the finite instance has the required properties.
