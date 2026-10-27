# Issue #261: reduction semantics audit (2026-10-27)

**Status:** source-checked diagnosis; does not select or implement a replacement
for the MB09/Myers reduction. The general flow maximality question remains open.

## Primary-source facts

I independently retrieved Medvedev and Brudno, *Maximum Likelihood Genome
Assembly* (2009), §6.2 from PMC3154397 on 2026-10-27. The text says to build a
bidirected overlap graph with overlaps of length at least `o_min`, then perform
“transitive edge reduction, where we remove any overlap that is spelled by two
shorter overlaps,” calling the result the transitively reduced graph. Observation
7 is stated for walks in that reduced graph. Section 6.2 then says the original
double-stranded genome corresponds to a circuit and uses vertex lower bound 1.
The primary paper's prose does not specify the combinatorial test for “spelled
by,” nor whether the intermediate read must be distinct, what strand orientations
qualify, or whether the graph's own reduction is applied recursively or
simultaneously. The repo's `docs/section62-mb09-bidirected-graph-audit.md`
independently transcribes the same passage and earlier audits two interpretations;
this note therefore confirms and sharpens that existing audit rather than
claiming discovery of a previously unrecorded source gap.

## Audit of the repository's two tests

The current `AssemblyP1/Section62BidirectedFlow.lean` `isReducibleB` tests a
candidate overlap of length `e` via two overlaps of lengths `l₁,l₂`, both
strictly less than `e`, and the composition equation

```text
l₁ + l₂ - L = e
```

where `L` is read length and subtraction is natural subtraction. For positive
`l₁,l₂ < e < L`, one has `l₁ + l₂ ≤ 2e - 2 < L + e`; but equality to `e` after
natural subtraction requires `l₁ + l₂ ≥ L + e`. Thus this exact predicate is
unsatisfiable on proper overlaps. This is a valid diagnosis of the implementation,
not evidence that the source operation is vacuous. In particular, “strictly
shorter” could mean shorter than the read length, rather than shorter than the
candidate overlap; and a two-edge *path spelling a string* need not be captured
by the equation as currently attached to two maxima.

`isReducibleLongerB` instead removes a candidate when both overlaps through a
middle strand are longer than the candidate. This is closer to one conventional
transitive-overlap intuition but checks neither identity of the composed spelled
string nor full bidirected incidence compatibility. It is not established as
Myers (2005)'s reduction and cannot currently support Observation 7.

Consequently the reduction semantic gap remains live even though the earlier
vacuity lemma is correct. Counterexamples relying on the unreduced graph or on
either predicate transfer to source-faithful §6.2 only after proving candidate-
set inclusion (for negative transfer) or graph-language preservation and the
Observation-7 visit/occurrence identity (for positive transfer).

## Required certificate for a successor

For each direct edge `x→y` and proposed intermediate strand `m`, a proposed
replacement definition should provide a finite spelling certificate: oriented
overlap matches `x→m` and `m→y`, the implied placement offsets, and a proof that
the resulting spelled segment is exactly the direct overlap (including endpoint
incidence consistency in the bidirected graph). It should state its strictness
convention and the `o_min` domain. Before reusing any ML result it must separately
establish (a) equality of the sets of spelled molecules/walks before and after
reduction, and (b) that every read's walk visits equal its number of occurrences
as a submolecule. MB09 asserts the latter as Observation 7 but gives no proof in
the retrieved paragraph; it cannot be inferred merely from language preservation.

## Issue status

No source-faithful correction, general necessary-and-sufficient maximality
criterion, or transfer of previous full-overlap failures is established here.
Keep #261 and parent #255 open. This audit narrows the next work to independently
reconstructing Myers's reduction and proving its graph-language/occurrence
properties, then repeating the small-instance flow/circuit census on that exact
graph. Existing results for integer versus half-integral flows, likelihood
choice, orientation/reverse-complement classes, and non-spelled flows remain
separate axes and are not resolved by this audit.

**Sources:** MB09 §6.2, <https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/>;
Myers 2005 is cited by MB09 as the reduction source, but its algorithm has not
been reconstructed in this note.
