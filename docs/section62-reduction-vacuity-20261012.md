# §6.2 transitive-reduction predicate: vacuity audit (2026-10-12)

**Status:** a kernel-checked diagnostic of the current implementation, not a
replacement definition or a solution of the general §6.2 ML classification.

## Formal discrepancy

In `AssemblyP1/Section62BidirectedFlow.lean`, `isReducibleB` attempts to
remove a direct overlap of length `e` between length-`L` reads when two
intermediate overlaps of lengths `l₁` and `l₂` satisfy all of:

- `0 < l₁ < e` and `0 < l₂ < e`;
- `l₁ + l₂ - L = e`, using natural-number subtraction;
- ordinary read overlaps are proper: `e < L`.

Those requirements cannot hold simultaneously. Indeed
`l₁ + l₂ <= 2e - 2 < L + e`. For a positive result of the natural
subtraction to equal `e`, one would require at least `l₁ + l₂ >= L + e`.
The Lean audit makes this rigorous, including all zero-length boundaries.

`Section62ReductionVacuityAudit.lean` proves that the predicate is false
on every proper-overlap edge and that filtering a list of such edges by the
current `transitivelyReduced` definition leaves the list unchanged. All
exposed theorems are checked with `#print axioms`.

## Source-fidelity implication

Medvedev and Brudno, *Maximum Likelihood Genome Assembly* (2009), §6.2
describe a nontrivial transitive edge reduction corresponding to a two-step
spelling of the same sequence and attribute it to Myers (2005). The current
model cannot be that operation if it never deletes an edge.

The alternative `isReducibleLongerB` already in the repository uses longer
path overlaps, but it does **not** enforce the full same-spelling composition
identity or prove the requisite bidirected incidence compatibility. It should
not automatically replace the literal predicate without source and proof audit.

A suitable successor should specify an intermediate read/orientation and
prove (rather than assume) spelling equivalence, graph-language preservation,
and Observation 7's vertex-throughput interpretation. Reassess dependent
counterexample claims under that corrected model.

**References:** Medvedev–Brudno (2009), §6.2,
https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/ .
