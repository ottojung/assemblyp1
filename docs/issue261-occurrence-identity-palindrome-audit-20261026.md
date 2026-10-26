# Issue #261: occurrence identity under RC-palindrome quotienting

**Scope.** This note answers only whether the current tagged-edge representation
retains occurrence identity when a strand is self reverse-complementary. It does
not assert genome-to-flow inclusion or transfer a maximality result.

## Finding: two different identities are present

`Section62PhysicalHalfIncidence.lean:23-27` defines a tagged strand as
`W × Bool`, `cls (w,b) = (w,false)`, and `flip (w,b) = (w,!b)`. The bit is an
orientation tag on the *same word value*; it is not an occurrence identifier.
In the quotient `Section62PhysicalEdgeOrbit.lean:66-102`, an edge is equivalent
only to itself or its `reverseEdge`. Thus the quotient forgets which of those
two oriented representations was used, and does not preserve a tagged
occurrence ID (none is encoded). It does **not**, however, identify arbitrary
distinct edge values just because one endpoint word is palindromic.

The distinction matters in two concrete ways:

1. The exact word-based palindrome example at
   `Section62PalindromeEdgeMultiplicityAudit.lean:38-78` proves
   `rcWord ATAT = ATAT`, `strandsOf rcWord [ATAT] = [ATAT,ATAT]`, and that the
   legacy `overlapEdges` list contains the same edge value four times. A
   `BdFlow` is a function on edge values (not list positions), while the
   feasibility folds traverse that list (same file, lines 13-17 and 56-79).
   Therefore four enumerated occurrences are not four independently weighted
   edge occurrences in that representation. This is an exact duplication
   witness, not a claim about the intended MB09 multiplicity convention.

2. In the tagged physical-orbit model, `Section62PhysicalEdgeOrbit.lean:202-237`
   checks `ATAT` with overlap length 2: four orientation cases `E1`..`E4`
   collapse to three orbits, since `reverseEdge E1 = E4`, while `E2` and `E3`
   are self-reversing and remain different from each other and from `E1`'s
   orbit. This is correct quotienting by reversal of an edge representation,
   but it is not quotienting by independent occurrence identity.

## Bounded conclusion / missing premise

No occurrence-identity-preservation lemma follows from these definitions:
the occurrence index is erased before `BdFlow` is applied, and duplicate edge
values share a single flow coordinate. A future occurrence-level flow model
would need an explicit occurrence/index type and a map from occurrences to
physical edge orbits, together with a stated rule for whether duplicate
palindrome-generated occurrences add multiplicity or are deduplicated. Until
that rule is fixed, proofs about orbit coordinates cannot be interpreted as
proofs about independently weighted occurrences. Conversely, the current
quotient does preserve the physical edge-orbit distinction it defines; it does
not merge the three ATAT loop orbits into one.

## Validation and provenance

Source definitions cited above are in `Section62PhysicalHalfIncidence.lean`,
`Section62PhysicalEdgeOrbit.lean`, and
`Section62PalindromeEdgeMultiplicityAudit.lean`. Their exact finite statements
are kernel-checked in the cited Lean files. This document adds no Lean code and
makes no claim about MB09's intended treatment beyond the ambiguity already
recorded by the source audit.
