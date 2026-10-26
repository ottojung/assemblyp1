# Bounded genome-to-orbit-flow bridge and its RC limit (#261)

**Status: conditional inclusion lemma plus a concrete non-inclusion for a
naive oriented lift.** This note separates two candidate models that are easy
to conflate. It makes no claim that the repository's quotient graph is the
source graph of MB09 §6.2.

## Candidate and score declarations

The first model has candidates **spelled circular genomes** of a fixed length
`N`, up to rotation. Its observations are oriented length-`L` reads drawn
independently from a uniformly chosen circular start. The likelihood is the
exact iid product
`prod_r (number of starts spelling r / N)^(sample multiplicity of r)`.
Truth is admitted. The second, formal model has candidates **integer physical
orbit flows** on the finite reversal-orbit list in
`Section62PhysicalEdgeOrbit`; balance is equality of positive and negative
half-incidence totals. Neither model is the legacy oriented `BdFlow` model.
The argument below concerns feasible incidence vectors, not likelihood
maximality; no exact-genome likelihood is defined on arbitrary orbit flows.

## Conditional incidence inclusion

Let `G` be a circular word with `N >= L`, and let `e_i` be its oriented
length-`L` window beginning at circular position `i`. Suppose an oriented
overlap graph contains the edge occurrences
`e_i -> e_(i+1)` for every `i`, with the overlap length `L-1`; suppose further
that mapping each such edge occurrence to its physical reversal orbit preserves
its two physical half-incidences as defined by `posHalf` and `negHalf`.
Assign one unit of physical flow to each occurrence (so repeated edge types
receive their multiplicity), and zero to other orbits. At every vertex class,
this flow is balanced: the negative half-incidence contributed by the arrival
at position `i` cancels the positive half-incidence of the same circular
window-chain junction, with loop incidences counted with their half-edge
multiplicity. Its positive visit vector is the molecule-class frequency vector
of the circular length-`L` windows.

Thus, **under the stated source-incidence-preserving edge-occurrence map**,
each circular genome's molecule-class spectrum is in the physical orbit-flow
visit image (and the mapped flow has total edge multiplicity `N`). This is a
conditional inclusion, not an identification: it supplies no converse and
does not establish the hypothesis for MB09's graph or its transitive
reduction. The existing Lean modules establish two adjacent facts but do not
close this map: `Section62PhysicalHalfIncidence.posHalf_reverse` and
`negHalf_reverse` preserve the separate endpoint counts under the formal edge
reversal, including loops; `Section62ObservedMoleculeCount` identifies RC-class
word counts for already-spelled reduced signed circuits, including palindromes.
Neither proves that a circular-window occurrence maps to the needed physical
edge orbit with those incidences, nor that it survives reduction. In
particular `Section62Flow.Spelling.step` is parameterized at `readLen - 1`,
whereas `overlapEdges` admits any proper length in `[oMin, readLen)`; a
source-faithful correspondence must explain how those occurrence records are
generated and related, not infer their presence from the endpoint graph API.

## Counterexample to the naive oriented lift

The unconditional alternative of representing a physical orbit flow by
copying its weight onto both oriented representatives and then using legacy
departure throughput is false. The kernel-checked `Atat` construction in
`Section62PhysicalEdgeOrbit` has one mixed-sign self-loop orbit of physical
weight one. It has physical positive and negative visit count `1` and is
balanced, while the induced oriented flow has legacy departure throughput
`2`. The declarations `orbit_balanced`, `orbit_visit_one`,
`inherited_throughput_two`, and `inherited_throughput_not_physical` establish
the discrepancy. This refutes that specific map as a visit-vector-preserving
bridge; it does **not** refute the conditional physical-incidence inclusion
above.

## Orientation versus RC classes: witness, not a transfer

For circular-genome candidates `AAATT` (truth) and `AAATA`, both length five,
with observed oriented reads `AAA,AAA,AAT,ATT` at `L=3`, `o_min=1`, the exact
uniform-start iid competitor/truth likelihood ratio is `0` when oriented read
types are retained, and `1` when reads and spectra are indexed by
reverse-complement molecule class. Truth is admitted in both pairwise
comparisons. This exact witness changes the pairwise verdict but gives no
candidate-set inclusion between oriented spectra and physical orbit flows:
the quotient changes the observation alphabet and the likelihood, while the
conditional inclusion above only maps a spectrum into a visit-vector image.
Consequently no maximality result transfers between these three domains from
this pair alone.

## Independent checks and remaining obligations

`python3 scripts/verify_261_rc_orientation_class.py` checks the finite exact
likelihood witness with rational arithmetic. The orbit-loop discrepancy is
kernel-checked in `AssemblyP1/Section62PhysicalEdgeOrbit.lean`. The general
genome-to-physical-flow inclusion remains an explicit conditional lemma until
the graph and junction-incidence hypotheses are formalized and verified.

Still OPEN: (i) identify edge occurrences and multiplicities in MB09's physical
RC overlap multigraph, including transitive reduction; (ii) prove the stated
occurrence map preserves signed half-incidences and vertex lower bound 1 for
arbitrary overlap and palindrome cases (the existing reversal and observed
class-count results are compatible but are not that proof); (iii) determine
whether the physical flow visit image is larger than the circular-genome
spectrum image in this source-faithful graph; (iv) relate the oriented and
quotient likelihood maximizers on the *whole* genome candidate universe; (v)
general maximality, fixed-`N` binomial, half-integral/real relaxations. Keep
#261 and #255 open.
