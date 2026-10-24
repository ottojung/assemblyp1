# Issue #261 exact bounded cell: AGA/CTC RC support, spelled-vs-flow gap

This is the third bounded graph-to-score cell for #261 and the second RC
support beyond the ACA/CAC cells: it shows the spelled-circuit vs
integer-flow maximality separation is not specific to one support.

## Instance and semantics

DNA encoding `A=0,C=1,G=2,T=3`, reads of length `L=3`, overlap floor
`o_min=1`, observed molecule classes `AGA` and `CTC` completed by their
genuine reverse complements `TCT` and `GAG` (no palindromes). The complete
graph has 8 edges (four of overlap length 2); signed incidences follow
representative vs reverse-complement strand as in
`AssemblyP1/Section62BidirectedFlow.lean`.

Candidate class: integer edge-multiplicity flows on the complete graph, edge
lower bound 0, vertex throughput lower bound 1, zero signed-incidence balance,
zero terminal usage. Spelled subclass: circular maximal-overlap (`L-1=2`)
circuits visiting both observed classes and satisfying the opposite-incidence
condition. Truth: the length-4 spelled circuit `AGA -> GAG -> AGA -> GAG`
(each step overlap 2; `GAG` is the reverse complement of `CTC`, so the walk
alternates observed classes via RC strands), throughput `d*=(2,2)`, feasible
as a walk flow with multiplicity 2 on each directed edge. Bounded spelling universe: circuit
lengths 2 through 4; exhaustive enumeration gives spectra `(1,1)` and
`(2,2)`.

Likelihood: fixed-external-`N` product-binomial core on the two observed
coordinates, `N=4`, sample `x=(1,2)`, `n=3`: `K(d;x)=prod d_i^xi
(N-d_i)^(n-xi)`. Unobserved-class coordinates are omitted/fixed at zero by
stated convention; this cell does not adjudicate the source interpretation of
those coordinates.

## Exact counterexample

The verifier finds a 0/1 edge-multiplicity integer flow with throughput
`(1,2)`: balanced (zero) at both vertices, throughputs at least one, no
terminals, and not a spelled spectrum in the bounded universe. Exact scores:
`K(2,2)=64` (truth), `K(1,2)=72` (flow). The other spelled spectrum `(1,1)`
scores 27, so the truth is spelled-maximal but strictly beaten over the
stated feasible integer-flow class.

Executable witness:
`scripts/verify_261_flow_cell_agactc.py` enumerates all simple 0/1 edge flows
and all circular strand sequences through length 4, and re-certifies both
explicit flows against incidence and vertex-bound constraints.

This is one more bounded support/length universe, not a general criterion. It
does not establish unbounded spelling results, transitive-reduction
invariance, real half-integral relaxation claims, or a coordinate convention
for unobserved classes. General maximality, reduction, real-LP and coordinate
convention axes remain OPEN; #261 and #255 remain open.
