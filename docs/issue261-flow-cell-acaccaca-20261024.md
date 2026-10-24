# Issue #261 exact bounded cell: ACAC/CACA at L=4, o_min=2

Third independent RC-support flow cell, complementing the `ACA/CAC` and
`AGA/CTC` cells at `L=3, o_min=1`. It obtains the same strict separation
between spelled-circuit maximality and integer-flow maximality at a new
length/overlap floor and on a new support pair.

## Instance and semantics

Use DNA encoding `A=0,C=1,G=2,T=3`, reads of length `L=4`, overlap floor
`o_min=2`, and the two observed molecule classes represented by `ACAC` and
`CACA`. Their genuine reverse complements are `GTGT` and `TGTG`
(hand-checked: `rc(ACAC)=GTGT`, `rc(CACA)=TGTG`; no palindromes; two distinct
RC classes). The graph contains all proper overlaps of lengths 2 and 3 among
these four strands, with the signed incidences determined by representative
strand versus reverse-complement strand as in
[`Section62BidirectedFlow.lean`](../AssemblyP1/Section62BidirectedFlow.lean).
The enumerated complete graph has 8 edges (four of length 3).

Candidate class for the comparison: integer edge-multiplicity flows on this
complete graph, with edge lower bound 0, vertex throughput lower bound 1,
signed-incidence balance zero, and zero terminal usage. The spelled subclass is
circular sequences of observed strands using maximal overlaps `L-1=3`,
satisfying the bidirected opposite-incidence condition and visiting both
observed classes. The truth is the spelled circuit
`ACAC -> CACA -> ACAC -> CACA`, whose throughput is `d*=(2,2)` and whose walk
flow is feasible. The bounded spelling universe is circuit length 2 through 4;
exhaustive enumeration gives spectra `(1,1)` and `(2,2)`.

Likelihood is the fixed-external-`N` product-binomial core on the two observed
coordinates, with `N=4`, sample `x=(1,2)`, and `n=3` reads:
`K(d;x)=∏ dᵢ^xᵢ (N-dᵢ)^(n-xᵢ)`. Coordinates for unobserved molecule classes
are omitted/fixed commonly at zero, as a stated convention; this finite result
does not adjudicate the source interpretation of those coordinates.

## Exact counterexample

The verifier finds a 0/1 edge-multiplicity integer flow with throughput `(1,2)`
(edges `TGTG->TGTG(2)`, `GTGT->TGTG(3)`, `TGTG->GTGT(3)`; balance zero at both
vertices, throughputs ≥ 1). It is not a spelled spectrum in the bounded
spelling universe. Exact scores are `K(2,2)=64` for truth and `K(1,2)=72` for
the flow. Therefore the truth is spelled-maximal but not maximal over the
stated feasible integer-flow class.

The executable exact-integer verifier is
[`verify_261_flow_cell_acaccaca.py`](../scripts/verify_261_flow_cell_acaccaca.py);
it enumerates all simple 0/1 edge flows as a bounded feasibility cross-check
and all circular strand sequences through length 4, and independently checks
both explicit flows against the incidence and vertex-bound constraints.

## Controls and scope

Mutation control: changing the asserted spelled set (e.g. adding `(1,2)`) or
the asserted `K` values makes the verifier fail; changing the defeater target
to a spelled image removes the strict separation. Hand-checked DNA complements
above; `K(2,2)=2^1·2^2·2^2·2^1=64`, `K(1,2)=1^1·3^2·2^2·2^1=72`.

This is one bounded support and length universe, not a general criterion. It
does not establish an unbounded spelling result, sample realizability under
every sequencing convention, transitive-reduction invariance, or any real
half-integral relaxation claim. Those and other RC supports remain OPEN; #261
and #255 remain open.
