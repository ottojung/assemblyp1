# Issue #261 exact bounded cell: ACA/CAC, expanded spelling universe

This rechecks the `ACA/CAC` RC support while explicitly expanding its spelled
length universe to circuits of length 2 through 4. It obtains a strict
separation between spelled circuit maximality and integer-flow maximality for a
different fixed-N binomial sample.

## Instance and semantics

Use DNA encoding `A=0,C=1,G=2,T=3`, reads of length `L=3`, overlap floor
`o_min=1`, and the two observed molecule classes represented by `ACA` and
`CAC`. Their genuine reverse complements are `TGT` and `GTG`; there are no
palindromes. The graph contains all proper overlaps of lengths 1 and 2 among
these four strands, with the signed incidences determined by representative
strand versus reverse-complement strand as in
[`Section62BidirectedFlow.lean`](../AssemblyP1/Section62BidirectedFlow.lean).
The enumerated complete graph has 8 edges (four of length 2).

Candidate class for the comparison: integer edge-multiplicity flows on this
complete graph, with edge lower bound 0, vertex throughput lower bound 1,
signed-incidence balance zero, and zero terminal usage. The spelled subclass is
circular sequences of observed strands using maximal overlaps `L-1=2`, satisfying
the bidirected opposite-incidence condition and visiting both observed classes.
The truth is the spelled circuit `ACA -> CAC -> ACA`, whose throughput is
`d*=(2,2)` and whose walk flow is feasible. The bounded spelling universe is
circuit length 2 through 4; exhaustive enumeration gives spectra `(1,1)` and
`(2,2)`.

Likelihood is the fixed-external-`N` product-binomial core on the two observed
coordinates, with `N=4`, sample `x=(1,2)`, and `n=3` reads:
`K(d;x)=∏ dᵢ^xᵢ (N-dᵢ)^(n-xᵢ)`. Coordinates for unobserved molecule classes
are omitted/fixed commonly at zero, as a stated convention; this finite result
does not adjudicate the source interpretation of those coordinates.

## Exact counterexample

The verifier finds a 0/1 edge-multiplicity integer flow with throughput `(1,2)`.
Both vertex throughputs are at least one; its signed balance is zero at both
vertices and it uses no terminals. It is not a spelled spectrum in the bounded
spelling universe. Exact scores are `K(2,2)=64` for truth and `K(1,2)=72` for the
flow. Therefore the truth is
spelled-maximal but not maximal over the stated feasible integer-flow class.

For `x=(1,2)`, the other spelled spectrum `(1,1)` scores below the truth, so the
truth is spelled-maximal. The executable exact-integer verifier is
[`verify_261_flow_cell_aatt.py`](../scripts/verify_261_flow_cell_aatt.py); it
enumerates all simple 0/1 edge flows as a bounded feasibility cross-check and
all circular strand sequences through length 4, and independently checks both
explicit flows against the incidence and vertex-bound constraints.

This is one bounded support and length universe, not a general criterion. It does
not establish an unbounded spelling result, sample realizability under every
sequencing convention, transitive-reduction invariance, or any real
half-integral relaxation claim. Those and other RC supports remain OPEN; #261
and #255 remain open.
