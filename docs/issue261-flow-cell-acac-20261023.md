# Issue #261 bounded flow cell: spelled-maximal truth with a strict flow defeater (ACA/CAC, L=3, o_min=1)

Child of #255; parent scope: the `issue261-sweep-scope-matrix-20261023.md` matrix on
branch `research/261-scope-matrix-RQZTG1WbAejzEkEnSWm7Wr-chemical` (commit
`5d61318`, not on `main`).
This note instantiates that matrix's "smallest next bridge" for one observed RC
support. Independent exact-integer witness; verifier:
[`scripts/verify_261_flow_cell_acac.py`](../scripts/verify_261_flow_cell_acac.py).
The stricter shortest-edge boundary is independently exhaustively checked by
[`scripts/verify_261_acac_short_edge_boundary.py`](../scripts/verify_261_acac_short_edge_boundary.py).

## Fixed instance (source-faithful MB09 Sec. 6.2)

* Alphabet `A=0,C=1,G=2,T=3`; strands `ACA=(0,1,0)`, `CAC=(1,0,1)`,
  `TGT=(3,2,3)=rc(ACA)`, `GTG=(2,3,2)=rc(CAC)`; RC verified against the
  Watson-Crick complement in the verifier.
* Observed molecule support `verts={ACA,CAC}` (two RC classes, no palindromes);
  `readLen L=3`, `o_min=1`; complete `overlapEdges` graph: 8 edges (4 of length
  1, 4 of length 2); literal `isReducibleB` is vacuous on this instance
  (checked), so the reduced graph equals the complete graph — no
  reduction-ambiguity caveat applies here.
* Candidate objects: integer `BdFlow`s with zero-terminal `Feasible62`
  (`edgeLB=0`, `vertexLB=1`, signed-incidence balance `0` at both vertices,
  throughput `d` per molecule class). Terminal convention: `noTerminals`.
* Likelihood: Sec. 6.1 fixed-external-`N` product-binomial core
  `K(d;x)=prod d_i^{x_i}(N-d_i)^{n-x_i}` with external `N=3`, sample `x=(2,1)`
  (`n=3`, full support on both observed classes). Unobserved molecule
  coordinates are fixed at `0` for all flow candidates (common factor, so the
  ranking is valid within this convention; the convention choice itself stays
  OPEN per the support adjudication). Throughputs with a coordinate `>N` are
  outside the binomial probability domain and excluded from the comparison.

## Proven statements (exact, finite)

1. **Truth candidate status.** The spelled 2-circuit `(ACA -> CAC -> ACA)` uses
   maximal overlaps (len 2), satisfies `BidirectedCircuit`, visits both observed
   vertices, and its walk flow `f*=(0->1)+(1->0)` is zero-terminal feasible with
   throughput `d*=(1,1)`. So the truth is an admitted spelled feasible candidate.
2. **Spelled-maximal.** The spelled visit set visiting both vertices at `n<=4`
   is exactly `{(1,1),(2,2)}`; under `K(.;x)` with `N=3,x=(2,1)` both score `8`,
   so the truth is spelled-maximal (tied, not unique).
3. **Strict flow defeater.** The integer flow
   `f=(3->3 len1)+(0->1 len2)+(2->3 len2)` is zero-terminal feasible with
   throughput `(2,1)` (non-spelled: `(2,1)` is not a spelled visit vector) and
   scores `K=16>8`. Hence the spelled-maximal truth is **not** flow-maximal.
4. **Conclusion for the cell.** Spelled-maximality does not imply
   flow-maximality under the same fixed-`N` binomial objective, even on a
   reduction-vacuous genuine `o_min=1` bidirected graph with a feasible spelled
   truth. This resolves the scope matrix's bounded falsification target for one
   cell; it is not a general maximality criterion (still OPEN).

## Shortest-overlap boundary (finite exhaustive result)

The strict flow defeater in this cell is genuinely dependent on allowing the
shortest observed overlap length. The independent checker enumerates all
`4^8=65,536` nonnegative edge-flow vectors: because every edge contributes to
its source-class throughput and candidates are restricted to throughput at most
`N=3`, each edge coordinate is at most 3, so this is exhaustive for this
probability-bounded flow set. It filters the literal `Feasible62` conditions and
scores the two observed coordinates with the same exact fixed-`N` binomial core.

* With all eight edges, the maximum score is 16 and its only throughput vector
  is `(2,1)`, strictly above the truth score 8.
* After excluding all four length-1 edges (leaving only maximal length-2 edges),
  the maximum is 8, attained at `(1,1)` and `(2,2)`; there is no strict flow
  defeat of the truth.

Thus, **in this finite cell and under the stated throughput-bound/unobserved-zero
convention**, the strict flow defeat requires a length-1 edge. The literal
project `isReducibleB` predicate removes no edge in this graph, as checked by
both verifiers, so this result is stable under that predicate. It does not
establish how a source-faithful spelling-preserving MB09 transitive reduction
acts in general, nor any global criterion or transfer from full overlap.

## What stays OPEN

General necessary-and-sufficient flow-maximality conditions, throughput-image
characterization, transitive-reduction interaction in non-vacuous instances,
orientation/RC quotients beyond this non-palindromic pair, the real LP
relaxation, sample realizability at arbitrary overlap, and the
unobserved-coordinate convention all stay OPEN. #261 and #255 stay open.
