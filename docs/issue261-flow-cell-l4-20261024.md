# Issue #261 second bounded flow cell: spelled-maximal truth with a strict flow defeater (ACAC/CACA, L=4, o_min=1)

Child of #255. Second instantiation of the bounded-cell pattern from
`docs/issue261-flow-cell-acac-20261023.md` on a non-isomorphic instance:
read length `L=4` (12 edges vs 8), a different RC support, and a larger
spelled class. Independent exact-integer witness; verifier:
[`scripts/verify_261_flow_cell_l4.py`](../scripts/verify_261_flow_cell_l4.py).

## Fixed instance (source-faithful MB09 Sec. 6.2)

* Alphabet `A=0,C=1,G=2,T=3`; strands `ACAC=(0,1,0,1)`, `CACA=(1,0,1,0)`,
  `GTGT=rc(ACAC)`, `TGTG=rc(CACA)`; RC verified against the
  Watson-Crick complement in the verifier; no palindromes (4 strands, 2 RC classes).
* Observed molecule support `verts={ACAC,CACA}`; `readLen L=4`, `o_min=1`;
  complete `overlapEdges` graph: 12 edges (4 each of lengths 1, 2, 3);
  literal `isReducibleB` is vacuous on this instance (checked: it would need
  `ln >= L+2 = 6`, impossible for `ln <= L-1`), so the reduced graph equals the
  complete graph — no reduction-ambiguity caveat applies here.
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

1. **Truth candidate status.** The spelled 2-circuit `(ACAC -> CACA -> ACAC)`
   uses maximal overlaps (len 3), satisfies `BidirectedCircuit`, visits both
   observed vertices, and its walk flow (edges 8+9) is zero-terminal feasible
   with throughput `d*=(1,1)`. So the truth is an admitted spelled feasible
   candidate.
2. **Spelled class and spelled-maximality.** The spelled visit set visiting
   both vertices at `n<=8` is exactly the diagonal
   `{(1,1),(2,2),(3,3),(4,4)}` (no off-diagonal spelled visit vector exists at
   any checked length). Under `K(.;x)` with `N=3,x=(2,1)` the scores are
   `8, 8, 0, 0` (diagonal identity `K((k,k))=[k(N-k)]^n`; out-of-domain
   coordinates excluded), so the truth is spelled-maximal (tied, not unique).
3. **Strict flow defeater.** The integer flow (edges 8+9 plus the `ACAC->ACAC`
   len-2 self-loop, edge 4) is zero-terminal feasible with throughput `(2,1)`
   (non-spelled: `(2,1)` is not a spelled visit vector) and scores `K=16>8`.
   Hence the spelled-maximal truth is **not** flow-maximal.
4. **Conclusion for the cell.** Spelled-maximality does not imply
   flow-maximality under the same fixed-`N` binomial objective on a second,
   structurally distinct reduction-vacuous genuine `o_min=1` bidirected graph
   with a feasible spelled truth. The separation is not an artifact of the
   `L=3` ACA/CAC instance shape: it persists at `L=4` with a four-element
   diagonal spelled class.

## What stays OPEN

General necessary-and-sufficient flow-maximality conditions, throughput-image
characterization, transitive-reduction interaction in non-vacuous instances at
`L>3`, orientation/RC quotients beyond non-palindromic pairs, the real LP
relaxation, sample realizability at arbitrary overlap, and the
unobserved-coordinate convention all stay OPEN. #261 and #255 stay open.
