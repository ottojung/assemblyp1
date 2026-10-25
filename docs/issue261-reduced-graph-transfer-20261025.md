# Issue #261: spelled-vs-flow separation transfers to the transitively reduced graph

## Candidate-class clarification (flows vs spelled circuits vs circular genomes)

The parent bounded cells (`AGA/CTC`, `ACA/CAC`) use a three-level hierarchy
that this note keeps unchanged:

1. **Integer flows**: edge-multiplicity flows on the overlap graph, edge
   lower bound 0, vertex throughput lower bound 1, zero signed-incidence
   balance, zero terminal usage. These need NOT spell one circular genome;
   a flow is a coverage/balance object, not a genome hypothesis.
2. **Spelled circuits**: closed strand walks using maximal overlaps
   (`L-1`), satisfying the opposite-incidence condition and visiting both
   observed classes. Every spelled circuit induces a walk flow, so spelled
   images sit inside flow images -- but the converse fails.
3. **Truth**: admitted as the length-4 spelled circuit (throughput `(2,2)`)
   in both parent cells; the claim is "spelled-maximal but not
   flow-maximal", never "truth is the unique maximizer".

Likelihood is the fixed-external-`N` product-binomial core on the two
observed coordinates (`N=4`, `x=(1,2)`, `n=3`); unobserved coordinates are
omitted/fixed at zero by stated convention, not source-adjudicated.

## Transfer result

The parent (1,2) defeaters use an overlap-1 self-loop edge, so transitive
reduction removes them and transfer is not free. Re-enumeration on the
4-edge reduced graph (both RC supports) gives:

- Reduced 0/1 flow images are `{(1,1),(2,2)}` -- the (1,2) defeater is gone.
- Every reduced edge crosses observed classes, so EVERY closed walk
  (spelled circuit of any length) has a diagonal image `(k,k)`.
- A new explicit multiplicity<=2 feasible reduced-graph flow has image
  `(1,3)` with `K=81 > 64`, off-diagonal hence non-spelled at any length.

So the separation "spelled-maximal truth beaten by an integer flow"
transfers to the transitively reduced graph, with a new defeater.
Executable witness: `scripts/verify_261_reduced_graph_transfer.py`.

## Scope limits (OPEN)

Bounded L=3/o_min=1 two-class cells; fixed-N binomial only; unobserved
coordinates by convention; integer flows (half-integral/real-LP OPEN);
general maximality criterion, other RC supports, unbounded spelling OPEN.
Keep #261 and #255 open.
