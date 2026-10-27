# A full-overlap spelled counterexample transfers to every lower overlap floor

**Status:** exact finite implication for the *spelled-circuit candidate class*;
no claim of invariance for all §6.2 flows or of a general maximality criterion.

## Claim and scope

Fix `L = 3`, the DNA alphabet `{A,T}` with reverse complement `A↔T`, and
`o_min ∈ {1,2}`. Use the usual bidirected graph containing all proper
suffix/prefix overlaps of length at least `o_min`, then any edge reduction that
deletes edges but does not alter the surviving edge objects. In this graph, the
spelled-circuit candidate class contains two circuits which refute truth
maximality under the §6.1 fixed-external-`N` binomial likelihood. This establishes
the required candidate-set inclusion for this negative conclusion; it does not
establish anything positive about maxima over the larger flow class.

For a fixed read set and edge-deletion reduction, the full-overlap graph is a
subgraph of each lower-floor graph: every length-`L−1` edge satisfies
`o_min ≤ L−1`. Both witnesses below use only length-2 edges, and those exact
edge objects also survive the two repository reduction predicates: the literal
“spelled by two shorter overlaps” predicate cannot delete a maximal length-2
overlap; the “two strictly longer overlaps” predicate cannot delete one because
there is no proper overlap longer than 2. The literal predicate is the source
wording approximation; the latter is not certified as Myers's spelling-preserving
algorithm. Therefore the transfer is conditional on the graph retaining these
maximal edges, a direct finite check here, not on reduction invariance generally.

## Instance and exact counts

| Quantity | Truth | Competitor |
|---|---|---|
| circular genome | `S = AAATT` | `D = AAAATT` |
| length | `G=5` | `6` |
| length-3 windows, as strands | `AAA,AAT,ATT,TTA,TAA` | `AAA,AAA,AAT,ATT,TTA,TAA` |
| molecule classes (`w ~ rc(w)`) | `AAA,AAT,AAT,TAA,TAA` | `AAA,AAA,AAT,AAT,TAA,TAA` |
| class throughput | `(1,2,2)` | `(2,2,2)` |

The observed placements are starts `(0,1,4)` in `S`, with one read at each
placement, so `n=3` and `x=(1,1,1)` on classes `(AAA,AAT,TAA)`. Set the external
§6.1 denominator to `N=|S|=5`. Truth is admitted: its own cyclic window walk
is a circuit, and its three observed read classes have throughput at least 1.
The competitor is likewise a circular genome and gives a circuit. Thus the
candidate class here is **spelled circular genomes/circuits**, a subset of flows;
the proof does not identify all flows with genomes.

Every consecutive window pair in these walks has suffix/prefix overlap 2:

```text
S: AAA→AAT→ATT→TTA→TAA→AAA
D: AAA→AAA→AAT→ATT→TTA→TAA→AAA
```

The transitions involving reverse-complement classes use the strand shown, so
the quotient classes do not erase orientation: `ATT ~ AAT`, `TTA ~ TAA`; the
other representatives are `AAA` and `AAT/TAA`. For each walk, the arriving and
departing bidirected incidences are opposite at every visit. Giving each listed
transition one unit (accumulating repeated edges) yields integral edge flow,
zero signed-incidence balance at each of the three class vertices, zero terminal
usage, edge lower bounds 0, and vertex throughputs at least 1. Since all edge
lengths are 2, the edge certificate is identical for `o_min=2` (full overlap)
and `o_min=1` (genuine shorter-overlap edges are also present, but unused).

## Likelihood and transfer proof

Use only the literal §6.1 product of per-class binomial marginals with fixed
external `N=5`, not the exact multinomial and not a likelihood with candidate
length substituted for `N`. For a class with `x=1`, its factor, up to the common
binomial coefficient, is `(d/5)(1-d/5)^2`. At `AAA`, the candidate changes
`d:1→2`, giving

```text
[(2/5)(3/5)^2] / [(1/5)(4/5)^2] = (18/125)/(16/125) = 9/8.
```

The `AAT` and `TAA` throughputs remain 2, so their likelihood ratios are 1.
All other read-molecule classes have zero observed count and zero throughput in
both genomes, hence their factors are 1. The full likelihood ratio is exactly
`9/8 > 1`.

For each `o_min ∈ {1,2}`, both circuits are feasible in the unreduced graph, and
the maximal overlap edges used above survive both finite reductions just
described. Therefore `truth ∈ C_o` and `competitor ∈ C_o`, where `C_o` is the
spelled-circuit candidate set on that graph, and `L(competitor)>L(truth)`. This
proves non-maximality in the spelled class at both floors. Since
`C_o ⊆ F_o` by the circuit-to-flow inclusion, it also proves non-maximality in
the corresponding flow set **provided that same reduction retains the displayed
edges**. This is a failure transfer by inclusion, not a positive-claim transfer.

## Boundary: no arbitrary-overlap phenomenon is witnessed here

This is a *lower-floor graph transfer*, not a counterexample whose spelling
needs a short edge. Every circular genome walk uses overlap `L−1=2`, so both
truth and competitor are exactly the full-overlap witnesses from
`docs/bridging-se62-flow-ml-counterexample.md`. The additional shorter edges at
`o_min=1` are irrelevant to their feasibility. Consequently the witness does
not resolve the specifically non-spelled/general-flow maximality problem, does
not prove that ML maxima are unchanged as `o_min` varies, and does not address
half-integral relaxation or a different RC/orientation flow semantics. Those
remain open.

The numerical counts and ratio were independently recomputed with exact
integer arithmetic using a short Python check in this run; the existing
kernel-checked §6.2 witness and graph certificates are in
`AssemblyP1/Section62BridgingCounterexample.lean` and
`scripts/verify_se62_mb09_bidirected_graph.py`. This note records the precise
inclusion argument and its limit; it does not claim that those artifacts
formalize arbitrary `o_min`.
