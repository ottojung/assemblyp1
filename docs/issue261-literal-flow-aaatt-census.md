# Literal §6.2 integral-flow census on the AAATT graph

## Question and source model

This finite experiment asks whether the complete-spectrum truth `AAATT` has a
strictly better exact variable-length multinomial likelihood among literal
integral §6.2 flows on its observed-molecule graph. The likelihood is
`∏_v (d_v/N)^{x_v}`, where `x` is the truth's complete circular read spectrum
and a candidate throughput vector `d` has total `N`.

The graph uses read length `L=3`, overlap floor `o_min=2=L−1`, and molecule
vertices `{AAA,AAT,TAA}` (a molecule is identified with its reverse-complement
class). The primary-source transcription and independent construction of this
10-edge signed bidirected graph are in
[`section62-mb09-bidirected-graph-audit.md`](section62-mb09-bidirected-graph-audit.md),
especially §§1–3. That audit checks both the literal “spelled by two shorter
overlaps” reduction and the alternative longer-overlap reading; neither removes
an edge here. Source definitions are encoded in
[`Section62BidirectedFlow.lean`](../AssemblyP1/Section62BidirectedFlow.lean):
`overlapEdges`, `transitivelyReduced`, `sgnRep`/`sgnTgt`, `balCore`,
`throughput`, and `Feasible62`. The source correspondence and limitations of
that formalization are stated in the module header and in
[`issue261-general-bidirected-flow-ml.md`](issue261-general-bidirected-flow-ml.md).

The truth spectrum is `x=(1,2,2)` in vertex order `(AAA,AAT,TAA)`, its length is
5, and its exact likelihood is `16/3125`. Candidate flows are integral edge
weight assignments, not spelled circuits: for each fixed `N`, the script
enumerates every weak composition of `N` over the graph's ten edge variables,
then retains assignments whose signed balance is zero at every read molecule
and whose three departure throughputs are each at least 1. Because every graph
edge has one departure endpoint, the edge weights sum to the throughputs and
thus to `N`. Edge lower bounds are 0 and upper bounds are infinite. The flows
being searched use no supersource/sink edges, matching `Feasible62`'s explicit
zero-terminal subdomain.

## Result (finite census)

Reproduce with:

```sh
python3 scripts/search_261_literal_flow_aaatt.py
```

The exact-rational census reports the following numbers of feasible edge-flow
assignments and their best score for each candidate length:

| `N` | feasible edge assignments | best score | best throughput(s), `(AAA,AAT,TAA)` |
|---:|---:|---:|---|
| 1–4 | 0 | none | — |
| 5 | 12 | `16/3125` | `(1,2,2)` |
| 6 | 33 | `1/216` | `(1,2,3)`, `(1,3,2)` |
| 7 | 54 | `81/16807` | `(1,3,3)` |
| 8 | 74 | `81/16384` | `(2,3,3)` |
| 9 | 116 | `32/6561` | `(2,3,4)`, `(2,4,3)` |
| 10 | 185 | `16/3125` | `(2,4,4)` |

None of these scores strictly exceeds the truth score. For `N=5`, the census
recovers the truth throughput and ties it for the maximum. The independently
audited flow construction and graph/reduction checks are exercised by
`scripts/verify_se62_mb09_bidirected_graph.py`.

## Scope boundary

This establishes completeness only for the stated graph, integral zero-terminal
flows, and `1≤N≤10`. It does not establish that `AAATT` is maximal among all
circular genomes, does not produce the requested spelled-maximal-but-flow-
nonmaximal counterexample, and does not settle any unbounded or general
maximality implication. It also does not include nonzero terminal usage. The
broader question of whether a spelled-maximal truth can fail to be
flow-maximal under the literal §6.2 candidate set remains open.
