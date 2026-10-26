# Issue #261: bounded RC candidate-set audit (2026-10-26)

## Independent census check

I independently ran the verifier from commit `2ea8a105aa5c3b3994471a0061cfed2df1a78c8e`
against a fresh clone of `https://github.com/ottojung/assemblyp1` at
`origin/main` (`234f3480d7589c8fc4e056c91dda91343fe64ece`). With Python 3 it
reproduces four canonical binary length-five genomes, 840 truth/competitor/sample
comparisons, 163 ratio changes, and seven oriented-zero / RC-one cases. The
named witness is `AAATT` against `AAATA`, sample `AAA,AAA,AAT,ATT`, with exact
ratios 0 and 1 respectively.

## What this witness does and does not transfer

The verifier's candidate universe consists of canonical *spelled circular
genome classes* over the binary alphabet, with every sampled triple taken from
the truth's five circular windows. This establishes that the orientation/RC
quotient can change a likelihood comparison even when both candidate genomes
spell their molecule windows. It does not establish that the truth is maximal
in either universe, nor does it compare arbitrary feasible flows or circuits.

In the project's fixed-vertex overlap graph, the witness's observed vertices
are `AAA`, `AAT`, and `ATT`. Its sample windows yield directed overlaps
`AAA→AAT` (length 2) and `AAT→ATT` (length 2), while `ATT→AAA` is a proper
overlap of length 1. Thus both circular words use available proper overlaps;
this fact alone says nothing about whether a source-faithful transitive
reduction retains all three steps. The exact reduced graph is therefore an
additional premise required before treating this as an admissible-circuit
counterexample. It is not a flow counterexample: the existing
`Section62SpelledFlowImageRefutation` already refutes equality of feasible-flow
throughput image and spelled-visit set, and no inclusion in the reverse
direction is established by this census.

Candidate-set transfer is one-way: a strictly better candidate in a subset
refutes maximality in a superset only when the candidate is admitted there
(and the score is the same). A comparison that ties or favors truth within the
spelled subset cannot prove maximality over the larger feasible-flow set.
Consequently this census neither resolves the flow-level RC maximality claim
nor licenses transfer through transitive reduction. The remaining bounded
cell is an explicit OPEN item: compute the spelling-preserving reduced graph
for the named witness, then enumerate admissible oriented circuits and compare
their RC classes; separately test the same instance's feasible integer-flow
image. Keep exact uniform-start likelihood and fixed-external-N binomial
likelihood distinct.

## Reproduction

The prior verifier is available on remote branch
`agent-ntZkWC6dtHLi0tf3ahURGj-issue261` at the commit above. Its exact-rational
run passed independently. Board issue comments could not be fetched in this
runtime (`gh` is not installed); the branch SHA was verified with
`git ls-remote`.
