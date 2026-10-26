# Bounded arbitrary-support circulation census (issue #257)

This note records a finite computational cross-check of the incidence/delta
criterion in `docs/source-notes/issue-257-rigid-read-graphs.md`. It is not a
new general theorem or a replacement for the exact criterion there.

## Exact finite scope

The script `scripts/verify_257_rank3_multigraphs.py` enumerates labelled
connected directed multigraphs on `1..4` vertices, allowing loops and parallel
arcs, with cycle rank `|E|-|V|+1 <= 3`. It retains cells with a positive
integral circulation of total mass `G <= 6`. For each cell it enumerates
positive integral arc vectors `B`, checks incidence balance directly, and
classifies the truth `A` rigid iff no different `B` has both the same total and
the same incidence balances. The implementation uses no library imports.

The run covered **3732 support/total cells**. A brute-force scope statement is
not a proof beyond these sizes. In particular, this does not establish a
uniform polynomial-time characterization or settle arbitrary graph/genome
topologies.

## Multiplicities matter

One support in the census is two parallel directed self-loops on one vertex.
At total `G=2`, truth `(1,1)` is rigid: positivity and total force the unique
vector `(1,1)`. On the identical support at total `G=3`, truth `(1,2)` is
non-rigid, with alternative `(2,1)`. Thus support topology alone does not
determine rigidity; the length/multiplicity data is essential. The same
example is also a mutation control: a deliberately false support-only
classifier assigning identical labels to both instances is rejected.

This is a multigraph example, not asserted to be an `L`-mer support. The census
is explicitly arbitrary directed multigraphs. Translating the counterexample
to a realizable de Bruijn support is a separate question.

## Reproduction

```sh
python3 scripts/verify_257_rank3_multigraphs.py
python3 scripts/check-research-docs.py
```

The verifier reports 3732 cells, checks the exhibited rigid/non-rigid cases by
direct incidence enumeration, runs the mutation control, and exits nonzero on
failed assertions.
