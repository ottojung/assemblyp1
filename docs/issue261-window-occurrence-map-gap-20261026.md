# Source-faithful circular-window occurrence map gap (#261)

**Result: the repository has not yet defined enough structure for a Lean theorem
mapping an actual circular-window occurrence into a `Tagged` physical edge.**
This note records the precise interface gap rather than asserting the conditional
inclusion in `issue261-orbit-genome-bridge-20261026.md`.

## Definitions inspected

The repository remote is `https://github.com/ottojung/assemblyp1.git`; the
checkpoint branch `agent-WxPuKX5PIRD5ABDMpPbg1o-legged-issue261` resolves locally
and via `git ls-remote` to `30fe5f1daa8a6fdb30d8717bd4c50dc97f3795fe`.

`AssemblyP1.Section62Flow` in `AssemblyP1/Section62BidirectedFlow.lean` is the
source-string model. It supplies `BdEdge`, `bdEdge`,
`overlapEdges (toList) (rep) (rc) readLen oMin verts`, and defines edge
availability by suffix/prefix equality (lines 121–153). Thus it can identify
which oriented strand words overlap and the signed endpoint incidences chosen by
`rep`.

`AssemblyP1.Section62PhysicalHalfIncidence` and
`AssemblyP1.Section62PhysicalEdgeOrbit` instead use `Tagged W := W × Bool`,
with the vertex class/sign operations and `physMk` on `BdEdge A (Tagged W)`.
They prove incidence facts for a *given tagged edge*, including separate
endpoint occurrences on loops (`ForwardLoop.loop_halfIncidence`) and invariance
under reversing that edge. They do not import or mention `toList`, `rc`,
`overlapEdges`, a circular sequence, a window start, or an occurrence-indexed
edge list.

No function currently maps a source-level strand to `(word, orientation bit)`
with a specification tying the word to its reverse complement. Nor is there a
relation proving that consecutive circular length-`L` windows provide the
endpoint strands and signs of an available `overlapEdges` entry, then that this
entry can be represented as a `BdEdge A (Tagged W)` with the same physical
half-incidences. Choosing such a function arbitrarily would not prove the
source correspondence: at a self-RC word, word equality alone cannot identify
the selected strand traversal or establish whether the orientation bit is
canonical or occurrence-specific.

## Exact unresolved obligations

To prove incidence preservation for an occurrence, the source adapter must
provide (at least):

1. an indexed circular genome and a length-`L` window operation, including the
   wraparound convention;
2. a strand-content function into the `W` words used by `Section62Flow`, and an
   involutive RC operation with a theorem that the opposite tagged orientation
   denotes the reverse-complement content;
3. for every adjacent pair of starts, an `overlapEdges` witness at the specified
   overlap length (or a proof that the actual MB09 occurrence convention chooses
   another length); and
4. a conversion to the two endpoint occurrences consumed by `posHalf` and
   `negHalf`, proving equality of each signed incidence separately, including
   coincident endpoints and self-RC labels.

Until those definitions and hypotheses exist, no exact theorem can establish
edge availability or incidence preservation from circular windows. The already
proved `ForwardLoop.loop_halfIncidence` is strictly downstream: it proves the
counts after a tagged loop has been supplied. No counterexample to a properly
specified adapter follows from this absence of definitions. Genome-to-flow
inclusion, reduction survival, likelihood/maximality transfer, and all other
#261 claims remain open; #261 and #255 stay open.

## Reproduction / verification

Inspected `Section62BidirectedFlow.lean` (`BdEdge`, `bdEdge`, `overlapEdges`),
`Section62PhysicalHalfIncidence.lean`, `Section62PhysicalEdgeOrbit.lean`, and
the predecessor note above. The predecessor's focused check was
`lake build AssemblyP1.Section62PhysicalEdgeOrbitAudit`; no source adapter was
added here, so no new Lean theorem or build result is claimed.

Operational lookup: `gh issue view 261 --repo ottojung/assemblyp1 --comments`
could not run because `gh` is unavailable. A fresh clone from the local partial
promisor checkout also failed when Git could not fetch missing object
`6a33da29f79a1ac1d111350f016b06e497ee038b`; work therefore proceeded in the
verified existing repository on a uniquely named branch. No issue-board comment
was posted from this environment.
