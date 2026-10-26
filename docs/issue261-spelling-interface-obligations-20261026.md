# Issue #261: spelling interface obligations (2026-10-26)

This note sharpens the conditional bridge recorded in
`issue261-window-step-bridge-audit-20261026.md`. It records what the existing
Lean interface establishes and what an arbitrary-threshold genome inclusion
proof must additionally provide. It does not claim that every MB09 feasible
flow is a genome, or that the transitive reduction preserves genome steps.

## Source semantics and formal boundary

MB09 §6.2 (Medvedev and Brudno, *Maximum Likelihood Genome Assembly*, 2009,
PMC3154397) says the vertices are read molecules, edges are all bidirected
overlaps of length at least `o_min`, and the original double-stranded genome
corresponds to a circuit. Observation 7 identifies a walk's visit count at a
read with its submolecule multiplicity in the spelled molecule. The source
audit and quotations are in `section62-mb09-bidirected-graph-audit.md` §1;
the four signed strand-overlap cases are audited there against §3.1–3.4.

In `AssemblyP1/Section62BidirectedFlow.lean`, `Spelling` supplies only
`strand : Fin n → W` and nonemptiness. `W` is abstract: the record has no
alphabet, content function, cyclic sequence, or statement that a strand is a
window of that sequence. `StepsInGraph` and `VisitsObserved` are therefore
appropriately explicit premises of `SpelledFeasible62`, not consequences of
the present `Spelling` type. This is a type-level gap, not a counterexample to
the source's genome-to-circuit statement.

## Exact unreduced edge obligation

For `overlapEdges ... readLen oMin verts`, an edge at position `i` is available
if the following hold:

1. `oMin ≤ readLen - 1` and `readLen - 1 < readLen`;
2. `sufOf (toList (strand i)) (readLen - 1) =
   preOf (toList (strand (next i))) (readLen - 1)`;
3. both strands occur in `verts ++ verts.map rc`.

The list-generation bounds are then satisfied because overlap lengths range over
`List.range readLen`; `bdEdge` supplies the signed endpoint incidences. A
source-faithful sufficient interface for item 2 would provide a circular
sequence `S`, identify each `toList (strand i)` with its length-`readLen`
window in `S`, and prove the cyclic window shift identity, including wraparound.
For item 3 it must supply observed-molecule membership for every position and
the reverse-complement-class enumeration law. None of these equalities follows
from the current abstract `Spelling` fields.

This proves only the shape of a conditional construction; it is not yet a Lean
lemma or evidence that an arbitrary input satisfies its hypotheses. In
particular, an observed-read premise must not be silently replaced by truth
admission: the sampled observed vertex set need not contain every window of the
truth. See `primitive-62-uniqueness-no-hstruth.md` for an explicit distinction.

## Reduction and candidate-class separation

Membership in `overlapEdges` does not imply membership in
`transitivelyReduced`. For each step, reduction survival is a separate
non-reducibility obligation under the exact `isReducibleB` predicate (and any
source interpretation fork remains separately audited). Consequently this
interface does not prove candidate-set inclusion from circular genomes into
reduced-graph flows. It also does not identify integral flows, half-integral
relaxations, bidirected circuits, and circular genomes, nor select exact versus
fixed-`N` likelihood or a candidate length universe. Those remain open axes of
#261/#255; no maximality transfer is made.
