# Issue #261: reduction and occurrence correspondence boundary (2026-10-27)

**Status:** source-checked idealized result and explicit counterexample to the
stronger vertex/occurrence claim. This does not settle ML maximality.

## Audited definitions and theorem boundary

MB09 §6.2 describes deleting an overlap “spelled by two shorter overlaps” and
asserts Observation 7 for walks in the reduced graph. It does not define that
phrase in the paragraph. Myers (2005) §2 describes an idealized transitive edge
by exact equality of the sequence spelled along a two-edge path and the direct
edge. The repository makes this interpretation explicit in
`Section62MyersIdealTransitivity.TwoHopSameSpelling`: a legal intermediate
observed strand, two proper overlaps, matching suffix/prefix incidences, and
equal spelled words. Under equal-length reads and a proper direct overlap, its
Lean theorem `reducible_iff_ideal_two_hop` proves equivalence to the equation
`l₁ + l₂ = L + e.len`; it is not an audit of Myers's noisy practical algorithm.

`Section62SimultaneousReduction.reduction_preserves_language` further proves
that every complete-graph edge has a chain in the simultaneously reduced graph
with the same spelled word. Its termination argument is concrete: the equation
forces each detour overlap strictly longer than the direct overlap, so extension
length `L - overlap` strictly decreases on recursive expansion. Thus the
one-step detour legs need not survive; the expansion theorem handles cascades.
These are graph-language statements in the repository's idealized,
equal-length, error-free model. They do not establish equivalence to approximate
FUZZ heuristics or all practical Myers details.

## Counterexample: spelling preservation does not preserve occurrence counts

The exact finite regression already kernel-checked in
`Section62SimultaneousReduction` uses length-five strings
`sx=01234`, `m₁=23412`, `m₂=12341`, `sy=41200`. The edge `sx→sy` with overlap 1
is replaced through `m₁` with overlaps 3 and 3 (`3+3=5+1`). That first leg is
itself reducible through `m₂` with overlaps 4 and 4 (`4+4=5+3`). The terminal
chain `sx→m₂→m₁→sy` spells exactly `012341200`, the same word as the direct edge.
Both spellings have the length-five sliding-window multiset
`{01234,12341,23412,34120,41200}`. But the direct graph walk visits only
`[sx,sy]`, while the reduced expansion visits `[sx,m₂,m₁,sy]`; in particular,
`34120` is a physical window absent from the observed vertex set. Therefore
neither equality of spelled strings nor its multiset of *all physical windows*
implies equality between graph-vertex visits and physical occurrence counts.

This is a counterexample to the stronger correspondence sometimes implicitly
needed to transfer an ML objective based on vertex throughput. It is not a
counterexample to MB09 Observation 7 under its intended, still-to-be-reconciled
walk/occurrence definitions: the theorem here is about arbitrary graph chains,
not specifically a feasible flow or the exact walk semantics of that
observation. Observation 7 cannot be inferred solely from language preservation.

## What Observation 7 identifies (and what the repository models)

MB09 §3.2 defines a bidirected walk by successive incident edges whose
incidences at every interior vertex are opposite; a cycle additionally closes
with opposite incidences at its first vertex. Section 3.3 defines an overlap
edge by orientation-specific strand matches between molecule vertices.
Observation 7 in §6.2 identifies a read-vertex's number of visits by a walk
with the number of occurrences of that read-molecule as a submolecule of the
candidate spelled by the walk. It is not an assertion that every feasible flow
is itself one walk.

The repository keeps these objects separate in
`AssemblyP1/Section62BidirectedFlow.lean`:

* `BdEdge` (lines 86–100) stores departure/arrival strands, overlap length,
  and signed endpoint incidences. `overlapEdges` (147–154) constructs them
  from suffix/prefix equality over observed strands. `Chain` in
  `Section62SimultaneousReduction.lean` (61–66) only checks endpoint-strand
  adjacency. It does not check MB09's opposite-incidence walk rule. The latter
  is modeled by `OppositeAtInterior` and `BidirectedCircuit` (Flow.lean
  455–468).
* `spellChain` (SimultaneousReduction.lean 68–74) spells a linear edge-list
  chain by appending each arrival read past that edge's overlap. The two-hop
  theorem and `reduction_preserves_language` therefore concern `Chain` paths
  and linear-word equality; they do not produce a bidirected circuit or circular
  genome.
* `Spelling` (Flow.lean 412–420) is a nonempty cyclic list of strands, while
  `Spelling.visits` (448–453) counts positions by molecule representative.
  `Spelling.flow` (438–446) is the integer edge-traversal multiplicity of that
  cyclic walk. `SpelledFeasible62` (491–510) additionally requires circuit
  validity, graph membership, survival of reduction, and a feasible integral
  flow. No theorem here says every `Feasible62` flow has such a spelling.
* `BdFlow` is `BdEdge → ℕ` (252); `Feasible62` imposes vertex throughput at
  least one, signed balance, and zero terminal usage (375–408). These local
  constraints do not imply that the positive support is one connected cyclic
  walk with those exact multiplicities. A rational/half-integral relaxation
  also has a different coefficient domain from this literal natural-valued
  object.

For a circular spelling already given as a cyclic sequence of length-`L`
windows, its window positions are exactly the occurrences counted by
`Spelling.visits`, after quotienting by the declared representative/RC
convention. Identifying this with `throughput` further requires the walk-flow
and departure-count convention to agree. The L=5 witness above shows that
linear word preservation alone does not identify graph-vertex visits with
physical window occurrences: an intermediate spelling vertex can be absent
from the observed vertex set. For a circular candidate, one must in addition
prove incidence-compatible closure and account for wraparound windows; a
linear `spellChain` equality proves neither.

Thus the narrow implication is: **for a candidate already represented by a
valid bidirected circular walk, its read-molecule occurrence counts are the
counts of its cyclic windows under the chosen molecule orientation convention.**
This is the intended observation-level bridge, not a theorem that arbitrary
balanced flows are spelled circuits, nor that the repository's idealized
simultaneous deletion is exactly MB09's operational reduction. Flow,
spelled-circuit and circular-genome maximality remain distinct candidate
classes until those bridges and their objective preservation are proved.

## Consequences for #261

The idealized graph-language reduction has a precise kernel-checked proof, but
the graph-language-to-observation correspondence remains an independent proof
obligation. Before transferring a maximality failure or positive ML claim, state
the candidate universe (flows, spelled circuits, or circular genomes), truth
admission, length universe, orientation/RC quotient, and likelihood, then prove
the relevant inclusion/equality of candidate sets and objective values. This
audit establishes none of those transfers. Integer and half-integral flow
classes, exact versus fixed-N binomial likelihood, and non-spelled flows remain
separate open axes. Keep #261 and parent #255 open.

## Evidence

Primary sources: Medvedev–Brudno, *Maximum Likelihood Genome Assembly* (2009),
§6.2, <https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/>; Myers, *The fragment
assembly string graph* (2005), §2–§3. Repository evidence:
`AssemblyP1/Section62MyersIdealTransitivity.lean`,
`AssemblyP1/Section62SimultaneousReduction.lean`, and
`AssemblyP1/Section62BidirectedFlow.lean` (definitions cited inline), plus
`docs/section62-simultaneous-reduction-284.md`. The Lean regression is exact
and `decide`-checked as recorded there; this note adds no new formal theorem.
