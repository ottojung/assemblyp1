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
`docs/section62-simultaneous-reduction-284.md`. The Lean regression is exact
and `decide`-checked as recorded there; this note adds no new formal theorem.
