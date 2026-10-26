# #261 physical-orbit occurrence lemma: precise interface gap (2026-10-26)

## Scope and verified source

Audited `AssemblyP1/Section62PhysicalEdgeOrbit.lean` together with
`Section62PhysicalHalfIncidence.lean`, `Section62SpelledFlowAdapter.lean`, and
the repository's `Section62GenericAnchorSpelling` / reduced-circuit window
interfaces at `origin/main` (`1a51baa7f6d9b6a4c43cf94a6a3676ac302974b5`).
The repository remote is `https://github.com/ottojung/assemblyp1`.

The physical orbit file defines only a quotient of abstract tagged signed edges,
the endpoint half-incidences, finite-list orbit-flow totals, and an `ATAT`
example. It defines no circular-window occurrence extractor, no map from a
window occurrence to a tagged edge, no edge-availability predicate for such an
occurrence, and no physical graph induced by a circular spelling. Therefore the
requested unconditional statement that every extracted circular-window
occurrence maps to a physical orbit is not currently expressible from this
module's definitions. The gap is falsifiable: search of the file finds no
occurrence/window/extraction/availability declaration.

`Section62SpelledFlowAdapter.spelling_flow_feasible` has an explicit hypothesis
`hSteps : ∀ i, sp.step ... i ∈ edges`; this is an edge-membership premise for
its abstract oriented graph, not a definition or proof of a physical-orbit
window extractor. `Section62PhysicalEdgeOrbit` likewise does not connect its
`PhysEdge` quotient to `Spelling.step` or to the anchored circular-window
results. Thus neither the spelled-circuit adapter nor the generic spelling
lemmas discharge the missing source-to-physical-edge map.

## Strongest source-local implication

For any already-given physical edge orbit `q`, any weight `w`, and vertex `v`,
the contribution `w * physPos v q` and `w * physNeg v q` is representative
independent: choose any oriented tagged edge representative `e`; the existing
`physPos_mk`, `physNeg_mk`, `physPos_reverse`, and `physNeg_reverse` establish
that replacing `e` by `reverseEdge e` leaves both signed endpoint counts
unchanged. This also covers self-RC/palindromic edges: the quotient permits a
fixed point of reversal, and the half-incidence definitions count both endpoint
slots separately. The existing `ATAT` witnesses confirm the mixed-sign loop
has one positive and one negative half-incidence, while `++` / `--` loops
contribute two on the matching side. These facts concern already-defined
physical edges; they do not establish that a genome window occurrence
generates one.

The next exact lemma requires a source-faithful adapter, e.g. a definition
`windowOccurrenceEdge` mapping a circular start to a tagged signed overlap,
plus explicit hypotheses that its endpoint words overlap at the selected
length, its endpoint signs match the spelling orientations, and the resulting
edge is present in the modeled edge set. Prove that adapter first, then compose
with `physMk` and use the existing orbit/half-incidence results. Keep the
transitive-reduction survival obligation separate: membership in an unreduced
edge set does not imply survival under reduction.

No claim is made here about candidate-set inclusion, flows spelling one genome,
the truth's feasibility, exact versus fixed-`N` likelihood, arbitrary overlap
floor, or maximality transfer.

## Validation

`lake build AssemblyP1.Section62PhysicalEdgeOrbitAudit` passes at the verified
remote source. Its `#print axioms` audit reports only the expected quotient
axioms (`propext`, `Quot.sound`) on quotient-derived statements; loop incidence
computations themselves have no axioms. `git diff --check` passes. This note is
an audited diagnostic, not a new Lean theorem.
