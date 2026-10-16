# RC-palindromic reads and overlap-list multiplicity (#284)

_Status: Lean-checked representation audit. No reinterpretation of the
historical flow graph is asserted._

The implemented §6.2 graph is a **list of edges**:
`strandsOf rc verts = verts ++ verts.map rc`, and
`overlapEdges` iterates over the list of oriented source and target strands.
The `verts` list represents **molecule classes**, while `rc` enumerates
their opposite strands.

For a *reverse-complement palindrome* `w = rc w`, the enumeration
`strandsOf rc [w]` produces `[w,w]`. Any valid self-overlap `w→w` is
therefore generated four times, as a list value, even though its complete
`BdEdge` structure (including endpoint incidences) is identical.

## Kernel-checked, nontrivial regression

`AssemblyP1.Section62PalindromeEdgeMultiplicityAudit` uses the repository's
actual two-base DNA `Base` and `comp` operations, not a toy identity
involution. The read `ATAT` (length 4) satisfies `rc ATAT = ATAT`
and has a valid proper length-2 overlap with itself. It proves:

- `palindrome_strands_duplicate`: `strandsOf rc [ATAT] = [ATAT,ATAT]`.
- `originalGraph_eq_quadruple`: the generated edge list consists of
  **four identical** `ATAT→ATAT` overlap-2 `BdEdge` values.
- `dedupGraph_singleton`: `eraseDups` leaves **one** such edge.
- `mem_overlapEdgesDedup_iff`: a parameterized theorem proving that
  canonicalizing the edge list preserves **all edge-membership statements**
  for any alphabet, molecule type, involution and graph parameters.
- `palindrome_index_dimensions_differ`: the original and deduplicated
  edge lists have lengths 4 and 1.
- `duplicate_graph_throughput_four`, `canonical_graph_throughput_one`:
  assigning **one** unit of flow to the ONE edge value gives throughput **4**
  on the original edge list and **1** on the canonical list.
- `palindrome_dedup_feasible_one`,
  `palindrome_original_not_feasible_one`: the same unit edge-value flow and
  the same one-copy observed palindrome spectrum, with zero terminal use,
  are **feasible in the deduplicated graph and infeasible in the original**.
  This is a concrete, kernel-checked difference in the current feasibility
  semantics, not merely a hypothetical dimension discrepancy.

All proofs use only Lean's standard permitted axioms (and some none); no
`sorry`, `native_decide`, or extra axioms.

## Constructive comparison: keep orientation separate from its DNA word

MB09 [§3.3](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/)
enumerates four possible combinations of positive/negative endpoint
orientations and distinguishes overlap incidences even when the two DNA
words coincide. This motivates a **second**, independent model, now
kernel-checked in this audit:

- `taggedReadWord : Bool → List Base` maps **both distinct** strand
  orientation tags to the same palindrome `ATAT`.
- `taggedRc : Bool → Bool` flips the tag, and `taggedRep` identifies
  both orientations with one molecule class.
- `taggedGraph` has four **distinct** bidirected edge values with all
  four different incidence-sign pairs; Lean proves
  `tagged_graph_nodup` and `tagged_sign_pairs_distinct`.
- `tagged_unit_throughput_one` proves that one unit of flow on one
  orientation-labelled edge contributes exactly **one** to throughput,
  despite the DNA word itself being palindromic.

This is an explicit **orientation-tagging alternative** to collapsing
identical words via `eraseDups`, and illustrates what information the
original `W := List Base` representation loses. It remains a
comparison model, not an automatic correction of the historical source
algorithm: whether symmetric orientation cases should be identified
must be settled from its physical graph convention.

## What remains open

The source model distinguishes molecule classes and strand orientations,
but does not automatically tell us whether four numerically equal
`BdEdge` entries for a self-complementary molecule represent **four
physical overlaps**, one overlap, or another weighted/multigraph convention.

**Crucial implementation fact:** `BdFlow A W` is a function **of the
`BdEdge` value**, not of an edge-list position. Thus the four equal edge
records cannot have independent flow assignments. The implemented
`throughput` folds the list and counts the same edge's assigned value
four times. The concrete zero-terminal `Feasible62` theorem above shows
this can genuinely change whether a one-copy candidate is feasible.

These results prove an **actual difference between the two implemented
feasible sets**. They do *not* alone decide what multiplicities the original
MB09/Myers physical graph intends, nor invalidate witnesses without RC
palindromes.

The additive `overlapEdgesDedup` is offered for comparison; the legacy
`strandsOf`, `overlapEdges` and `Feasible62` semantics are not changed.
A future source-faithful result must specify the intended multiplicity
convention (including palindrome incidences) and prove the appropriate
mapping from one flow domain to the other.

Related: `Section62ObservedMoleculeCount` counts a palindromic word
**once** in the read-spectrum *value*, whereas this audit concerns the
separate **edge-list representation**. Those facts are compatible.
