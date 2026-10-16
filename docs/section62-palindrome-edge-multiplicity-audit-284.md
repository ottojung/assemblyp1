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

All proofs use only Lean's standard permitted axioms (and some none); no
`sorry`, `native_decide`, or extra axioms.

## What remains open

The source model distinguishes molecule classes and strand orientations,
but does not automatically tell us whether four numerically equal
`BdEdge` entries for a self-complementary molecule should be **four
different flow channels**, one channel, or a weighted/multigraph
representation. `BdFlow` and edge-indexed finite feasibility constraints
may distinguish list positions even when the edge values are identical.

Therefore these theorems establish an **exact representation-level ambiguity**,
not by themselves a falsification of MB09/Myers or of previously proved
finite non-palindromic witnesses.

The additive `overlapEdgesDedup` is offered for comparison; the legacy
`strandsOf`, `overlapEdges` and `Feasible62` semantics are not changed.
A future source-faithful result must specify the intended multiplicity
convention (including palindrome incidences) and prove the appropriate
mapping from one flow domain to the other.

Related: `Section62ObservedMoleculeCount` counts a palindromic word
**once** in the read-spectrum *value*, whereas this audit concerns the
separate **edge-list representation**. Those facts are compatible.
