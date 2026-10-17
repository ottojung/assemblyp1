# Reversal-quotiented physical signed-edge incidences (#261)

This kernel-checked **bounded algebraic construction** isolates one missing
ingredient in the source-model correspondence.

The merged `Section62PhysicalHalfIncidence` formalizes positive/negative
signed half-incidence counts for a tagged edge, counting BOTH endpoint
incidences even for loops, and proves these counts invariant under reversal.

`Section62PhysicalOrbitQuotient` constructs a **Setoid quotient** of tagged
edges by the involution `reverseEdge`. Its equivalence identifies exactly
`e` with `reverseEdge e`, not arbitrary edges with identical words, overlap
lengths or endpoints. Both positive and negative incidence functions descend
to well-defined functions on the quotient, via `Quotient.lift`. In particular,
an orbit is now ONE mathematical edge identity, so flow weights can be indexed
by physical orbits rather than duplicated ordered strand representations.

The definitions `orbitVisits`, `orbitNegativeVisits`, and `OrbitBalanced`
describe finite weighted orbit-incidence sums and their equality.

**Not proved here:** the quotient's source edge set is exactly MB09 §6.2's
bidirected overlap multigraph (including parallel physical edge IDs); flow
equivalence under transitive reduction; the source vertex-splitting throughput
bounds; preservation of spelled circular genomes or contig decompositions;
equivalence of physical-flow and finite-sample ML optimizers. Even a balanced
physical edge-orbit flow need not be one genome without extra Eulerian and
spelling conditions. These remain open in issue #261.

No `sorry`, `admit`, project axioms, or `native_decide`.
