# Issue #257: incidence-kernel witness and two-walk certificates

## Exact bridge

Fix a finite directed multigraph with edge set `E`, incidence map `M`, and a
positive integral circulation `A`. Write `s=A-1`. Non-rigidity is equivalent
to existence of an integral vector `δ` such that

```
Mδ=0,   Σₑδₑ=0,   δ≠0,   δₑ≥-sₑ for every e.
```

Equivalently it is existence of **two nonnegative integral circulations** `f,g`
with `Σf=Σg`, `f≠g`, and `f-g≥-s`: given `δ`, split it coordinatewise into
`δ⁺-δ⁻`. Their divergences agree. Route the opposite of that common divergence
using nonnegative integral flow `h` to obtain `M(δ⁺+h)=M(δ⁻+h)=0`; strong
connectivity guarantees such routing by sending each integer supply along a
directed path to integer demand. Then set `f=δ⁺+h`, `g=δ⁻+h`. Conversely
`δ=f-g` immediately has all four properties. Equal totals follow from
`Σδ=0`. The lower box is preserved exactly, not relaxed.

The graph hypothesis needed for the forward construction is the routing
property (every integral zero-sum divergence can be routed); strong
connectivity is sufficient, but the proof only needs routing for the particular
divergence obtained from `δ⁺`. The reverse implication needs no connectivity.
If the incidence balance is imposed only on a vertex subset, routing must be
available in that same balance domain; edges leaving it cannot silently be
ignored.

## Walk formulation caveat

Every nonnegative integral circulation decomposes into directed cycles, so it
is a finite **collection** of closed walks. It is the count vector of one
closed walk precisely when its positive-multiplicity support is connected
(Euler circuit in the directed multigraph of edge copies). In the strongly
connected ambient graph, add to `h` a nonnegative circulation whose support is
connected and spans all vertices; this makes both constructed supports
connected without changing `f-g`. Thus the asserted single-walk formulation
holds under strong connectivity, but the two-walks must have unrestricted
length: their lengths are their respective total multiplicities, equal by the
zero-sum condition. There is no bound by `G` in this argument. If walks are
allowed to be empty, explicitly require distinct count vectors; the box and
equal-length conditions alone do not preclude both being empty.

This separates the algebraic certificate (two nonnegative circulations) from
the literal walk certificate (two connected Eulerian supports). The former is
the exact statement formalized in `AssemblyP1/TwoWalkRigidity.lean`; the latter
uses the connectivity augmentation just described. No polynomial complexity
claim follows from the equivalence.

## Verification / provenance

The source in `docs/source-notes/issue-257-rigid-read-graphs.md` §12 and
`AssemblyP1/TwoWalkRigidity.lean` states the bridge and its routing hypothesis.
This audit is a proof review of that argument, not an independent kernel proof.
`gh issue view` could not be run in this runtime (`gh` is not installed), so
latest board comments/live ownership were not independently checked. Existing
untracked files in the checkout were left untouched.
