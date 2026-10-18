# #261 Layer A: the bidirected Euler circuit theorem (MB09 §3.4 Observation 1)

Primary source: A. Medvedev and M. Brudno, *Maximum Likelihood Genome Assembly*,
*J. Comput. Biol.* **16**(8) (2009) 1101–1116, §3.4 Observation 1:
<https://medvedevgroup.com/papers/jcb09.pdf>

> A bidirected graph contains an Eulerian circuit iff it is connected and
> balanced.

and §4.1, which builds a physical bidirected de Bruijn edge per `k`-molecule and
proves that a bidirected tour spells circular DNA.  See also Medvedev, Georgiou,
Myers and Brudno, *Computability of Models for Sequence Assembly*, WABI 2007,
Lemma 1: <https://www.cs.utoronto.ca/~brudno/medvedev_etal_wabi07.pdf>

This note records **Layer A** of the #261 source model: the abstract topological
Euler statement for a finite signed bidirected *multigraph* presented by physical
edge IDs.  It is deliberately separated from the source-specific spelling layer
(B) and the §6.2 flow/ML layer (C).

## 1. Source-aligned assumptions

A finite signed bidirected multigraph is presented by a finite **physical edge
ID** type `E` and a finite vertex type `V`.  Each physical edge `e` has two
**endpoint occurrences** (half-edges) `(e, false)` and `(e, true)`, and each
occurrence carries

* a vertex `endVtx e b`, and
* an incidence sign `endSgn e b ∈ {+1, -1}`.

This is MB09 §3.2's *multigraph*: parallel physical edges with the same endpoints
are distinct edge IDs, and a self-loop has two distinct endpoint occurrences, so
both of its incidences are counted.  The involution `flip` swaps the two
occurrences of an edge and is fixed-point-free.

The two source hypotheses are:

* **balanced**: at every vertex the number of positive incidences equals the
  number of negative incidences among the half-edges of the edges in `U`
  (`Balanced U`), which is MB09 §3.4's `pos(f)(v) − neg(f)(v) = 0` for the
  multiplicity vector that is `1` on `U`;
* **connected**: the vertices incident to `U` form one connected class under the
  relation "joined by an edge of `U`" (`SupportConnected U`).

A **bidirected transition** `ValidStep a b` (MB09 §3.2) says that `b` departs
from the vertex at which `a` arrives, with the opposite sign.  A **closed
alternating trail** `IsClosedTrail hs` is a nonempty cyclic list of half-edges
with distinct physical edges and every consecutive transition — including the
wrap-around — valid.  `IsEulerTrailOn U hs` additionally requires the physical
edges to be exactly `U`, each once.

## 2. The Lean interface

`AssemblyP1/BidirectedEulerian.lean` defines `SignedBiGraph V E`, `Half E`,
`flip`, `ValidStep`, `Balanced`, `SupportConnected`, `IsClosedTrail` and
`IsEulerTrailOn`, together with the counting machinery `signIndic`, `setImb`,
`trailImb`.

The full sufficiency target is named as the `Prop` `EulerianSufficient`.

## 3. What is kernel-checked

* `balanced_of_isEulerTrailOn` — the **necessary** direction.  Each visit of a
  closed trail enters and leaves with opposite signs, so its edge set is
  balanced.  The proof is the telescoping identity `trailImb_telescope` (the
  signed imbalance of a valid trail is the departure sign of the first step plus
  the arrival sign of the last) combined with `setImb_usedEdges` (the edge set's
  imbalance is the trail's imbalance).
* `exists_extension` — the **no-dead-end** lemma, the counting heart of
  Observation 1.  In a balanced edge set `U`, a valid open trail with distinct
  edges drawn from `U` that is not yet closed can always be extended by an unused
  edge of `U`.  The proof shows the unused residual imbalance at the current
  vertex is `−t` or `−2t` (where `t = ±1` is the required departure sign) while,
  if no opposite-sign incidence were available, it would be a nonnegative
  multiple of `t`; contradiction.
* `exists_closed_circuit` — a nonempty balanced edge set admits a closed
  alternating circuit through any prescribed incidence, obtained as a maximal
  valid trail (maximality over the finite type of nodup lists of half-edges).  It
  is the connected-component-free core of Observation 1, and it handles
  mixed-sign loops, `++` loops, and parallel physical IDs with identical signed
  endpoints.

## 4. What is *not* claimed

The assembly of `exists_closed_circuit` over a connected support into a *single*
Euler tour on all of `U` — splicing the circuits of `U` at shared vertices, using
that connectivity forces distinct circuits to meet — is the remaining step and is
**not** claimed here.  `EulerianSufficient` records that target explicitly.

Nothing in Layer A claims any source-specific spelling: it does not prove that a
particular §6.2 read-overlap flow is a single circular genome, nor that the
abstract graph is MB09's physical read-overlap graph, nor any
Observation-7 visit/occurrence correspondence.

## 5. Layered roadmap (kept distinct)

* **A (this note).**  Abstract signed bidirected multigraph Euler theorem.
* **B.**  MB09 §4.1 `k`-molecule edge construction and Watson–Crick orientation
  spelling: which Euler tours spell a circular genome, with the required
  `k`-molecule spectrum and length.  This is the *shortest-assembly* special case.
* **C.**  MB09 §6.2 read-overlap flow: transitive reduction, supersource/supersink,
  and the decomposition of an arbitrary flow into a *collection* of signed
  contig walks by connected components (cutting at synthetic edges).  The source
  itself says any flow can be decomposed into a collection of walks representing
  a non-contiguous assembly; the single-Euler theorem is the connected circular
  special case, not the general §6.2 statement.

## 6. Independent finite verification

`scripts/verify_261_bidirected_eulerian.py` enumerates all finite signed
bidirected multigraphs on a small vertex set (physical edge IDs, independent
endpoint signs, loops and parallel IDs) and checks, sharing no code with Lean,

* that `Balanced ∧ SupportConnected ∧ #edges > 0` is equivalent to the existence
  of a single cyclic alternately-signed tour using every edge once;
* the necessary direction (an Euler tour forces balanced and connected);
* a mutation control (dropping the wrap-around transition) that must disagree, so
  the tour search cannot be vacuous.

Run: `python3 scripts/verify_261_bidirected_eulerian.py V max_edges`.  At
`V=2, max_edges=4` it checks 4844 graphs with 304 balanced-connected nonempty
instances and zero disagreements (matching the board's independent census); at
`V=2, max_edges=5` and `V=3, max_edges=3` likewise zero disagreements.
