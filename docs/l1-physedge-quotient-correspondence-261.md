# L1 source-graph correspondence: physical RC overlap multigraph ↔ PhysEdge quotient (#261)

_Status: bounded research increment, 2026-10-19. This note records a precise
candidate mapping, an exhaustive finite cross-check, and one concrete Lean
instantiation. It does **not** claim the full L1 correspondence or any ML
maximality result. It changes no merged claim and edits no classification._

_Reproduction:_ `python3 scripts/verify_261_l1_physedge_quotient.py` (exit 0;
594 small overlap graphs, checks W1-W6).

## The question

The merged quotient abstraction (`AssemblyP1.Section62PhysicalEdgeOrbit`,
`AssemblyP1.Section62PhysicalHalfIncidence`) defines the `PhysEdge` quotient of
tagged signed edges by the reversal setoid `RevRel` (`e ≈ e'` iff `e' = e` or
`e' = reverseEdge e`).  The identification of this quotient with MB09's
**physical** RC overlap multigraph (§6.2, Fig. 1) — preserving **edge
multiplicity** and **signed self-loop incidence** — is the OPEN L1 link
(`docs/section62-reversal-orbit-correspondence-gap-255.md`).

## The candidate mapping (formal definition)

**Physical RC overlap multigraph** (MB09 §3.1, §3.3, §6.2).  Vertices are
molecule classes; a class `c` has representative strand `s(c)` and reverse
complement `n(c) = rc s(c)`.  For an ordered pair of distinct classes
`(c1, c2)` and length `len` there are up to **four** physical edges, one per
strand-overlap case, each with a signed incidence at each endpoint class:

| case | strand overlap        | sign at `c1` | sign at `c2` |
|------|-----------------------|--------------|--------------|
| 1    | `suf(s1)=pre(s2)`     | `+1`         | `-1`         |
| 2    | `suf(s1)=pre(n2)`     | `+1`         | `+1`         |
| 3    | `suf(n1)=pre(s2)`     | `-1`         | `-1`         |
| 4    | `suf(n1)=pre(n2)`     | `-1`         | `+1`         |

A **self-loop** at `c` has up to **three** physical edges (mixed, `++`, `--`)
with signed incidences `(pos,neg)` at `c` equal to `(1,1)`, `(2,0)`, `(0,2)`.

**Tagged model** (`Tagged W = W × Bool`).  A tagged strand is `(word, bit)`;
`cls (w,b) = (w,0)` is the class representative, `flip (w,b) = (w,1-b)` the
other strand.  The string content is `word` when `bit = 0` and `rc word` when
`bit = 1` (the content-tracking reading; this is the only reading under which
the four strand-overlap cases are faithfully represented).  Case `k` is
represented by the tagged edge `bdEdge cls · · len` with the signs in the table.

**Candidate mapping.**  `physical edge ↦ physMk (tagged edge)`, the reversal
orbit of any representing tagged edge.

## What the cross-check verifies (W1-W6)

`scripts/verify_261_l1_physedge_quotient.py` re-transcribes the Lean definitions
literally (no shared code) and checks, exhaustively on 594 small overlap graphs
(binary reads of length 3 and 4, all subsets of size 1-3, `o_min ∈ {1,2,3}`,
plus the audit's `{000,001,011}` witness):

* **W1/W6** well-definedness: every tagged edge in one orbit determines the same
  (unordered endpoint classes, length, sign at each endpoint class);
* **W2** fibre size: every orbit has exactly 1 or 2 tagged representatives;
* **W3** loop incidence: a loop orbit has constant `(posHalf,negHalf)` at the
  class, in `{(1,1),(2,0),(0,2)}`;
* **W4** multiplicity: the set of orbits between two classes at a fixed length
  equals the independently counted set of physical strand-overlap edges;
* **W5** every non-loop orbit has fibre size 2, and the two mixed-type edges
  between distinct classes are **distinct** orbits;
* **W6** sign-at-endpoint is a function of the orbit.

**Result: all 594 instances pass (exit 0).**  5074 tagged edges → 3027 physical
orbits (1567 loop orbits).  The correspondence holds on this family.

## Lean instantiation (kernel-checked)

`AssemblyP1/Section62L1PhysEdgeCorrespondence.lean` proves
`twoClass_fourOrbits`: for two distinct classes the four tagged edges (cases
1-4) have **four distinct** `physMk` values, with the four distinct sign
patterns.  This is the edge-multiplicity half of the correspondence: the four
physical edges are not identified by the quotient (in particular the two
mixed-type edges are distinct orbits).  Together with the merged ATAT self-loop
witness (`Section62PhysicalEdgeOrbit.Atat`: three loop orbits with
`(pos,neg) = (1,1),(2,0),(0,2)`), this pins the orbit structure for both
distinct-class and self-loop edges.  No `sorry`/`admit`/`axiom`/`native_decide`.

## Verdict

**PARTIAL / bounded increment.**  The candidate mapping is well-defined and
preserves edge multiplicity and signed self-loop incidence on the checked
family, and one concrete Lean instance is kernel-checked.  What remains OPEN:

* the content-tracking reading of `Tagged W` is a **modeling choice**; the
  transport of the *actual* `overlapEdges` set (with its `toList`/`rep`/`rc`
  parameters) to physical orbits is not proved here;
* no transport of vertex lower bounds, read-copy counts, spells, contig /
  genome walks, or the exact ML objective to physical orbits;
* no claim that a physical orbit flow is a single circular genome.

This increment is non-overlapping with #284 (spelling-preserving transitive
reduction and visit-count transport) and #272 (Bayesian side information).
#255 and #261 remain OPEN.
