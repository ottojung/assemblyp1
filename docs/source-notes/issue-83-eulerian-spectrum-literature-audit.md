# Literature audit: indistinct spectrum copies and primitive multiplied realizations

_Status: primary-source audit for issue #83, 2026-09-24. Claims about what
papers prove are **source facts**. The identifications with this repository are
**modeling choices**; conclusions about coverage of the issue are bounded
literature-audit conclusions, not novelty claims._

## Conclusion

No directly matching theorem was found that solves either substantive leaf of
issue #83. There are close primary results, but each has a convention that is
material:

1. For a fixed-length circular string, equality of complete length-`L` spectra
   is bijective with equality of the sequence of distinct edge types in an
   Eulerian tour of the spectrum-induced multigraph. The singleton fibre
   condition is consequently a cyclic-spelling uniqueness condition, and its
   forward equivalence with unique cyclic spelling is essentially definitional.
   Standard BEST counts and several uniqueness theorems count or distinguish
   parallel edge instances and therefore do **not** directly characterize the
   quotient required here.
2. Farrell and Levine give existence, counts, and minimal length for
   prescribed edge multiplicities, but their "primitive" is a primitive Laplacian
   period vector, not a primitive (aperiodic) circular word. Tesler does use
   "primitive" in the aperiodic-word sense and counts multisets of primitive
   cycles with prescribed edge multiplicities, but for a fixed complete de
   Bruijn graph and uniform multiplicity. Neither theorem characterizes when a
   primitive spectrum has another primitive realization of a different length.

## Objects that must not be conflated

For an oriented circular word `S` of length `G`, let `spec_L(S)` be its
length-`L` spectrum, and let `X` be the directed graph whose vertices are
occurring `(L-1)`-mers and whose edge types are occurring `L`-mers. Replace edge
type `e` by `spec_L(S)(e)` labelled copies when a tour is considered as a walk in
an ordinary edge-instance multigraph.

Issue #83 uses the quotient in which a walk is recorded as a cyclic sequence
of edge **types**: two tours that differ only by exchanging the labels of equal
parallel copies are the same spelling. This is not the object counted by BEST,
whose spanning trees and tours live on the edge-instance multigraph. Nor does
rotation introduce an additional free factor after fixing a canonical first
edge occurrence: a tour that starts with a specified edge instance and its
quotient under rotation are related by a bijection. Periodic words introduce a
genuine stabilizer and require separate handling.

Three uses of "primitive" also differ:

- **primitive circular word:** not a proper power; equivalently an aperiodic
  rotation class. This is Tesler, §8.1, and this repository's meaning.
- **primitive period vector:** a positive integer kernel vector of a directed
  graph Laplacian whose coordinates have gcd one. This is Farrell and Levine,
  following Björner and Lovász, Lemma 3.
- **primitive period vector of an Eulerian graph:** the constant all-one vector.
  Farrell and Levine, Lemma 3.

A result about the second notion says nothing by itself about the first.

## 1. Same-length spectrum fibres

### 1.1 The standard Eulerian reduction

The primary genome-assembly source Compeau, Pevzner, and Tesler, *Why are de
Bruijn graphs useful for genome assembly?* (2011, published version; DOI
[10.1038/nbt.2023](https://doi.org/10.1038/nbt.2023)), explains both the ideal
case and multiplicities. Its multiplicity construction says that if a `k`-mer
has multiplicity `m`, one connects its prefix to its suffix by `m` directed
edges. It also notes that the resulting graph is balanced because the indegree
and outdegree at a `(k-1)`-mer equal its occurrence count. The paper and its Box
1 identify the Eulerian circuit with the circular superstring. [source fact]

This matches issue #83's fixed support and fixed total `G` only after the
required mapping: spectrum entries become multiplicities, and the candidate
word must use every support edge with exactly its supplied multiplicity. [modeling
choice]

Pevzner, `k`-tuple DNA sequencing: computer analysis (1989, DOI
[10.1080/07391102.1989.10507752](https://doi.org/10.1080/07391102.1989.10507752)),
Theorem 7.5 as quoted by Acosta and Tomescu gives a cycle-intersection-tree
criterion for a unique Eulerian circuit. Their later primary presentation is
Nidia Obscura Acosta and Alexandru I. Tomescu, *Simplicity in Eulerian
Circuits: Uniqueness and Safety*, arXiv:2208.08522v2, §1.1 and Corollary 1. It
states uniqueness up to rotation by the cut-vertex condition

```text
A(G) = {v : outdeg(v)=1 or (outdeg(v)=2 and v is a cut vertex of U(G))},
```

where `U(G)` forgets orientation. [source fact]

This theorem is close to graph-theoretic simplification packet #83.2, but its
object is an Eulerian circuit on **distinguishable** edge instances. Section
1.1 and footnote 2 say explicitly that edge occurrence, not just vertex
occurrence, controls whether a walk appears, and §1.2 says that parallel edges
give at least two Eulerian circuits. Therefore applying the criterion directly
to the spectrum multiplicity multigraph is incorrect: any `L`-mer of count at
least two creates parallel instances, although their exchange is invisible in
the spectrum. [source fact + modeling conclusion]

### 1.2 BEST and prescribed multiplicities

Farrell and Levine, *Multi-Eulerian Tours of Directed Graphs*, Electronic
Journal of Combinatorics 23(2) (2016), #P2.21,
DOI [10.37236/5588](https://doi.org/10.37236/5588), explicitly permit loops and
multiple edges. Theorem 1 gives the BEST count for tours of an Eulerian
directed multigraph. Their Definition 1 and Theorem 2 replace edge `e` from
`u` to `v` by `pi_u` copies and count tours of the resulting edge-instance
multigraph. Their Definition 2 and Theorem 6 do the same for arbitrary
prescribed edge multiplicities `lambda_e`. The proof says that occurrences of
each edge can be labelled by an arbitrary permutation, which is exactly the
labelling that the spectrum quotient forgets. [source fact]

Consequently these theorems answer existence and labelled-tour counts for a
**fixed** multiplicity vector. They do not directly count, or test uniqueness
of, type-level cyclic spellings. [modeling conclusion]

### 1.3 Tesler's quotient count

Glenn Tesler, *Multi de Bruijn Sequences*, arXiv:1708.03654v1, §§2.1, 8, and 9,
is the closest audited source. It constructs the complete multigraph with `m`
labelled copies per `k`-mer. Theorem 9.1 bijects cycle partitions of the
edge-instance multigraph with edge-successor bijections. Corollary 9.2 counts
those partitions with distinguishable edges. Theorem 9.3 then factors out
`prod_e nu_e!`, where the copies of edge type `e` are indistinguishable, and
splits periodic cycles into their primitive powers. The resulting formula
counts multisets of aperiodic cycles with prescribed edge multiplicities. [source
fact]

This is an important exact precedent for the warning in issue #83: the
indistinguishable-copy quotient is a separate operation, not a raw BEST count.
It is not, however, a uniqueness criterion for arbitrary spectrum-induced
graphs. Tesler's §9 states a graph-partition framework for arbitrary balanced
graphs with prescribed edge multiplicities, but it counts a multiset of cycles.
The earlier complete uniform de Bruijn construction is the special case in
which the theorem's general graph framework is specialized. The singleton
cyclic spelling and rotation-orbit questions of #83 are different. [source fact
+ modeling conclusion]

## 2. Primitive words with multiplied edge multiplicities

### 2.1 Tesler: matching word convention, restricted graph data

Tesler defines a sequence primitive exactly when it is not a proper power and
equivalently when all rotations of its cyclic word are distinct (§8.1, pp. 18–19
of the PDF). A multicyclic de Bruijn sequence is a multiset of such primitive
cycles whose aggregate `k`-mer multiplicity is exactly `m` (§8.1). Theorem 9.3
counts these aggregate realizations with prescribed edge multiplicities after
the `nu_e!` quotient. [source fact]

Tesler's §9 is therefore closer to arbitrary-support graph data than the
earlier complete-uniform construction, but it does **not** state a criterion
for:

- a singleton normalized spectrum, where aggregate edge multiplicities are
  proportional rather than fixed (positive proportional vectors have the same
  support, so a different support is not a live ambiguity);
- existence of two different primitive singleton cycles on the same
  prescribed aggregate spectrum;
- different total lengths;
- a single connected Eulerian cycle as opposed to a multiset of cycles.

Those distinctions are the core of issue #83 packet 3. [modeling conclusion]

The older de Bruijn and Klarner source cited by Tesler—*Multisets of aperiodic
cycles*, SIAM Journal on Algebraic and Discrete Methods 3 (1982), 359–368, DOI
[10.1137/0213046](https://doi.org/10.1137/0213046)—is the predecessor for
counting multisets of aperiodic cycles. Tesler's §8.1 and reference [6] identify
that convention. It likewise does not supply the variable-length normalized
spectrum collision criterion sought here. [source fact + modeling conclusion]

### 2.2 Farrell–Levine: matching prescribed multiplicities, different "primitive"

Farrell and Levine's Definition 1 calls a tour `pi`-Eulerian when it uses every
edge from vertex `v` exactly `pi_v` times; Theorem 2 gives existence and a
labelled count, and Theorem 5 gives minimal tour length. In their §“Lemma 3,”
a period vector is a positive integer vector in the Laplacian kernel, and
"primitive" means that its entries have gcd one. Every period vector is a
positive integer multiple of the unique primitive period vector. [source fact]

Thus this paper directly studies multiplied edge uses, but its primitive tour
is a minimal solution of vertex-wise degree equations. If the graph is already
Eulerian, that period vector is all ones and the paper reduces to ordinary
labelled Eulerian tours. It is not a theorem about aperiodic/primitive words and
does not compare proportional spectra of different lengths. [modeling
conclusion]

## 3. Leaf-by-leaf determination for issue #83

### Packet 1: same-length exact criterion

A known theorem directly states the issue's unique cyclic edge-type spelling
criterion, with the quotient built into the object. No theorem was found doing
so. The straightforward iff is the mapping between a fixed-length circular word
and its cyclic type-word in the Euler tour, so it is essentially definitional
unless a new local quotient-graph criterion is derived. [bounded literature-audit
conclusion]

### Packet 2: graph-theoretic simplification

Acosta–Tomescu supplies a sharp linear-time criterion for the distinguishable
edge-instance convention. It is a useful source of switching ideas, but its
published theorem is not valid for the indistinguishable parallel-copy quotient
without a new adaptation. Tesler proves that the copy-labeling quotient is
nontrivial and gives the appropriate factorial quotient for cycle partitions.
No directly matching arbitrary-support graph criterion was found. [bounded
literature-audit conclusion]

### Packet 3: variable-length normalized-spectrum fibres

Tesler supplies the strongest convention match for primitive words and
prescribed multiplicities, but enumerates fixed, uniform complete-graph spectra
and aggregate multisets of primitive cycles. Farrell–Levine supplies arbitrary
prescribed multiplicities but uses a different meaning of primitive. Neither
gives the requested collision characterization for proportional integer spectra
and different total lengths. No direct theorem was found. [bounded
literature-audit conclusion]

### Packet 4: uniform finite-data recovery

The sources above concern population spectra and Eulerian reconstruction, not
the stronger requirement that one structural property make every admissible
sufficiently informative finite realization uniquely ML-recoverable. Nothing in
the audited theorems states that leaf. [bounded literature-audit conclusion]

## Primary-source bibliography

1. N. G. de Bruijn and J. A. Klarner, “Multisets of aperiodic cycles,” *SIAM
   Journal on Algebraic and Discrete Methods* **3** (1982), 359–368, DOI
   10.1137/0213046.
2. Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome Assembly*, J.
   Comput. Biol. **16** (2009), 1101–1116, DOI 10.1089/cmb.2009.0047. Relevant
   here only as the assembly-likelihood context; it does not supply the sought
   uniqueness theorem.
3. Phillip E. C. Compeau, Pavel A. Pevzner, Glenn Tesler, “Why are de Bruijn
   graphs useful for genome assembly?,” *Nature Biotechnology* **29**
   (2011), 18–25, DOI 10.1038/nbt.2023.
4. Pavel A. Pevzner, “`k`-tuple DNA sequencing: computer analysis,” *Journal of
   Biomolecular Structure and Dynamics* **7** (1989), 63–73, DOI
   10.1080/07391102.1989.10507752.
5. Matthew Farrell and Lionel Levine, “Multi-Eulerian Tours of Directed
   Graphs,” *Electronic Journal of Combinatorics* **23**(2) (2016), #P2.21, DOI
   10.37236/5588.
6. Glenn Tesler, “Multi de Bruijn Sequences,” arXiv:1708.03654v1 (2017),
   especially Definitions 1–2 and Theorems 2, 5, 6, 9.1, and 9.3.
7. Nidia Obscura Acosta and Alexandru I. Tomescu, “Simplicity in Eulerian
   Circuits: Uniqueness and Safety,” arXiv:2208.08522v2 (2023), especially §1.1,
   footnote 2, §1.2, and Corollary 1.
