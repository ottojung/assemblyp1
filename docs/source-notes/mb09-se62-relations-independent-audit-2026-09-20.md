# Independent primary-text audit of Medvedev–Brudno §6.2: circuits, feasible flows, per-vertex lower bounds, observed multiplicities, and the optimized object

_Status: independent primary-source audit, 2026-09-20, written for issue #36.
Every claim is labelled **source fact** (directly quoted or paraphrased from the
primary text), **source-supported inference** (a reading forced or strongly
supported by source facts), **mathematical fact**, **verified computation**,
**repository fact**, or **open**._

_Scope. This note audits only the Medvedev–Brudno (2009) §6.1–6.2 object and
what follows from it for the Shomorony et al. (2016) sentence and for
same-length witnesses. It does not review any PR, does not select the 2016
referent, and does not re-decide the strand/oriented-vs-molecule fork; it
records where that fork is load-bearing._

_Reproduction:_ `python3 scripts/verify_mb09_se62_relations_audit.py`
(self-contained, exact `fractions.Fraction`, deterministic, exits non-zero on
any failed assertion).

---

## 0. Result at a glance

The primary text fixes the following exact relation chain, which is
independently reconstructed in §1–§3:

1. **Read/molecule space is per-type.** `§6.1` indexes the model by
   `k`-molecule `i` and lets `d_i` be "the number of times the `k`-molecule `i`
   appears in `D`". `§6.2` then identifies `d_i` with "the value of the flow
   through vertex `i`". **Source fact.**
2. **The truth genome is a circuit, not the optimized object.** "the original
   double-stranded genome corresponds to a circuit (assuming high enough
   coverage)". The optimization is over **flows**; the flow "represents a
   (non-contiguous) assembly of the genome". **Source fact.**
3. **Per-vertex lower bound is `1`, independent of `x_i`.** "Each vertex has a
   lower bound of 1 since it represents a read that must be present in the
   genome at least once. All other lower bounds are 0 and all upper bounds are
   infinity." **Source fact.**
4. **Observed multiplicities `x_i` enter only the objective.** `x_i` is the
   number of trials whose outcome is type `i`; it is not a flow bound. The
   feasible set is determined by the observed *support* and the overlap graph,
   not by the magnitudes `x_i`. **Source fact + source-supported inference.**
5. **The §6.2 objective is the §6.1 separable binomial approximation with an
   external `N`, not the exact multinomial.** `§6.2` uses the convex per-vertex
   costs `c_i`; `§6.1` derives
   `c_i(d_i) = −(x_i log d_i) − (n − x_i) log(N − d_i)` from the product of
   binomial marginals and states that the exact multinomial "is not possible"
   to make separable. **Source fact.**
6. **The optimized object is a flow / copy-count vector, not a sequence.**
   Sequences are recovered later by the `§7` heuristic. **Source fact.**

Two consequences for issue #36 (detailed in §4–§6):

- The `§6.2` reading is a **flow-feasible restriction of reading (2)'s fixed-`N`
  binomial objective**, with a flow (not a sequence) as the optimized object.
- The candidate-set-inclusion transfer that carries the same-length `#31`/`#32`
  witnesses to arbitrary lengths **does not carry into the `§6.2` feasible
  set**, because that set is graph/support-determined, not length-sliced. The
  same-length `§6.2` residue is therefore a genuinely separate question. A
  same-length `§6.2` witness `AAATAT → AAAAAT` is independently reproduced in
  §5; its arithmetic is exact, and its validity is conditional on the
  molecule-class reading that `§6.2`'s own `d_i ↔ vertex` identification
  forces.

---

## 1. Method and artifact

The primary text was extracted locally with `pdftotext -layout` from a cached
copy of the published article; no repository predicate or script was imported.

| Artifact | Locator | SHA-256 |
|---|---|---|
| MB09 full article PDF (J. Comput. Biol. 16(8) 1101–1116) | `jcb09.pdf` | `bfeaec37de55e87c35438108c33a8052f0fd6eb56f2903bb1d50d2793d8a5aa3` |

The repository's other notes quote the same paper from `PMC3154397` (HTML body)
and from the author's 2010 thesis; the quotations below agree with those
readings. [repository fact + verified computation]

---

## 2. Verbatim primary passages

### 2.1 Read and molecule space

> "A DNA molecule is an unordered pair of strings (also called strands) that are
> reverse complements of each other. … A *k*-molecule is a DNA molecule whose
> corresponding strings have length `k`. The *k*-molecule-spectrum* of a DNA
> molecule is the set of all `k`-molecules that are its submolecules." (`§3.1`)

> "Each read is represented by a single node, and each overlap (edge) has an
> orientation at both endpoints." (`§1.1`)

> "we show how to construct a bidirected de Bruijn graph, where each *k*-molecule
> is represented only once." (`§4.1`)

[source fact]

### 2.2 The exact and approximate likelihoods

> "Let `D` be a circular genome of length `N(D)`, and let `d_i` denote the
> number of times the `k`-molecule `i` appears in `D`. … In each trial, a
> position is uniformly sampled from `D` and the outcome of the trial is the
> `k`-molecule beginning at that position. For a given `i`, the probability that
> the outcome of a single trial is `i` is simply `d_i/N(D)`. Let the random
> variable `X_i` denote the number of trials whose outcome is `i`. There are
> `4^k` such variables … When taken together, their joint distribution is
> exactly the multinomial distribution …" (`§6.1`)

> "In our approach, we attempt to assemble the genome with the maximum global
> read-count likelihood. Equivalently, we minimize the negative log of this
> likelihood, `− log L`. We will eventually want to solve this using convex cost
> bidirected flow, so we need `− log L` to be a separable convex function in
> terms of the `d_i`'s. … Unfortunately, since the multinomial distribution has
> the constraint that `N(D) = Σ_i d_i`, this is not possible." (`§6.1`)

> "Because in the binomial approximation the length of the genome `N(D)` is a
> constant that is independent of each `d_i`, we can replace it by `N`, which is
> the length of the actual genome from which the reads were sampled. … For our
> experiments, we assume that the genome size is known." (`§6.1`)

> "Now we can write `− log L = K + Σ_i c_i(d_i)`, where `K` is some positive
> constant independent of all `d_i`, and
> `c_i(d_i) = −(x_i log d_i) − (n − x_i) log(N − d_i)`." (`§6.1`)

[source fact]

### 2.3 The §6.2 object

> "We are now ready to describe our algorithm for predicting copy counts. The
> first step is to build a bidirected overlap graph from the set of reads, which
> are DNA molecules. The vertices of this graph are the reads, and the edges are
> all possible bidirected overlaps of length at least `o_min` … We then perform
> transitive edge reduction …" (`§6.2`)

> "**Observation 7.** Let `r` be a read and `W` a walk in the transitively
> reduced bidirected overlap graph. The number of times `W` visits `r` is equal
> to the number of times `r` appears a submolecule of the molecule spelled by
> `W`." (`§6.2`)

> "In this graph, the original double-stranded genome corresponds to a circuit
> (assuming high enough coverage). … Next, we define a convex min-cost biflow
> problem on this graph, with bounds and costs on both the edges and the
> vertices. **Each vertex has a lower bound of 1 since it represents a read that
> must be present in the genome at least once. All other lower bounds are 0 and
> all upper bounds are infinity.** … By Observation 7, the `d_i`'s described
> above actually correspond to the value of the flow through vertex `i`, and we
> let `c_i` be the convex cost functions for the vertices. We finally solve the
> biflow problem …" (`§6.2`)

> "Since any flow can be decomposed into a collection of walks, our flow
> represents a **(non-contiguous) assembly** of the genome, and the flow going
> through each vertex represents the number of time the read is present in the
> assembly." (`§6.2`)

[source fact]

### 2.4 The flow definition and the meaning of "circuit"

> "The function `f : E → N` is called a flow if for every edge,
> `l(e) ≤ f(e) ≤ u(e)`, and for every vertex `v`, the flow along the
> positive-incident edges minus the flow along the negative-incident edges is
> equal to `b(v)`." (`§3.4`)

> "A tour is a walk that traverses every edge of `G` at least once. A circuit is
> a tour that is cyclical." (`§3.4`)

[source fact]

---

## 3. The exact relation, stated as a chain

The following chain is the audit's core. Each link is a source fact or a
source-supported inference from §2.

**(R1) The model index is the `k`-molecule type.** `§6.1` defines `d_i` as the
number of occurrences of `k`-molecule `i` in `D`. `§6.2` asserts that these same
`d_i` equal the flow through vertex `i`. Therefore the graph vertices of `§6.2`
are the observed `k`-molecule types, and two sampled reads with the same
molecule are one vertex, not two. [source fact + source-supported inference]

**(R2) The truth genome induces a closed walk.** "the original double-stranded
genome corresponds to a circuit"; by Observation 7, the number of visits to a
vertex equals the number of occurrences of that molecule in the spelled genome.
Hence the truth induces a flow with throughput `d_S` at each vertex.
[source fact]

**(R3) The feasible object is an integral flow, not a circuit.** `§3.4` defines
a flow by edge bounds plus vertex balance. `§6.2` sets edge lower bounds `0`,
vertex lower bounds `1`, and all upper bounds `∞` (plus a supersource/supersink
with prohibitive cost to make it a circulation). Any such flow is feasible, and
"any flow can be decomposed into a collection of walks". A circuit is only a
special (single-walk, edge-covering) flow; the truth is one, but competitors
need not be. [source fact]

**(R4) The lower bound is `1` per vertex and does not use `x_i`.** The text is
literal: "Each vertex has a lower bound of 1 … All other lower bounds are 0".
Observed multiplicity `x_i` is a trial count in `§6.1`; it is not stated as a
flow bound. Thus `d_i ≥ x_i` is a *strengthening* not present in the source.
[source fact + source-supported inference]

**(R5) The feasible set is determined by the observed support and the graph, not
by the magnitudes `x_i`.** The vertex set is the support of `x` (observed
molecule types), and the edge set is built from the read molecules and `o_min`;
neither depends on how many times each type was observed. `x_i` appears only in
the costs `c_i`. Consequently two read sets with the same support but different
multiplicities have the same feasible flow set and different optima.
[source-supported inference]

**(R6) The objective is the `§6.1` separable binomial with external `N`.**
`§6.2` uses the convex vertex costs `c_i`, which `§6.1` derives from the product
of binomial marginals after replacing `N(D)` by the externally known `N`. The
exact multinomial is explicitly *not* separable and is therefore *not* what
`§6.2` optimizes. [source fact]

**(R7) The optimized object is a copy-count flow; a sequence is downstream.**
The variables are edge flows, equivalently vertex throughputs `d_i`; the output
is a "(non-contiguous) assembly". Recovering a single sequence is the job of the
`§7` "From Flow to Contigs" heuristic. [source fact]

### 3.1 The objective's domain

The costs `c_i(d_i) = −(x_i log d_i) − (n − x_i) log(N − d_i)` are real-valued
only when `0 < d_i < N`. The source states the upper bounds as `∞`, but the
objective itself excludes `d_i ≥ N` (the `log(N − d_i)` term is undefined or
`−∞`). So the effective domain of the `§6.2` objective is `1 ≤ d_i < N` on each
vertex; the repository's use of `d_w ∈ [1, N]` is the objective's domain, not an
extra flow bound. [source-supported inference]

### 3.2 Summary table

| Object | Source definition | Type | Depends on `x_i`? |
|---|---|---|---|
| read / molecule type | `§3.1`, `§4.1`; one vertex per `k`-molecule | vertex | no (only support) |
| genome circuit | `§6.2`; closed walk, Observation 7 | special flow | throughputs via `x`? no |
| feasible `§6.2` flow | `§3.4` + `§6.2`: edge `0 ≤ f ≤ ∞`, vertex `d ≥ 1` | integral flow | support only |
| observed multiplicity `x_i` | `§6.1`: trial counts | objective data | — |
| `§6.2` cost `c_i` | `§6.1` binomial approximation | convex per-vertex | yes |
| optimized object | `§6.2` convex min-cost biflow | flow / copy counts | through costs |
| output sequence | `§7` heuristic | contigs | downstream |

---

## 4. Consequences for issue #36

### 4.1 What the `§6.2` reading is

If the 2016 phrase "the maximum-likelihood formulation of the AP (Medvedev and
Brudno, 2009)" is read as `§6.2`, then:

1. the objective is the **fixed-`N` product of binomial marginals** (reading
   (2)'s objective), not the exact multinomial; and
2. the candidate universe is the **flow-feasible set** `F_flow(R)`, not "all
   circular sequences"; and
3. the optimized object is a **flow / copy-count vector**, so "the
   maximum-likelihood **sequence**" in the 2016 sentence is a type mismatch
   unless an extra flow→sequence step is supplied. That step is the `§7`
   heuristic, which the source does not present as likelihood-optimal.

[source-supported inference; consistent with
`mb-formulation-referent-reconciliation.md` §4]

### 4.2 Why candidate-set inclusion does not transfer into `§6.2`

For readings (1)/(2), the candidate class is a set of circular sequences; the
length-`G` class is a subset, so a same-length competitor that beats the truth
also beats it in the unrestricted class. This is the transfer used by
`same-length-witnesses-candidate-set-inclusion.md` §3.

That argument requires the candidate class to be **length-sliced** and
**independent of the read graph**. `F_flow(R)` is neither: it is a set of flows
on a graph whose vertices are the observed support and whose edges depend on
`o_min` and the transitive reduction. A same-length sequence `D` belongs to
`F_flow(R)` only if its molecule spectrum is a feasible flow. Therefore:

- the `#31` (`AAABB → AAAAB`) and `#32` (`AAACC → AAAAC`) same-length competitors
  are **not** established to be in `F_flow(R)`; the repository already records
  that their competitors carry unobserved windows;
- the negative transfer to `§6.2` must be done with a **different witness** that
  is itself flow-feasible.

[mathematical fact + source-supported inference; consistent with
`same-length-witnesses-candidate-set-inclusion.md` §4–§5]

### 4.3 What is already known about the `§6.2` residue

The repository's `§6.2`-feasible witnesses that beat a bridged truth are
**different-length**:

| Witness | `|S|` | `|D|` | objective | ratio |
|---|---|---|---|---|
| `AAATT → AAAATT` | 5 | 6 | `§6.1` binomial, `N=5`, `n=3` | `9/8` |
| `AAAT → TAAAA` | 4 | 5 | `§6.1` binomial, `N=4`, `n=5` | `32/27` |

[repository fact; independently re-checked arithmetic in the cited notes]

So the **same-length** `§6.2` residue is a separate axis. It is closed by the
witness in §5 under the molecule-class + per-vertex reading, and remains open
under the per-occurrence strengthening and under the oriented single-strand
reading. [verified computation + open]

---

## 5. Independent check of the same-length `§6.2` witness

The following is recomputed from scratch by
`scripts/verify_mb09_se62_relations_audit.py` (no repository code imported).

```text
truth            S = AAATAT          G = 6
competitor       D = AAAAAT          |D| = 6   (same length)
read length      L = 3
realized starts  (0, 0, 1, 3, 5)     n = 5
external size    N = 6
observed         x    = { AAA:2, AAT:1, ATA:1, TAA:1 }
truth spectrum   d_S  = { AAA:1, AAT:1, ATA:3, TAA:1 }
competitor spec  d_D  = { AAA:3, AAT:1, ATA:1, TAA:1 }
```

- Molecule classes collapse reverse complements (`TAT ↦ ATA`), so the cyclic
  windows `AAA AAT ATA TAT ATA TAA` of `S` give `d_S(ATA) = 3`.
- `support(x) = support(d_S) = support(d_D) = {AAA, AAT, ATA, TAA}`. Under (R1)
  and (R4), this is exactly the `§6.2` condition for a spelled molecule to be an
  admissible candidate: every observed read vertex carries at least one unit.
- Both `S` and `D` are spelled by their cyclic length-3 window walks, hence are
  admissible `§6.2` candidates by Observation 7.
- Exact objective values:

```text
§6.1 binomial, N = 6, n = 5 :  L_6.1(D)/L_6.1(S) = 5
same-length exact multinomial:  L_exact(D)/L_exact(S) = 3
```

[verified computation; matches the independently derived
`agent/same-length-se62-0920` artifact
`docs/section62-same-length-bidirected-counterexample.md`]

**Load-bearing condition.** The witness needs (a) reverse-complement collapse
(one vertex per molecule class) and (b) the source's per-vertex lower bound `1`
rather than the per-occurrence strengthening `d ≥ x`. Under `d ≥ x`, the truth
itself is not a candidate (`d_S(AAA) = 1 < x_AAA = 2`). Under a strict oriented
`4^k` indexing, `S`'s window `TAT` is unobserved, so the truth's support does not
match `x`. Both are genuine source forks, not artifacts of the computation.
[source-supported inference + open]

---

## 6. Modeling cautions and one scope correction

These are offered independently of the existing audits.

1. **Identity-indexed vertices are a variant, not `§6.2`.** Some repository
   formalizations index the overlap-graph vertices by *read identity* (start
   position), so two reads of the same molecule become distinct parallel
   vertices. That is **not** the `§6.2` object as forced by (R1): the
   flow-through-vertex `i` is identified with `§6.1`'s per-`k`-molecule `d_i`,
   so identical molecules are one vertex. The identity-indexed graph is a
   legitimate variant, but any "amplification via parallel vertices" derived
   from it is a property of that variant, not of the source model. Any note
   using it should label the choice explicitly. [source fact + source-supported
   inference]

2. **A single spelled walk is a restriction, not `§6.2` feasibility.** `§6.2`
   explicitly says any flow decomposes into "a collection of walks" and calls
   the result a "(non-contiguous) assembly". Requiring the flow to decompose
   into a single closed walk that spells one candidate `D` restricts the
   candidate set to spelled molecules. That is the right object for a
   *sequence-level* restriction of `§6.2`, but it must be named as a modeling
   choice rather than folded into the source definition. [source fact]

3. **Scope correction.**
   `docs/source-notes/same-length-witnesses-candidate-set-inclusion.md` §5
   item 1 ("No current witness has both the truth and the competitor
   sequence-level `§6.2`-feasible") is true on `main` and on this branch, but is
   superseded by the unmerged same-length witness of §5. The sentence should be
   read as branch-scoped and updated when that artifact is integrated.
   [repository fact]

No discrepancy was found in the objective used by the kernel-checked
`FeasibleType` witness: it is the `§6.1` fixed-`N` product of binomial marginals
(reading (2)'s objective), consistent with (R6).
[repository fact + verified computation]

---

## 7. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| `§6.1` indexes by `k`-molecule; `d_i` is an occurrence count | source fact | `§6.1` quote |
| `§6.2` identifies `d_i` with the flow through vertex `i`; duplicates collapse | source fact + source-supported inference | `§6.2`, `§4.1` |
| Truth genome is a circuit; optimization is over flows | source fact | `§6.2` quote |
| Per-vertex lower bound is `1`; `d_i ≥ x_i` is not stated | source fact | `§6.2` quote |
| `x_i` enters only the objective; feasible set depends on support | source-supported inference | (R5) |
| `§6.2` objective is the `§6.1` binomial, not the exact multinomial | source fact | `§6.1`–`§6.2` quotes |
| Optimized object is a flow / copy-count vector | source fact | `§6.2` quote |
| Effective domain is `1 ≤ d_i < N` | source-supported inference | `log(N−d_i)` term |
| Candidate-set inclusion does not transfer into `F_flow(R)` | mathematical fact | (R3), §4.2 |
| `AAATAT → AAAAAT` is a same-length `§6.2` witness with ratios `5` (binomial), `3` (exact) | verified computation | §5 script |
| That witness needs molecule-class collapse + per-vertex lower bound | source-supported inference | §5 |
| Identity-indexed vertices and a single-walk requirement are modeling variants, not `§6.2` | source fact + source-supported inference | §6 |
| Which 2016 referent, tie semantics, oriented-vs-molecule fork | open | not settled here |

---

## 8. Reproduce

```sh
python3 scripts/verify_mb09_se62_relations_audit.py
```

The script recomputes the window spectra, observed multiplicities, support
equality, the `§6.1` binomial ratio, and the same-length exact ratio for
`AAATAT → AAAAAT`, and asserts each stated value. It shares no code with the
repository's other searches.

Primary source: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, *J. Comput. Biol.* **16**(8) (2009) 1101–1116, `§1.1`, `§3.1`,
`§3.4`, `§4.1`, `§6.1`–`§6.2`, `§7`.
