# Independent source-semantic reconstruction of Medvedev–Brudno §6.2 (issue #36)

_Status: independent primary-source reading + reconciliation, 2026-09-20. This
note reads §6.2 of Medvedev–Brudno (2009) directly and pins the six aspects that
issue #36 must fix before any bridging-to-ML claim is well posed: graph
construction, vertex/edge bounds, conservation, objective/cost, treatment of
reverse complements, and the object the optimization returns. It is deliberately
**not** a counterexample search and does **not** redo the `o_min`-dependence
computation of the independent flow-reconstruction packet; see §6._

Every claim is labelled **source fact** (quoted or immediate from the text),
**source-supported inference**, **mathematical fact**, **interpretation**, or
**source gap**. This note does not select a referent for the Shomorony et al.
(2016) sentence.

Primary source: Paul Medvedev and Michael Brudno, “Maximum Likelihood Genome
Assembly,” *Journal of Computational Biology* 16(8), 2009, 1101–1116,
DOI [10.1089/cmb.2009.0047](https://doi.org/10.1089/cmb.2009.0047), full text
[PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/). Section numbers
below are Medvedev–Brudno’s. The displayed formulas are images in the PMC HTML;
the cost formula used here was read from the equation image this run (`c_i(d_i) =
-(x_i log d_i) - (n - x_i) log(N - d_i)`), consistent with the reading already
recorded in the repository.

---

## 0. Answers at a glance

| Aspect | Source-faithful answer | Status |
|---|---|---|
| Graph construction | Bidirected **read-overlap** graph, **not** the de Bruijn graph: vertices are reads (DNA molecules), edges are all bidirected overlaps of length ≥ `o_min`, then transitive reduction; a supersource/supersink is added | source fact |
| Vertex bounds | Each read **vertex** has lower bound `1`; no other positive lower bounds; all upper bounds `∞`; a vertex bound is realized on the §5.2 split edge `v⁻→v⁺` | source fact |
| Edge bounds | All edge lower bounds `0`; all upper bounds `∞`; no total constraint `Σ_i d_i = N` | source fact |
| Conservation | Bidirected signed-incidence balance `pos − neg = b(v)` (§3.4); §6.2 makes the augmented graph a **circulation**, so conservation holds counting the source/sink edges | source fact |
| Objective/cost | Convex **vertex** costs `c_i` = §6.1 separable binomial negative log-likelihood with external `N`, plus prohibitively large costs on source/sink edges; edge costs otherwise unspecified (read as `0`) | source fact / source gap |
| Reverse complements | A read **is** its DNA molecule (unordered reverse-complement pair), so the two strands are one vertex; bidirected edges track strand orientation; a walk and its reverse spell reverse complements | source fact |
| Returned object | A **flow** (possibly fractional), explicitly a “(non-contiguous) assembly”; a sequence only if the support is a single circuit, and actual contigs come from the §7 **heuristic**, not the optimization | source fact |
| Solver status | §6.2 solves via §5.2 + §5.1 (monotonization to a directed LP): half-integral optima in general and at worst a **2-approximation** to the optimal integral flow | source fact + mathematical fact |

---

## 1. Graph construction

**Source fact.** §6.2:

> “The first step is to build a bidirected overlap graph from the set of reads,
> which are DNA molecules. The vertices of this graph are the reads, and the
> edges are all possible bidirected overlaps of length at least `o_min`, where
> `o_min` is a parameter to our algorithm. We then perform transitive edge
> reduction, where we remove any overlap that is spelled by two shorter overlaps.
> This procedure is identical to the one described in Myers (2005), and we refer
> to the resulting graph as the transitively reduced bidirected overlap graph.
> While the set of possible DNA molecules spelled by the graph remains unchanged,
> the reduction drastically reduces the number of edges.”

Three points matter for issue #36:

1. This is an **overlap graph over reads**, not the bidirected *de Bruijn* graph
   of §4.1. The de Bruijn-graph statement “each k-molecule is represented only
   once” is about §4.1; the §6.2 statement is “the vertices … are the reads.”
2. `o_min` is a **free parameter**. The transitive reduction is explicitly
   stated to preserve the set of spelled molecules, so the sequence-level
   feasible set is governed by the pre-reduction edge set (all overlaps ≥
   `o_min`), not by which edges survive reduction.
3. The reads are **DNA molecules** (§3.1: “An unordered pair of strings … that
   are reverse complements of each other”). A read and its reverse complement
   are therefore one vertex, not two; §4.1’s spelling convention confirms that
   walks spell double-stranded molecules.

**Source gap.** The text says “the set of reads” but the §6.1 data are `n` reads
with type counts `x_i`. It does not explicitly say that duplicate sampled reads
are collapsed into one vertex. This is load-bearing; §2 resolves the reading.

---

## 2. Vertex and edge lower bounds (and the per-type reading)

**Source fact.** §6.2:

> “Next, we define a convex min-cost biflow problem on this graph, with bounds
> and costs on both the edges and the vertices. Each vertex has a lower bound of
> 1 since it represents a read that must be present in the genome at least once.
> All other lower bounds are 0 and all upper bounds are infinity.”

So:

- exactly one class of positive lower bounds exists: `1` on each read vertex;
- every edge lower bound is `0`, including edges incident to the supersource and
  supersink;
- every upper bound is `∞`.

**Source fact (vertex bound realization).** §5.2 explains that a vertex bound is
carried on a split edge: split `v` into `v⁻` and `v⁺`, reconnect incoming edges
to `v⁻` and outgoing edges to `v⁺`, and add `v⁻→v⁺`; “assign any lower/upper
bounds, as well as any costs, associated with `v` to the edge from `v⁻` to
`v⁺`.” §6.2 then identifies the §6.1 copy count `d_i` with “the value of the flow
through vertex `i`,” i.e. the flow on `v⁻→v⁺`. The bound `1` is thus a bound on
the **flow through the read vertex**, equivalently on the copy count `d_i`.

### 2.1 Resolving per-type versus per-occurrence

The independent §6.2 optimization-semantics note on branch
`agent/se62-optimization-semantics-0920` records this as a source ambiguity. I
reproduce the ambiguity and then resolve it; the resolution is the main new
determination of this note.

- **Text.** The source says a vertex “represents a read that must be present in
  the genome **at least once**.” Presence-once is a statement about the read
  *type*, not about how many times that type was sampled.
- **Statistics.** `x_i` is the observed count of `n` independent draws with
  replacement. The §6.1 objective uses `x_i` only as *data* inside
  `c_i(d_i) = -(x_i log d_i) - (n - x_i) log(N - d_i)`. Sampling with
  replacement means an observed count `x_i = 5` is not evidence that the genome
  contains five copies. A constraint `d_i ≥ x_i` would not be source-faithful
  and would be statistically unjustified; a constraint `d_i ≥ 1` for observed
  types is exactly the claim “it was sampled, so it exists.”
- **Graph semantics.** If duplicate sampled reads were kept as parallel
  vertices, every distinct read would have to be counted once per sample simply
  to satisfy the lower bounds, which is the per-occurrence strengthening under a
  different name. The source’s own evaluation (§8.2) compares “the flow going
  through every vertex in the overlap graph to the number of times that **the
  corresponding read** appears in the original genome,” i.e. one copy-count per
  read type.

**Determination.** The literal §6.2 lower bound is **per read vertex/type**:
`d_i ≥ 1` for every observed read molecule. The condition `d_D(w) ≥ x_w` for
every sampled occurrence is a strictly stronger **variant**, not a co-equal
reading. This agrees with the repository’s
[`reverse-complement-strand-convention.md`](reverse-complement-strand-convention.md)
(§2.3 item 2) and with the fixed-length per-type witness family.

**Consequence.** Any claim that the §6.2 candidate set excludes the `AAATAT`
family must either use the per-occurrence strengthening or the `o_min = L−1`
special case (§6); both must be named explicitly.

---

## 3. Flow conservation and the supersource/supersink

**Source fact (§3.4).** For a bidirected graph with edge bounds `l, u` and
vertex balances `b(v)`, a function `f` is a flow when `l(e) ≤ f(e) ≤ u(e)` for
every edge and, for every vertex `v`, “the flow along the positive-incident edges
minus the flow along the negative-incident edges is equal to `b(v)`.” At a link
the incidence is `±1`; at a loop it is `±2` or `0` (§3.2), so a loop contributes
twice its flow to the balance. A vertex with `b(v) = 0` is balanced, and a
connected balanced bidirected graph has an Eulerian circuit (Observation 1).

**Source fact (§6.2).** “We make a final change to the graph by adding a
supersource and supersink … This is a standard modification that will allow us
to convert a flow to a circulation problem.” The supersource/sink edges get
“prohibitively large costs … so that their usage is minimized.”

**Reconstruction (source-supported inference).**

- The augmented graph carries a circulation: conservation holds at *every*
  vertex, counting the source/sink edges in the signed incidence.
- The net signed flow of the original overlap-graph edges at a read vertex is
  therefore the net source/sink flow there. The text never fixes `b(v)` for the
  read vertices, so it is imprecise to say that read vertices are balanced
  (`b(v) = 0`); what is fixed is that the *augmented* graph is a circulation.
- Decomposing the circulation and cutting the source/sink edges yields a set of
  source-to-sink paths together with cycles. The paths are the linear contigs of
  §7; the net flow out of the supersource equals the number of such walks
  (contigs). Minimizing source/sink usage is thus a **contig-count penalty** on
  top of the likelihood.
- No constraint links the source/sink flow or the total `Σ_i d_i` to the
  external `N`. In particular §6.2 imposes **no** `Σ_i d_i = N`; the exact §6.1
  identity `N(D) = Σ_i d_i` belongs to the exact multinomial that §6.2 has
  replaced.

---

## 4. Objective and cost

**Source fact.** §6.2 defines “a convex min-cost biflow problem … with bounds and
costs on both the edges and the vertices.” The vertex figures are the §6.1
separable binomial costs (the exact multinomial was explicitly abandoned as not
separable):

```text
c_i(d_i) = -(x_i log d_i) - (n - x_i) log(N - d_i),
```

with external `N` (the actual/estimated genome length) and observed type counts
`x_i` over `n` reads. The source says “we let `c_i` be the convex cost functions
for the vertices,” and the only edge costs it names are the “prohibitively large
costs” on the supersource/sink edges.

Two consequences:

- **Only observed read vertices are indexed.** §6.1’s product ranges over all
  `4^k` types; §6.2 has a vertex only for an observed read. A spelled molecule
  may contain a length-`L` window that is not an observed read (it lies between
  two reads whose overlap is shorter than `L − 1`); it contributes no vertex and
  no likelihood factor. So §6.2 is **not** §6.1 restricted — it silently drops
  the `x_i = 0` factors. This is a source gap about the intended model.
- **Edge costs other than source/sink are unspecified.** Reading them as `0` is
  natural for a copy-count objective, but the text does not say it.

**Source fact (solver status).** §6.2 solves the biflow by “first applying the
reductions of Section 5.2 and then using the efficient algorithm of Section 5.1.”
§5.1 is Hochbaum monotonization to a directed, totally unimodular LP:

> “Though this results in a 2-approximation algorithm in the worst case, it found
> the optimal solution on almost all our input instances.”
>
> “the optimal solution of the LP is guaranteed to be half-integral (a multiple
> of 0.5) … the monotonized flow is at worst a 2-approximation to the optimal
> integral flow.”

and §8.2 reports that “half-integral flows were observed with some parameter
settings (too low coverage, too low `o_min`),” while the experimental parameters
produced integral flows. **Mathematical consequence:** the literal §6.2 pipeline
is not a certified exact optimizer of the convex biflow, and its vertex flows
(the `d_i`) may be fractional in general. Any theorem whose candidate is “the
§6.2 optimum” must say whether it means the ideal convex biflow, its
piecewise-linear approximation, or the monotonized half-integral output.

---

## 5. Reverse complements and strand orientation

**Source fact.** §3.1: “A DNA molecule is an unordered pair of strings (also
called strands) that are reverse complements of each other. We say a molecule
corresponds to each of its two constitutive strings, and vice-versa.” §6.2 reads
are DNA molecules, so a read vertex is a strand pair: a read and its reverse
complement are the **same** vertex. §3.3 gives each bidirected edge an
orientation at each endpoint; §1.1 says a walk in the bidirected overlap graph
“spell[s] a double-stranded string (molecule)”; §4.1 says “the string spelled by
`w`’s reverse walk is the reverse complement of the string spelled by `w`.”

**Interpretation.** The reverse-complement identification is built into what a
§6.2 vertex is, not an optional quotient the modeler adds. A §6.2 candidate is a
double-stranded object and “the sequence” it spells is defined only up to
reverse complement. This is distinct from the 2016 exposition, which is
single-strand, concludes “up to cyclic shifts,” and introduces reverse
complements only as §4.1 preprocessing that *adds* orientation nodes rather than
quotienting them (see
[`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md)
and the branch artifact `reverse-complement-strand-convention.md`).

---

## 6. What the optimization returns

**Source fact.** §6.2’s own closing sentence:

> “Since any flow can be decomposed into a collection of walks, our flow
> represents a **(non-contiguous) assembly** of the genome, and the flow going
> through each vertex represents the number of time the read is present in the
> assembly.”

So the §6.2 object is a flow (a copy-count vector on read vertices plus an edge
flow realizing it), and it explicitly need **not** be a single sequence. Only the
special case in which the flow’s support is a single circuit is a circular
genome; the source notes the true genome “corresponds to a circuit (assuming high
enough coverage).” Any actual sequence is produced later, in §7: “there is an
exponential number of decompositions possible” and “we use a heuristic” to pick
one, so the flow-to-contig map is not part of the optimization and is not a
likelihood.

**Sequence-level caution (`o_min`).** Even when one restricts to a single
spellable molecule, Observation 7 counts visits to read *vertices*, not every
length-`L` window of the spelled molecule. For `o_min < L − 1` a walk may skip an
unobserved intermediate window, so “spellable by a §6.2 walk” is weaker than
“every length-`L` window is an observed read.” The two coincide only at
`o_min = L − 1`. The repository’s tracked membership notes
(`section-6-2-feasible-set-membership.md`,
`section62-bidirected-flow-feasibility.md`) state the support-equality criterion
without that restriction; the independent flow-reconstruction packet on branch
`analysis/se62-independent-reconstruction` corrects it to support containment
plus cyclic `(L − o_min)`-density. This note accepts that correction and does not
redo it.

**Consequence for issue #36.** A statement about “the maximum-likelihood
**sequence**” cannot literally be a statement about the §6.2 flow optimum. At
best it is a statement about the circuit/spellable sub-case of §6.2, or about the
§6.1 sequence-level objectives. Before any bridging counterexample is read as
settling the published question, the model must fix: the objective layer
(exact §6.1 / binomial approximation / §6.2 flow), `o_min`, the lower-bound
reading (per-type or per-occurrence), and whether candidates are
circular-equivalence classes and/or reverse-complement classes.

---

## 7. Reconciliation with the existing repository notes

| Existing statement | Status after this reconstruction |
|---|---|
| §6.2 searches a bidirected flow, not a sequence; vertices are reads with per-vertex lower bound `1`; objective is the §6.1 binomial vertex cost (`section62-bidirected-flow-feasibility.md` §§1–2) | **Confirmed** independently |
| §6.2 imposes no `Σ_i d_i = N` (`mb09-objective-semantics.md` §5, branch `agent/mb09-objective-semantics-0920`) | **Confirmed** |
| The sequence-level feasible set is `supp(spec_L(D)) = supp(R)` (`section-6-2-feasible-set-membership.md`) | **Correct only at `o_min = L−1`**; general criterion is containment + `(L−o_min)`-density (flow-reconstruction packet) |
| Per-type vs per-occurrence lower bound is a source ambiguity (`section62-optimization-semantics.md` §3, branch `agent/se62-optimization-semantics-0920`) | **Resolved here (per-type)** by the presence-once wording, the statistical role of `x_i`, and §8.2’s per-read comparison |
| “Treats it as a circulation (`b(v)=0` on read vertices)” (`section62-optimization-semantics.md` §4) | **Refined**: only the *augmented* graph is a circulation; the text does not fix `b(v)=0` on read vertices, and the original-graph imbalance is the source/sink contribution |
| §5.1 solve path is a worst-case 2-approximation with half-integral optima (`section62-optimization-semantics.md` §2) | **Confirmed** from §5.1 verbatim; consequence for “the §6.2 optimum” made explicit in §4 above |

No claim in this note contradicts the two flow notes’ headline conclusions; the
residual gap they identify (which MB09 object the 2016 sentence denotes) remains
open and is out of scope here.

---

## 8. Epistemic classification

| Claim | Status |
|---|---|
| §6.2 builds a bidirected read-overlap graph, edges = overlaps ≥ `o_min`, transitive reduction, supersource/sink | source fact |
| Vertices are read molecules represented once; revcomp strands share a vertex | source fact |
| Vertex lower bound `1`, all other lower bounds `0`, all upper bounds `∞`; vertex bound realized on the §5.2 split edge | source fact |
| Lower bound is per read type, not per sampled occurrence | source-supported inference (presence-once + statistics + §8.2) |
| Conservation is signed-incidence balance; §6.2 augments to a circulation; read-vertex `b(v)` unspecified | source fact + source-supported inference |
| Objective = §6.1 separable binomial convex vertex cost with external `N`; source/sink edge penalty; other edge costs unspecified | source fact + source gap |
| Only observed read vertices are indexed, so §6.2 is not §6.1 restricted | source fact + mathematical fact |
| §6.2 imposes no `Σ_i d_i = N` | source fact + source reading |
| Solver is monotonization with half-integral optima and worst-case 2-approximation | source fact |
| §6.2 output is a flow / non-contiguous assembly; sequences are §7 heuristics | source fact |
| Sequence-level spelling is `o_min`-dependent | mathematical fact (flow-reconstruction packet) |
| Which MB09 object the 2016 sentence denotes | unresolved source ambiguity, out of scope |

---

## 9. Cross-references

- [`medvedev-brudno-candidate-class.md`](medvedev-brudno-candidate-class.md) —
  candidate-length and exact/approximate/flow separation.
- [`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md)
  — what the 2016 citation does and does not denote.
- [`shomorony-ml-reference.md`](shomorony-ml-reference.md) — 2016 model and
  reconstruction target.
- Branch artifacts not on `main`:
  - `docs/source-notes/mb09-objective-semantics.md` (branch
    `agent/mb09-objective-semantics-0920`) — §6 objective/copy-count analysis.
  - `docs/source-notes/section62-optimization-semantics.md` (branch
    `agent/se62-optimization-semantics-0920`) — first §6.2 optimization-semantics
    note; this note independently reconstructs and reconciles it.
  - `docs/section62-feasibility-independent-reconstruction.md` (branch
    `analysis/se62-independent-reconstruction`) — corrected `o_min`-dependent
    spelling criterion, not redone here.
  - `docs/source-notes/reverse-complement-strand-convention.md` (branch artifact)
    — strand/equivalence conventions.
