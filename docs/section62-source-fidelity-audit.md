# Source-fidelity audit of Medvedev–Brudno §6.2 and its effect on the §6.2 counterexample frontier

_Status: independent primary-source reconstruction + mathematical audit +
exact-rational computation, 2026-09-20. Every claim is labelled **source fact**,
**source-supported inference**, **modeling decision**, **mathematical argument**,
**verified computation**, **kernel-checked result**, **source gap**, or **open**._

_Reproduction: `python3 scripts/verify_se62_source_fidelity.py` (self-contained,
exact `fractions.Fraction`, deterministic, under a second; exits non-zero on any
assertion failure)._

_Subject of the audit:_ the §6.2 model and the kernel-checked witness in
[`bridging-se62-flow-ml-counterexample.md`](bridging-se62-flow-ml-counterexample.md)
and `AssemblyP1/Section62BridgingCounterexample.lean` (branch
`analysis/bridging-se62-ml-lean-0920`). This note does not settle which
Medvedev–Brudno object the 2016 sentence denotes, and it does not modify any
`source: @ottojung` intent.

---

## 0. Bottom line

1. **The primary-source pipeline of §6.2 is reconstructed in §1.** It is:
   reads are DNA molecules (unordered reverse-complement pairs, one graph
   vertex per read); edges are bidirected overlaps of length at least a free
   parameter `o_min`; a transitive edge reduction removes overlaps spelled by
   two shorter overlaps; a supersource and supersink (thesis: plus a return edge
   supersink → supersource) turn the flow into a circulation; every read vertex
   has lower bound `1`, all other lower bounds `0`, all upper bounds `∞`; the
   vertex cost is the §6.1 separable binomial cost in `d_i`, parameterised by
   the observed count `x_i`, the read count `n`, and the external genome size
   `N`; the output is explicitly a **"(non-contiguous) assembly"**. [source
   facts, §1]

2. **Two tracked conventions are not source-faithful, and both widen the
   frontier.**
   - **(M1) `o_min` / spelling criterion.** The tracked note uses the
     sequence-level criterion `supp(spec_L(D)) = supp(x)` ("support equality").
     That is exact only for `o_min = L − 1`. The source leaves `o_min` free and
     uses `o_min = 17..21` with `L = 25`; the correct general criterion is
     **support containment plus `(L − o_min)`-density** of the observed-read
     windows. For `o_min < L − 1`, a spelled molecule may contain unobserved
     windows, so support equality is strictly too strong. [mathematical
     argument + verified computation, §3.1, §4]
   - **(M2) Vertex lower bound.** The tracked kernel note uses the
     per-occurrence bound `d_w ≥ x_w`. The source's lower bound is `1` per read
     *vertex*, and each read is one node, so the literal reading is the
     **per-type** bound `d_w ≥ 1`. The source is silent about duplicate
     sampling, so per-occurrence is a legitimate *modeling decision*, but it is
     stricter than the source and is not the literal reading. [source fact +
     source-supported inference + source gap, §3.2, §4]

3. **The existing kernel-checked witness survives the source-faithful reading.**
   `S = AAATT → D = AAAATT` is sequence-level §6.2 feasible under per-type lower
   bounds and the containment + density criterion for every `o_min ≤ 2` (all
   positions are allowed), with binomial ratio `9/8`. So the negative
   conclusion is robust to M1 and M2. [verified computation + kernel-checked
   result, §4]

4. **But the frontier strictly grows.** Under the source-faithful
   molecule + per-type + containment reading with `o_min = 1`, the tracked
   support-equality criterion *excludes* a smaller witness that is nevertheless
   valid: truth `S = AAAT`, competitor `D = AAAAT`, binomial ratio `16/9` and
   candidate-intrinsic-length exact ratio `1024/625`. [verified computation, §4]
   Hence the tracked bounded searches that fixed support equality (or
   `o_min = L − 1`) are not exhaustive for the source-faithful feasible set,
   although their headline negative conclusions remain true.

---

## 1. Primary-source reconstruction of §6.2

Primary sources:

- Paul Medvedev, Michael Brudno, "Maximum Likelihood Genome Assembly,"
  *J. Comput. Biol.* **16**(8) (2009) 1101–1116, DOI `10.1089/cmb.2009.0047`,
  [PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/). Section 6.2 is
  titled "Putting it all together".
- Paul Medvedev, *Genome Graphs*, PhD thesis, University of Toronto, 2010,
  handle `https://hdl.handle.net/1807/26297`, Chapter 4, §4.4 "Finding the copy
  counts". This is the dissertation version of §6.2 and carries one detail the
  journal omits (the return edge, §1.4 below).

### 1.1 Reads, molecules, reverse complements

> "A DNA molecule is an unordered pair of strings (also called strands) that are
> reverse complements of each other. We say a molecule corresponds to each of
> its two constitutive strings, and vice-versa." (MB09 §3.1)

> "Kececioglu (1992) introduced an elegant method for dealing with
> double-strandedness by modeling overlaps between DNA molecules using a
> bidirected overlap graph. **Each read is represented by a single node** …"
> (MB09 §1.1, Fig. 1 context)

> "… we show how to construct a bidirected de Bruijn graph, where **each
> k-molecule is represented only once**." (MB09 §4.1)

**Source facts.** A read is a DNA molecule, i.e. an unordered reverse-complement
pair; a word and its reverse complement are the same object. A molecule is
represented by a single vertex. This makes the vertex set closed under reverse
complement: the equivalence relation is the dihedral one (reverse complement),
not merely cyclic shift.

**Source-supported inference (per-type vertices).** Combined with §8.2 — "we
compared the flow going through every vertex in the overlap graph to the number
of times that the **corresponding read** appears in the original genome" — the
vertices are read *types* (molecule classes), so the lower bound `1` of §1.5 is
per type, `d_w ≥ 1`.

**Source gap.** MB09 never says how duplicate samples of the same read type are
treated. Per-type is the literal reading of "each read is represented by a
single node"; per-occurrence (`d_w ≥ x_w`) is a separate modeling decision.

### 1.2 The bidirected read-overlap graph

> "The first step is to build a bidirected overlap graph from the set of reads,
> which are DNA molecules. **The vertices of this graph are the reads**, and the
> edges are all possible bidirected overlaps of length at least `o_min`, where
> `o_min` is a parameter to our algorithm." (MB09 §6.2)

Bidirected overlap is defined in §3.3 by the four strand-orientation cases
(`p(x)`/`n(x)` positive/negative strand labels; positive/negative incidence),
and the edge construction is attributed to Kececioglu (1992). **Source fact.**
The graph is a bidirected multigraph (MB09 §3.2); edge incidence is in
`{−2,−1,0,1,2}`.

**Source gap / modeling decision.** `o_min` is a free parameter. In the §8
experiments `L = 25` and `o_min ∈ {17,18,19,20,21}`, so `o_min < L − 1 = 24`.
Any source-faithful statement must either name `o_min` or cover its range; the
tracked criterion silently takes `o_min = L − 1`.

### 1.3 Transitive edge reduction

> "We then perform transitive edge reduction, where we remove any overlap that
> is spelled by two shorter overlaps. This procedure is identical to the one
> described in Myers (2005) … While **the set of possible DNA molecules spelled
> by the graph remains unchanged**, the reduction drastically reduces the number
> of edges." (MB09 §6.2; the thesis says "similar to" rather than "identical")

**Source fact.** The reduction preserves the set of spelled molecules. This is
what licenses checking feasibility on the unreduced graph and asserting a walk
exists in the reduced graph.

### 1.4 Supersource / supersink and circulation

Journal §6.2:

> "We make a final change to the graph by adding a supersource and supersink to
> the graph. This is a standard modification that will allow us to convert a
> flow to a circulation problem (Ahuja et al., 1993)."

Thesis §4.4 (the omitted detail):

> "We make a final change to the graph by adding a supersource and supersink to
> the graph, **and an edge out of the supersink into the supersource**. This is
> a standard modification that will allow us to convert a flow to a circulation
> problem."

**Source facts.** The augmented graph has a designated supersource `s` and
supersink `t`; the thesis explicitly adds the return edge `t → s`. Flow on the
return edge counts the number of walks (contigs). Edge costs on the
source/sink-incident edges are made prohibitively large "so that their usage is
minimized" — i.e. the §6.2 objective penalises the number of contigs and is
therefore *not* the pure §6.1 likelihood for multi-contig flows. For a single
circuit (one walk) the penalty is the same for truth and competitor and cancels
in a comparison.

### 1.5 Bounds, flow conservation, and `d_i`

> "Next, we define a convex min-cost biflow problem on this graph, with bounds
> and costs on both the edges and the vertices. **Each vertex has a lower bound
> of 1** since it represents a read that must be present in the genome at least
> once. **All other lower bounds are 0 and all upper bounds are infinity.**"
> (MB09 §6.2)

The bidirected flow definition is §3.4:

> "The function `f` is called a flow if for every edge, `l(e) ≤ f(e) ≤ u(e)`,
> and for every vertex `v`, the flow along the positive-incident edges minus the
> flow along the negative-incident edges is equal to `b(v)`."

**Source facts.** Feasibility is `l(e) ≤ f(e) ≤ u(e)` on every edge plus the
vertex balance constraint; after the supersink → supersource edge the problem is
a circulation (`b ≡ 0`). Vertex lower bound is `1` per read vertex; edge lower
bounds `0`, upper bounds `∞`.

> "By Observation 7, the `d_i`'s described above actually correspond to the
> value of the flow through vertex `i`, and we let `c_i` be the convex cost
> functions for the vertices." (MB09 §6.2)

**Source fact.** `d_i` is the vertex flow at read vertex `i` (the copy count).
Observation 7 (thesis Observation 9):

> "Let `r` be a read and `W` a walk in the transitively reduced bidirected
> overlap graph. The number of times `W` visits `r` is equal to the number of
> times `r` appears a submolecule of the molecule spelled by `W`."

### 1.6 How `d_i` and `x_i` enter the cost

§6.1 gives the objective. The exact global read-count likelihood is a
multinomial over all `4^k` read types with candidate-intrinsic length `N(D)`:

> "Let `D` be a circular genome of length `N(D)`, and let `d_i` denote the
> number of times the `k`-molecule `i` appears in `D` … the probability that the
> outcome of a single trial is `i` is simply `d_i/N(D)`… When taken together,
> their joint distribution is exactly the multinomial distribution …"

Because `N(D) = Σ_i d_i`, `−log L` is not separable; MB replace `N(D)` by an
external `N` (the true genome length, assumed known) and use the product of
per-type binomials. The thesis gives the resulting per-type cost verbatim:

> `c_i(d_i) = −(x_i log d_i) − (n − x_i) log(N − d_i)`

where `x_i` is the observed count of read type `i`, `n` the number of reads, and
`N` the external genome size. **Source facts.** So `x_i` enters the cost as the
exponent/weight of type `i`; `d_i` enters as the flow variable; the domain
requires `0 < d_i < N`. The `x_i = 0` types contribute the factor
`(1 − d_i/N)^{n}` in the literal product.

### 1.7 The output need not be a sequence

> "Since any flow can be decomposed into a collection of walks, our flow
> represents a **(non-contiguous) assembly** of the genome, and the flow going
> through each vertex represents the number of time the read is present in the
> assembly." (MB09 §6.2)

> "In general, any flow can be decomposed into a collection of walks, which, in
> our case, correspond to the assembled contigs. … we use a heuristic to find
> one where the length of the walks (contigs) is large …" (MB09 §7)

**Source facts.** §6.2's candidate object is a flow, not a sequence; single
molecules correspond to circuits. Sequence recovery is a post-hoc §7 heuristic.

### 1.8 Journal vs thesis evidence table

| Element | Journal §6.2 | Thesis §4.4 | Label |
|---|---|---|---|
| vertices are reads (molecules) | yes | yes | source fact |
| edges = overlaps `≥ o_min` | yes | yes | source fact |
| transitive reduction preserves spelled molecules | yes ("identical to Myers 2005") | yes ("similar to") | source fact |
| supersource/supersink | yes | yes | source fact |
| return edge supersink → supersource | omitted | **explicit** | source fact (thesis) |
| vertex lower bound `1`, others `0`, uppers `∞` | yes | yes | source fact |
| vertex cost = §6.1 binomial cost | yes | yes (formula) | source fact |
| output "non-contiguous assembly" | yes | yes | source fact |
| Observation number | 7 | 9 | source fact |
| duplicate-read convention | not stated | not stated | source gap |
| `o_min` value | free parameter | free parameter | source fact |

---

## 2. The tracked repository model

The tracked note+script+Lean (`analysis/bridging-se62-ml-lean-0920`) assert:

- **Feasibility** `Feasible(d,x) := (∀c, 0<d c ↔ 0<x c) ∧ ∀c, x c ≤ d c`, i.e.
  support equality plus the per-occurrence lower bound (`Section62BridgingCounterexample.lean:128`,
  `scripts/verify_se62_bridging_flow_counterexample.py:170`).
- **Statement (P):** if `I_s` holds and the truth-induced flow is admissible,
  then the truth-induced flow maximizes the §6.1 objective over the §6.2
  feasible set. (Note §2.)
- **Witness:** `S = AAATT`, `D = AAAATT`, molecule/revcomp reading, ratio `9/8`.

The tracked note is explicit that it does not settle the referent, and it labels
the per-occurrence choice. The audit below asks whether the *source-faithful*
reading changes the frontier.

---

## 3. Mismatch audit

### 3.1 M1 — spelling criterion: support equality vs containment + density

Observation 7 plus the §4.1 spelling method ("this method of traversing a walk
in a bidirected graph to spell a molecule works for any graph whose edges are
bidirected overlaps") yields the following characterization. [mathematical
argument]

> **Criterion.** A circular molecule `D` is spelled by a closed walk in the
> read-overlap graph with overlap threshold `o_min` (visiting every observed
> read vertex at least once) iff
> **(C1)** every observed read type occurs as a length-`L` window of `D`, and
> **(C2)** the positions of `D` whose length-`L` window is an observed read are
> cyclically `(L − o_min)`-dense (maximum cyclic gap `≤ L − o_min`).

_Proof sketch._ Placing a read at each allowed position gives consecutive reads
overlapping by `L − gap ≥ o_min` that agree on the overlap (both are windows of
`D`) and whose union covers `D`, hence a closed walk spelling `D`; support
containment makes every observed read vertex visited. Conversely a closed walk's
visits are exactly occurrences of reads (Observation 7), giving (C1); consecutive
vertices are joined by overlaps `≥ o_min`, giving (C2). ∎

For `o_min = L − 1`, (C2) forces every position to be allowed, so the criterion
collapses to `supp(spec_L(D)) = supp(x)` — the tracked criterion. For
`o_min < L − 1`, unobserved windows are permitted and the feasible set strictly
grows. **Source fact:** `o_min` is a free parameter and the source's own
experiments use `o_min < L − 1`. **Frontier impact:** any search or theorem that
assumes support equality (or implicitly `o_min = L − 1`) covers only a proper
sub-frontier.

### 3.2 M2 — lower bound: per-type vs per-occurrence

The source fixes the lower bound at `1` per read vertex and represents each read
once (§1.1, §1.5). The literal reading is therefore `d_w ≥ 1` (per-type).
Per-occurrence (`d_w ≥ x_w`) is **not** stated and is a modeling decision; the
source is silent about duplicate sampling (source gap). [source fact +
source-supported inference + source gap]

**Frontier impact:** per-type admits strictly more candidates. Since
`d_w ≥ x_w ⇒ d_w ≥ 1`, every per-occurrence witness is a fortiori a per-type
witness, but not conversely. A per-occurrence search therefore cannot be
presented as a per-type frontier unless the relaxation is recorded.

### 3.3 M3 — unobserved read types in the objective

§6.1's product ranges over all `4^k` read types; §6.2's graph has vertices only
for observed reads, so a spelled molecule containing an unobserved window (which
M1 permits for `o_min < L − 1`) contributes no vertex and hence no likelihood
term, whereas the literal §6.1 factor would be `(1 − d_i/N)^n`. [source fact +
source gap]

**Frontier impact:** changes numeric likelihood ratios for candidates with
unobserved windows. The kernel witness is support-equal, so M3 does not affect
it; the M1-widened frontier does encounter M3.

### 3.4 M4 — read length vs `k`-molecule index

§6.1 indexes `k`-molecules (`4^k` variables); §6.2's vertices are reads.
Identifying the read length `L` with the §6.1 molecule size `k` is necessary for
Observation 7 to identify the vertex flow with `d_i`, but MB09 does not state
`L = k` explicitly. [modeling decision] The tracked model makes this
identification; it should be recorded as such.

### 3.5 Flow conservation, source/sink, and the objective

The tracked sequence-level criterion never invokes the balance constraint or the
source/sink penalty, because it tests single-molecule spelling. For a single
circuit the walk gives an integral balanced flow and the source/sink penalty is
identical for both candidates, so the §6.1 comparison is valid *within the
circuit sub-case*. But the §6.2 objective on the full flow set includes the
contig-count penalty and ranges over non-contiguous assemblies; a statement
"(P) over the §6.2 feasible set" should say whether it is restricted to
circuits. [source fact + modeling decision] This does not affect the witnessed
refutations (both candidates are single molecules) but affects the phrasing of
(P).

---

## 4. Independent verification

`scripts/verify_se62_source_fidelity.py` (exact rationals; all assertions pass):

- **(A) Kernel witness is source-faithful-robust.** `S = AAATT`, `D = AAAATT`,
  `L = 3`, molecule (`A↔T`) reading, starts `(0,1,4)`. `I_s` holds; both `S`
  and `D` satisfy containment + density for `o_min ∈ {1,2}`; both satisfy the
  per-type lower bound; binomial ratio `9/8`. Every position is an allowed
  window, so support equality also holds and the witness satisfies even the
  tracked criterion. [verified computation; the finite instance is
  kernel-checked in `AssemblyP1/Section62BridgingCounterexample.lean`]
- **(B) Support equality is the `o_min = L − 1` case.** (Single-strand
  contrast, `S = AAABB`, `D = AAAABB`, `L = 3`, `o_min = 1`.) The truth has the
  unobserved window `BBA`; support equality excludes it, but containment +
  density (max gap `2 = L − o_min`) admits it, and the competitor has larger
  objective (`27/16` binomial, `3125/1944` exact). [verified computation]
- **(C) A source-faithful molecule-convention witness excluded by the tracked
  criterion.** Truth `S = AAAT` (`G = 4`), starts `(0,0,1,2)`, `L = 3`,
  molecule (`A↔T`) reading, `o_min = 1`, external `N = 4`, `n = 4`.
  - `I_s` holds (coverage; the length-1 triple `A@0,1,2` all-bridged;
    interleaving vacuous).
  - `x = {AAA:2, AAT:1, ATA:1}`; `d_S = {AAA:1, AAT:1, ATA:1, TAA:1}`;
    `d_D = {AAA:2, AAT:1, ATA:1, TAA:1}` for `D = AAAAT`.
  - Both satisfy containment + density (max gap `2 = L − o_min`) and the
    per-type bound; the truth has the unobserved window `TAA`, so support
    equality *fails*.
  - Binomial ratio `16/9 > 1`; candidate-intrinsic-length exact ratio
    `1024/625 > 1`.
  [verified computation, bounded search context in the note body below]

The witness (C) is the mechanism in miniature: with external `N = 4`, the
observed count `x(AAA) = 2` is compatible with the truth having only one `AAA`
copy (per-type lower bound `1`), so lengthening the molecule to `AAAAT` to give
`AAA` two copies strictly increases the §6.1 objective. The tracked
support-equality criterion rejects the truth (`TAA` unobserved) and the
per-occurrence criterion rejects it (`d_S(AAA)=1 < x(AAA)=2`); the
source-faithful criterion accepts both truth and competitor.

Bounded search context (same script family, a `/tmp` exploration, not part of
the committed script): a binary `G = 4`, `L = 3`, `o_min = 1` scan enumerated
all truths, all `I_s`-valid start multisets, and all binary candidates up to
length `|D| = G + 2`, and found `840` molecule-convention containment-only
candidates (truth or competitor not support-equal) with whole-molecule
feasibility and binomial ratio `> 1`; witness (C) is one of the smallest. This
is **bounded evidence**, not a completeness proof.

---

## 5. Frontier impact

| Item | Tracked model | Source-faithful reading | Effect |
|---|---|---|---|
| Spelling criterion | support equality | containment + `(L−o_min)`-density | feasible set strictly grows for `o_min < L−1` |
| Lower bound | per-occurrence `d_w ≥ x_w` | per-type `d_w ≥ 1` | feasible set grows; per-occurrence witnesses remain valid |
| Kernel witness `AAATT→AAAATT` (`9/8`) | valid | **valid** (all windows allowed) | negative conclusion robust |
| Tracked bounded searches | support equality / `o_min = L−1` | not exhaustive | completeness claims do not transfer |
| New frontier witnesses | excluded | e.g. `AAAT→AAAAT` (`16/9`) | new negative instances available |

**What survives:** the §6.2 negative conclusion — `I_s` does not force
truth-ML-optimality under the molecule reading — is confirmed under the
source-faithful conventions; the kernel-checked witness is a valid instance of
the broader statement. **What changes:** the tracked feasible set is a strict
sub-frontier; searches scoped by support equality or `o_min = L − 1` are not
exhaustive, and the source-faithful frontier contains additional witnesses such
as (C).

---

## 6. Unresolved register

1. **Referent.** Which Medvedev–Brudno object the 2016 sentence denotes remains
   a recorded source ambiguity, unaffected by this audit. [open]
2. **Duplicate-read convention.** MB09 does not state how duplicate samples are
   represented; per-type vs per-occurrence is a genuine source gap, not a fact.
3. **`o_min`.** The source leaves it free; a sequence-level theorem must name it
   or quantify over it. [open]
4. **Unobserved-type factors.** Whether the intended objective penalises
   unobserved windows (as §6.1 does) or drops them (as §6.2's read-only vertex
   set does) is unresolved. [source gap]
5. **Non-contiguous flows.** The sequence-level question restricts to circuits;
   whether the published question also ranges over multi-contig flows is not
   settled here. [open]

---

## 7. Citations

- Paul Medvedev, Michael Brudno, "Maximum Likelihood Genome Assembly,"
  *J. Comput. Biol.* 16(8) (2009) 1101–1116, DOI `10.1089/cmb.2009.0047`,
  PMCID `PMC3154397`: §1.1 (Fig. 1), §3.1, §3.2, §3.3, §3.4, §4.1, §6.1,
  §6.2, §7, §8.2.
- Paul Medvedev, *Genome Graphs*, PhD thesis, University of Toronto, 2010,
  Ch. 4 §4.4 (Observation 9; the supersink → supersource return edge).
- Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
  "Information-optimal genome assembly via sparse read-overlap graphs,"
  *Bioinformatics* 32(17) (2016) i494–i502, DOI `10.1093/bioinformatics/btw450`.
- Repository: `docs/bridging-se62-flow-ml-counterexample.md` and
  `AssemblyP1/Section62BridgingCounterexample.lean`
  (branch `analysis/bridging-se62-ml-lean-0920`).
