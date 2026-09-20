# Independent reconstruction of Medvedev–Brudno §6.2 and source-fidelity audit of the repository's §6.2 model/search code

_Status: independent primary-source reading + reconstruction + line-by-line code
audit, 2026-09-20. All claims are labelled **source fact**, **source
ambiguity**, **mathematical fact**, **verified by reading**, or
**interpretation**. This note does not settle the source-ambiguous Shomorony et
al. (2016) open question, and it does not choose a referent for the phrase "the
maximum-likelihood formulation of the AP (Medvedev and Brudno, 2009)"._

_Scope. The audit compares the reconstructed §6.2 object against the repository
artifacts that claim to model or search it. Those artifacts live on **unmerged
branches**; `main` contains none of them. Branch artifacts are cited as
`<branch>:<path>` and were read at a pinned commit (hashes in §8), because
branch tips move. Two artifacts observed in the shared working tree
(`docs/bridging-se62-flow-ml-counterexample.md`,
`scripts/verify_se62_bridging_flow_counterexample.py`) were **untracked** at the
time of writing and are treated separately in §5.8._

---

## 0. Verdict at a glance

1. **The reconstructed source object.** §6.2 optimizes an integer **min-cost
   convex bidirected flow (biflow)** on the **transitively reduced bidirected
   read-overlap graph**. Vertices are **reads as DNA molecules** (unordered
   reverse-complement strand pairs); edges are **bidirected overlaps of length at
   least `o_min`**; every read vertex has lower bound `1`, all other bounds are
   `0`, all upper bounds are `∞`; a **supersource/supersink** converts the flow to
   a circulation with **prohibitively large costs** on the source/sink edges; and
   the **vertex flow `d_i`** (the flow on the split edge `v⁻→v⁺`) is the §6.1
   copy count. The solver returns an **edge flow plus the induced
   vertex-throughput vector**, not a genome. [source fact; §1–§3]

2. **The repository does not currently contain a source-faithful §6.2 model.**
   No artifact — `main` or branch — builds the **bidirected** graph with
   endpoint orientation incidence, applies the **transitive reduction**, models
   the **supersource/supersink**, or represents `d_i` as a vertex flow of that
   graph. Every Python artifact uses **directed suffix–prefix overlaps** on
   strings or reverse-complement quotient classes. [verified by reading; §5]

3. **`o_min` is the load-bearing hidden parameter.** The source's own error-free
   experiments use reads of length `25` and vary `o_min` from `17` to `21`
   (`L−1 = 24`). Therefore the source regime is `o_min < L−1`, in which a spelled
   molecule may contain length-`L` windows that are **not** observed reads. The
   criterion "sequence-level §6.2 feasible ⇔ support equality" is exact only for
   the special value `o_min = L−1`, and most repository artifacts silently assume
   it. [source fact (L, o_min); mathematical fact (criterion); §4, §5.1]

4. **Defects are of four kinds**, not one: (a) criteria stated without their
   `o_min`/strand scope; (b) labels that overstate a directed forward-walk check
   as a bidirected-flow check; (c) unmodeled source features (transitive
   reduction, supersource/sink penalty, endpoint orientation); and (d) conflation
   of the §6.1 *exact multinomial*, the §6.1 *separable binomial approximation*,
   and the §6.2 *observed-vertex-only* objective. [verified by reading; §5]

5. **Positive/counterexample deliverables survive, but with narrower scope than
   their prose suggests.** Read-tiled circuits and spelled molecules are valid
   §6.2 circuits a fortiori (a directed circuit is a bidirected circuit), so the
   *counterexample* notes remain valid for their stated sub-case. The
   *zero-counterexample* searches are only exhaustive for the `o_min = L−1` and
   directed/single-strand scopes they actually enumerate. [mathematical fact;
   §5.9, §6]

---

## 1. Primary source facts

Primary source: Paul Medvedev, Michael Brudno, "Maximum Likelihood Genome
Assembly," *J. Comput. Biol.* 16(8) (2009) 1101–1116,
DOI [10.1089/cmb.2009.0047](https://doi.org/10.1089/cmb.2009.0047),
[PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/). Quotations below
were read from that PMC record on 2026-09-20.

### 1.1 §6.2, verbatim

> "We are now ready to describe our algorithm for predicting copy counts. The
> first step is to build a bidirected overlap graph from the set of reads, which
> are DNA molecules. **The vertices of this graph are the reads**, and the edges
> are all possible bidirected overlaps of length at least `o_min`, where `o_min`
> is a parameter to our algorithm. We then perform **transitive edge reduction**,
> where we remove any overlap that is spelled by two shorter overlaps. This
> procedure is identical to the one described in Myers (2005), and we refer to
> the resulting graph as the **transitively reduced bidirected overlap graph**.
> While the set of possible DNA molecules spelled by the graph remains unchanged,
> the reduction drastically reduces the number of edges. Moreover, we have the
> following observation:"

> **Observation 7.** "Let `r` be a read and `W` a walk in the transitively
> reduced bidirected overlap graph. The number of times `W` visits `r` is equal
> to the number of times `r` appears a submolecule of the molecule spelled by
> `W`."

> "In this graph, the original double-stranded genome corresponds to a circuit
> (assuming high enough coverage). We make a final change to the graph by adding
> a **supersource and supersink** to the graph. This is a standard modification
> that will allow us to convert a flow to a **circulation** problem (Ahuja et
> al., 1993). Next, we define a convex min-cost biflow problem on this graph,
> with bounds and costs on both the edges and the vertices. **Each vertex has a
> lower bound of 1** since it represents a read that must be present in the
> genome at least once. **All other lower bounds are 0 and all upper bounds are
> infinity.** We add **prohibitively large costs** to the edges from/to the
> supersource/sink so that their usage is minimized. By Observation 7, the `d_i`'s
> described above actually correspond to **the value of the flow through vertex
> `i`**, and we let `c_i` be the convex cost functions for the vertices."

> "We finally solve the biflow problem by first applying the reductions of
> Section 5.2 and then using the efficient algorithm of Section 5.1. Since any
> flow can be decomposed into a collection of walks, our flow represents a
> **(non-contiguous) assembly** of the genome, and the flow going through each
> vertex represents the number of time the read is present in the assembly."

### 1.2 Supporting definitions (source facts)

- **Molecule (§3.1).** "A DNA molecule is an unordered pair of strings (also
  called strands) that are reverse complements of each other."
- **Bidirected overlap (§3.3).** An edge between molecules `x,y` is positive- or
  negative-incident at each endpoint, and is a bidirected overlap when one of
  four orientation cases holds (pos/neg, pos/pos, neg/neg, neg/pos) matching the
  strands that overlap. The length of the overlap is the underlying string
  overlap length.
- **Bidirected balance (§3.4).** A flow satisfies `l(e) ≤ f(e) ≤ u(e)` and, at
  each vertex `v`, "the flow along the positive-incident edges minus the flow
  along the negative-incident edges is equal to `b(v)`." The incidence value is
  `±1` at a link and `±2` or `0` at a loop.
- **Vertex split (§5.2).** To put bounds/costs on a vertex, split `v` into
  `v⁺, v⁻`; reconnect in-edges to `v⁻` and out-edges to `v⁺`; add edge `v⁻→v⁺`;
  put the vertex bounds/costs on that edge.
- **§6.1 objective.** Exact global read-count likelihood is the **multinomial**
  with `p_i = d_i/N(D)` and the constraint `N(D) = Σ_i d_i`; because that is not
  separable, the paper replaces it by the product of per-type **binomial**
  marginals with an **external** fixed `N` (the true genome length) and assumes
  the genome size is known. The separable cost is
  `c_i(d_i) = −x_i log d_i − (n − x_i) log(N − d_i)`, real for `0 ≤ d_i ≤ N`.
- **Solver character.** §5.1's implementation reduces bidirected flow to
  directed flow by monotonization; the paper states the resulting algorithm is a
  **2-approximation in the worst case** with **half-integral** optima in general,
  and reports that it found the optimum on almost all instances.
- **`o_min` and read length (§8.2).** "The reads generated were always of length
  25 … The minimum overlap length (`omin`) was varied from 17 to 21." Hence
  `o_min < L−1 = 24` in the paper's own experiments. [source fact; independently
  read]

### 1.3 Source ambiguities (must be named by any theorem)

- **Vertex multiplicity.** "The vertices of this graph are the reads" (a
  multiset input) versus the per-vertex lower bound "1 … must be present at
  least once." If duplicate reads collapse to one vertex, the bound is once per
  **distinct molecule** (per-type); if each read copy is a vertex, it is once per
  **copy** (per-occurrence). The source does not say. `d_i` denotes the same
  quantity in both readings; only the lower-bound set differs.
- **Transitive-reduction algorithm.** "Identical to Myers (2005)" is named but
  not specified; on bidirected/string graphs different reductions are possible
  and they change the flow polytope (not the set of spelled molecules).
- **Unobserved length-`L` windows.** For `o_min < L−1` a spelled molecule can
  contain windows that are not read vertices. §6.2 gives them no vertex, so they
  contribute no likelihood factor, unlike the §6.1 product over all `4^k` types.
  Whether the intended objective should penalize them has no source resolution.
- **Tie/equivalence and contiguity.** The returned object is a flow; recovering a
  sequence needs the §7 heuristic (large-contig decomposition), which is not a
  likelihood.

---

## 2. The reconstructed §6.2 optimization

Let `R` be the observed reads (DNA molecules), `L` the read length, `o_min` a
fixed overlap threshold, `x_w` the observed count of read/molecule type `w`,
`n = Σ_w x_w`, and `N` the externally supplied genome length.

1. **Vertex set (`V`).** Read molecule types present in `R` (per-type reading) or
   read copies (per-occurrence reading), under the chosen reading of §1.3. Each
   vertex is an unordered reverse-complement pair. [source fact + ambiguity]
2. **Edge set (`E`).** One bidirected edge per pair of overlapping reads, with an
   independent orientation at each endpoint, of overlap length `≥ o_min`, per
   §3.3. Multi-edges are allowed (§3.2). [source fact]
3. **Transitive reduction.** Delete overlaps "spelled by two shorter overlaps,"
   per Myers (2005); the spelled-molecule set is unchanged, Observation 7 holds
   on the result. [source fact; convention ambiguity]
4. **Bounds.** `l(v) = 1` for every read vertex, `l ≡ 0` on edges and on
   non-read vertices, `u ≡ ∞`. [source fact]
5. **Balance and supersource/sink.** A flow satisfies the signed-incidence
   balance `pos(f)(v) − neg(f)(v) = b(v)`. Adding a supersource/supersink makes
   the read-vertex balances zero (a circulation) while allowing the assembly to
   be a collection of open walks; the source/sink edges carry a prohibitively
   large cost, so their total use (equivalently, the number of contigs) is
   minimized as a secondary criterion. [source fact]
6. **Vertex split and `d_i`.** Via §5.2, `d_i` is the flow on `v⁻→v⁺`; by
   Observation 7 it equals the number of times read vertex `i` is visited by the
   flow, i.e. the number of times the read occurs in the (possibly
   non-contiguous) assembly. [source fact]
7. **Objective.** Minimize `Σ_i c_i(d_i) + (large)·(#source/sink edges used)` with
   `c_i(d) = −x_i log d − (n − x_i) log(N − d)`, `0 ≤ d ≤ N`. There is **no**
   constraint `Σ_i d_i = N`; `N` is only the binomial denominator and the domain
   bound. The exact multinomial identity `N(D) = Σ_i d_i` belongs to §6.1 and is
   discarded by the approximation. [source fact + mathematical fact]
8. **Solution object.** An integral (in the source's experiments) edge-flow
   assignment, plus the induced vertex-flow vector `d` over observed read
   vertices. Not a string. The §7 decomposition into contigs is heuristic and
   outside the optimization. [source fact]

---

## 3. What the optimizer returns (explicitly)

The optimizer returns a **flow**:

- an edge function `f : E → ℤ≥0` with the edge/vertex bounds and signed-incidence
  balance above (after adding the supersource/sink and vertex-splitting
  reductions); and
- the **induced vertex-copy-count vector** `d` (one coordinate per read vertex),
  which is the object the §6.1 cost is evaluated on.

It does **not** return a circular genome. A single circuit is a special case (the
true genome, given coverage); generally the flow decomposes into a collection of
walks, and §7 selects a decomposition by a separate heuristic. [source fact]

---

## 4. The corrected sequence-level criterion

Fix `k = L` (so the flow through a read vertex matches the §6.1 `k`-molecule
count via Observation 7). For a circular molecule `D`, call position `p`
**allowed** if its length-`L` window is an observed read molecule.

**Criterion (single strand).** `D` is spelled by a closed walk in the
transitively reduced read-overlap graph with minimum overlap `o_min` iff

1. every observed read type occurs as a window of `D`
   (`supp(x) ⊆ supp(spec_L(D))`); and
2. the allowed positions are cyclically **`(L − o_min)`-dense**: every cyclic gap
   between consecutive allowed positions is at most `L − o_min`.

_Proof sketch._ Place a read at each allowed position; consecutive reads overlap
by `L − gap ≥ o_min` and agree, and the placements cover `D`, giving a walk that
spells `D`. Conversely a closed walk's visits are exactly read occurrences
(Observation 7), so (1) holds, and consecutive visited positions are `o_min`-
overlapped, so gaps are `≤ L − o_min`. ∎ [mathematical fact]

For `o_min = L−1`, (2) forces every position allowed, so the criterion collapses
to **support equality** `supp(spec_L(D)) = supp(x)`. For the source's regime
`o_min < L−1`, support containment (not equality) is correct and unobserved
windows are permitted. The criterion lifts to the double-stranded reading by
comparing molecule classes. [mathematical fact]

---

## 5. Line-by-line fidelity comparison

Legend for severity: **F** = false as stated (or overclaimed scope), **L** =
mislabel/imprecision, **M** = source feature unmodeled, **S** = scope limitation
(honestly labelled or not).

### 5.1 `scripts/verify_flow_feasible_counterexample.py` (working tree, untracked)

- Builds no overlap graph, no transitive reduction, no `o_min` (only cyclic
  `L`-windows). **M, S**
- Single-strand strings; no molecule classes, no bidirected incidence. **M**
- Derives `d_D = x` by read-tiling and calls it "flow-feasible" (lines 19–20,
  134); the cyclic-window check uses `L−1` overlaps (line 138). **L, M**
- Check (6) treats the truth's unobserved windows `BCB,CBC` as proof the truth is
  not flow-feasible (lines 145–146). This is the `o_min = L−1` support-equality
  criterion; at `o_min < L−1` the correct test is containment plus
  `(L−o_min)`-density. (For this particular truth the conclusion survives, but
  the stated reason is not source-faithful.) **F (reason), S (scope)**
- Likelihood ratio (lines 150–156) is the **fixed-length exact multinomial**, not
  the §6.1 binomial that §6.2 optimizes. **L**

### 5.2 `scripts/support_feasibility_search.py` (working tree, untracked)

- No graph/reduction/`o_min`; candidates are single circular molecules. **M, S**
- Docstring lines 13–15 call the per-occurrence class `d_D(w) ≥ x_w` "the
  lower-bound-one-per-read-vertex reading of Medvedev–Brudno section 6.2." The
  source lower bound is `1` per vertex; `d_w ≥ x_w` is the **per-occurrence**
  reading, a different set. **F (label)**
- Labels support-containment as "a necessary condition for D to be spelled by a
  closed walk" (lines 9–13). Not necessary for `o_min < L−1`. **F**
- Objective ratio (lines 209–223) is fixed-length exact multinomial. **L**

### 5.3 `scripts/verify_issue36_conservation_lemma.py` (branch `analysis/issue36-conservation-lemma-0920`)

- Handles single-strand (`comp=None`) and revcomp molecule classes (`mol`,
  lines 79–84); good on strand identity, but no bidirected incidence. **M**
- Models a circulation as a repeated closed walk (lines 233–243); no
  supersource/sink and no open paths. **M (partial)**
- `[A]` docstring (lines 20–22) claims separability "extends … to the whole
  section 6.2 bidirected-flow class"; the per-coordinate bound is valid over any
  box, but the claim ignores the source/sink penalty and the bidirected graph.
  **L**
- `[B]` "actual section 6.2 flow" examples are **directed** single-strand overlap
  graphs (lines 246–308). The conclusion that `Σ d_w = N` is not a flow
  constraint is correct; the certificates are not double-stranded §6.2 flows.
  **L**
- Arithmetic cores (`[A]`, `[D]`) are correct. **—**

### 5.4 `AssemblyP1/Model.lean`, `AssemblyP1/OpenProblem.lean` (main)

- No §6.2 content: `AssemblyModel` is explicitly "not yet the … Medvedev–Brudno
  model." `genomeEquiv` mentions cyclic shift only, not reverse complement.
  Honest scaffolding, but any theorem instantiated here has no §6.2 flow layer.
  **M (acknowledged)**

### 5.5 `scripts/se62_actual_flow_search.py` / `..._certificate.py` (branch `se62-actual-flow-feasibility`)

- `build_graph` builds a raw **directed** overlap graph on `V = supp(x)`;
  `o_min = L−1` hard-coded (search call, line 175); no transitive reduction
  (argued vacuous at `o_min = L−1`); no bidirected graph. **M, S**
- Search says "single-strand reading for a clean directed flow graph" (line 7);
  no orientation. **M**
- Inconsistency: candidate lower bounds are per-type `1 ≤ d_v` (ranges, line 156)
  but the truth filter requires `spec[w] ≥ x_w` (per-occurrence, line 187), while
  the docstring/companion doc call the truth "per-type feasible." **L**
- Flow feasibility enforces `in = out = d_v` (circulation); no source/sink, no
  open paths. **M (partial)**
- `walk_certificate` uses the canonical **forward** suffix–prefix overlap only
  (line 170 ff.); it does not track the four §3.3 orientation cases. The title
  "actual §6.2 bidirected-flow certificate" overstates. **L**
- Dead code `if u != v or True:` (line 132). **—**
- The optimality argument (separable coordinate maximum + realizability) is
  correct and the ratios reproduce. **—**

### 5.6 `se62_bidirected_feasibility_search.py`, `se62_fixed_length_bidirected_search.py`, `se62_feasible_set_membership.py` (branches)

- All three use the **support-equality** sequence criterion with no `o_min`
  (`o_min = L−1` hidden) and single molecules, not flows. **F (scope), M**
- `se62_feasible_set_membership.py`'s `obs7_ok` requires the induced visited
  windows to equal the full spectrum; its docstring claims a walk overlapping by
  less than `L−1` "violates Observation 7." Observation 7 does **not** require
  every spelled window to be a visited read; that is exactly what `o_min < L−1`
  permits. Consequently its assertion that `AAAAC` is not sequence-level
  feasible is wrong under the source's parameter regime (the
  `se62-independent-reconstruction` branch demonstrates `o_min=1` feasibility).
  **F**
- `walk_is_bidirected_circuit` (fixed-length search) checks only forward
  consecutive `L−1` overlaps; no orientation. **L**
- Fixed-length per-type witness `AAATAT → AAAAAT` is a genuine directed forward
  circuit, hence a fortiori a §6.2 circuit; the conclusion is valid, the
  "bidirected" label is not. **L**

### 5.7 `AssemblyP1/Section62FlowObstruction.lean`; `docs/section-6-2-feasible-set-membership.md`; `docs/section62-bidirected-flow-feasibility.md`

- `Section62Feasible := WindowSupported ∧ LowerBounded` (lines 67–84) and the
  doc-comment "are exactly the sequence-level §6.2 feasible set" (lines 29–30)
  are valid only for `o_min = L−1`. The kernel-checked finite facts about
  `AAABCBC`/`AAAAABC` are true for this predicate; the predicate under-covers the
  source's feasible set. **F (scope)**
- `docs/section62-bidirected-flow-feasibility.md` §7 item 2 "the obstruction …
  is support-theoretic and therefore independent of `o_min`" is false on the
  competitor side: the `#31`/`#32` competitors become spellable at `o_min ≤ 1`.
  **F**
- These docs correctly state that §6.2 candidates are flows, that `d_i` is the
  vertex flow, and that the output may be non-contiguous. **—**

### 5.8 Untracked working-tree artifact `docs/bridging-se62-flow-ml-counterexample.md` + companion script (not on any branch at audit time)

- Good source-object separation in the note (§1–§2), and the `AAATT → AAAATT`
  computation (`9/8`) is exact and correct for its stated sub-case.
- But `feasible(...)` (script lines 170–172) is again **support equality** plus
  per-occurrence lower bounds — the `o_min = L−1` criterion. For this instance
  all windows are observed, so the witness is robust; the *statement* the note
  refutes is nonetheless narrower than the full §6.2 feasible set. **S**
- The note's §3.3 claims "the full literal §6.1 ratio (zero-count factors
  retained)", but `binom_product` (lines 187–192) iterates only over observed
  types and **omits** the unobserved factors. Both candidates here have
  `supp = supp(x)`, so the omitted factors are `1` and the ratio is unaffected;
  the phrasing is imprecise. **L**
- `binom_product` is the §6.1 **binomial approximation**, not the exact
  multinomial; the note elsewhere says so, but the phrase "literal §6.1" can be
  read as the exact objective. **L**
- The witness is a spelled molecule (a circuit), so it does not test the
  genuinely non-spellable flow class; that is acknowledged. **S**

### 5.9 `scripts/se62_nonspellable_flow_search.py`, `docs/section62-nonspellable-flow-counterexample.md` (branch `issue36-nonspellable-flow`)

- Builds a raw **directed** overlap graph and an ad hoc "junction-containment"
  string reduction; `o_min` is parameterized (good), but the graph is not
  bidirected and orientation is not tracked. The note candidly states "the
  bidirected orientation flips are not modelled here" (§5 item 3). **M
  (acknowledged)**
- Flows are integer **circulations** (cycle cone); no supersource/sink or open
  paths, as the note states. **M (acknowledged)**
- Best hygiene in the set: it explicitly refuses to call its full-graph
  `o_min=1` witness a source counterexample because the winning edge is
  transitively reducible, and it labels the "string graph" reduction as one of
  several possible readings of the source's reduction. **—**

### 5.10 `scripts/se62_spelling_feasibility.py`, `docs/section62-feasibility-independent-reconstruction.md` (branch `se62-independent-reconstruction`)

- The **only** artifact that implements the corrected `o_min`-parameterized
  criterion (containment + `(L−o_min)`-density). Single-strand; the
  reverse-complement lift is stated but not implemented; single molecules only.
  **S (acknowledged)**
- Correctly refutes the tracked support-equality criterion and demonstrates
  `o_min=1` feasibility of the `#31`/`#32` competitors. **—**
- This branch's criterion is the one that should be adopted as the canonical
  sequence-level definition (with the strand lift added).

---

## 6. Consequences for the current research frontier

1. **Counterexamples remain valid but are sub-case statements.** A spelled
   molecule's cyclic window walk is a valid bidirected walk (a directed circuit
   is a bidirected circuit), so the fixed-length and per-type/per-occurrence
   sequence-level witnesses stand. They refute statements quantified over
   spelled molecules, not over the full non-contiguous §6.2 flow polytope with
   source/sink penalty. [mathematical fact]
2. **Zero-counterexample claims need their scope restated** in terms of `o_min`,
   strand reading, candidate class (molecule vs flow), and read count `n`.
   Several current zeros are `o_min = L−1` / `n = G` / single-strand artifacts.
   [verified by reading]
3. **The genuinely open §6.2 question** — whether a *non-spellable* flow can beat
   a truth-feasible bridged genome on the **transitively reduced bidirected**
   graph — is not settled by any of the above. The `issue36-nonspellable-flow`
   branch's bounded single-strand string-graph zero is the closest evidence, and
   it is bounded. [source/model]
4. **`main` has no §6.2 model**, and the branch artifacts contradict each other
   on the feasible-set criterion. Reconciliation should pick the corrected
   `o_min`-parameterized criterion (§5.10) and record the per-type/per-occurrence
   and strand readings explicitly.

---

## 7. Recommended canonical definitions (for a future Lean statement)

```text
ReadMolecule      := unordered reverse-complement pair of strings
BidirectedGraph   := vertices = read molecules; edges carry (pos|neg) incidence
                     at each endpoint; edge exists iff overlap length >= o_min
TransitiveReduce  := remove an overlap spelled by two shorter overlaps
                     (algorithm to be fixed from Myers 2005 and documented)
VertexBound       := l(read vertex) = 1; l(edge) = 0; u = infinity
Flow              := f with signed-incidence balance pos(f) - neg(f) = b
VertexFlow d_i    := flow on split edge v- -> v+   (Observation 7)
Objective         := sum_i c_i(d_i) + M * (#source/sink edges),  M >> 0
                     c_i(d) = -x_i log d - (n - x_i) log(N - d),  0 <= d <= N
Returns           := edge flow + vertex-throughput vector d (NOT a genome)
```

Every future §6.2 theorem should name: the vertex-multiplicity reading
(per-type vs per-occurrence), `o_min`, the transitive-reduction algorithm, the
strand reading, and whether candidates are flows or spelled molecules.

---

## 8. Method, reproduction, and pinned artifacts

- Primary source retrieved from
  [PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/) on 2026-09-20;
  §6.2 and §8.2 read directly. The `o_min = 17..21`, `L = 25` fact is in the
  §8.2 experimental-setup paragraph ("The reads generated were always of length
  25 … The minimum overlap length (`omin`) was varied from 17 to 21.").
- Branch artifacts read at pinned commits:

  | branch | commit | relevant files |
  |---|---|---|
  | `analysis/issue36-conservation-lemma-0920` | `03a695e` | `scripts/verify_issue36_conservation_lemma.py`; `docs/section62-conditional-conservation-lemma.md` |
  | `analysis/se62-actual-flow-feasibility` | `618ebc1` | `scripts/se62_actual_flow_search.py`; `scripts/se62_actual_flow_certificate.py`; `scripts/se62_bidirected_feasibility_search.py`; `scripts/se62_fixed_length_bidirected_search.py`; `scripts/se62_feasible_set_membership.py`; `AssemblyP1/Section62FlowObstruction.lean`; `docs/section-6-2-feasible-set-membership.md`; `docs/section62-bidirected-flow-feasibility.md` |
  | `analysis/se62-independent-reconstruction` | `eb68458` | `scripts/se62_spelling_feasibility.py`; `docs/section62-feasibility-independent-reconstruction.md` |
  | `analysis/issue36-nonspellable-flow` | `e227eb3` | `scripts/se62_nonspellable_flow_search.py`; `docs/section62-nonspellable-flow-counterexample.md` |
  | `analysis/issue36-nonspellable-broader` | `6b22d48` | `scripts/se62_nonspellable_broader_search.py` |

- Untracked working-tree artifacts observed and audited in §5.8 (not durable as
  of this audit): `docs/bridging-se62-flow-ml-counterexample.md`,
  `scripts/verify_se62_bridging_flow_counterexample.py`.

---

## 9. Epistemic status

| Claim | Status | Basis |
|---|---|---|
| §6.2 graph, transitive reduction, supersource/sink, lower bound 1, `d_i` = vertex flow, non-contiguous output | **source fact** | MB09 §6.2, verbatim §1.1 |
| Molecule = unordered revcomp pair; bidirected overlap orientation cases | **source fact** | MB09 §3.1, §3.3 |
| Balance is signed incidence `pos − neg = b` | **source fact** | MB09 §3.4 |
| Vertex split realizes vertex bounds/costs on `v⁻→v⁺` | **source fact** | MB09 §5.2 |
| Objective = §6.1 separable binomial with external `N`; no `Σ d_i = N` | **source fact** | MB09 §6.1–6.2 |
| Solver is a 2-approximation via monotonization | **source fact** | MB09 §5.1 |
| Source experiments use `L = 25`, `o_min = 17..21` (`o_min < L−1`) | **source fact** | MB09 §8.2 |
| Sequence-level criterion = containment + `(L−o_min)`-density | **mathematical fact** | §4 proof sketch |
| Repository artifacts use directed suffix–prefix walks, not the bidirected graph | **verified by reading** | §5 |
| Support-equality criterion is the `o_min = L−1` case; used unlabelled by most artifacts | **verified by reading + mathematical fact** | §4, §5 |
| Per-type vs per-occurrence vertex reading | **source ambiguity** | §1.3 |
| Which MB09 object the 2016 sentence denotes | **open** | out of scope |

---

## 10. References

1. P. Medvedev and M. Brudno. "Maximum Likelihood Genome Assembly."
   *Journal of Computational Biology* 16(8):1101–1116, 2009.
   DOI [10.1089/cmb.2009.0047](https://doi.org/10.1089/cmb.2009.0047);
   full text [PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/).
2. E. W. Myers. "The fragment assembly string graph." *Bioinformatics*
   21(Suppl. 2):ii79–ii85, 2005.
3. I. Shomorony, S. H. Kim, T. A. Courtade, and D. N. C. Tse.
   "Information-optimal genome assembly via sparse read-overlap graphs."
   *Bioinformatics* 32(17):i494–i502, 2016.
   DOI [10.1093/bioinformatics/btw450](https://doi.org/10.1093/bioinformatics/btw450).
4. See [the open-problem note](open-problem.md) and
   [the MB candidate-class source note](source-notes/medvedev-brudno-candidate-class.md)
   for the repository's published-problem framing.

