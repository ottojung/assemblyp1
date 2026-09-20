# MB09 §6.2 primary definitions: independent audit for PR #39 (`AAATT → AAAATT`)

_Status: independent primary-source reading + independent graph reconstruction,
2026-09-20. Written from the Medvedev–Brudno (2009) text only; the concurrent
branch artifact `docs/section62-mb09-bidirected-graph-audit.md` and its script
were **not** used, so the agreement recorded in §5 is genuine cross-checking,
not a summary. All claims are labelled **source fact**, **source-internal
tension**, **modeling choice**, **mathematical argument**, **verified
computation**, or **open**._

_Reproduction:_ `python3 scripts/verify_se62_definitions_independent_audit.py`
(self-contained, exact `fractions.Fraction`, deterministic, exits non-zero on any
failed assertion). The script re-derives the 10-edge graph, both closed
bidirected walks, their vertex throughputs, the `9/8` ratio, the oriented
non-collapsed alternative, and the PR #39 prose-error discrepancy.

_Scope._ This note audits the *definitions* needed to judge PR #39 and checks
the `AAATT → AAAATT` witness against them. It does not settle which MB09 layer
the Shomorony et al. (2016) sentence denotes, nor the tie/maximizer question.

## 0. Source locators

Primary source: Paul Medvedev, Michael Brudno, “Maximum Likelihood Genome
Assembly,” *Journal of Computational Biology* **16**(8), 2009, pp. 1101–1116.
DOI [10.1089/cmb.2009.0047](https://doi.org/10.1089/cmb.2009.0047);
open full text [PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/).

The PMC HTML carries no page anchors for §6 (grep finds page digits only in the
1101–1103 and 1114–1116 ranges), so the precise section numbers and the
equation-image identifiers below locate the text; the print pages for §6.1–6.2
are within 1101–1116. The §6.1 display equations are the PMC images
`M26` … `M33`, in order:

| image | content | surrounding text (verbatim) |
|---|---|---|
| M26 | `d_i / N(D)` | “the probability that the outcome of a single trial is `i` is simply [M26]” |
| M27 | multinomial joint density | “their joint distribution is exactly the multinomial distribution, given by [M27]” |
| M28 | global read-count likelihood `L((d_i) \| (x_i))` | “which we call the global read-count likelihood: [M28]” |
| M29 | separable cost target `Σ_i c_i(d_i)` | “we need to find convex functions `c_i` such that [M29]” |
| M30 | multinomial constraint | “the multinomial distribution has the constraint that [M30]” |
| M31 | binomial-approximation `L` | “The resulting approximation for `L` is thus [M31]” |
| M32 | factor `K` | “Now we can write [M32], where `K` is some positive constant independent of all `d_i`” |
| M33 | convex cost `c_i` | “and [M33]” |

[source fact]

## 1. The §6.2 definitions, as stated

### 1.1 Vertex identity and reverse complements

§3.1 (source fact):

> “A **DNA molecule** is an unordered pair of strings (also called strands)
> that are reverse complements of each other. We say a molecule corresponds to
> each of its two constitutive strings, and vice-versa. … A **k-molecule** is a
> DNA molecule whose corresponding strings have length `k`. The
> **k-molecule-spectrum** of a DNA molecule is the set of all `k`-molecules that
> are its submolecules.”

§4.1 (source fact), for the bidirected de Bruijn graph: “each *k*-molecule is
represented only once.” §1.1: “Each read is represented by a single node.”

§6.2 (source fact): “The first step is to build a bidirected overlap graph from
the set of reads, which are DNA molecules. **The vertices of this graph are the
reads** …”

**Audit reading.** A read and its reverse complement are the *same* vertex,
because a read is a molecule and a molecule *is* its two revcomp strands.
Duplicated samples of one molecule collapse to one vertex. [source fact +
source-supported inference]

**Caveat (source-internal tension).** §6.1 says of the outcome variables: “There
are **4^k** such variables,” i.e. oriented `k`-mers, not revcomp classes. The
molecule vocabulary (classes) and the literal `4^k` count are inconsistent;
this is recorded in `docs/source-notes/medvedev-brudno-candidate-class.md` and
`docs/source-notes/reverse-complement-strand-convention.md` (branch artifact).
The tension is load-bearing for PR #39 — see §4.1. [source fact]

### 1.2 Transitively reduced overlap graph

§6.2 (source fact): edges are “all possible bidirected overlaps of length at
least `o_min`,” followed by “transitive edge reduction, where we remove any
overlap that is spelled by two shorter overlaps … we refer to the resulting
graph as the **transitively reduced bidirected overlap graph**.” The paper
states “the set of possible DNA molecules spelled by the graph remains
unchanged.” [source fact]

### 1.3 Bidirected edge semantics

§3.2 (source fact): each edge carries an independent positive/negative incidence
at each endpoint; the incidence matrix is `I_G : V × E → {−2,−1,0,1,2}`, with a
loop having value `±2` when twice incident with one sign. The balance is
`b(v) = in-degree − out-degree`. A walk requires that at every interior vertex
the two incident edges “have opposite orientations”; a walk is *cyclical* when
its endpoints coincide and the first and last edges have opposite orientations
there.

§3.3 (source fact): a bidirected edge between molecules `x, y` is an overlap iff
one of four strand-overlap cases holds (`p(x)` vs `p(y)`, `p(x)` vs `n(y)`,
`n(x)` vs `p(y)`, `n(x)` vs `n(y)`), each fixing the two endpoint incidences; the
overlap length is the underlying string-overlap length.

**Audit reading.** A step of a walk may flip strand orientation at a vertex; the
strand read at a visit is determined by the incidence of the entering edge
(§4.1: “if we enter a node on a positive-incident edge we read the negative
k-mer, if on the negative incident we read the positive k-mer”). [source fact]

### 1.4 Vertex and edge lower bounds

§6.2 (source fact, verbatim): “Each vertex has a lower bound of 1 since it
represents a read that must be present in the genome at least once. **All other
lower bounds are 0 and all upper bounds are infinity.**”

**Audit reading.** The lower bound is **1 per distinct read vertex** (per
molecule), *not* the observed sampling multiplicity `x_w`. There is no source
basis for `d_w ≥ x_w` in §6.2. An observed read sampled `x_w > 1` times still
contributes one vertex with lower bound `1`. [source fact]

**Caveat (source-internal tension).** §6.2 sets *all upper bounds to infinity*,
but the §6.1 binomial marginal `(d_i/N)^{x_i}(1 − d_i/N)^{n−x_i}` is defined as a
probability only for `d_i ≤ N` (and the log-cost `c_i` is finite only for
`d_i < N` when `n > x_i`). The “domain bound `d_i ≤ N`” asserted by PR #39 is a
consequence of the objective, not of the §6.2 graph bounds. [source-internal
tension; relevant only if a witness has some `d_i > N`]

### 1.5 Flow conservation

§3.4 (source fact): a flow satisfies `l(e) ≤ f(e) ≤ u(e)` and, at every vertex,
`pos(f)(v) − neg(f)(v) = b(v)`.

§6.2 (source fact): supersource/supersink are added “to convert a flow to a
circulation problem,” with “prohibitively large costs to the edges from/to the
supersource/sink so that their usage is minimized.” §5.2 (source fact): a vertex
is split `v⁻ → v⁺`, and “any lower/upper bounds, as well as any costs,
associated with `v`” are placed on the split edge, so vertex throughputs and
vertex costs are flow variables.

**Audit reading.** Admissibility is an integral bidirected flow with the stated
bounds/balance plus (optionally) supersource/sink usage priced. A closed walk is
the special case with `b(v) = 0` everywhere and no source/sink usage. [source
fact]

### 1.6 Copy-count `d_i` extraction

§6.1 (source fact): “Let `D` be a circular genome of length `N(D)`, and let
`d_i` denote the number of times the `k`-molecule `i` appears in `D`.” §6.2
(source fact): “By **Observation 7**, the `d_i`’s described above actually
correspond to the value of the flow through vertex `i`, and we let `c_i` be the
convex cost functions for the vertices.”

Observation 7 (source fact): “Let `r` be a read and `W` a walk in the
transitively reduced bidirected overlap graph. The number of times `W` visits
`r` is equal to the number of times `r` appears a submolecule of the molecule
spelled by `W`.”

**Audit reading.** For a spelled molecule, `d_i` is the number of occurrences of
read molecule `i` as a submolecule; it is intrinsic to the molecule and equals
the vertex throughput of any spelling walk. [source fact]

**Caveat (notational slide).** §6.1 indexes `i` by `k`-molecules (its literal
`4^k` variables); §6.2 indexes `i` by read vertices (whole reads). Identifying
the §6.1 copy count with the §6.2 vertex flow requires the read molecule to *be*
the `k`-molecule, i.e. `k =` read length. The paper does not state this. For
PR #39 (`L = 3`, binary alphabet) the two spaces happen to coincide at `k = 3`.
[source-internal tension]

### 1.7 What plays the role of “a sequence”

§6.2 (source fact): “Since any flow can be decomposed into a collection of
walks, our flow represents a **non-contiguous** assembly of the genome, and the
flow going through each vertex represents the number of time the read is present
in the assembly.” §6.2 also states the double-stranded genome “corresponds to a
circuit (assuming high enough coverage).”

**Audit reading.** The §6.2 primitive candidate is a *flow*, not a sequence; a
single sequence is a closed walk/circuit spelling a molecule (a special flow).
So “the maximum-likelihood sequence” of the 2016 question is not literally the
§6.2 object; a counterexample may legitimately use a single spelled molecule
(stronger than using a non-contiguous flow), but a proof about the flow optimum
is not automatically a statement about sequences. [source fact + modeling
choice]

## 2. Independent reconstruction of the graph for `{AAA, AAT, TAA}`

Alphabet `{A,T}` (`A = 0`, `T = 1`), involution `A ↔ T`, read length `L = 3`,
`o_min = 2 = L−1`. The three observed read molecules and their strands:

| molecule | positive `p` | negative `n` |
|---|---|---|
| `AAA` | `AAA` | `TTT` |
| `AAT` | `AAT` | `ATT` |
| `TAA` | `TAA` | `TTA` |

Enumerating the four §3.3 strand cases over proper overlaps of length
`[o_min, L) = {2}` gives exactly **10 bidirected edges** (all length 2):
`AAA→AAA` (p/p and n/n), `AAA→AAT` (p/p), `AAA→TAA` (n/n), `AAT→AAA` (n/n),
`AAT→AAT` (p/n, twice-positive loop), `AAT→TAA` (n/n), `TAA→AAA` (p/p),
`TAA→AAT` (p/p), `TAA→TAA` (n/p, twice-negative loop). This is independently the
same 10-edge graph as the concurrent branch artifact. [verified computation]

At `o_min = 1` the graph has additional length-1 overlaps; none is used below,
and MB09 states the transitive reduction preserves the set of spelled molecules,
so the witness is unaffected by the `o_min ∈ {1,2}` choice. [source fact +
verified computation]

### 2.1 The two closed bidirected walks

Both candidates are spelled by cyclic length-3 window walks. Writing visits as
molecule@strand:

- truth `S = AAATT` (`G = 5`): visits `AAA@p, AAT@p, AAT@n, TAA@n, TAA@p`;
- competitor `D = AAAATT` (`G = 6`): visits `AAA@p, AAA@p, AAT@p, AAT@n, TAA@n,
  TAA@p`.

For each candidate the script confirms: every consecutive pair is a real graph
edge (suffix/prefix overlap `L−1 = 2`); at every interior visit the arriving
incidence is the negation of the departing incidence (MB09 §3.2); the walk is
closed; every read vertex has throughput `≥ 1`; the signed-incidence balance is
`0` at every read vertex; and no supersource/supersink edge is used. By
Observation 7 the throughputs are

```text
d_S = {AAA:1, AAT:2, TAA:2},   d_D = {AAA:2, AAT:2, TAA:2}.
```

[mathematical argument + verified computation]

### 2.2 The §6.1 ratio

With the observed counts `x = {AAA:1, AAT:1, TAA:1}`, external `N = 5`, and
`n = 3`, the separable binomial product (all other factors `1`) gives

```text
L(D)/L(S) = [(2/5)(3/5)^2] / [(1/5)(4/5)^2] = 18/16 = 9/8 > 1.
```

The only coordinate that changes is `AAA` (`1 → 2`). [verified computation]

**Consequence.** Under the §6.2 molecule/lower-bound-1 reading, `S` and `D` are
admissible §6.2 circuits and `D` strictly beats `S`; so `I_s` plus §6.2
admissibility of the truth does **not** force the truth to be §6.1-optimal.
[mathematical argument; finite instance only]

## 3. The PR #39 prose defect (independent finding)

PR #39 prints the truth spectrum as `d_S = {AAA:2, AAT:2, TAA:1}` in its §0 and
its §3 window table (and in the verifier docstring). The start-3 cyclic window of
`AAATT` is `S[3]S[4]S[0] = T T A = TTA`, whose revcomp is `TAA`, **not** `TTT`.
The correct occurrence counts are `d_S = {AAA:1, AAT:2, TAA:2}` — the values the
Lean module proves (`dS 0 = 1`, `dS 1 = 2`, `dS 4 = 2`) and the companion Python
script prints. The false table is internally inconsistent with the same
document’s §3.3, which correctly computes the changing factor as `AAA` (`1 → 2`).
The ratio `9/8` is unaffected because all observed classes have `x = 1`, so the
defect is documentation-only — but it means an issue-comment “correction” that
instead blamed the `TAA` factor was itself based on the false table. [verified
computation]

## 4. Ambiguities that bear on `AAATT → AAAATT`

### 4.1 Reverse-complement collapse is load-bearing

The truth’s **oriented** length-3 windows are `AAA, AAT, ATT, TTA, TAA`, while
the observed oriented reads at starts `(0,1,4)` are `AAA, AAT, TAA`. Thus
`supp(spectrum_oriented(S)) ⊋ supp(x)`: under the literal oriented `4^k` index
space of §6.1, `S` is *not* support-feasible. The witness becomes feasible only
after collapsing `ATT ↦ AAT` and `TTA ↦ TAA`, i.e. under the §3.1 molecule
vocabulary. [verified computation]

Consequently the witness is a **cross-convention panel**: MB09's molecule
vocabulary plus MB09's per-vertex lower bound `1`, evaluated with the §6.1
binomial objective. That panel is MB09-faithful under the molecule reading, but
it is not the literal `4^k` formula, and it is not Shomorony et al.'s
single-strand, cyclic-shift-only theory. It must be named as a panel, not
presented as a consequence of either paper alone. [source fact + modeling
choice]

### 4.2 Residual ambiguity register

| item | status |
|---|---|
| vertex = read DNA molecule, revcomp pair collapsed | **source fact** (§3.1, §4.1, §6.2) |
| §6.1 “`4^k` variables” vs revcomp classes | **source-internal tension**, unresolved by the text |
| §6.1 `d_i` are `k`-molecule counts; §6.2 `d_i` are read-vertex flows | **source-internal tension**; coincides only if `k =` read length |
| vertex lower bound `1` (per molecule), edge lower bounds `0`, upper bounds `∞` | **source fact** (§6.2) |
| objective defined only for `d_i ≤ N` while §6.2 upper bound is `∞` | **source-internal tension** |
| candidate is a flow (possibly non-contiguous), single sequence = circuit | **source fact** (§6.2) |
| which MB09 layer (exact multinomial / §6.1 binomial / §6.2 flow) the 2016 sentence denotes | **open** (issue #36) |
| tie semantics (truth a maximizer vs unique up to equivalence) | **open** |
| single-strand and fixed-candidate-length sub-cases | **open** |

## 5. Independent cross-check of the concurrent graph audit

The concurrent branch artifact `docs/section62-mb09-bidirected-graph-audit.md`
(on `agent/exact-mb09-graph-audit`) reaches the same conclusions from its own
script: the same 10-edge graph at `o_min = 2`, the same two circuits, the same
throughputs `d_S = {AAA:1, AAT:2, TAA:2}` / `d_D = {AAA:2, AAT:2, TAA:2}`, the
same `9/8` ratio, and the same `d_S` prose error. The two reconstructions were
written independently and agree, so the graph/flow part of the witness is
cross-verified to the level of two independent exact computations. [verified
computation]

The independent note adds to that artifact three source caveats the artifact
does not foreground: (i) the load-bearing revcomp collapse (§4.1); (ii) the
§6.1 `d_i` `k`-molecule vs §6.2 read-vertex identification requiring
`k =` read length (§1.6); and (iii) the objective-domain `d_i ≤ N` vs the §6.2
upper bound `∞` (§1.4). None affects the `AAATT` instance (`max d = 2 < N = 5`),
but each matters before the witness is cited as a general source-faithful
theorem.

## 6. What this note does and does not establish

**Does.** It pins the §6.2 definitions to their primary text and equation
locators; independently reconstructs the `{AAA, AAT, TAA}` graph and both
circuits; confirms the `9/8` ratio; records the PR #39 prose error and its
correction; and separates the source facts from the four residual tensions.

**Does not.** It is not a Lean proof; the graph/flow check is exact computation,
not kernel-checked. It does not decide the Shomorony referent, the strand/panel
choice, the tie semantics, or the single-strand / fixed-length sub-cases, and it
does not establish any non-spellable-flow result.

## 7. Epistemic summary

| claim | status |
|---|---|
| §3.1/§3.3/§3.4/§5.2/§6.1/§6.2 definitions as quoted above | **source fact** (PMC3154397; §-numbers and images M26–M33) |
| `4^k` vs molecule classes; `k`-molecule vs read vertex; `d_i ≤ N` vs `u = ∞` | **source-internal tensions** |
| 10-edge graph, two closed bidirected walks, throughputs, LB1, balance 0 | **mathematical argument + verified computation** (two independent scripts agree) |
| `L_{6.1}(D)/L_{6.1}(S) = 9/8 > 1` | **verified computation** |
| PR #39 prose `d_S` is wrong (`{AAA:2,AAT:2,TAA:1}`) and the correct value is `{AAA:1,AAT:2,TAA:2}` | **verified computation** |
| witness load-bearing on revcomp collapse (fails under the oriented `4^k` support test) | **verified computation** |
| which MB09 layer / tie semantics / strand panel the 2016 sentence denotes | **open** |

Cross-references: `docs/source-notes/medvedev-brudno-candidate-class.md`,
`docs/source-notes/reverse-complement-strand-convention.md` (branch artifact),
`docs/source-notes/mb-formulation-referent-reconciliation.md`,
`docs/open-problem.md`. Branch artifacts not on `main`:
`docs/section62-mb09-bidirected-graph-audit.md` and PR #39’s
`docs/bridging-se62-flow-ml-counterexample.md`.
