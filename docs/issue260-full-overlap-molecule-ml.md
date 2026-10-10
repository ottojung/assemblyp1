# Full-overlap reverse-complement molecule ML maximality (issue #260)

_Status: terminal research report for AssemblyP1 issue #260, a child of the
program #255.  Independent primary-source re-read of the Medvedev–Brudno (2009)
§6.1–6.2 text (re-fetched from PMC3154397), exact finite computation, and a
kernel-checked abstract characterization.  Every claim is labelled **source
fact**, **modeling choice**, **mathematical proof**, **kernel-checked**,
**verified computation**, **project-level strengthening**, or **open**._

_Reproduction:_

```sh
python3 scripts/verify_issue260_fulloverlap_molecule_ml.py     # exact, deterministic
lake build AssemblyP1.FullOverlapMoleculeML                    # kernel check
lake env leanchecker AssemblyP1.FullOverlapMoleculeML          # kernel replay
```

_Scope fence._  This report is the **full-overlap** (`o_min = L − 1`),
**fixed genome length** (`|D| = |S| = G`), reverse-complement **molecule** domain
only.  Arbitrary overlap and variable length are explicitly **open** and belong
to sibling issue #261; the oriented/same-length and binomial universes are #256,
#257, #258, #259 and are not re-decided here.

---

## 0. Verdict at a glance

1. **The source-faithful iff is true.**  In the full-overlap fixed-length
   reverse-complement molecule model, with the truth genuinely admissible (so
   the observed read support equals the truth's molecule-class support), the
   truth maximizes the exact multinomial likelihood against every admissible
   spelled candidate for **every** finite sample satisfying the literal
   Shomorony §6.4 coverage-and-bridging predicate **iff** its normalized
   molecule-count vector is the unique admissible one.  [kernel-checked
   `AssemblyP1.FullOverlapMoleculeML.robust_maximality_iff_unique` +
   mathematical proof]
2. **The general criterion behind the iff** is *coordinatewise dominance on the
   truth's support*: the truth never loses on any realizable sample iff no
   admissible competitor strictly exceeds the truth's count on any class the
   truth contains.  Uniqueness of the normalized count vector is exactly the
   special case of this dominance obtained when candidates are constrained to
   the observed support (the §6.2 vertex lower bound `1`).  [kernel-checked
   `exactLik_le_of_forall_le`; mathematical proof]
3. **The iff is delicate about the candidate universe.**  If the §6.2
   vertex-lower-bound discipline is dropped and "spelled candidate" is relaxed
   to *all* spelled length-`G` genomes (support free), the iff **fails**: the
   explicit pair `AATT → AAAT` has a non-unique count vector yet the truth still
   dominates every realizable sample.  [kernel-checked
   `broad_reading_counterexample`; verified computation]
4. **Bridging sufficiency is refuted (known, reused).**  The literal §6.4
   predicate plus genuine §6.2 spelled feasibility of both candidates does not
   force truth-maximality: the same-length witnesses `W1` (`AAATAT → AAAAAT`,
   exact ratio `3`) and, under the per-occurrence strengthening, `W2`
   (`ATATACAC → ATACACAC`, exact ratio `3/2`) are the non-uniqueness witnesses
   that make the "only if" direction non-vacuous.  [kernel-checked, reused from
   `AssemblyP1.HistoricalCoverageSameLengthWitnesses`]
5. **Remaining open.**  Which Medvedev–Brudno layer the 2016 sentence denotes;
   the per-occurrence strengthening as a *source* rule; arbitrary overlap and
   variable length (#261); and whether the strict support-equality reading is
   the intended one (a source-fidelity question, §8).  None of these is decided
   here.

---

## 1. Independent source audit

### 1.1 Method

The Medvedev–Brudno (2009) text was re-fetched directly from PMC3154397 and the
§3.1–3.4, §5.2, §6.1, §6.2 passages re-read against the repository's
`docs/section62-mb09-bidirected-graph-audit.md` and the Lean layer.  The
Shomorony et al. (2016) §6.4 reading is the repository's documented source
reconstruction in `docs/bridging-source-semantics.md`, whose primary citations
(Bresler–Bresler–Tse 2013; Shomorony et al. 2016) are checked for consistency
with the accepted-paper text; the supplement PDF is binary and was **not**
re-extracted here, so the Shomorony-specific clauses are labelled as a
consistency check of the repository's source note, not as a fresh extraction.
Where the two sources disagree, the disagreement is recorded as a source fork
rather than resolved by fiat.

### 1.2 Medvedev–Brudno §6.1–6.2 (source facts, re-read from PMC3154397)

- §3.1: “A DNA molecule is an unordered pair of strings … that are reverse
  complements of each other”; a `k`-molecule is such a pair of length-`k`
  strings; the `k`-molecule-spectrum is the set of `k`-molecules that are
  submolecules.  [source fact]
- §3.3: a bidirected edge carries a signed incidence at each endpoint; its
  length is the underlying string-overlap length.  [source fact]
- §3.4: a flow satisfies `l(e) ≤ f(e) ≤ u(e)` and, at every vertex, the flow
  along positive-incident edges minus the flow along negative-incident edges
  equals `b(v)`.  [source fact]
- §5.2: the vertex split `v⁻ → v⁺` carries the vertex bounds and costs, so `dᵢ`
  is the flow through vertex `i`.  [source fact]
- §6.1: the exact global read-count likelihood is the multinomial
  `n! / ∏ᵢ xᵢ! · ∏ᵢ (dᵢ / N(D))^{xᵢ}`; the paper replaces `N(D)` by an external
  known genome size `N` and factors the multinomial into independent binomial
  marginals.  The `4^k` index count is the oriented-`k`-mer count and conflicts
  with the molecular index set; the repository resolves the operative index set
  to observed molecule classes in
  `docs/source-notes/mb09-se61-index-orientation-resolution.md`.  [source fact]
- §6.2, verbatim (re-read): “The first step is to build a bidirected overlap
  graph from the set of reads, which are DNA molecules.  The vertices of this
  graph are the reads, and the edges are all possible bidirected overlaps of
  length at least `o_min` … We then perform transitive edge reduction … the
  transitively reduced bidirected overlap graph.”  Observation 7: “The number of
  times `W` visits `r` is equal to the number of times `r` appears a submolecule
  of the molecule spelled by `W`.”  And: “Each vertex has a lower bound of `1`
  since it represents a read that must be present in the genome at least once.
  All other lower bounds are `0` and all upper bounds are infinity.  We add
  prohibitively large costs to the edges from/to the supersource/sink so that
  their usage is minimized.”  [source fact]

### 1.3 Shomorony et al. §6.4 (repository reconstruction, consistency-checked)

The information-feasible set `I_s` requires coverage, every maximal triple
repeat all-bridged, and every interleaved repeat pair bridged, with the strict
copy-bridging normalization `r < t` and `t + ℓ < r + L` on the integer lift
(`docs/bridging-source-semantics.md`).  The literal §6.4 refinement replaces
“sampled base coverage” by **read-string matching coverage** and quantifies the
triple clause over **all** three-occurrence repeats
(`AssemblyP1.HistoricalCovers.HistoricalInformationFeasibleLiteral`,
`AssemblyP1.HistoricalCovers.IsTripleOccurrence`).  [source fact, via the
repository's source note]

**Source fork kept explicit.**  The accepted 2016 text does not say which
Medvedev–Brudno layer its phrase “the maximum-likelihood formulation of the AP”
denotes, nor whether competitors are length-constrained; those remain the
program's recorded ambiguity (`docs/source-notes/shomorony-mb-formulation-provenance.md`).
This report fixes the full-overlap, fixed-length, molecule layer and says so.

---

## 2. The model used here (modeling choices)

| ID | Choice | Justification |
|---|---|---|
| M1 | Circular truth `S` of length `G`; read length `L` with `2 ≤ L ≤ G`; **full overlap** `o_min = L − 1`. | MB09 §6.2; issue #260 scope |
| M2 | Read types are reverse-complement **molecule classes** `c(w) = min(w, rc w)`; the observation is the class count vector `x`. | MB09 §3.1, §4.1 |
| M3 | Candidates are **spelled** circular words `D` of length `G` whose consecutive-window walk is a closed §6.2 flow; the throughput is the molecule-class spectrum `d_D`. | MB09 §6.2 + Observation 7; “genuinely spelled” of #260 |
| M4 | The §6.2 vertex lower bound `1` on the observed reads means `supp(d_D) ⊇ supp(x)`; because a spelled candidate on the observed graph uses only observed vertices, `supp(d_D) = supp(x)`. | MB09 §6.2 |
| M5 | The objective is the exact multinomial §6.1 likelihood with intrinsic length `N(D) = G` (all candidates length `G`). | MB09 §6.1; “fixed genome length” of #260 |
| M6 | The hypothesis is the literal §6.4 predicate `HistoricalInformationFeasibleLiteral`. | Shomorony et al. §6.4 |
| M7 | The truth is **genuinely admissible**: `S` is itself a spelled candidate, so `supp(A) = supp(x)` for the samples considered. | issue #260 |

Under M1–M7 the comparison `L(D;x) ≤ L(S;x)` is, after cancelling the positive
observation-only factor `n!/∏xᵢ!` and the common `G^{-n}`,

```text
∏_c d_D(c)^{x_c} ≤ ∏_c d_S(c)^{x_c},
```

which is the natural-number product `exactLik` of
`AssemblyP1/FullOverlapMoleculeML.lean`.  [modeling choice + mathematical fact]

---

## 3. The characterization (kernel-checked)

Let `A = d_S` be the truth's molecule-class count vector and `F` a finite set of
admissible competitor count vectors, each with `∑ B = ∑ A = G` and the same
support as `A` (the strict §6.2 reading, M4+M7).

**Theorem 3.1 (`robust_maximality_iff_unique`).**

```text
(∀ x, supp x ⊆ supp A → ∀ B ∈ F, exactLik B x ≤ exactLik A x)  ↔  ∀ B ∈ F, B = A.
```

*Proof.*  `⟸` is immediate.  `⟹`: if `B ≠ A`, equal totals force some `w` with
`A w < B w`; the equal-support hypothesis gives `w ∈ supp A`; the concentrated
sample `x = e_w` (which is realizable because `w ∈ supp A`) gives
`exactLik B x = B w > A w = exactLik A x`, a contradiction.  ∎
[kernel-checked; no `sorry`, no `axiom`; axioms `propext`, `Classical.choice`,
`Quot.sound`]

**Proposition 3.2 (`exactLik_le_of_forall_le`).**  If every observed coordinate
satisfies `B c ≤ A c`, then `exactLik B x ≤ exactLik A x` for every realizable
`x`; this is the general *coordinatewise dominance* criterion, of which
uniqueness is the strict-reading special case.  [kernel-checked]

**Sample realizability (the `⟹` witness).**  The concentrated sample `x = e_w`
is not an arbitrary count vector: it is produced by adding `M` reads at a start
whose window class is `w`.  Adding reads preserves the literal §6.4 predicate
(coverage and bridging are monotone under adding reads), so the amplified sample
is itself `I_s`-admissible whenever a base `I_s` sample observing `supp A`
exists.  For truths with no `I_s`-admissible sample the universal statement is
vacuous; the theorem is therefore stated over the abstract sample domain and the
realizability bridge is this paragraph.  [mathematical proof + modeling choice]

**Non-vacuity (reused, kernel-checked).**  `W1`'s truth `AAATAT` has a
kernel-checked `HistoricalInformationFeasibleLiteral` certificate at starts
`{0,1,3,5}`, which observes all four classes `supp(A)`.  So the `⟹` direction is
not vacuous on the witnesses.  [kernel-checked, reused]

**`W1` instantiation (`w1_not_robust`, `w1_amplified_beats`).**  `W1`'s truth
and competitor vectors `(1,1,3,0,1,0,0,0)` and `(3,1,1,0,1,0,0,0)` have equal
total `6` and equal support, but differ; the amplified sample `x = e_AAA` gives
`exactLik = 3 > 1 = exactLik`, so the truth is not robustly maximal.  This is the
abstract-level content of the merged `W1` counterexample.  [kernel-checked]

---

## 4. Why the candidate universe matters (kernel-checked refutation)

The strict §6.2 reading forces `supp(d_D) = supp(x)`; this is exactly what makes
uniqueness equivalent to maximality.  If one instead takes the broad reading —
“admissible spelled candidates are all spelled length-`G` genomes”, dropping the
vertex-lower-bound discipline — the equivalence **fails**.

**Proposition 4.1 (`broad_reading_counterexample`).**  Over the class space
`(AAT, TAA, AAA, ATA)` the truth `AATT` has count vector `A = (2,2,0,0)` and the
competitor `AAAT` has `B = (1,1,1,1)`.  Then `∑ B = ∑ A = 4`, `B ≠ A`, and yet
`exactLik B x ≤ exactLik A x` for every `x` supported inside `supp A = {AAT,TAA}`
because `B` is coordinatewise `≤ A` there.  So non-uniqueness coexists with
sample-uniform maximality.  [kernel-checked; verified computation]

The mechanism is a **support mismatch**: `AAAT` spends mass on the unobserved
classes `AAA, ATA` while staying below the truth on the observed classes.  Under
the strict §6.2 reading such a candidate is not admissible (its window walk would
use vertices absent from the observed read graph), which is precisely why the iff
holds there and fails here.  [mathematical proof]

This is the precise sense in which #260's “construct feasible count vectors from
**genuinely spelled bidirected flows**, not oriented support proxies” matters:
the candidate universe must be the spelled flows *on the observed graph*, not
all spelled genomes.  [modeling choice]

---

## 5. Relation to the known `W1`/`W2` refutations

The merged PR #142 witnesses remain the reason the iff is not vacuous:

| witness | truth `S` | competitor `D` | `G` | support | exact ratio | status |
|---|---|---|---|---|---|---|
| `W1` | `AAATAT` | `AAAAAT` | 6 | equal | 3 | kernel-checked |
| `W2` (per-occurrence) | `ATATACAC` | `ATACACAC` | 8 | equal | 3/2 | kernel-checked |

Both have **equal support**, so they are *strict-reading* competitors and
exhibit the non-uniqueness that Theorem 3.1 predicts; both are genuine §6.2
spelled candidates and both satisfy the literal §6.4 predicate.  The abstract
module reproduces `W1`'s non-uniqueness and its amplified sample.  The
independent script re-derives `W1`'s exact ratio `3` and §6.1 binomial ratio `5`.
[kernel-checked, reused + verified computation]

### 5.1 Per-occurrence strengthening (W2) is not the source rule

Under the project-level per-occurrence strengthening `d_D(c) ≥ x_c`, the
amplification argument of Theorem 3.1 **breaks**: the amplified coordinate is
bounded by `x_w ≤ d_D(w)`, which is fixed, so `x = e_w` with large `M` is
inadmissible.  `W2` shows the strengthened statement is false, and Medvedev–Brudno
§6.2 states only the per-vertex lower bound `1`, not per-occurrence.  Whether
some *other* sample realizes a strict defeat under the strengthening is a
separate finite question; this report leaves it **open** for #258/#259.  [verified
computation + open]

---

## 6. What is settled for #260, and what is not

**Settled (kernel-checked + audited).**

1. Under the strict source-faithful reading (M1–M7), truth-maximality over every
   realizable literal-§6.4 sample is equivalent to uniqueness of the normalized
   molecule-count vector (Theorem 3.1).
2. The general criterion is coordinatewise dominance on the truth's support
   (Proposition 3.2).
3. The iff genuinely depends on the §6.2 vertex-lower-bound discipline; the
   broad “all spelled genomes” reading refutes it (Proposition 4.1).
4. `W1` instantiates the non-uniqueness and the amplified defeating sample.

**Not settled (explicit open matrix for #260's scope).**

| # | Open claim | Why it is open |
|---|---|---|
| O1 | Which Medvedev–Brudno layer the 2016 sentence denotes | source ambiguity, program-level |
| O2 | Whether the strict support-equality reading (M4) is the intended candidate universe | source-fidelity; the accepted text does not spell out the vertex-lower-bound consequence |
| O3 | The per-occurrence strengthening as a source rule, and its robust classification | project-level strengthening; W2 refutes it, general classification open (#258/#259) |
| O4 | Arbitrary overlap `o_min ≤ L − 1` and variable length | explicitly fenced to #261 |
| O5 | Whether a non-spellable *maximizer* exists at `o_min = L − 1` | separate question, not addressed |
| O6 | The exact likelihood objective vs the §6.1 binomial approximation in the sentence | program-level source ambiguity |

The claims of this report are stated only for the full-overlap, fixed-length,
molecule universe and do **not** transfer silently to O4; positive statements do
not transfer at all without a proved candidate-set inclusion.  [modeling choice]

---

## 7. Reproduce

```sh
python3 scripts/verify_issue260_fulloverlap_molecule_ml.py
lake build AssemblyP1.FullOverlapMoleculeML
lake env leanchecker AssemblyP1.FullOverlapMoleculeML
```

The script independently recomputes molecule-class spectra, the strict and broad
candidate sets, the strict-reading iff over 1708 truths, the `AATT → AAAT`
refutation, `W1`'s exact and binomial ratios, and `AATT`'s vacuous literal §6.4
status.  It is deterministic, exact (`fractions.Fraction`), and exits non-zero
on any failed assertion.

---

## 8. Epistemic status

| Claim | Status |
|---|---|
| MB09 §6.1 exact multinomial and §6.2 bidirected overlap graph, vertex LB 1, transitive reduction, supersource/sink, Observation 7 | **source fact** (PMC3154397, re-read) |
| Shomorony/Bresler §6.4 coverage + all-triples + interleaved bridging, strict normalization | **source fact** via repository source note (consistency-checked) |
| Full-overlap `o_min = L − 1`, fixed length `G`, molecule classes, exact objective, genuine truth admissibility | **modeling choice** (M1–M7) |
| `robust_maximality_iff_unique`, `exactLik_le_of_forall_le`, `robust_maximality_of_unique` | **kernel-checked** (`AssemblyP1.FullOverlapMoleculeML`, axioms `propext`, `Classical.choice`, `Quot.sound`) |
| `w1_not_robust`, `w1_amplified_beats`, `broad_reading_counterexample` | **kernel-checked** (same module) |
| strict-reading iff over all small truths | **verified computation** (1708 truths) |
| `W1` exact ratio `3`, binomial ratio `5` | **kernel-checked** (reused `AssemblyP1.HistoricalCoverageSameLengthWitnesses`) + verified computation |
| O1–O6 | **open** |

Primary sources: Medvedev & Brudno (2009), *J. Comput. Biol.* 16(8) 1101–1116,
§3.1–3.4, §5.2, §6.1–6.2, [PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/);
Shomorony, Kim, Courtade & Tse (2016), *Bioinformatics* 32(17) i494–i502,
Eq. (1) and §6.4 supplement; Bresler, Bresler & Tse (2013), *BMC Bioinformatics*
14(Suppl 5):S18.
