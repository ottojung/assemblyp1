# Finite universe of readings of the 2016 ML open question: audit with justified exclusions

_Status: primary-source interpretation inventory for issue #208 (parent #217),
2026-10-09; **terminal for #208** — the inventory is complete, every claim is
sourced and tagged, and the remaining gaps are named in §6 rather than open
work. This note re-derives, by execution, a **finite** and
**source-supported** enumeration of the readings of the Shomorony et al. (2016)
maximum-likelihood question, records the candidate-universe, length, tie, and
representation conventions attached to each cell, and lists the exclusions with
their justifications. It compares, but does not replace,
[`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md).
It does **not** select a referent, does **not** settle the published question,
and does **not** duplicate the mathematical-case work of issues #209–#216._

_Every claim is tagged **source fact**, **mathematical fact**,
**verified computation**, **source-supported inference**,
**interpretation**, **repository fact**, **research choice**, or **source
gap**. The tags `fact`/`inference`/`choice` are used in that spirit: a claim
supported by a retrieved primary artifact is a fact; a claim derived from
facts by reasoning is an inference; a claim chosen by this repository without
source compulsion is a research choice._

_Reproduce: `python3 scripts/verify_finite_interpretation_audit.py` (pure
arithmetic) and `python3 scripts/verify_finite_interpretation_audit.py
--sources <dir>` (with the hash-verified artifacts of §1). The script is
self-contained, deterministic, and exits non-zero on any failed assertion._

_Companion notes landed in the same change (2026-10-09): each of them was
**referenced by live repository documentation but missing**, and this audit
recovered or authored it._
- [`shomorony-ml-quantifier-sequence-resolution.md`](shomorony-ml-quantifier-sequence-resolution.md)
  — exists on the unmerged `analysis/issue36-*` branches, referenced by
  [`../literature/post2016-bridging-ml-citation-chain-2026-09-20.md`](../literature/post2016-bridging-ml-citation-chain-2026-09-20.md)
  §5.3: **recovered and re-verified here**.
- [`shomorony-mb-formulation-referent-reconciliation.md`](shomorony-mb-formulation-referent-reconciliation.md)
  — referenced by name at
  [`../oriented-same-length-ml-88.md`](../oriented-same-length-ml-88.md) §1.3
  but never present on any branch: **authored here** as the Shomorony-side /
  repository-side counterpart of the MB09-side reconciliation.

---

## 0. Bottom line

1. **The universe of readings is finite and enumerable: 64 cells**, the product
   of four source-grounded axes: objective layer (4) × representation panel (2)
   × candidate universe (4) × conclusion schema (2). 48 cells are specific
   objective readings; 32 of those are sequence-valued; the remaining 16
   specific cells instantiate the §6.2 flow object, which is not
   sequence-valued without a flow→sequence bridge that no source supplies.
   [source-supported inference; §3]

2. **The axis choices are decision-relevant, not presentational.** Exact
   rational arithmetic on one instance shows the exact multinomial (variant E)
   and the fixed-`N` binomial (variant A) rank the same candidate pair in
   **opposite** directions (`9/8` vs `59049/62500`), and that the read-type
   representation flips variant E's ordering (`9/8` → `1/3`) while leaving
   variant A's sign fixed (`59049/62500` → `1/5`). A result proved at one cell
   therefore does not transfer to another cell. [verified computation; §4]

3. **No primary source selects a cell.** The accepted 2016 text names
   Medvedev–Brudno by bibliography only, never with a section, equation,
   objective formula, length convention, or tie rule. [source fact; §2.1]

4. **Eight cell families are excluded with justification** (§5): the flow layer
   as a *sequence-level* referent (X1); the flow feasible set crossed with
   sequence-valued schemas (X2); molecule read types paired with
   cyclic-shift-only equivalence (X3); a true-length competitor restriction
   under the exact multinomial (X4); “all circular candidates” as the domain of
   the fixed-`N` binomial (X5); any genome equivalence coarser than the two
   panels (X6); the meta-reading `P` as witness-settleable (X7); and the
   doubled-strand `2G`/`2N` data model as a reading of the 2016 sentence (X8).
   Each exclusion is a statement about **source support**, not about
   mathematical legitimacy: excluded cells may still be legitimate restricted
   research subproblems.

5. **Composition gap (new in this audit).** Neither Medvedev–Brudno (2009) nor
   the 2010 thesis contains any bridging concept (0 occurrences of “bridg*”),
   and Shomorony et al. contain no likelihood formula. The 2016 sentence's
   antecedent (bridging conditions) and its consequent (maximum likelihood)
   come from two different papers that never reference each other's
   formalisms; **no source performs the composition the sentence asks
   about**. In the contemporaneous bridging literature the phrase
   “maximum-likelihood formulation” already cited *two* papers (Myers 1995 and
   Medvedev–Brudno 2009), so the 2016 phrase names a family, not an object.
   [source fact + source-supported inference; §6.5, §2.4]

6. **Measured unresolved gaps** (§6): the referent selection; the publisher
   supplement (HTTP 403 through Cloudflare, re-measured this run); MB09's
   `4^k`-versus-molecule-class counting tension; maximizer-versus-uniqueness
   semantics; the Varma et al. (2011) full text (abstract verified through a
   secondary reproduction only); and one dead citation locator in a sibling
   source note, machine-detected by `scripts/audit_source_note_citations.py`.

---

## 1. Independent retrieval and verification (execution log, 2026-10-09)

This run **re-downloaded all eight artifacts over HTTP** (every request
returned HTTP 200) and re-computed their SHA-256 digests with `sha256sum`:
**all eight match the ledger by execution.** Earlier turns of this same front
had cached them in `scratch-208/sources` with a `sha256sum -c` ledger beside
them (`hashes.txt`); the cached bytes and the freshly downloaded bytes are
identical, so every quotation below was read from bytes whose digest is
recorded here. The corrected `InfoOptimalAssy.pdf` digest (64 hex digits; the
malformed 63-digit form was fixed in companion commit `ad05fc9`) is among
them. [verified computation]

| Artifact | Locator | SHA-256 |
|---|---|---|
| Shomorony et al., OUP-typeset article | `https://people.eecs.berkeley.edu/~courtade/pdfs/InfoOptimalAssy.pdf` | `ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043ac3fce3c4da` |
| Shomorony et al., author-accepted manuscript | `https://people.eecs.berkeley.edu/~courtade/pdfs/NSG.pdf` | `daeb5b3163d92643affc2398a387217cb57e5e33ce0dd5ebbfccabf621454f2c` |
| Shomorony et al., earlier preprint + supplement | `https://web.stanford.edu/~gkamath/nsgIlan.pdf` | `f2a9f6a64f75cbf4c2cfaec6f794c779907f165c986261bec7a2aa72a3e6954a` |
| Medvedev–Brudno (2009), published JCB PDF | `https://medvedevgroup.com/papers/jcb09.pdf` | `bfeaec37de55e87c35438108c33a8052f0fd6eb56f2903bb1d50d2793d8a5aa3` |
| Howison–Zapata–Dunn (2013) author PDF | `https://mark.howison.org/Howison-Bioinformatics-2013.pdf` | `bc25681f820b151467df79d7122c5b16a64892b2f15fa3636ace09350762c935` |
| Ghodsi, arXiv:1302.4391 | `https://arxiv.org/pdf/1302.4391` | `6af4c06a37b46afef3961613d62e67fa8375c801b1c4a6a2ea12e256ddd9716c` |
| Medvedev 2010 thesis (server returns extracted **text**, not a PDF) | `https://utoronto.scholaris.ca/server/api/core/bitstreams/5cf61055-a13a-430e-9b9e-20a6be4ff56a/content` | `97b604706ad288136616917262b3ab7662d5b2b28a4af1a8a2d4b680b3e42a63` |
| Bresler–Bresler–Tse (2013), arXiv:1301.0068 (**added to the ledger by an
earlier turn of this front; re-verified by re-download this run**) | `https://arxiv.org/pdf/1301.0068` | `adc32a908ab06d033a778bd75d43eacc0463c4cc4231720684b4b2941cccae59` |

Publisher endpoints re-measured this run: the OUP article page
(`https://academic.oup.com/bioinformatics/article/32/17/i494/2243782`), the
article-PDF endpoint, and a supplementary-material endpoint for the same
article all return **HTTP 403 behind a Cloudflare challenge** (the response body
carries the "Just a moment" interstitial). The accepted supplementary ZIP
(sections A–G) therefore remains uninspected; this is a re-measured gap, not an
inherited one. [verified computation]

**Extraction artifacts encountered (repository fact).** Quote matching on the
byte-verified PDFs must normalize several extraction artifacts or it fails on
correct text: the accepted article hyphenates “se- quence” across a line
break; MB09 uses the U+FB02 “ﬂ” ligature, renders subscripts as plain “d_i” →
“di”, renders the fraction `d_i/N(D)` as “di N(D)” with the slash lost, renders
“=” through a Symbol font, and inserts a space before “)” in
“(Medvedev and Brudno, 2009 )”. Bresler–Bresler–Tse extract with a typeset
prime (U+2032) in “s′” and interleaves footnote text into the sentence. The
audit script's matcher expands ligatures, folds curly apostrophes and typeset
primes, and tests flattened, de-hyphenated, hyphen-joined, subscript-dropped,
slash-as-space, minus-tightened, and punctuation-spaced variants on both
sides. **Negative control (new this run):** the matcher must *not* match
fabricated passages, cross-source passages, or one-word-wrong passages (e.g.
“There are 16 k such variables”, “we assume that the genome size is unknown”);
the script asserts all of them fail in every artifact, so the positive checks
above are evidence rather than tautology. [repository fact; re-verified this run]

---

## 2. Source facts established by this run

### 2.1 The 2016 accepted text

- The Discussion's final paragraph contrasts parsimony with optimization
  formulations and states: “The maximum-likelihood formulation of the AP
  (Medvedev and Brudno, 2009), on the contrary, seems to be robust to these
  issues … **Understanding whether bridging conditions can be used to
  guarantee that the maximum-likelihood sequence is the true sequence is
  currently an open question.**” [source fact]
- Full-text census of the 9-page typeset article: exactly **3** occurrences of
  “likelihood” (two in that paragraph, one in the MB09 reference title),
  **0** occurrences of “multinomial”/“binomial”, **10** of “Medvedev”, **1**
  of “genie” (which concerns tuning the string-graph overlap parameter, not
  the ML formulation). There is no section, equation, or page pointer into
  Medvedev–Brudno. [verified computation]
- **Lexical exhaustiveness sweep of the accepted text (machine-checked this
  run).** The words that would have to appear if the sentence carried a
  formula, a candidate class, a tie rule, a competitor length, or the section
  6.2 flow object are all **absent**: 0 occurrences of “flow”, “biflow”,
  “copy number”, “copy count”, “competitor”, “maximizer”, “argmax”.
  “candidate” occurs exactly **twice**, never as a genome candidate class —
  once as “two candidates for successor” (graph successors) and once as
  “a good candidate for the ‘correct’ formulation” (about the formulation, not
  about sequences). “tie” occurs **4 times**, always as the graph algorithm's
  arbitrary edge ordering (“breaking ties arbitrarily” / “Ties are broken
  arbitrarily otherwise”), never about the likelihood. The only “length `G`” in
  the whole article fixes the **true** sequence (`we will assume that s is a
  circular sequence of length G`); there is no competitor-length statement
  anywhere. The accepted text therefore supplies *no* formula, *no* candidate
  class, *no* likelihood tie rule, *no* length constraint on a competitor, and
  *no* flow object. [source fact + verified computation; §5 exclusions X1–X8
  rest on this]
- The data model: true circular sequence `s` of length `G`; `N` reads of
  common length `L`, **error-free**, drawn “independently and uniformly at
  random from the set of length-`L` substrings of `s`” with circular indexing;
  targets are `s` **up to cyclic shifts**. [source fact]
- Reverse complement appears only as preprocessing that *adds* reads, never
  as an identification of a read with its reverse complement. [source fact]

### 2.2 The earlier author-hosted preprint

- The preprint framed the relevant optimization as a **fixed-`G`** problem: “One
  way to prevent this undesirable property … is to consider a genie-aided
  formulation where the target genome length `G` is given.” [source fact]
- It quotes Bresler et al.: “If a triple repeat in `s` is not bridged or an
  interleaved repeat in `s` is not bridged, then there exists a sequence
  `s′ ≠ s` with the **same likelihood** as `s`.” [source fact]
- Its own supplement (§6.1–6.4: decremental hashing, effective overlaps,
  Eulerian reduction, bridging conditions) contains **no likelihood
  definition**; the preprint's 3 “likelihood” occurrences are the ML-formulation
  sentence, the bibliography title, and the Bresler statement. [verified
  computation]
- The author-accepted manuscript (`NSG.pdf`, 8 pages) contains no supplement
  or appendix. [verified computation]

### 2.3 Medvedev–Brudno (2009), §3.1, §6.1, §6.2 (verbatim, re-located this run)

- §6.1 exact model: “Let `D` be a circular genome of length `N(D)`, and let
  `d_i` denote the number of times the `k`-molecule `i` appears in `D`. … In
  each trial, a position is uniformly sampled from `D` and the outcome of the
  trial is the `k`-molecule beginning at that position. For a given `i`, the
  probability that the outcome of a single trial is `i` is simply
  `d_i/N(D)`. … When taken together, their joint distribution is exactly the
  multinomial distribution …” with “**There are `4^k` such variables**”.
  [source fact]
- §6.1 approximation: “Since in the binomial approximation the length of the
  genome `N(D)` is a constant that is independent of each `d_i`, we can
  replace it by `N`, which is the length of the actual genome from which the
  reads were sampled. … **For our experiments, we assume that the genome size
  is known.**” Cost per type: `c_i(d_i) = −(x_i log d_i) − (n − x_i) log(N − d_i)`.
  (The paper reads “**Since** in the binomial approximation”, not “Because”: the
  preceding sentence is the “Because the number of trials … is typically large”
  clause. This audit corrects a misquote inherited from
  [`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md)
  §2.2, which was corrected in the same change.)
  [source fact]
- §6.2 algorithm: “The first step is to build a bidirected overlap graph from
  the set of reads, which are DNA molecules. The vertices of this graph are
  the reads … Each vertex has a lower bound of `1` … By Observation 7, the
  `d_i`'s described above actually correspond to the value of the flow through
  vertex `i` … our flow represents a **(non-contiguous) assembly** of the
  genome …” [source fact]
- §6 title: “PREDICTING COPY-COUNTS USING MAXIMUM LIKELIHOOD”; the abstract
  proposes “a maximum likelihood framework for assembling the genome that is
  the most likely source of the reads”. [source fact]
- Read model: §3.1 defines a `k`-molecule as a double-stranded molecule (an
  unordered reverse-complement pair) and represents “each `k`-molecule … only
  once”; §6.1 is error-free by construction (the trial outcome is the exact
  `k`-molecule at the sampled position), and the paper's three “error-free”
  mentions are all outside §6.1's model definition — two in the §8.1 dataset
  description (one in the main clause, one in the same sentence's
  parenthetical) and one in the conclusion's “In our experiments, we make two
  major assumptions—that the reads are error-free …”. [source fact]
- **No bridging concept exists anywhere in MB09 or the thesis** (0 occurrences
  of “bridg*” in the full text of each). [verified computation]

### 2.4 The 2010 thesis and contemporary usage

- Thesis Chapter 4 (“Maximum likelihood genome assembly”) carries the same
  exact-versus-fixed-`N` text, including “since the multinomial distribution
  has the constraint that `N(D) = Σ_i d_i`, this is not possible” and “we
  assume that the genome size is known”. [source fact]
- Howison, Zapata & Dunn (2013): the MB ML assembler “requires as a parameter
  the accurate size of the target genome”. [source fact]
- Varma, Ranade & Aluru (2011): the abstract advertises eliminating “the
  requirement to a priori know a stringent estimate of the length of the
  genome”, which confirms that a-priori genome length was *part of* the MB
  formulation as read by the community. Re-verified this run from OpenAlex's
  abstract reproduction of DOI `10.1109/ICCABS.2011.5729873`
  (`https://api.openalex.org/works/doi:10.1109/ICCABS.2011.5729873`, JSON
  abstract-inverted index; the publisher abstract is elided at Semantic
  Scholar and IEEE is closed-access). Still not the publisher's artifact.
  [source fact via abstract reproduction; source gap for the full text]
- Ghodsi (arXiv:1302.4391v3): a contemporaneous ML-assembly formulation that
  assumes the assembly length is known, and notes that the resulting optimum
  has “many tours, all of which will have equal likelihood”. Its prefix graph
  gives “each read … correspond[s] to a vertex” (deduplicated graph structure)
  while the objective counts `n_i` = “the number of times read i ‘appears’ in
  `A`” (raw multiplicities) — the same two-layer read-set model that the 2016
  and MB09 papers use on their respective sides. [source fact]
- Howison, Zapata & Dunn (2013) §5: “a maximum likelihood assembly is the
  assembly that has the highest likelihood” — the W schema (truth is a
  maximizer), not S (every maximizer is the truth). This is the community's
  definition of the term, not a statement about the 2016 sentence's intended
  schema. [source fact]
- **Bresler–Bresler–Tse (2013)** — the paper whose Theorem 1 the Shomorony
  preprint restates — list “maximum-likelihood [16], [11]” among the
  “optimization-based formulations” of assembly, where reference [16] is
  **Myers (1995)** and [11] is **Medvedev–Brudno (2009)**. The community label
  “maximum-likelihood formulation” therefore already spans **more than one
  paper** in 2013, and neither of them is the Shomorony paper; the 2016 phrase
  “the maximum-likelihood formulation of the AP” is a label on a family, not a
  pointer to a unique formal object. [source fact; supports the P reading of
  §3.1 being a family]
- The same paper's data model uses a **different length/strand convention**
  than any Shomorony version: “DNA is double-stranded and consists of a
  length-`G` sequence `u` and its reverse complement `ũ` … defining `s` as the
  length-`2G` concatenation of `u` and `ũ`, transforming each read into itself
  and its reverse complement so that there are `2N` reads.” Under that remap
  the true sequence has length `2G` and there are `2N` reads. No Shomorony
  version uses it: in the accepted text reverse complement is preprocessing
  that *adds* reads (1 occurrence, §2.1), and the model is a single-stranded
  circular `s` of length `G` with `N` reads. [source fact + source-supported
  inference; exclusion X8]

---

## 3. The finite universe: four axes

Each axis enumerates values **stated by a source** (or, where marked, a value
the repository needs for classification). The product is the universe of
readings; §5 excludes the unsupported cells.

### 3.1 Axis O — objective layer (4 values)

| Value | Definition | Source status |
|---|---|---|
| **E** | exact global read-count multinomial, candidate-intrinsic `N(D)`: `L_E(D|x) = n!/∏_i x_i! · ∏_i (d_i/N(D))^{x_i}`; defined for every nonempty circular candidate | MB09 §6.1's named target, explicitly abandoned as not separable; never named by 2016 [source fact] |
| **A** | separable fixed-`N` product of binomial marginals: `∏_i (d_i/N)^{x_i}(1 − d_i/N)^{n−x_i}` with external `N` = true genome length, assumed known | MB09 §6.1's operative objective; thesis; Howison; Varma; Ghodsi; the authors' own fixed-`G` preprint framing [source fact + source-supported inference] |
| **F** | §6.2 bidirected read-overlap-graph flow feasible set (per-vertex lower bound 1; output a “(non-contiguous) assembly”) | MB09 §6.2's algorithm; returns a flow, not necessarily a sequence [source fact] |
| **P** | unspecified general ML principle / objective family (“the maximum-likelihood formulation of the AP” with no formula) | the safest literal reading of the 2016 sentence [interpretation] |

E, A, F, and P are exactly the four readings of
[`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md)
§5; that note ranks them by literal text / named ideal / operative method, and
this audit re-uses its enumeration as the O axis without re-ranking it.
[repository fact]

### 3.2 Axis R — representation panel (2 coupled values)

The read-type space and the genome equivalence are **one coupled choice**
(`equivalence-and-tie-wellposedness.md`): under molecule read types a
candidate and its reverse complement always tie, so the strong schema forces
reverse complement into the equivalence; under oriented read types it does
not. The panels are therefore paired, not independent. [mathematical fact]

| Panel | Read types | Equivalence | Forced by |
|---|---|---|---|
| **R-oriented** | oriented length-`L` substrings (Shomorony convention; the literal `4^k` count of MB09 §6.1) | cyclic shift | Shomorony's circular exposition; cyclic-shift invariance of the exact likelihood [source fact + mathematical fact] |
| **R-molecule** | reverse-complement `k`-molecule classes, `(4^k + p_k)/2` of them (`p_k = 4^{k/2}` even `k`, else 0) | cyclic shift **and** reverse complement (dihedral) | MB09 §3.1/§4.1/§6.2; “every maximizer is the truth” under molecule types requires RC [source fact + mathematical fact] |

MB09 is internally inconsistent on this axis: §6.1 writes `4^k` variables
(oriented `k`-mers) while its model vocabulary and §6.2 graph are molecular
(`(4^k + p_k)/2` classes: 32 at `k=3`, 136 at `k=4`). The literal `4^k`
formula and the molecular graph cannot both be literal; given §6.2, the
index set is molecule classes. [source fact + source-supported inference;
mb09-se61-index-orientation-resolution.md; verified computation in §4.4]

### 3.3 Axis U — candidate universe (4 values) and the length conventions

| Value | Universe | Length convention | Source status |
|---|---|---|---|
| **U1** | all nonempty circular candidates | E: candidate-intrinsic `N(D)`, no restriction, multinomial slice `Σ d_i = N(D)`. A: no length in the formula, but the objective is **definedness-limited**: `d_i < N` is required for every type (else `log(N − d_i)` is undefined) | U1 is the literal E domain [source fact]. The A domain restriction is a refinement of “all circular candidates” [source-supported inference] |
| **U2** | candidates of the true length `G` | competitor length pinned to the true length | no source pins the *competitor* length; partial support from the fixed-`N` operative method (which needs the true length `N` known), the preprint's fixed-`G` framing, and Ghodsi's known-length formulation [source fact for the method, interpretation for the competitor restriction] |
| **U3** | §6.2 sequence-level spelled candidates: circular sequences whose length-`L` window support equals the observed read support (per-vertex lower bound 1) | any length, but support equality | MB09 §6.2 + §4.1/§7 (unobserved classes have no vertex, so `d_i = 0` there) [source fact + source-supported inference] |
| **U4** | §6.2 general flow feasible set | flows decomposed into walks; not sequences | MB09 §6.2 literal [source fact] |

**Length conventions, summarized (choice-relevant):** under E the candidate's
own length is inside the objective; under A the length parameter is external
and assumed known while the candidate's length appears nowhere; under F no
competitor length is constrained at all; Shomorony's own model fixes the true
genome length `G` but says nothing about a competitor's. The three are
therefore not interchangeable, and a same-length witness belongs to U2 and U1
simultaneously while a different-length witness does not. [source-supported
inference; mathematical fact for the inclusion]

**Representation conventions, summarized (choice-relevant):** the read-type
panel (axis R), the genome equivalence, and the **strand convention of the data
model** are three distinct things. The 2016 model is single-stranded circular
`s`, length `G`, `N` reads; the reverse complement appears only as
preprocessing. The literature's *other* convention — BBT's doubled-strand remap
to a length-`2G` sequence with `2N` reads (§2.4) — never appears in any
Shomorony version, so it is recorded as an excluded reading (X8) rather than as
a cell of the universe.

### 3.4 Axis T — conclusion schema (2 values) and the tie conventions

| Value | Schema | Tie convention |
|---|---|---|
| **W** | `∀ candidate, L(candidate) ≤ L(truth)` (truth is a maximizer) | none needed |
| **S** | `W ∧ (∀ candidate, L(candidate) = L(truth) → candidate ≈ truth)` (every maximizer is the truth up to `≈`) | requires `≈` to contain cyclic shift; contains reverse complement iff the panel is R-molecule; no coarser `≈` has source support |

No source states a tie-break, a uniqueness claim, or an equivalence relation;
the singular “the maximum-likelihood sequence” cannot distinguish W from S.
[source gap] Ties are generic: Ghodsi records many equal-likelihood optima,
and Bresler's theorem (as quoted in the preprint) exhibits a distinct sequence
with the same likelihood exactly when bridging fails. [source fact]

### 3.5 Cardinality

`4 (O) × 2 (R) × 4 (U) × 2 (T) = 64` cells. Because **P is a meta-reading**
whose instances include E and A (and arguably F), the distinct *specific*
hypotheses number `3 × 2 × 4 × 2 = 48`; of the specific layers only E and A
are sequence-valued, so `2 × 2 × 4 × 2 = 32` specific cells are sequence-valued.
The remaining 16 specific cells instantiate the flow object F, which is not
sequence-valued without a flow→sequence bridge (§5, exclusion X1). [verified
computation; interpretation for the P reading being a family]

---

## 4. The axes are decision-relevant (exact computations)

All ratios below are exact rational numbers recomputed by
`scripts/verify_finite_interpretation_audit.py`; the instance is
`S = AAATAT`, `D = AAAAAT`, `G = 6`, `L = 3`, reads sampled at starts
`(0,0,2,4,2)` so `x = {AAA:2, ATA:3}`, `n = 5`. Since `|S| = |D|`, the exact
multinomial ratio's `N(D)` factors cancel. [verified computation]

### 4.1 Objective layer (E vs A): same pair, opposite verdicts

| panel | `L_E(D)/L_E(S)` | `L_A(D)/L_A(S)` | agree? |
|---|---|---|---|
| R-oriented | `9/8 > 1` (D beats S) | `59049/62500 < 1` (S beats D) | **no** |
| R-molecule | `1/3 < 1` | `1/5 < 1` | yes |

A result proved for E does not transfer to A and vice versa; the objective
layer is choice-relevant. [mathematical fact + verified computation]

### 4.2 Representation panel: sign movement

Under E the panel flips the verdict (`9/8 > 1` → `1/3 < 1`); under A it does
not (`59049/62500 < 1` → `1/5 < 1`). The read-type representation is
therefore decision-relevant for the exact multinomial and presentational-only
(sign-wise) for this instance of the binomial. Cross-check: on `main`'s
kernel-checked witness (starts `(0,0,1,3,5)`, molecule convention) the same
pair gives `3` (E) and `5` (A). [verified computation; repository fact]

### 4.3 Bounded agreement inside the bridging class (NOT a proof)

Enumerating the binary alphabet at `(G,L,mult) = (6,3,2,4)` molecule and
oriented and `(5,4,2,4)` oriented, restricted to instances satisfying the
Shomorony `I_s` predicate, the two objectives' signs agree on **every**
in-bridging-class instance: `374`, `374`, and `1230` `I_s` instances
respectively, with `0` E/A sign disagreements, and the §4.1 disagreement
witness lies outside `I_s`. This is bounded evidence only; its completeness is
not proved. [bounded computation]

### 4.4 `k`-molecule class arithmetic

`#classes = (4^k + p_k)/2` with `p_k = 4^{k/2}` for even `k` and `0` for odd
`k`, verified by enumeration for `k ≤ 6`: `2, 10, 32, 136, 512, 2080` versus
`4, 16, 64, 256, 1024, 4096`. [mathematical fact + verified computation]

---

## 5. Exclusions (each is a statement about source support, not mathematical legitimacy)

- **X1 — F as a sequence-level referent.** The 2016 sentence asks whether “the
  maximum-likelihood **sequence**” is the truth; §6.2 optimizes over flows and
  MB09 route the single-sequence question to a §7 heuristic. Reading F at the
  sequence level requires a flow→contig/decomposition step that neither source
  supplies. **Excluded from the sequence-valued count**; the flow reading
  remains a live reading whose sequence-level meaning is unresolved.
  [source fact + interpretation; reconciliation §4]
- **X2 — U4 crossed with W/S.** The §6.2 general flow feasible set contains
  non-contiguous assemblies; a flow witness does not answer a question phrased
  about sequences, for the same reason as X1. [source fact + interpretation]
- **X3 — Molecule read types with cyclic-shift-only equivalence.** Under
  molecule types every candidate ties with its reverse complement, so schema S
  would be false for every observation. The panel pairing is forced; the
  “molecule + cyclic-only” combination is excluded. [mathematical fact]
- **X4 — U2 (true-length competitors) as a source reading of E.** MB09 §6.1
  restricts nothing about competitor length; the 2016 sentence says nothing
  either. U2 is retained as a cell only because the repository's witnesses and
  the operative lineage use it; a U2 theorem is a **restricted** result for E.
  [source-supported inference; research choice to keep the cell]
- **X5 — “All circular candidates” as A's domain.** A is defined only where
  `d_i < N` for every type, so its literal domain is smaller than U1. The
  refinement does not weaken any existing witness (the #32 pair has every
  `d_i ≤ 2 < N = 5`) but corrects the stated universe. [source-supported
  inference; reconciliation §6]
- **X6 — Equivalences coarser than the panels.** No source proposes
  identifying candidates with different composition (e.g. by spectrum); the
  largest source-supported equivalence is dihedral under R-molecule and
  cyclic-shift-only under R-oriented. [source fact]
- **X7 — P admits no finite witness.** If the phrase denotes an objective
  family rather than a formula, no single proof or counterexample settles it,
  because the objective is not fixed. P's 16 cells are therefore excluded from
  witness-sufficiency claims entirely. [interpretation; mathematical fact]
- **X8 — doubled-strand `2G`/`2N` remap as the 2016 data model.** BBT remap
  double-stranded DNA into the single-strand model by concatenating `u` and its
  reverse complement into a length-`2G` `s` with `2N` reads (§2.4). That is a
  genuine length/strand convention in the bridging literature, but no Shomorony
  version uses it — the accepted text's single “reverse complement” mention is
  preprocessing that adds reads, and the model is single-stranded circular `s`
  of length `G` with `N` reads. Reading the 2016 sentence under a `2G`/`2N`
  convention would therefore be a *repository* choice, not a source reading.
  [source fact for both models; interpretation for the exclusion]

---

## 6. Unresolved source gaps (register)

1. **Referent.** No primary source selects among E, A, F, P (§3.1); the
   accepted text, MB09's self-description, the thesis, the 2013 survey, the
   earlier preprint, and the 2013 Ghodsi formulation all bear on it and none
   decides it. [source gap]
2. **Publisher supplement.** The accepted supplementary ZIP (sections A–G)
   returns HTTP 403 (Cloudflare) from every endpoint tried this run. It is the
   last unexamined accepted artifact that could contain a likelihood, length,
   or tie definition. The preprint's own supplement was examined and contains
   no likelihood definition; that does not close the publisher's ZIP.
   [source gap, re-measured 2026-10-09]
3. **MB09 `4^k` vs molecule classes.** Source-internal tension; resolved in
   favour of molecule classes *given §6.2*, but a formalization must name its
   choice. [source-internal tension; §3.2]
4. **Maximizer vs uniqueness.** W vs S is not decided by the sentence or by
   MB09. Contemporary usage leans toward W: Howison, Zapata & Dunn (2013) §5
   define "a maximum likelihood assembly is the assembly that has the highest
   likelihood"; Ghodsi (arXiv:1302.4391v3) notes "the resulting Eulerian graph
   may have many tours, all of which will have equal likelihood," acknowledging
   ties without adopting schema S. Neither source states a tie-break or
   uniqueness claim. [source fact for both quotations; source gap for the
   schema selection; §3.4]
5. **Composition of antecedent and consequent.** Shomorony's bridging
   conditions and MB09's likelihood are never composed by any source (no
   “bridging” in MB09/thesis; no formula in Shomorony). Every reading of the
   2016 sentence is a *proposed composition* of two decoupled formalisms, and
   the bridging hypothesis in the 2016 sense has not been shown to be
   expressible in MB09's read-graph/flow setting. [source-supported inference]
6. **Varma et al. (2011) full text.** Abstract re-verified this run from
   OpenAlex's reproduction only; the publisher artifact is not open access.
   [source gap, minor]
7. **Repository-provenance gap, closed this run.** Two notes referenced by live
   documentation were absent from the working tree:
   `shomorony-ml-quantifier-sequence-resolution.md` (referenced by
   [`../literature/post2016-bridging-ml-citation-chain-2026-09-20.md`](../literature/post2016-bridging-ml-citation-chain-2026-09-20.md)
   §5.3) existed only on the unmerged `analysis/issue36-*` branches and was
   recovered and re-verified here; `shomorony-mb-formulation-referent-reconciliation.md`
   (referenced by name at
   [`../oriented-same-length-ml-88.md`](../oriented-same-length-ml-88.md) §1.3)
   never existed on any branch and was authored here. Several further
   source-notes are still referenced only as unmerged-branch artifacts
   (`se62-feasibility-necessity-determination.md`,
   `mb09-se62-likelihood-index-adversarial-audit.md`,
   `oriented-se62-rigidity-audit-2026-09-20.md`, `se62-revcomp-index-decision.md`,
   `uniform-oriented-rigidity-obstruction.md`, `ml-objective-candidate-class-resolution.md`,
   `primary-provenance-verification.md`, and others); those are **outside this
   front's scope** and are recorded so a later reconciliation pass can land
   them. [repository fact; verified by `git log --all --diff-filter=A`]
8. **Dead provenance locator (new; measured, not repaired).** One *labelled*
   unmerged-branch citation carries a locator that no longer resolves:
   `docs/source-notes/mb09-se61-index-orientation-resolution.md` §5 and its
   cross-reference block cite `docs/source-notes/se62-revcomp-index-decision.md`
   as living on branch `analysis/se62-revcomp-index-decision-0920`, commit
   `7bb1f3a`. **Neither resolves**: the branch is absent from `origin`
   (`git ls-remote origin`, 422 refs) and `7bb1f3a` is not an object in this
   repository (`git cat-file -t` fails). The note is therefore an unverifiable
   citation, not a recoverable one. This is a sibling front's note and is out of
   scope here; it is recorded because the reading inventory's provenance chain
   depends on it. `scripts/audit_source_note_citations.py` detects this class of
   defect by execution (24 resolving citations across 11 distinct notes, 4
   labelled unmerged-branch citations, 1 dead locator). [repository fact;
   verified by execution, 2026-10-09]

---

## 7. Epistemic classification (roll-up)

| Claim | Status | Basis |
|---|---|---|
| 2016 sentence names MB by bibliography only; no section/equation/formula/length/tie pointer | source fact | §2.1 census (3 likelihood, 0 multinomial/binomial, 1 genie) |
| Shomorony model: circular `s`, length `G`, `N` error-free length-`L` reads, uniform, target up to cyclic shift | source fact | §2.1 |
| MB09 §6.1 exact multinomial with candidate-intrinsic `N(D)` and `Σ d_i = N(D)` | source fact | §2.3 quotes |
| MB09 replaces `N(D)` by external `N`, assumes genome size known | source fact | §2.3 quote |
| MB09 §6.2 returns a possibly non-contiguous flow | source fact | §2.3 quote |
| MB09/thesis contain no bridging concept | source fact | §2.3 census (0 “bridg*”) |
| 2010 thesis carries the same exact/fixed-`N` text | source fact | §2.4 |
| Howison/Ghodsi treat known genome size/length as part of the MB-lineage method; Varma's improvement removes it | source fact | §2.4 |
| Howison et al. define ML assembly as the highest-likelihood assembly (W schema) | source fact | §2.4; Howison §5 |
| Ghodsi's prefix graph uses the two-layer read-set model (vertex per read type, counts track multiplicities) | source fact | §2.4; Ghodsi §1 |
| Ghodsi notes equal-likelihood tours exist but does not adopt schema S | source fact | §2.4; Ghodsi §2 |
| BBT cite *two* papers (Myers 1995, MB09) as “maximum-likelihood” formulations | source fact | §2.4 |
| BBT's doubled-strand `2G`/`2N` model is not used by any Shomorony version (X8) | source fact + interpretation | §2.4, §5 |
| E and A rank one pair oppositely; panel flips E's sign only | verified computation | §4.1–4.2, script groups 1–2 |
| Bounded `I_s` agreement of E and A signs | bounded computation | §4.3 |
| `(4^k + p_k)/2` class counts | mathematical fact | §4.4 |
| Universe cardinality 64 = 48 specific + 16 meta; 32 specific sequence-valued | verified computation | §3.5, script group 5 |
| E/A/F/P = the reconciliation's four readings | repository fact | §3.1 |
| P is a meta-family containing E and A | interpretation | §3.5 |
| F is not sequence-valued without a flow→sequence bridge (X1, X2) | interpretation | §5 |
| A's domain is definedness-limited (X5) | source-supported inference | §5 |
| U2 is a restriction without full source support (X4) | source-supported inference | §5 |
| Keeping E/A/F/P distinct in the Lean contract is the repository's choice | research choice | ml-formalization-contract.md |
| Referent, supplement, tie semantics, composition, dead citation locator | source gap | §6 |

---

## 8. Relation to `mb-formulation-referent-reconciliation.md` and the parent matrix

The reconciliation note (2026-09-20) established the four-reading
enumeration, their ranking by textual/named/operative fit, the
sequence-versus-flow structural argument, the fixed-`N` domain refinement, and
the witness-sufficiency matrix. This audit:

- **re-verifies its source facts by execution** this run (all eight ledger
  hashes match, after re-downloading every artifact fresh; every quoted passage
  was re-located in the byte-identical artifacts) — including the two hash
  corrections and extraction-robustness fixes needed to do so, and the
  Bresler–Bresler–Tse retrieval that the recovered quantifier note depends on;
- **keeps its four readings as the O axis** (§3.1) and **imports its §4
  argument as exclusion X1** and its **§6 refinement as exclusion X5**, so the
  two notes are consistent by construction;
- **adds** the finite 64-cell grid with the panel coupling (R), the four
  candidate universes with explicit length conventions (U), the two schemas
  with tie conventions (T), the decision-relevance arithmetic (§4), the full
  exclusion list (§5), the composition gap (§6.5), the lexical exhaustiveness
  sweep (§2.1), the doubled-strand `2G`/`2N` convention and the two-citation
  provenance of the community's “maximum-likelihood” label (§2.4), and the
  re-measured supplement, thesis and citation-provenance gaps (§1, §6).

**Where the two notes differ, and why.** The reconciliation note *ranks* the
four readings (literal text → (4); named ideal → (1); operative method → (2))
and records a best-intended-referent interpretation; this audit deliberately
does **not** rank them, because its mandate is to justify a *finite*
source-supported *universe* rather than to select a member. It also records two
readings the reconciliation note treats as a single flow object: the §6.2
feasible set is split into the sequence-level spelled candidates (`U3`) and
the general flows (`U4`), because the exclusions apply to them differently
(X1 vs X2). The reconciliation note's `4^k`-versus-molecule tension and its
tie-semantics gap are carried over unchanged as §6 items 3–4.

For the parent #217 matrix axes (objective, candidate/length, strand,
bridging, flow, maximizer/ties) the mapping is: objective = O; candidate/length
= U with §3.3's length conventions; strand = R; flow = F/U4 with exclusion X1–X2;
bridging = the composition gap §6.5; maximizer/ties = T with §3.4. The
mathematical per-cell settlement is owned by issues #209–#216 and is
deliberately not duplicated here; the mapping of the repository's already
kernel-checked surfaces onto these cells is recorded in
[`shomorony-mb-formulation-referent-reconciliation.md`](shomorony-mb-formulation-referent-reconciliation.md)
§2, and the sequence-valued quantifier argument that exclusion X1 leans on is
[`shomorony-ml-quantifier-sequence-resolution.md`](shomorony-ml-quantifier-sequence-resolution.md).

## 9. Reproduce

```sh
python3 scripts/verify_finite_interpretation_audit.py                 # pure arithmetic
python3 scripts/verify_finite_interpretation_audit.py --sources DIR   # + hash-verified PDF census
python3 scripts/audit_source_note_citations.py                        # source-note citation provenance
python3 scripts/check-research-docs.py                                # docs integrity incl. digest lengths
```

`DIR` is the artifact cache of §1 (this front's is the untracked
`scratch-208/sources`, which carries its own `sha256sum -c` ledger
`hashes.txt`). `--sources` **fails** when the cache is incomplete: a census
that verified nothing must not report success. `--allow-partial` downgrades
that to a partial check and prints `MISSING` for every absent artifact, so a
partial pass can never be mistaken for a full one.

Primary sources: Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C.
Tse, *Information-optimal genome assembly via sparse read-overlap graphs*,
Bioinformatics 32(17) (2016) i494–i502 (accepted text, author-accepted
manuscript, earlier preprint + supplement); Paul Medvedev, Michael Brudno,
*Maximum Likelihood Genome Assembly*, J. Comput. Biol. 16(8) (2009) 1101–1116,
§3.1, §6.1–6.2; Paul Medvedev, *Genome Graphs*, PhD thesis, University of
Toronto, 2010, Ch. 4; Guy Bresler, Ma'ayan Bresler, David Tse, BMC
Bioinformatics 14(Suppl 5):S18 (2013); Howison, Zapata, Dunn, Bioinformatics
29(23) (2013) 2959–2963; Varma, Ranade, Aluru, ICCABS 2011, 165–170 (abstract);
Mohammadreza Ghodsi, arXiv:1302.4391v3.
