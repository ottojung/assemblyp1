# Is “strict oriented + same candidate length + MB09 §6.2” a source-live reading of the 2016 open question?

_Status: focused source-fidelity determination for the entry condition of issue
#45, 2026-09-21, written against `origin/main` at `f60ca5f`. It answers one
question only: is the conjunction **strict oriented single-strand read types +
fixed candidate length `|D| = G` + Medvedev–Brudno (2009) §6.2 spelled-candidate
feasibility** a formulation that the primary sources actually select, or is it
an artificial strengthening assembled across sources? It does not re-prove the
rigidity theorem of
[`oriented-se62-rigidity-theorem.md`](oriented-se62-rigidity-theorem.md), does
not settle the published question, and does not choose a referent. Every claim
is labelled **source fact**, **mathematical fact**, **source-supported
inference**, **modeling choice**, **interpretation**, or **source gap**._

## 0. Determination

**The conjunction is not a unitary source-live formulation of the published
question.** Each of its three conjuncts is individually motivated by *a* source,
but no primary text selects their intersection, and two of the pairwise
intersections are in direct tension:

| conjunct | individual source status | tension with the conjunction |
|---|---|---|
| strict oriented single-strand read types | **source fact** for Shomorony et al.’s theoretical model (their `I_s` is defined on an oriented circular string) | contradicts §6.2, whose vertices “are the reads, which are DNA molecules” (reverse-complement classes) |
| fixed candidate length `\|D\| = G` | **not a source statement**; at best a **modeling choice** motivated by the known-genome-size operational reading | contradicts §6.1’s exact multinomial, whose length `N(D)` is candidate-intrinsic; and §6.2 fixes no candidate length at all |
| MB09 §6.2 spelled-candidate feasibility | **interpretation** — one of four referents, and an *algorithm* whose output is a possibly non-contiguous flow, not a sequence | the 2016 sentence asks about “the maximum-likelihood **sequence**” |

The decisive source distinction is the one issue #45 names explicitly:
**MB09’s externally known genome size `N` is a parameter of the likelihood, not a
constraint that competitors have length `N`.** “Known `N`” therefore does not
invoke the same-length rigidity theorem, and same-length is an added
restriction. Combined with the oriented/§6.2 strand mismatch, the conjunction is
an **artificial strengthening** — legitimate as a boundary/control probe, but
not a source-live disambiguation of the published question. §5 records the
consequence for the #45 entry condition.

## 1. Primary-source re-verification

The Medvedev–Brudno (2009) quotations below were re-located this run in the
retrieved full text of *Maximum Likelihood Genome Assembly*, *J. Comput. Biol.*
16(8) 1101–1116, PMC3154397 (DOI `10.1089/cmb.2009.0047`). The Shomorony et al.
(2016) quotations were re-located this run in the extracted text of the accepted
typeset article `InfoOptimalAssy.pdf` (SHA-256
`ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043acfce3c4da`, the hash
already recorded on `main`). `N(D)`-vs-`N`, §6.1–6.2 vertex/orientation
semantics, and the Discussion sentence are load-bearing and were read directly
this run. The MB09 §8.2 sentence, the Howison/Varma operational reading, and the
Ghodsi quotation are cited from the repository’s recorded byte-identical
retrievals (see the cross-referenced notes) and are not load-bearing on their
own.

## 2. Known external `N` is not fixed candidate length

### 2.1 The source facts

**MB09 §6.1, exact model (source fact).** “Let `D` be a circular genome of
length `N(D)`, and let `d_i` denote the number of times the `k`-molecule `i`
appears in `D`. … the probability that the outcome of a single trial is `i` is
simply `d_i/N(D)`. … There are `4^k` such variables … the joint distribution is
exactly the multinomial distribution”. The length `N(D)` is **candidate-
intrinsic**; the multinomial constraint `N(D) = Σ_i d_i` ties the candidate’s
length to its own copy-count vector. No common competitor length is imposed:
the argmax ranges over circular genomes `D`, each carrying its own `N(D)`.

**MB09 §6.1, approximation (source fact).** “Since in the binomial approximation
the length of the genome `N(D)` is a constant that is independent of each `d_i`,
we can replace it by `N`, which is the length of the actual genome from which
the reads were sampled. … **For our experiments, we assume that the genome size
is known.**” Here `N` is the fixed denominator of each marginal. The text
*replaces a quantity inside the probability model*; it does **not** add a
constraint `|D| = N` to the candidate class.

**MB09 §6.2 (source fact).** The graph vertices are the reads as molecules; “Each
vertex has a lower bound of `1` since it represents a read that must be present
in the genome at least once. All other lower bounds are `0` and all upper bounds
are infinity.” The optimum is a flow, and “any flow can be decomposed into a
collection of walks, our flow represents a **(non-contiguous) assembly** of the
genome”. There is **no total-flow or candidate-length equation** of the form
`Σ_i d_i = N` or `|D| = G`.

**MB09 §8.2 (source fact).** “Our algorithm relies on having an estimate on the
length of the genome” — again a required *input/parameter*, not a stated
competitor-length restriction.

**Contemporaneous operational reading (source fact).** Howison, Zapata & Dunn
(2013) describe the MB09 ML assembler as requiring “the accurate size of the
target genome” **as a parameter**; Ghodsi (arXiv:1302.4391v3) states “We have to
assume that the length of the genome being assembled (denoted by `L`) is
known.” Both are statements about the likelihood parameter, and Ghodsi is a
different paper, not the cited MB09 formulation.

**Shomorony et al. (2016) (source fact).** In the data-generating model the
*true* genome `s` has fixed length `G`, and reads are sampled independently and
uniformly from its `G` length-`L` substrings. The Discussion sentence says
nothing about the length of a *competitor* in “the maximum-likelihood
formulation of the AP (Medvedev and Brudno, 2009)”.

### 2.2 The distinction, stated exactly

- `N(D)`: the candidate’s own length, an argument of the exact objective.
  Free across competitors. [source fact, §6.1]
- `N`: the true genome size, substituted into the binomial marginals because it
  is assumed known. A **likelihood parameter**, held fixed while optimizing.
  [source fact, §6.1]
- `|D| = G`: a **constraint on the candidate class**. It appears in no MB09
  sentence; it is imposed by the repository’s fixed-length variants. [source gap
  — absence of a source statement]

Conflating the second and third is exactly the error issue #45 warns against.
The integrated conclusion-semantics note already records the same point
([`conclusion-semantics-determination.md`](conclusion-semantics-determination.md)
§2.5; [`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md)
§6.3). [source fact + repository fact]

### 2.3 Why same-length is attractive anyway (and why that is not source-liveness)

If candidate length is **free** under the exact multinomial, the objective is
exactly invariant under tandem repetition `D ↦ D^k` (`N(D^k) = k N(D)`,
`occ(D^k, w) = k·occ(D, w)`, so `occ/N` is unchanged). Every truth `S` is then
tied by `S²`, a distinct and longer candidate, with **no bridging hypothesis at
all**; the strong “unique-up-to-equivalence” schema is false for every truth.
[mathematical fact; recorded in `conclusion-semantics-equivalence-and-length.md`
§3] Same-length is therefore a *repair that makes the strong-schema question
non-vacuous*, and the known-genome-size reading makes it operationally natural.
But “the question is more interesting with a length restriction” is not evidence
that the published sentence *has* that restriction. [interpretation]

## 3. The three conjuncts and their pairwise tensions

### 3.1 Strict oriented single-strand: source-live for `I_s`, not for §6.2

Shomorony et al. define a circular sequence `s` and a set `I_s` on oriented
length-`L` substrings; reverse complements enter only as §4.1 experimental
preprocessing (“before running NOT-SO-GREEDY, we preprocess the set of reads to
include each read and its reverse complement”). Oriented single-strand is thus a
faithful convention for *their* bridging antecedent. [source fact]

MB09 §6.2, by contrast, builds the optimized graph on reverse-complement
molecules: §1.1 “A read … is actually a DNA molecule”; §3.1 “A DNA molecule is
an unordered pair of strings … reverse complements of each other”; §4.1 “each
`k`-molecule is represented only once”; §6.2 “the vertices of this graph are the
reads, which are DNA molecules”. So “strict oriented + §6.2” crosses the two
papers’ strand models and is not a single source’s object. The strand audit
[`uniform-strand-convention-search-2026-09-20.md`](uniform-strand-convention-search-2026-09-20.md)
and the index resolution
[`mb09-se61-index-orientation-resolution.md`](mb09-se61-index-orientation-resolution.md)
established the same mismatch from the computational and the §6.1-index side
respectively. [source fact + source-supported inference]

### 3.2 Same-length against §6.1 and against §6.2

- Against §6.1 exact: `N(D)` is candidate-intrinsic; fixing `|D| = G` is an
  added restriction. [source fact, §2.1]
- Against §6.2: no candidate-length equation exists; the optimum is a flow and
  may be non-contiguous. [source fact, §2.1]

### 3.3 §6.2 is itself a reading and is sequence-incongruent

The 2016 sentence asks whether “the maximum-likelihood **sequence** is the true
sequence”. MB09’s four candidate objects differ on exactly this:

| MB09 object | returns | a sequence? |
|---|---|---|
| exact multinomial (`N(D)`) | circular `D` | yes |
| fixed-`N` binomial | circular `D` | yes |
| §6.2 biflow | flow / non-contiguous assembly | **not necessarily** |
| broad ML principle | unspecified | n/a |

[source fact + interpretation; `mb-formulation-referent-reconciliation.md` §4]
Reading §6.2 directly into a sentence about “the sequence” requires the extra
spelled-circuit step the repository formalizes as support equality. That step is
a reasonable modeling choice; it is not stated by either paper. [source gap]

## 4. What the published question can support

The four source-supported readings of the MB09 phrase
([`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md)
§5) and their relation to the conjunction:

1. **Exact multinomial over circular sequences**, free length. Source-live.
   The strong schema is false by tandem invariance with no bridging. The
   conjunction would add both same-length and §6.2, neither of which this
   reading contains.
2. **Fixed-`N` binomial over circular sequences.** Source-supported as MB09’s
   operative sequence-level method and by Howison/Varma. `N` is a parameter;
   same-length remains an added restriction, and §6.2 is absent.
3. **§6.2 flow.** Live as MB09’s algorithm; gives a flow, and is molecular, so
   “strict oriented” is foreign to it.
4. **Broad ML principle.** No formula; no finite witness or rigidity statement
   settles it.

The conjunction is not one of these. It is the intersection of (an oriented
antecedent borrowed from Shomorony) with (a §6.2 feasibility condition borrowed
from MB09) and (a same-length restriction borrowed from the operational
known-size reading). No primary text selects that intersection. [source gap +
interpretation]

**Strongest source-live defense of the conjunction, and its failure.** The best
case is: “MB09 say the genome size is known, MB09 are molecular, and Shomorony’s
`I_s` is placement-based and orientation-agnostic; so orient the molecule classes
and fix the candidate to the known length.” This fails at two points:
(i) “known `N`” is a likelihood parameter, not `|D| = N` (§2); and (ii) even
granting a fixed length, MB09’s ML object remains molecular, so strict oriented
scoring is still a substitution, not a reading. [interpretation]

## 5. Consequence for the rigidity theorem and the #45 entry condition

The strict-oriented same-length §6.2 rigidity theorem
([`oriented-se62-rigidity-theorem.md`](oriented-se62-rigidity-theorem.md),
`main` `cf6c357`) is a correct and useful **mathematical** result: under `I_s`
(only its triple-repeat clause) the truth’s length-`L` spectrum is the unique
positive circulation of total `G`, so every same-length §6.2 spelled candidate
ties the truth under any `(spec, x)`-objective, and variable length is
essential. [mathematical fact]

Its **source** status, however, is that of a strengthening/control:

- It proves rigidity for a candidate class that is *narrower* than every
  source-live class (§4): it adds same-length and §6.2 to an oriented model.
  A positive result on a narrowing is not a positive result on the published
  question. [interpretation]
- It does not make `oriented + same-length + §6.2` a disambiguation of the 2016
  sentence, and therefore it does not create a “positive finite disambiguation”
  that the #45 entry condition must first settle negatively.
- It remains valuable as evidence: it explains the repository’s bounded oriented
  zeros structurally, and it proves that any strict oriented sequence-level
  counterexample must be variable-length — which is exactly where the integrated
  strict oriented witness `AAATT → AAAAT` lives. [mathematical fact + repository
  fact]

**Determination for #45.** The conjunction falls under case (b) of the #45
comment: an artificial strengthening not selected by the sources. The entry
condition should explicitly exclude it (with this note as the reason), rather
than treating it as a live finite disambiguation that is still positive. The
materially live source disambiguations (referent among readings 1–4; strand
convention; tie/uniqueness/equivalence) remain as recorded on #36, and the
finite negative witnesses continue to cover the source-supported sequence-level
readings. Nothing in this note asserts that #45 is already unlocked; it only
removes the specific obstruction raised by the rigidity theorem.

## 6. What this note does and does not establish

**Does.** It documents, with primary-source quotations, that (a) known external
`N` is a likelihood parameter and not a candidate-length constraint; (b) strict
oriented read types are Shomorony’s convention but not §6.2’s; (c) §6.2 fixes no
candidate length and returns flows; and hence (d) their conjunction is a
cross-source modeling choice, not a source-live reading — the #45 case (b).

**Does not.** It does not choose among the four MB09 referents, does not claim
the published question is settled, does not revise the rigidity theorem or the
integrated witnesses, and does not claim that any source *forbids* the
conjunction — only that none selects it. Whether one may *choose* the
conjunction as a defensible formal target is a separate modeling decision; it is
not the published formulation. [source gap]

## 7. Epistemic classification

| claim | status | basis |
|---|---|---|
| Shomorony `I_s` is defined on an oriented circular sequence; reverse complement is §4.1 preprocessing | source fact | accepted `InfoOptimalAssy.pdf` §§2–3, §4.1, Discussion p. i501 |
| MB09 §6.2 vertices are reads as reverse-complement molecules; lower bound `1`; output may be non-contiguous | source fact | MB09 §1.1, §3.1, §4.1, §6.2 |
| MB09 §6.1 exact objective has candidate-intrinsic `N(D)` and no fixed competitor length | source fact | MB09 §6.1 |
| MB09 §6.1 approximation replaces `N(D)` by external known `N`; `N` is a likelihood parameter | source fact | MB09 §6.1, §8.2 |
| `\|D\| = G` is not stated by any cited source | source gap | absence in MB09 §6.1–6.2, §8.2 and accepted 2016 text |
| Free length makes the strong schema false by tandem invariance, no bridging needed | mathematical fact | `conclusion-semantics-equivalence-and-length.md` §3 |
| `oriented + same-length + §6.2` is a cross-source hybrid, not a source-live reading | interpretation | §§3–4 |
| The rigidity theorem is a narrowing/control, not a settlement of a source-live reading | interpretation | §§4–5 |
| #45 should exclude this conjunction as case (b) | source-analysis recommendation | §5 |

## 8. Cross-references and sources

Repository: [`conclusion-semantics-determination.md`](conclusion-semantics-determination.md)
(§2.5 length; [source gap]); [`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md)
(§6.3 known-`N` vs candidate length); [`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md)
(four referents, §4 sequence-vs-flow); [`mb09-se61-index-orientation-resolution.md`](mb09-se61-index-orientation-resolution.md)
(§6.2 index = molecule classes); [`oriented-se62-rigidity-theorem.md`](oriented-se62-rigidity-theorem.md)
(rigidity theorem); [`uniform-strand-convention-search-2026-09-20.md`](uniform-strand-convention-search-2026-09-20.md)
(witness strand placement); [`same-length-witnesses-candidate-set-inclusion.md`](same-length-witnesses-candidate-set-inclusion.md)
(negative transfer).

Primary: Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
*Information-optimal genome assembly via sparse read-overlap graphs*,
*Bioinformatics* 32(17) (2016) i494–i502, DOI `10.1093/bioinformatics/btw450`;
Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome Assembly*,
*J. Comput. Biol.* 16(8) (2009) 1101–1116, DOI `10.1089/cmb.2009.0047`,
PMC3154397; Mohammadreza Ghodsi, *Constructing a genome assembly that has the
maximum likelihood*, arXiv:1302.4391v3; Howison, Zapata, Dunn, *Toward a
statistically explicit understanding of de novo sequence assembly*,
*Bioinformatics* 29(23) (2013) 2959–2963, DOI `10.1093/bioinformatics/btt525`.
