# Referent reconciliation: “the maximum-likelihood formulation of the AP (Medvedev and Brudno, 2009)”

_Status: independent primary-source reconciliation for issue #36, 2026-09-20.
It re-reads the primary sources and reconciles the claims already recorded in
[`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md),
[`medvedev-brudno-candidate-class.md`](medvedev-brudno-candidate-class.md),
[`shomorony-ml-reference.md`](shomorony-ml-reference.md),
[`same-length-witnesses-candidate-set-inclusion.md`](same-length-witnesses-candidate-set-inclusion.md),
and [`../ml-formalization-contract.md`](../ml-formalization-contract.md).
It does not select a referent by fiat. Every claim is labelled **source fact**,
**source-supported inference**, **mathematical fact**, **interpretation**, or
**source gap**._

## 0. Bottom line

1. The accepted 2016 sentence is qualitative, paper-level, and never names a
   section, equation, objective, candidate class, length convention, or read
   model. **No primary source selects one referent.** (Source fact; §2.1, §3.)
2. Medvedev–Brudno (2009) contain **four** relevant objects, not one: the exact
   global read-count multinomial with candidate-intrinsic `N(D)`; the
   §6.1 separable/binomial approximation with an externally fixed genome length
   `N`; the §6.2 bidirected read-overlap-graph flow; and the underlying ML
   objective/principle. (Source facts; §2.)
3. A structural point that the existing notes do not state explicitly: the
   2016 sentence compares **sequences**. §6.2 returns a *flow*, which MB describe
   as a “(non-contiguous) assembly,” so §6.2 is not a sequence-level referent
   without an extra flow→contig/decomposition step that the source assigns to a
   §7 heuristic. (Source fact + interpretation; §4.)
4. For a *sequence-level* objective, the best operational fit is the fixed-`N`
   binomial approximation, not the exact multinomial: MB call the framework
   “maximum likelihood,” implement it through the fixed-`N` costs, say “we
   assume that the genome size is known,” and the 2010 thesis and 2013 survey
   both present that fixed-size method as *the* MB method. The exact multinomial
   is the named ideal that MB explicitly abandon as not separable.
   (Source-supported interpretation; §5.)
5. Consequently the repository’s fixed-length witnesses bear as follows: the
   #31 exact witness refutes reading 1, the #32 binomial witness refutes
   reading 2 (with one domain caveat, §6), and **neither touches reading 3**
   (the §6.2 feasible class) or settles reading 4 (the unspecified broad
   principle). (Mathematical fact + verified computation; §7.)

This agrees with the earlier provenance note’s caution and adds one refinement
(§6) and one structural argument (§4).

## 1. Independent retrieval and verification

All Shomorony artifacts and the MB09 full text were re-read for this note. The
stable PDF hashes match the ledger already on `main`:

| Artifact | Locator | SHA-256 | Match? |
|---|---|---|---|
| Shomorony et al., OUP-typeset article | `https://people.eecs.berkeley.edu/~courtade/pdfs/InfoOptimalAssy.pdf` | `ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043acfce3c4da` | yes |
| Shomorony et al., author-accepted manuscript | `https://people.eecs.berkeley.edu/~courtade/pdfs/NSG.pdf` | `daeb5b3163d92643affc2398a387217cb57e5e33ce0dd5ebbfccabf621454f2c` | yes |
| Shomorony et al., earlier preprint + supplement | `https://web.stanford.edu/~gkamath/nsgIlan.pdf` | `f2a9f6a64f75cbf4c2cfaec6f794c779907f165c986261bec7a2aa72a3e6954a` | yes |
| Howison–Zapata–Dunn (2013) author PDF | `https://mark.howison.org/Howison-Bioinformatics-2013.pdf` | `bc25681f820b151467df79d7122c5b16a64892b2f15fa3636ace09350762c935` | yes |
| MB09 full text (HTML) | `https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/` | fetched this run `4ba7622346d2da04ca8cb0eee6cd15d60fa1973ad03540014d7c1464e4310194` | **no — ledger `d52c6e89…`** |

**Provenance note (source fact).** The MB09 HTML byte-hash is not reproducible
across fetches (the page carries dynamic markup), so no source claim should rest
on that hash. All MB09 quotations below were re-read from the retrieved text
extraction and cross-checked against the author’s 2010 PhD thesis (below), so the
facts are verified even though the HTML hash drifted.

Additional primary source verified independently for this note:

- Paul Medvedev, *Genome Graphs*, PhD thesis, University of Toronto, 2010,
  Chapter 4 (“Maximum likelihood genome assembly”); handle
  `https://hdl.handle.net/1807/26297`, extracted text bundle
  `https://utoronto.scholaris.ca/server/api/core/bitstreams/5cf61055-a13a-430e-9b9e-20a6be4ff56a/content`.
  The thesis chapter is the dissertation version of MB09 and carries the same
  exact-vs-fixed-`N` text.

## 2. Source facts from Medvedev–Brudno (2009)

### 2.1 §6.1 exact global read-count likelihood (candidate-intrinsic length)

> “Let `D` be a circular genome of length `N(D)`, and let `d_i` denote the number
> of times the `k`-molecule `i` appears in `D`. … In each trial, a position is
> uniformly sampled from `D` and the outcome of the trial is the `k`-molecule
> beginning at that position. For a given `i`, the probability that the outcome
> of a single trial is `i` is simply `d_i/N(D)`. … When taken together, their
> joint distribution is exactly the multinomial distribution …”

The thesis states the same model and the length coupling explicitly:

> “… since the multinomial distribution has the constraint that
> `N(D) = Σ_i d_i`, this is not possible [to make `−log L` separable].”

**Source fact.** The exact objective has candidate-intrinsic length; `N(D)` is
not an external parameter, and the multinomial is defined on the slice
`Σ_i d_i = N(D)`. No fixed candidate length is imposed.

### 2.2 §6.1 separable/binomial approximation (external, known length)

> “Because in the binomial approximation the length of the genome `N(D)` is a
> constant that is independent of each `d_i`, we can replace it by `N`, which is
> the length of the actual genome from which the reads were sampled. The
> approximate length of the actual genome can be ascertained through one of a
> number of biological experiments, or through an Expectation-Maximization type
> approach. **For our experiments, we assume that the genome size is known.**”

The thesis gives the resulting cost verbatim:

> `c_i(d_i) = −(x_i log d_i) − (n − x_i) log(N − d_i)`

**Source fact.** The approximation fixes an external `N` and uses it in every
marginal. The exact multinomial’s `N(D)` has been removed from the objective.

**Source-supported inference (domain).** Because `c_i` contains `log d_i` and
`log(N − d_i)`, the approximation is only defined when `0 < d_i < N` for every
type `i`. The exact multinomial has no such bound (it is defined whenever
`D` is nonempty, since `Σ_i d_i = N(D)` automatically makes `d_i ≤ N(D)`). This
asymmetry is used in §6.

### 2.3 §6.2 bidirected read-overlap-graph flow

> “The first step is to build a bidirected overlap graph from the set of reads,
> which are DNA molecules. The vertices of this graph are the reads … Each vertex
> has a lower bound of 1 since it represents a read that must be present in the
> genome at least once. All other lower bounds are 0 and all upper bounds are
> infinity. … By Observation 7, the `d_i`’s described above actually correspond
> to the value of the flow through vertex `i` … Since any flow can be decomposed
> into a collection of walks, our flow represents a **(non-contiguous) assembly**
> of the genome …”

**Source fact.** The feasible objects are flows in a read-derived graph; the
output need not be a single sequence; actual sequences are produced later by a
§7 heuristic.

### 2.4 MB09’s own naming of “the maximum likelihood framework”

From the abstract and §6 title:

> “we propose a **maximum likelihood framework** for assembling the genome that
> is the most likely source of the reads … **In this setting**, we give a
> bidirected network flow-based algorithm that … accurately estimates the copy
> counts of repeats.”

> §6: “Predicting Copy-Counts Using Maximum Likelihood.”

**Source fact.** MB’s concrete, namesake ML object is the copy-count flow built
on the fixed-`N` approximation. The exact multinomial is *not* what their method
optimizes; the thesis itself says so (§2.1).

## 3. Source facts about how the term was read

- **Howison, Zapata & Dunn (2013), §5** (source fact): the Medvedev–Brudno ML
  assembler “requires as a parameter the accurate size of the target genome,”
  contrasted with Varma et al. (2011), which “starts from an approximate size and
  estimates the actual size during the optimization.”
- **Varma, Ranade & Aluru (2011)** (source fact): a paper titled “An Improved
  Maximum Likelihood Formulation …” whose advertised improvement is genome-size
  handling. This confirms that, in the community reading, genome-size treatment
  was *part of* the MB formulation.
- **Shomorony et al. earlier author-hosted preprint** (source fact, verified
  independently): the discussion of optimization formulations said the way to
  avoid repeat over-collapsing “is to consider a genie-aided formulation where
  the target genome length `G` is given.” The accepted text's corresponding
  passage instead carries the parsimony-vs-maximum-likelihood contrast and the
  paper-level Medvedev–Brudno open-question sentence; its only “genie-aided”
  occurrence concerns tuning the string-graph overlap parameter, not the ML
  formulation. (The version relationship is thus version evidence about the
  authors' framing, not a claim about a precise edit history.)

**Interpretation.** The same authors, one version earlier, framed the relevant
combinatorial optimization as a fixed-`G` problem. That does not make the
accepted sentence fixed-length (the accepted text dropped the passage), but it
is direct evidence about the authors’ mental model of the optimization they were
contrasting with parsimony.

## 4. The structural point: the sentence compares sequences, not flows

The 2016 sentence is about “the maximum-likelihood **sequence**.” MB09’s four
objects differ precisely on whether a sequence is returned:

| Object | What the optimization returns | Is it a sequence? |
|---|---|---|
| exact multinomial | a circular genome `D` | yes |
| fixed-`N` binomial | a circular genome `D` (scores `d_i`) | yes |
| §6.2 flow | a flow / “(non-contiguous) assembly” | **not necessarily** |
| broad ML principle | unspecified | n/a |

**Interpretation.** If Shomorony meant §6.2 literally, the phrase “the
maximum-likelihood sequence” would be a category error: §6.2 does not optimize
over sequences. The natural repair — restrict §6.2 to single-circuit supports —
is not stated in either paper and is not how MB describe the output (they route
the single-sequence question to a §7 heuristic). This is evidence *against*
reading 3 as the direct referent, independently of the length question. It is
also why a §6.2-feasible *flow* counterexample would not by itself answer a
question phrased about sequences.

## 5. The four readings, re-ranked

| Reading | What is denoted | Source support |
|---|---|---|
| (1) exact multinomial, candidate-intrinsic `N(D)` | MB09’s named “global read-count likelihood” | Named as the target; explicitly abandoned as not separable; no section pointer from 2016 |
| (2) §6.1 binomial, externally fixed true `N` | MB09’s operative sequence-level objective | MB’s framework/“assume genome size known”; thesis; Howison; Varma; the authors’ own fixed-`G` preprint framing |
| (3) §6.2 bidirected flow | MB09’s algorithm | MB call it the algorithm; returns a non-contiguous flow, not a sequence |
| (4) broad ML principle/objective family | “formulations” contrast in Shomorony | The accepted text fixes no formula; safest literal reading |

**Reconciliation of the two earlier ranks.** The provenance note ranked (4)
strongest by *literal textual fit* and (2) as the *operative* formulation. The
candidate-class note called (1) the “most literal” referent of the word
“formulation.” Both can hold because they measure different things: (4) is what
the sentence *says*; (1) is what the cited paper *names* as its likelihood; (2)
is what the cited paper *does*. The repository should treat “literal text,”
“named ideal,” and “operative method” as three axes, not one.

**Interpretation (well supported).** If one is forced to name the most likely
*intended mathematical referent* for a sequence-level statement, it is reading
(2): it is the MB objective that is actually posed, sequence-valued, and
consistent with the authors’ own prior fixed-`G` framing. This does **not**
upgrade reading (2) to a source fact.

## 6. Refinement: reading (2)’s candidate universe is not “all circular genomes”

[`same-length-witnesses-candidate-set-inclusion.md`](same-length-witnesses-candidate-set-inclusion.md)
§4 correctly transfers the negative result from the length-`G` subclass to any
superclass. For reading (2) the phrase “all circular candidates” must be read as
“all circular candidates on which the binomial objective is defined,” because
`c_i(d_i)` is undefined when `d_i ≥ N` (log of a nonpositive number), while for
reading (1) the objective is defined on every nonempty candidate.

This does not weaken the transfer: the #32 witness pair `AAACC` / `AAAAC` has
`|S| = |D| = N = 5` and every `d_i ≤ 2 < N`, so it lies in reading (2)’s domain.
The correction is to the stated universe, not to the refutation.

## 7. Witness-sufficiency matrix for the published question

“Refutes `truthIsML`” means: with the source bridging hypothesis `R ∈ I_s`
holding, a candidate strictly more likely than the truth exists.

| Reading | Objective / class | Status of current kernel-checked witnesses |
|---|---|---|
| (1) | exact multinomial, candidate-intrinsic `N(D)` | **Refuted** by #31 (`AAABB → AAAAB`, ratio 2) and the read-tiled witness, over all nonempty circular candidates, by candidate-set inclusion |
| (2) | fixed-`N` product of binomial marginals | **Refuted** by #32 (`AAACC → AAAAC`, ratio `1125/512`) on reading (2)’s domain; same-length pair, so inclusion transfers |
| (3) | §6.2 flow feasible set | **Not refuted.** No witness has both the truth and the competitor in the sequence-level §6.2 feasible set; and the phrase is sequence-level (§4), so even a feasible *flow* would need a flow→sequence bridge |
| (4) | broad principle | **Not refuted and not refutable by one witness**; the objective itself is not fixed by the source |

Consequences:

1. A negative settlement of the published question under reading (1) or (2) is
   already available in the repository, conditional on a source argument fixing
   the referent to that reading.
2. Under reading (3) or (4) the question remains open. The live mathematical
   residue is whether a bridged, sequence-level §6.2-feasible truth can be beaten
   by another feasible flow, and the live source residue is whether the 2016
   sentence can be shown to intend reading (3) or (4).

## 8. Unresolved register

1. **Referent.** No primary source selects among readings (1)–(4). The accepted
   text, the MB09 self-description, the thesis, the 2013 survey, and the earlier
   Shomorony preprint all bear on it but none decides it.
2. **Read-type space.** MB09 §6.1 writes “There are `4^k` such variables” while
   its model vocabulary is `k`-*molecules* (unordered reverse-complement pairs,
   `(4^k + p_k)/2` classes). The formula and the vocabulary are inconsistent; a
   formalization must name which it uses. This is orthogonal to the length
   question and does not change §7, but it changes what `x_i` and `d_i` index.
3. **Genome equivalence.** Shomorony’s theory uses cyclic shift only; MB09’s
   object is a double-stranded molecule (reverse complement). The 2016 sentence
   does not say which applies to the ML comparison.
4. **Conclusion semantics.** “the maximum-likelihood sequence is the true
   sequence” still does not disambiguate truth-is-a-maximizer from
   all-maximizers-are-truth.
5. **Publisher supplement.** The accepted supplement (sections A–G) remains
   uninspected (HTTP 403); it is the last unexamined accepted artifact that
   could contain a likelihood definition. It is a single PDF
   (`supp_material.pdf`), not a ZIP, and the accepted article's own inline
   pointers into A, B, C, E, F, G are all algorithm/proof/Lander–Waterman
   rather than likelihood; see
   [`shomorony-supplement-referent-evidence.md`](shomorony-supplement-referent-evidence.md).

## 9. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| Shomorony names MB only by paper-level bibliography; no section/equation/formula | source fact | accepted text §5 + full-text scan |
| MB09 §6.1 defines the exact multinomial with candidate-intrinsic `N(D)` and constraint `Σ d_i = N(D)` | source fact | MB09 §6.1 and 2010 thesis Ch. 4 |
| MB09 replaces `N(D)` by external `N` and assumes genome size known | source fact | MB09 §6.1; thesis |
| MB09 §6.2 returns a possibly non-contiguous flow, not a sequence | source fact | MB09 §6.2 |
| The 2013 survey and Varma treat MB ML as requiring a known genome size | source fact | Howison et al. §5; Varma et al. title/abstract |
| The 2016 preprint earlier framed the optimization as fixed-`G` | source fact | `nsgIlan.pdf` |
| Reading (4) is the safest literal reading of the sentence | interpretation | §5 |
| Reading (2) is the best operational sequence-level fit | interpretation | §5 |
| Reading (3) is a poor direct referent for the word “sequence” | interpretation | §4 |
| Reading (2)’s domain excludes `d_i ≥ N` | source-supported inference | §6 |
| The fixed-length witnesses refute readings (1) and (2) | mathematical fact + kernel-checked instances | §7 |
| Readings (3)–(4) remain open | source analysis + verified computation | §7–§8 |

## 10. Relation to existing repository documents

- [`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md)
  records the same source facts and the formulation-vs-algorithm split; this note
  adds the sequence-vs-flow argument (§4), the reading-(2) domain refinement
  (§6), and the independently verified 2010 thesis.
- [`medvedev-brudno-candidate-class.md`](medvedev-brudno-candidate-class.md) and
  [`shomorony-ml-reference.md`](shomorony-ml-reference.md) establish the
  exact/approximation/flow separation and the accepted-text ambiguity; this note
  does not revise their source facts.
- [`same-length-witnesses-candidate-set-inclusion.md`](same-length-witnesses-candidate-set-inclusion.md)
  supplies the candidate-set inclusion used in §7; its “all circular candidates”
  phrasing for reading (2) is refined in §6.
- [`../ml-formalization-contract.md`](../ml-formalization-contract.md) keeps
  Variants E/A/F and the two conclusion schemas separate; this note supports
  keeping that separation rather than collapsing it.

Primary sources: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, J. Comput. Biol. 16(8) (2009) 1101–1116, §6.1–6.2, PMC3154397;
Paul Medvedev, *Genome Graphs*, PhD thesis, University of Toronto, 2010, Ch. 4;
Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
*Information-optimal genome assembly via sparse read-overlap graphs*,
Bioinformatics 32(17) (2016) i494–i502, §2 and §5, DOI
`10.1093/bioinformatics/btw450`; Howison, Zapata, Dunn, *Toward a statistically
explicit understanding of de novo sequence assembly*, Bioinformatics 29(23)
(2013) 2959–2963, DOI `10.1093/bioinformatics/btt525`; Varma, Ranade, Aluru,
*An Improved Maximum Likelihood Formulation for Accurate Genome Assembly*,
ICCABS 2011, DOI `10.1109/ICCABS.2011.5729873`.
