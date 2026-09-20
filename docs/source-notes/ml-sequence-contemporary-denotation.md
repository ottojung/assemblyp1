# What “the maximum-likelihood sequence” denotes: newly retrieved contemporary evidence

_Status: independent primary-source audit for issue #36, 2026-09-20. This note
records **only material not already present** in
[`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md),
[`shomorony-ml-quantifier-sequence-resolution.md`](shomorony-ml-quantifier-sequence-resolution.md),
[`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md),
[`shomorony-ml-reference.md`](shomorony-ml-reference.md),
[`medvedev-brudno-candidate-class.md`](medvedev-brudno-candidate-class.md),
[`se62-feasibility-necessity-determination.md`](se62-feasibility-necessity-determination.md),
[`../literature/ml-tie-semantics.md`](../literature/ml-tie-semantics.md),
or the citation-context audit
[`../literature/citation-context-and-referent-audit-2026-09-20.md`](../literature/citation-context-and-referent-audit-2026-09-20.md).
Every claim is labelled **source fact**, **source-supported inference**,
**interpretation**, or **correction**. It does not settle the published question
and does not select a referent by fiat._

## 0. New findings only

1. **Length axis.** M. Ghodsi, *Constructing a genome assembly that has the
   maximum likelihood* (arXiv:1302.4391v3, 2016), a contemporaneous
   ML-assembly paper that cites Medvedev–Brudno (2009) for the sequencing model,
   states the assembly problem as maximizing the probability of a **superstring
   `A` of known length `L`**, and explains that `L` must be fixed because
   otherwise the objective is scale-invariant and admits infinitely many
   equal-value solutions. (Source fact; §1.)
2. **Tie axis.** The same paper states that the rounded solution “may have many
   tours, all of which will have equal likelihood. Therefore any final solution
   (assembled sequence) is, by itself, only one of many possible solutions.”
   (Source fact; §1.)
3. **MB09 self-label.** The *published* MB09 discussion calls its own object a
   “maximum likelihood framework for **sequence assembly**” (source fact; §2),
   even though the §6.2 algorithm returns a flow.
4. **Same-author tie statement.** Medvedev & Pop (2021) state “a genome
   reconstruction is never unique” (source fact; §3).
5. **Provenance corrections.** The accepted Shomorony supplement’s canonical
   filename is `btw450_supplementary_data.zip`; the accepted JCB PDF of MB09 is
   retrievable and byte-verified; and two existing repository claims about
   Ghodsi are wrong. (§4–§5.)

## 1. Ghodsi (2013 / v3 2016): the ML object is a known-length superstring

**Citation (source fact).** Mohammadreza Ghodsi, “Constructing a genome
assembly that has the maximum likelihood,” arXiv:1302.4391v3 [cs.CE], 7 Apr
2016 (v1 posted 2013-02-18). Retrieved PDF
`https://arxiv.org/pdf/1302.4391`, SHA-256
`6af4c06a37b46afef3961613d62e67fa8375c801b1c4a6a2ea12e256ddd9716c`.
Reference `[2]` is Medvedev & Brudno, *Maximum likelihood genome assembly*,
J. Comput. Biol. 16(8):1101–1116, 2009.

### 1.1 Abstract and §1: the ML sequence is a superstring

Abstract, p. 1 (source fact):

> “We formulate genome assembly problem as an optimization problem in which the
> objective function is the likelihood of the assembly given the reads.”

§1 Introduction, p. 1 (source fact):

> “The likelihood of an assembly is proportional to the probability of observing
> the sequenced reads, if so many reads were generated from the assembled
> sequence according to the sequencing model `[2, 1]`. Therefore, given a set of
> reads `R`, the genome assembly problem is to find a superstring `A`, which
> maximizes the probability of observing `R` [eq. (1)]:
> where `n_i` is the number of times read `i` ‘appears’ in `A`, and `L` is the
> length of `A`.”

(The exact exponent of `(n_i/L)` in eq. (1) is not resolved by text extraction;
the prose identification of `n_i` and `L` is unambiguous.)

**Source fact.** A contemporaneous ML-assembly formulation — citing MB09 as the
sequencing model — takes the optimized object to be a **single candidate
sequence (superstring) `A`**, not a flow.

### 1.2 §2 and its footnote: the candidate length is assumed known

§2 “A tractable optimization formulation,” opening of p. 2 (source fact):

> “We first express finding an optimal walk in terms of an integer programming
> problem. We have to assume that the length of the genome being assembled
> (denoted by `L`) is known.”

Footnote 5, p. 2 (source fact):

> “In general, the length of the genome can not be estimated using random
> fragments only. However, assuming most of the genome is non-repetitive, the
> length of the genome can be estimated. There are many exceptions to this
> assumption; notably polyploid organisms.”

Appendix B (“Authors Note”), bullet “Assembly length,” p. 6 (source fact):

> “We assume assembly length is known, and is a constant in the optimization.
> This is due to the fact that if `L` was a variable in (2)–(6), for any solution
> with a particular objective value, one can construct an infinite set of
> solutions with the same objective value by scaling the variables `x_{i,j}`,
> `n_i`, and `L`.”

**Source fact + interpretation.** In this ML formulation the candidate’s own
length appears in the objective (eq. (1)), but the optimization **fixes that
length to the known true genome length**. The stated justification is exactly
the scale-degeneracy that a free candidate length would introduce. This is
independent, contemporaneous evidence that the community meaning of “the
maximum-likelihood assembly/sequence” was a **fixed-length sequence** object,
matching MB09 §6.1’s replacement of `N(D)` by the externally supplied `N` and
consistent with issue #36 reading (2).

### 1.3 §3: the ML sequence is not unique

§3 “Constructing an assembly from an optimal fractional solution,” pp. 2–3
(source fact):

> “The rounding procedure must preserve the Eulerian property: for all vertices,
> in-degree must be equal to out-degree. Note that the resulting Eulerian graph
> may have many tours, all of which will have equal likelihood. Therefore any
> final solution (assembled sequence) is, by itself, only one of many possible
> solutions.”

Also §3, p. 3: “Any Eulerian cycle (or set of cycles) has the same likelihood.”
And Appendix B (“Authors Note”), p. 6: “All Eulerian cycles of the rounded
solution will have equal likelihood.”

**Source fact.** A contemporaneous ML-assembly source treats **maximal
likelihood as attained by many distinct sequences**. The singular phrase “the
maximum-likelihood sequence” therefore cannot, on this reading, be assumed to
denote a unique maximizer; a tie/equivalence convention is genuinely needed to
make the Shomorony conclusion well-posed. (This supplies the full quotation for
the witness the repository already cited only in paraphrase: see
`../literature-search-citation-graph-2026-09-19.md`, “Effect on the Lean model
and theorem statement,” item 3.)

## 2. MB09 published text: “maximum likelihood framework for sequence assembly”

**Citation (source fact).** P. Medvedev, M. Brudno, “Maximum Likelihood Genome
Assembly,” *J. Comput. Biol.* 16(8):1101–1116, 2009. Published PDF retrieved
`https://medvedevgroup.com/papers/jcb09.pdf`, SHA-256
`bfeaec37de55e87c35438108c33a8052f0fd6eb56f2903bb1d50d2793d8a5aa3`
(16 PDF pages; journal pagination confirmed as pp. 1101–1116).

§9 Discussion, PDF p. 15 (journal p. 1115) (source fact):

> “We have also introduced a maximum likelihood framework for **sequence
> assembly**, and shown that bidirected flow can be used to give a practical and
> efficient algorithm in this context.”

**Source fact.** MB’s own retrospective label for the framework is *sequence
assembly*, even though the §6.2 algorithm returns a “(non-contiguous)
assembly.” This is additional primary-source support that the MB ML object is
sequence-level, reinforcing the sequence-vs-flow argument already recorded in
`mb-formulation-referent-reconciliation.md` §4 and
`se62-feasibility-necessity-determination.md` §4.

## 3. Medvedev & Pop (2021): reconstruction is never unique

**Citation (source fact).** P. Medvedev, M. Pop, “What do Eulerian and
Hamiltonian cycles have to do with genome assembly?,” *PLoS Comput. Biol.*
17(5):e1008928, 2021, DOI `10.1371/journal.pcbi.1008928`, PMC8136698.
Abstract (source fact):

> “We give 2 arguments. The first is that **a genome reconstruction is never
> unique** and hence an algorithm for finding Eulerian or Hamiltonian cycles is
> not part of any assembly algorithm used in practice.”

**Interpretation.** MB09’s author, writing a formulation tutorial, states that
genome reconstruction is generically non-unique. This is not itself a statement
about ties among likelihood *maximizers*, so it does not resolve the
truth-is-*a*-maximizer vs all-maximizers-are-truth question; it is recorded only
as same-author background supporting that an equivalence/tie convention is
required before “the ML sequence is the true sequence” has a unique reading.

## 4. Accepted-supplement provenance (new)

**Source fact.** The 2018 Wayback Machine capture of the OUP article page
(`https://web.archive.org/web/20180605042822id_/https://academic.oup.com/bioinformatics/article/32/17/i494/2450780`)
exposes the accepted supplement under the filename

```
btw450_supplementary_data.zip
```

on `oup.silverchair-cdn.com/.../10.1093_bioinformatics_btw450/3/`, behind a
time-limited CloudFront signature (`Expires=1528266505`, i.e. 2018-06-06). The
signature is long expired and returns HTTP 403; a Wayback CDX query for the
supplement’s CDN path returns **no** archived copy, and Europe PMC/PMC hold metadata only
(`inPMC = N`, `inEPMC = N`). The accepted supplement therefore remains
unretrieved. (Correction: `shomorony-ml-reference.md` §“What remains to check”
guesses the filename `bioinformatics_32_17_i494_s1.zip`; the published link uses
`btw450_supplementary_data.zip`.)

## 5. Repository corrections forced by this audit

1. **`../literature/shomorony-group-post2016-identifiability-2026-09-20.md`
   §4** describes Ghodsi’s formulation as one “with … no fixed candidate
   length.” **This is wrong** (source fact): Ghodsi §2 and Appendix B explicitly assume
   the genome length is known and constant in the optimization, while eq. (1)
   writes the candidate length in the objective. The correct characterization is
   “superstring of *known/fixed* length”; see §1.2.
2. **`../literature-search-citation-graph-2026-09-19.md`** states that
   `../literature/ml-tie-semantics.md` “now cites” Ghodsi. **It does not**
   (grep finds no occurrence of `Ghodsi` in that file). The Ghodsi tie evidence
   is recorded in paraphrase only in the citation-graph note; the exact quotation
   is supplied here (§1.3).

## 6. Bearing on the issue #36 readings

| Issue #36 reading | What the new evidence adds |
|---|---|
| (1) exact multinomial, candidate-intrinsic `N(D)` | Ghodsi’s eq. (1) has the candidate length in the objective, like `N(D)`, but he immediately fixes it (§1.2). So a leading contemporaneous ML formulation is *not* optimized over variable-length candidates. |
| (2) §6.1 binomial, externally fixed `N` | Directly supported on the length axis: Ghodsi fixes the length to the known genome length and gives the scale-invariance reason (§1.2). Supports the known/fixed-length reading. |
| (3) §6.2 flow | The new MB09 phrase “framework for sequence assembly” (§2) is additional evidence that the MB object is sequence-valued, weighing against a literal flow referent. |
| (4) broad ML principle | Not addressed; the new sources fix a concrete objective, so they do not support reading the 2016 sentence as objective-free. |
| Tie/equivalence semantics | Ghodsi (§1.3) gives a contemporaneous source in which many distinct sequences attain maximum likelihood. This strengthens the repository’s decision to keep “truth is *a* maximizer” and “all maximizers are truth” separate. |

**Interpretation (bounded).** The new evidence reinforces the sequence-level,
known-length reading and the non-uniqueness of optima. It does **not** show that
Shomorony et al. intended Ghodsi’s specific objective, and it does **not** settle
which of the exact multinomial, the §6.1 binomial, or a broader principle the
2016 citation names. The referent remains underdetermined by the primary text.

## 7. Retrieval ledger

| Artifact | Locator | SHA-256 |
|---|---|---|
| MB09 published JCB PDF | `https://medvedevgroup.com/papers/jcb09.pdf` | `bfeaec37de55e87c35438108c33a8052f0fd6eb56f2903bb1d50d2793d8a5aa3` |
| Ghodsi, arXiv:1302.4391v3 | `https://arxiv.org/pdf/1302.4391` | `6af4c06a37b46afef3961613d62e67fa8375c801b1c4a6a2ea12e256ddd9716c` |
| Shomorony accepted PDF (re-verified) | `InfoOptimalAssy.pdf` | `ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043acfce3c4da` |
| Shomorony author-hosted preprint + supplement (re-verified) | `nsgIlan.pdf` | `f2a9f6a64f75cbf4c2cfaec6f794c779907f165c986261bec7a2aa72a3e6954a` |
| Medvedev–Pop 2021 | PMC8136698, `10.1371/journal.pcbi.1008928` | dynamically generated HTML; not hash-stable |
| Accepted supplement | `btw450_supplementary_data.zip` (expired signed URL only) | **unretrieved (403)** |

Re-verified independent full-text counts for the accepted Shomorony article
(`InfoOptimalAssy.txt`): `likelihood` occurs 3 times, `multinomial` 0,
`binomial` 0; the only `open question` occurrence is the Discussion sentence.

## 8. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| Ghodsi formulates ML assembly as maximizing `Pr[R|A]` over a superstring `A` | source fact | Ghodsi abstract, §1, p. 1 |
| Ghodsi assumes the genome/assembly length is known and fixed, citing scale invariance | source fact | Ghodsi §2, footnote 5, Appendix B (pp. 2, 6) |
| Ghodsi states many Eulerian tours have equal likelihood and the assembled sequence is only one of many | source fact | Ghodsi §3 (pp. 2–3), Appendix B (p. 6) |
| MB09’s published discussion calls the framework one for “sequence assembly” | source fact | MB09 JCB PDF, §9, p. 15 |
| Medvedev & Pop 2021 state “a genome reconstruction is never unique” | source fact | PMC8136698, abstract |
| The accepted supplement is named `btw450_supplementary_data.zip` and is unretrieved | source fact | 2018 Wayback capture; CDX; EPMC metadata |
| Ghodsi’s formulation fixes the candidate length | source fact (correction) | Ghodsi §2, Appendix B |
| The new evidence supports a sequence-level, known-length, non-unique-optima reading | interpretation | §1–§3, §6 |
| The 2016 referent remains underdetermined among (1)–(4) | source gap | §6 |
