# Independent verification: citation context of the 2016 Shomorony open question

_Status: independent source verification, 2026-09-20, for issue #36. A second
toolchain re-retrieved the controlling artifacts and re-read the in-text
citation contexts of
[`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md).
It confirms every substantive source fact there, records two provenance
corrections (one typographic, one about hashing HTML), and adds the
accepted-manuscript numbered-citation detail. It does **not** settle the
published open problem and does not touch the Section 6.2 flow-feasibility
question._

## 0. Method and relation to the existing note

This note was produced by re-retrieving the primary artifacts with `urllib`,
`pypdf` 6.19.0, the Crossref REST API, and the NCBI E-utilities/Europe PMC
metadata APIs, then reading the displayed text directly. It is a corroboration,
not a re-derivation of the interpretation:

- source facts below are independently reproduced;
- the ranking of the four candidate readings is left to
  [`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md)
  §6 and is not re-litigated here.

## 1. Artifact ledger (independently retrieved this run)

| Artifact | Locator | Bytes | SHA-256 |
|---|---|---|---|
| Published article (OUP typeset, Berkeley mirror) | `https://people.eecs.berkeley.edu/~courtade/pdfs/InfoOptimalAssy.pdf` | 715274 | `ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043acfce3c4da` |
| Author-accepted manuscript | `https://people.eecs.berkeley.edu/~courtade/pdfs/NSG.pdf` | 1208034 | `daeb5b3163d92643affc2398a387217cb57e5e33ce0dd5ebbfccabf621454f2c` |
| Howison–Zapata–Dunn (2013) author PDF | `https://mark.howison.org/Howison-Bioinformatics-2013.pdf` | 168236 | `bc25681f820b151467df79d7122c5b16a64892b2f15fa3636ace09350762c935` |
| Medvedev–Brudno (2009) full text | `https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/` | — | HTML (see §4.2; hash not stable) |

The two Shomorony hashes match the ledger in
`shomorony-mb-formulation-provenance.md` §2 and the older
[`primary-provenance-verification.md`](primary-provenance-verification.md) §1
byte-for-byte. The Howison author-PDF hash matches the main note's ledger
exactly. So the note's quotations are read from byte-identical artifacts.

## 2. The exact citation context (independently reproduced)

### 2.1 The open-question paragraph is the final paragraph of Discussion §5

Source fact: the accepted typeset has exactly five section headings
(`1 Introduction`, `2 Preliminaries`, `3 Methods`, `4 Results`, `5 Discussion`);
the open-question paragraph is the last paragraph of `5 Discussion`, and the
next content is `Acknowledgements`.

Verbatim from `InfoOptimalAssy.pdf` (line breaks normalised):

> "Another direction for future work, from a more theoretical standpoint, is
> understanding whether, in information-feasible instances of the AP, the output
> of NOT-SO-GREEDY coincides with the solution of a combinatorial optimization
> problem. Notice that while Theorem 1 guarantees the reconstruction of the true
> sequence s, there is no guarantee that this sequence corresponds to the
> solution of an optimization-based formulation of the AP such as those
> considered by Nagarajan and Pop (2009) and Medvedev and Brudno (2009). As
> mentioned by Medvedev and Brudno (2009), parsimony-based formulations tend to
> encourage an over-collapsing of the repeats, and the optimal solution is in
> general different from the true underlying sequence. The maximum-likelihood
> formulation of the AP (Medvedev and Brudno, 2009), on the contrary, seems to be
> robust to these issues, and thus a good candidate for the 'correct'
> formulation. Understanding whether bridging conditions can be used to
> guarantee that the maximum-likelihood sequence is the true sequence is
> currently an open question."

### 2.2 All in-text occurrences of the reference

Source fact: the accepted typeset contains exactly five in-text occurrences of
the string `Medvedev and Brudno`, in three distinct argumentative roles:

1. Introduction — attributed credit for the parsimony criticism:
   > "As pointed out by Medvedev and Brudno, 2009, parsimony-based formulations
   > can fail at producing the true sequence because long repeats tend to be
   > under-represented in the shortest sequence that is consistent with the
   > data."
2. End of Introduction — the paper's own lineage:
   > "The present paper should be understood as following the line of work of
   > Medvedev and Brudno (2009), Nagarajan and Pop (2009) and Medvedev et al.
   > (2007) in the study of the basic formulation of the AP and the computational
   > challenges associated with it..."
3. Discussion §5 — three occurrences inside the open-question paragraph
   (grouped as an optimization-based formulation; the parsimony attribution;
   and the maximum-likelihood formulation).

None of the five carries a section, equation, figure, theorem, or page pointer
into Medvedev–Brudno. This is the central negative source fact: the citation is
paper-level only.

### 2.3 Bibliography entry and its identity

Source fact, accepted typeset References (printed p. i502):

> "Medvedev,P. and Brudno,M. (2009) Maximum likelihood genome assembly.
> *J. Comput. Biol.*, **16**, 1101–1116."

Source fact, accepted manuscript (`NSG.pdf`) reference `[8]`:

> "[8] Paul Medvedev and Michael Brudno. Maximum likelihood genome assembly.
> Journal of computational Biology, 16(8):1101–1116, 2009."

Independent confirmation of the entry via Crossref, `api.crossref.org/works/10.1093/bioinformatics/btw450`
(the DOI's deposit lists its own 28 references): reference key
`...btw450-B13`, `author: Medvedev`, `year: 2009`,
`article-title: Maximum likelihood genome assembly`,
`journal-title: J. Comput. Biol`, `volume: 16`, `first-page: 1101`,
`DOI: 10.1089/cmb.2009.0047`. The same deposit separately lists
`...btw450-B19`, `author: Medvedev`, `year: 2007`,
`doi: 10.1007/978-3-540-74126-8_27` — the distinct parsimony/flow paper
(Medvedev, Georgiou, Myers, Brudno, "Computability of models for sequence
assembly"). So the 2009 citation is unambiguously the ML paper, not the 2007
flow paper.

### 2.4 Citation style differs between the two accepted artifacts

Source fact: the accepted manuscript cites numerically — "the maximum
likelihood formulation of the AP [8]" — while the publisher typeset renders the
same object as "(Medvedev and Brudno, 2009)". Reference `[8]` is Medvedev &
Brudno 2009. This is version/typography evidence only; it does not add or remove
a subsection pointer.

## 3. Medvedev–Brudno self-description (independently reproduced)

Verbatim, `PMC3154397`:

- Abstract:
  > "Furthermore, we propose a maximum likelihood framework for assembling the
  > genome that is the most likely source of the reads, in lieu of the standard
  > maximum parsimony approach (which finds the shortest genome subject to some
  > constraints). In this setting, we give a bidirected network flow-based
  > algorithm that, by taking advantage of high coverage, accurately estimates
  > the copy counts of repeats in a genome."
- §1.2 "Maximum likelihood genome assembly":
  > "We formulate the problem of genome assembly as maximizing the likelihood of
  > the observed read frequencies, rather than minimizing the length of the
  > genome. This problem can be formulated as a minimum cost bidirected flow
  > (biflow) problem with convex costs..."
- §6 introduction:
  > "In this section, we describe our maximum likelihood framework for genome
  > assembly, and give an algorithm that, given a set of reads (DNA molecules),
  > finds the genome that maximizes the global read-count likelihood."
- §6.1 exact objective: multinomial with per-type probability `d_i / N(D)` and
  `N(D) = Σ_i d_i`; candidate `D` is "a circular genome of length `N(D)`".
- §6.1 approximation:
  > "Since in the binomial approximation the length of the genome N(D) is a
  > constant that is independent of each d_i, we can replace it by N, which is
  > the length of the actual genome from which the reads were sampled. ... For
  > our experiments, we assume that the genome size is known."
- §6.2: the transitively reduced bidirected read-overlap graph, flow lower
  bound 1 per read vertex, "our flow represents a (non-contiguous) assembly".
- §8.2:
  > "Our algorithm relies on having an estimate on the length of the genome..."

These confirm the three distinct Medvedev–Brudno objects and the
formulation-vs-algorithm vocabulary: the exact `N(D)` objective is named as the
target; the external-`N` binomial expression is explicitly an approximation; the
flow construction is presented as the algorithm.

## 4. Corrections and hashing caveats

### 4.1 DOI error in the issue #36 comment (re-confirmed)

Source fact (Crossref): `10.1093/bioinformatics/btw267` resolves to "Genome
assembly from synthetic long read clouds," *Bioinformatics* **32**(12),
i216–i224 — not the Shomorony paper. The Shomorony et al. paper is
`10.1093/bioinformatics/btw450`, *Bioinformatics* **32**(17), i494–i502. The
existing issue #36 comment's "DOI 10.1093/bioinformatics/btw267" is a
transcription error.

Note for whoever updates the main note: `shomorony-mb-formulation-provenance.md`
§9 records the corrected DOI correctly but states the wrong *issue/pages* for
`btw267` — it writes "32(17), i216–i224"; Crossref gives **32(12)**, i216–i224.

### 4.2 The Medvedev–Brudno HTML hash is not a stable content identifier

The main note's §2 ledger records SHA-256
`d52c6e8998e055de69782a98a162410e870a7263d6e13e076bc617d01d0c0c2f` for the
PMC HTML. My independent fetch of the same URL produced
`627db98064cbdd8706b899b9035f7e24094c523394be750b99aee51c4f065f47` (205586
bytes). The retrieved body and every quoted paragraph match; the hash differs
because PMC serves a dynamic page (session/nonce/asset fingerprints). So the
HTML hash should not be treated as artifact identity. The reproducible anchors
for this source are the PMCID (`PMC3154397`), the DOI
(`10.1089/cmb.2009.0047`), and the verbatim quotations; if a byte-stable
artifact is needed, use a PDF/XML deposit rather than the HTML page.

## 5. Independent reproduction of the secondary reading

The Howison–Zapata–Dunn author PDF was re-retrieved (hash matches the main
note). Verbatim, §5 "Likelihood approaches":

> "Also, it requires as a parameter the accurate size of the target genome,
> which is not available in all de novo assembly projects. A related design for
> maximum likelihood assembly (Varma et al., 2011) uses a different formulation
> that starts from an approximate size and estimates the actual size during the
> optimization."

The in-text attribution is "(Medvedev et al., 2009)", but the paper's
bibliography entry is "Medvedev,P. and Brudno,M. (2009) Maximum Likelihood
Genome Assembly. *J. Comput. Biol.*, 16, 1101–1116" — i.e. the same MB09 paper.
This is a third-party source fact about how MB09's *method* was read
(size-as-parameter), not a statement about which MB09 section the 2016 phrase
denotes.

## 6. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| Open-question paragraph is the last paragraph of §5 Discussion | source fact | independent heading scan + position of next heading "Acknowledgements" |
| Accepted typeset gives no section/equation/figure pointer into MB09 | source fact | five in-text occurrences scanned; none carries a locator |
| Bibliography entry is "Medvedev,P. and Brudno,M. (2009) Maximum likelihood genome assembly. J. Comput. Biol., 16, 1101–1116" | source fact | accepted typeset References + NSG `[8]` + Crossref deposit `btw450-B13` |
| 2009 citation is the ML paper, distinct from the 2007 flow paper | source fact | Crossref deposit lists both `btw450-B13` and `btw450-B19` |
| Manuscript cites it numerically as `[8]`; typeset as author-year | source fact | `NSG.txt` vs `InfoOptimalAssy.txt` |
| MB09 self-describes a "maximum likelihood framework", distinct from the flow "algorithm" | source fact | MB09 abstract and §6 |
| MB09 §6.1 uses candidate `N(D)` and then replaces it by external known `N` | source fact | MB09 §6.1 |
| `btw267` is not the Shomorony paper; `btw450` is | source fact | Crossref |
| MB09 HTML hash is not reproducible | fact about retrieval | two fetches, same body, different hash |
| Howison et al. read MB09's method as consuming the target genome size | source fact | Howison §5; author PDF hash matches |
| Which MB09 object the 2016 phrase denotes | interpretation, unresolved | see `shomorony-mb-formulation-provenance.md` §6 |

## 7. What this note does not do

It does not decide the denotation of "maximum-likelihood formulation", does not
fix a competitor universe or length convention, and does not bear on whether the
kernel-checked same-length witnesses are flow-feasible. Those remain with
[`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md)
§7 and the active Section 6.2 packet.
