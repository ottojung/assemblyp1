# The accepted Shomorony supplement: what it is, and which referent evidence it can still supply

_Status: focused primary-source note for issue #36, 2026-09-20. It records only
material not already present in
[`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md),
[`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md),
[`shomorony-ml-reference.md`](shomorony-ml-reference.md), or
[`../literature-status.md`](../literature-status.md). Every claim is labelled
**source fact**, **source-supported inference**, **correction**, or **source
gap**. It does not select a referent by fiat and does not settle the published
question._

## 0. New findings only

1. **The accepted supplement is a single PDF, not a ZIP.** The 2016 OUP
   supplement landing page for `btw450` lists the artifact as “Supplementary
   Data – pdf file” and links
   `/content/suppl/2016/08/31/btw450.DC1/supp_material.pdf`. The two on-`main`
   notes call it “the accepted supplementary ZIP”; that packaging description is
   the later (2018 silverchair-era) delivery, not the 2016 artifact. (Source
   fact + correction; §1–§2.)
2. **The accepted typeset article itself cites Supplementary Material sections
   A, B, C, E, F, and G by name, inline, and every one of those pointers is to
   algorithm, proof, or Lander–Waterman/coverage content — none is to a
   likelihood, ML-objective, candidate-class, or tie definition.** (Source
   fact; §3.)
3. **Consequence.** The last unexamined accepted artifact is, by the accepted
   article's own cross-references, an appendix of algorithms and proofs. It is
   not, on the available evidence, a plausible locus of a definition that would
   select one of the four issue #36 readings. (Source-supported inference; §4.)
4. **It remains unretrieved.** `supp_material.pdf` returns HTTP 403 on OUP and
   has no Wayback capture; section D is not cited in the accepted main text, so
   its content is unknown. (Source gap; §1, §4.)

This sharpens, but does not overturn, the existing status: the accepted main
text selects none of the four readings, and no accepted artifact inspected so
far supplies a selection.

## 1. Retrieval provenance

| Artifact | Locator | SHA-256 / status |
|---|---|---|
| Accepted article, OUP-typeset PDF | `https://people.eecs.berkeley.edu/~courtade/pdfs/InfoOptimalAssy.pdf` | `ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043acfce3c4da` (matches main ledger) |
| 2016 supplement landing page | `https://web.archive.org/web/2016id_/http://bioinformatics.oxfordjournals.org/content/32/17/i494/suppl/DC1` | `8b27efdcdc1dbbd2e6f02a5b6f4f8182432537d883010dd67d1e02394ef547fc` |
| Accepted supplement PDF | `/content/suppl/2016/08/31/btw450.DC1/supp_material.pdf` (as linked by the landing page) | **unretrieved — HTTP 403**; no Wayback/CDX capture found |
| Accepted full-text HTML (2016 OUP platform) | archived copy read for cross-checks | `ce9210633beaa46ff6863697dd6aafe7432e00c1ad87016ad0b7f54f957ea163` |

The supplement landing page was reached through an exact-URL Wayback replay
(`web/2016id_/`), so the link target is the publisher's own 2016 `href` and not
a reconstruction. The `btw450_supplementary_data.zip` name reported elsewhere
belongs to the 2018 `oup.silverchair-cdn.com` re-packaging of the same
supplement; both resolve to a “Supplementary Data – pdf file”. No location
tried in this run returned the PDF bytes: the OUP direct path, the
silverchair-CDN signed path, and the Wayback Machine all fail.

## 2. Source fact: the accepted supplement is a PDF

The 2016 supplement page states, under “Supplementary Data”:

> “Supplementary Data files — Supplementary Data – pdf file”

and carries the anchor

```text
/content/suppl/2016/08/31/btw450.DC1/supp_material.pdf
```

So the accepted supplement has a single PDF body (the same sections A–G the
accepted article cites). Calling it a ZIP is a description of a later delivery
wrapper, not of the artifact the 2016 OUP page exposes. [source fact +
correction]

## 3. Source fact: everything the accepted article points into the supplement

The accepted typeset article cites the supplement by section name in eight
places, covering six distinct sections (A, B, C, E twice, F twice, G). Every
pointer is to algorithmic, proof, or coverage content:

| Supplement section | What the accepted main text says it contains | Locator (`InfoOptimalAssy.txt`) |
|---|---|---|
| A | sparse read-overlap graph construction (“As described in detail in Supplementary Material A, in this approach, for each vertex u ∈ V we include at most one edge (u,v), chosen in a greedy fashion.”) | §3, before Algorithm 1 |
| B | proof of Lemma 1 (“… has the following guarantee (proved in Supplementary Material B).” ) | §3, Lemma 1 |
| C | formal proof of Theorem 1 (“Theorem 1, which we formally prove in Supplementary Material C …”) | §3, Theorem 1 |
| E | computation of the effective overlaps (“A more detailed description of the computation of the effective overlaps is presented in Supplementary Material E.”) | §3, overlap pruning |
| F | Eulerian reduction, proof of Corollary 1 (“This reduction (which leads to the proof of Corollary 1) is described in Supplementary Material F.”) | §3, end |
| G | Lander–Waterman coverage depth / critical read length (“… is the Lander–Waterman coverage depth (see Supplementary Material G)”) | §2 |

Section D is **not** cited anywhere in the accepted main text, so its content
cannot be stated from the accepted article alone. [source fact]

**Corroboration.** The author-hosted preprint studied in
[`shomorony-ml-reference.md`](shomorony-ml-reference.md) §“Author-hosted version
and appended supplementary material” appends a Supplementary Material whose
sections cover the same topics (decremental hashing; effective overlaps;
Eulerian reduction; Bresler repeat/bridging conditions) and, on a full-text
search, contains no definition of the Medvedev–Brudno likelihood objective; its
only “likelihood” statement is the adjacent Bresler equal-likelihood ambiguity
result. [source fact, already on `main`]

## 4. What this does and does not settle

**It does not settle the referent.** The accepted supplement PDF itself is still
unretrieved, and section D is uncited. A likelihood/objective definition could
in principle sit in D or in unlabelled portions of A/B/C/E/F/G.

**It materially lowers the prior that the supplement is decisive.** The accepted
article enumerates the supplement's role through six by-name inline pointers,
and its sole “likelihood” vocabulary consists of the three Discussion/abstract
occurrences already recorded; the supplement is presented and used as the proof
and algorithm appendix. Nothing the accepted text says about its own supplement
concerns the maximum-likelihood formulation. [source-supported inference]

## 5. Bearing on the issue #36 readings

The new evidence selects none of the readings; it only removes the supplement as
the likely source of a decisive selection.

| Reading | Effect of this note |
|---|---|
| sequence objective (exact multinomial, candidate-intrinsic length; Variant E) | no change — supplement not cited for any objective |
| §6.1 fixed-`N` likelihood/approximation (Variant A) | no change |
| §6.2 flow optimization (Variant F) | no change — the sequence-vs-flow structural argument in [`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md) §4 is unaffected |
| deliberately broad ML framework | no change — no formula is fixed by either text or its supplement references |

In particular, this note is **not** evidence for reading (2) or (1) over the
other; the model-match argument and the fixed-`G` preprint framing remain the
positive evidence, and they are unaffected by what the supplement contains.

## 6. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| The 2016 OUP supplement landing page describes the artifact as a PDF and links `supp_material.pdf` | source fact | Wayback exact-URL replay of the 2016 supplement page |
| The on-`main` “supplementary ZIP” wording describes a later repackaging | correction | contrast of 2016 landing page with the 2018 silverchair filename |
| The accepted article cites supplement sections A, B, C, E, F, G for algorithms/proofs/Lander–Waterman, and none for ML | source fact | `InfoOptimalAssy.pdf` inline pointers; §3 table |
| Section D is uncited | source fact | full-text search of the accepted article |
| The accepted supplement is an appendix, not a likely ML-definition locus | source-supported inference | §3–§4 |
| The referent among the four readings remains unselected | source gap | §4–§5 |

## 7. Locators

- I. Shomorony, S. H. Kim, T. A. Courtade, D. N. C. Tse, “Information-optimal
  genome assembly via sparse read-overlap graphs,” *Bioinformatics* 32(17)
  (2016) i494–i502, DOI `10.1093/bioinformatics/btw450`; supplement landing page
  `bioinformatics.oxfordjournals.org/content/32/17/i494/suppl/DC1`, linked PDF
  `/content/suppl/2016/08/31/btw450.DC1/supp_material.pdf` (HTTP 403).
- Author-hosted preprint `https://web.stanford.edu/~gkamath/nsgIlan.pdf`
  (appended Supplementary Material, printed section 6, PDF p. 18 ff.).
- P. Medvedev, M. Brudno, “Maximum Likelihood Genome Assembly,” *J. Comput.
  Biol.* 16(8) (2009) 1101–1116, DOI `10.1089/cmb.2009.0047`, PMC3154397,
  §6.1–§6.2.
