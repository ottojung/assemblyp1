# Which Medvedev–Brudno formulation the Shomorony open question most plausibly denotes

_Status: independent source note, 2026-09-19. Independently re-retrieves and reads
the primary sources, then ranks the candidate referents of the 2016
"maximum-likelihood formulation of the AP". The ranking is **source analysis**;
the only new source fact is the corroborating earlier-version passage in §3.4.
It does not change the accepted-text ambiguity recorded in
`docs/source-notes/shomorony-ml-reference.md` and
`docs/source-notes/medvedev-brudno-candidate-class.md`._

## 1. Question and method

Shomorony et al. (2016) ask whether bridging conditions guarantee "that the
maximum-likelihood sequence is the true sequence". Medvedev–Brudno (2009)
contains at least three materially different objects that a reader could call
"the maximum-likelihood formulation of the AP". This note asks: **if a single
referent must be named, which is the most plausible denotation?**

The method is a direct re-reading of retrieved primary text, not a summary of
repository notes. Every quotation below was extracted from a file whose SHA-256
is recorded in §2.

## 2. Independent retrieval provenance

| Source | URL | SHA-256 |
|---|---|---|
| Shomorony accepted, publisher-formatted | `https://people.eecs.berkeley.edu/~courtade/pdfs/InfoOptimalAssy.pdf` | `ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043acfce3c4da` |
| Shomorony accepted manuscript | `https://people.eecs.berkeley.edu/~courtade/pdfs/NSG.pdf` | `daeb5b3163d92643affc2398a387217cb57e5e33ce0dd5ebbfccabf621454f2c` |
| Shomorony earlier author-hosted preprint | `https://web.stanford.edu/~gkamath/nsgIlan.pdf` | `f2a9f6a64f75cbf4c2cfaec6f794c779907f165c986261bec7a2aa72a3e6954a` |
| Medvedev–Brudno 2009 | `https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/` | retrieved 2026-09-19 |
| Bresler–Bresler–Tse 2013 | `https://pmc.ncbi.nlm.nih.gov/articles/PMC3706340/` | retrieved 2026-09-19 |

The three hashes match those already recorded in
`docs/source-notes/ml-accepted-text-source-verification.md` (unmerged branch
`agent/ml-layer-source-verification`), so the artifacts are the same versions.

The accepted Oxford article, its article PDF, and the
`btw450_supplement.zip` / `oup.silverchair-cdn.com` supplement endpoints each
return **HTTP 403** to the available retrieval path (independently reconfirmed
2026-09-19). The accepted supplement therefore remains unretrieved.

## 3. Source facts

### 3.1 Accepted 2016 open-question paragraph

`InfoOptimalAssy.pdf` (Section 5, Discussion), read end to end:

> "Another direction for future work, from a more theoretical standpoint, is
> understanding whether, in information-feasible instances of the AP, the output
> of N OT-SO-GREEDY coincides with the solution of a combinatorial optimization
> problem. Notice that while Theorem 1 guarantees the reconstruction of the true
> sequence s, there is no guarantee that this sequence corresponds to the
> solution of an optimization-based formulation of the AP such as those
> considered by Nagarajan and Pop (2009) and Medvedev and Brudno (2009). As
> mentioned by Medvedev and Brudno (2009), parsimony-based formulations tend to
> encourage an over-collapsing of the repeats, and the optimal solution is in
> general different from the true underlying sequence. **The maximum-likelihood
> formulation of the AP (Medvedev and Brudno, 2009), on the contrary, seems to be
> robust to these issues, and thus a good candidate for the ‘correct’
> formulation. Understanding whether bridging conditions can be used to
> guarantee that the maximum-likelihood sequence is the true sequence is
> currently an open question.**"

`NSG.pdf` (accepted manuscript) carries the substantively identical sentence.
"AP" is the paper's own abbreviation for the "assembly problem" (`AP` defined in
the Introduction, `InfoOptimalAssy.pdf` §1).

The accepted main text contains no likelihood formula, no `multinomial`, no
`binomial`, and no section/equation pointer into Medvedev–Brudno. The referent is
named only by a bibliography entry. This is the accepted-text ambiguity.

### 3.2 Medvedev–Brudno's actual objects

From `PMC3154397`, §6.1:

- **Exact global read-count likelihood.** "Let D be a circular genome of length
  N(D), and let d_i denote the number of times the k-molecule i appears in D …
  the joint distribution is exactly the multinomial distribution … we can
  consider the likelihood of the parameters of the distribution (d_i) given the
  outcome of the trials (x_i), which we call the **global read-count
  likelihood**." The per-trial probability is `d_i/N(D)`, and `N(D) = Σ_i d_i`.
- **Binomial/separable approximation.** "Because the number of trials (sampled
  k-molecules) is typically large, we can **approximate** the multinomial
  distribution as the product of the individual binomial distributions of each
  X_i. Since in the binomial approximation the length of the genome N(D) is a
  constant that is independent of each d_i, we can replace it by N, which is the
  length of the actual genome."
- **§6.2 flow optimization.** The convex min-cost biflow over the transitively
  reduced bipartite overlap graph, with lower bound 1 on each read vertex. MB:
  "Since any flow can be decomposed into a collection of walks, our flow
  represents a **(non-contiguous) assembly** of the genome."

MB's abstract frames the contribution as replacing "the standard maximum
parsimony approach (which finds the shortest genome subject to some
constraints)" with "a maximum likelihood framework for assembling the genome
that is the most likely source of the reads". Section 6.1 repeats that the
algorithm "finds the genome that maximizes the **global read-count
likelihood**".

### 3.3 Bresler et al. (2013) tie fact

`PMC3706340`, Theorem 1: "Given a DNA sequence s and a set of reads, if there is
a pair of interleaved repeats or a triple repeat whose copies are all unbridged,
then there is another sequence s' **of the same length** under which the
likelihood of observing the reads is the same." Ties are therefore a real
source-demonstrated phenomenon.

### 3.4 Earlier-version passage (new corroboration for the ranking)

The earlier author-hosted preprint (`nsgIlan.pdf`, created 2016-01-23), which
does **not** contain the accepted open-question sentence, contains this
Introduction passage (independently re-read; near the paragraph beginning "In
light of all these computational hardness results"):

> "To circumvent this issue, [8] proposed a **maximum likelihood (ML)
> formulation for assembly**. While such a formulation prevents the
> over-collapsing of repeats, **devising algorithms to find the ML sequence**
> given the read data is a daunting task, and existing approaches rely on the
> assumption of high coverage [8]."

This is direct evidence of the same authors' own vocabulary, in the same line of
work, one version earlier: Medvedev–Brudno "proposed a maximum likelihood (ML)
**formulation** for assembly", the object to be found is "**the ML sequence**",
and the hard part is the **algorithm** to find it (not the formulation). The
accepted phrase "the maximum-likelihood formulation of the AP" is a close
paraphrase of this preprint sentence.

## 4. Determination: the most plausible referent (analysis)

**Most plausible: the exact global read-count likelihood over circular candidate
genomes with candidate-dependent length (repository Variant E).**

Reasons, in order of weight:

1. **The word "formulation" contrasts objectives, not algorithms.** The 2016
   sentence contrasts "parsimony-based formulations" with "the maximum-likelihood
   formulation". Both are optimization *objectives* for the assembly problem. MB's
   exact global read-count likelihood is the object that constitutes the ML
   objective; the binomial is explicitly an approximation of it, and §6.2 is the
   algorithm that optimizes the approximation.
2. **MB name the exact object as the target.** MB say their algorithm "finds the
   genome that maximizes the **global read-count likelihood**" and define the
   likelihood in §6.1 under the candidate's own `N(D)`. The approximation is
   introduced with the word "approximate"; §6.1's phrase "the global read-count
   likelihood" names the exact object.
3. **The authors' earlier version says "ML formulation for assembly" and
   distinguishes it from "algorithms to find the ML sequence".** See §3.4.
4. **The 2016 conclusion is about a sequence.** MB explicitly describe the §6.2
   flow as a "(non-contiguous) assembly", which need not spell a single
   sequence. That makes §6.2 an especially poor fit for "the maximum-likelihood
   *sequence* is the true sequence".

**Second most plausible: the binomial/separable approximation (Variant A).** A
reader who equates "the MB formulation" with "what MB's published algorithm
actually optimizes" would land here, since §6.2 optimizes the approximation.
This reading is not excluded; it is weakened by MB's own labelling of the
binomial as an approximation and by the fixed external length it introduces.

**Least plausible: the §6.2 flow feasible set (Variant F).** It is an
algorithmic search space with read-vertex lower bounds and a non-contiguous
interpretation, not a formulation whose solution is a "sequence".

## 5. What would change the ranking

- Recovering the accepted supplement (sections A–G) or an explicit statement by
  the authors identifying exact vs. approximation. The supplement is the one
  unexamined primary-source artifact; it remains HTTP-403-blocked.
- Any later Shomorony/Courtade/Tse paper that names the MB objective would
  override this textual ranking.

Absent such evidence, the ranking above is an interpretation of a bare
bibliographic citation, not a source statement.

## 6. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| The accepted 2016 sentence names MB only by bibliography, with no formula/section/equation pointer | **Source fact** | `InfoOptimalAssy.pdf`, `NSG.pdf` |
| MB §6.1 defines the exact multinomial `d_i/N(D)`, then a binomial approximation, then §6.2 a read-overlap biflow | **Source fact** | `PMC3154397` §6.1–§6.2 |
| The earlier author-hosted preprint says MB "proposed a maximum likelihood (ML) formulation for assembly" and separates it from "algorithms to find the ML sequence" | **Source fact** | `nsgIlan.pdf` Introduction |
| Bresler Theorem 1 produces a same-length equal-likelihood competitor | **Source fact** | `PMC3706340` Theorem 1 |
| The exact global read-count likelihood (Variant E) is the most plausible referent of the 2016 phrase | **Source analysis / interpretation** | contrast of "formulations", MB's own naming, §3.4 |
| The approximation (Variant A) is a weaker but not excluded reading | **Source analysis / interpretation** | MB's actual algorithm optimizes it |
| The §6.2 flow set (Variant F) is the least plausible referent | **Source analysis / interpretation** | non-contiguous flow vs. "sequence" |
| Accepted supplement contents | **Not retrieved (403)** | independent reconfirmation 2026-09-19 |

## 7. Reconciliation with existing notes

- Consistent with `docs/source-notes/shomorony-ml-reference.md` and
  `docs/source-notes/medvedev-brudno-candidate-class.md`: those establish the bare
  citation and the three distinct MB objects; this note adds a ranked reading.
- Consistent with the unmerged `ml-accepted-text-source-verification.md` and
  `ml-objective-candidate-class-resolution.md`: those reach "unresolved" on the
  same evidence. This note does not overturn that; it states explicitly that the
  ranking is interpretation and that the honest source status remains a
  disjunction.
- Consistent with `docs/literature/ml-tie-semantics.md` on ties being unresolved
  in both papers. The Bresler same-length tie competitor means the exact
  objective (Variant E) genuinely admits ties, so "truth is a maximizer" and
  "all maximizers are the truth" must stay distinct regardless of which variant
  is chosen.

No conflict with the locked `docs/literature-status.md` is introduced; that
document is left unchanged.

## 8. Consequences for formalization

1. If the project names a single published referent for the open question, the
   exact global read-count multinomial over circular candidates with
   candidate-dependent length is the most defensible choice, **provided the note
   is labelled as interpretation and the parallel variants remain available.**
2. Every theorem must still name its ML layer, candidate universe, equivalence
   relation, and maximizer-vs-uniqueness conclusion, per
   `docs/ml-formalization-contract.md`.
3. The candidate universe and length semantics of Variant E are *not* fixed by
   the 2016 text; they remain an independent open source question.
4. The accepted supplement remains the one primary-source artifact that could
   still change the ranking, so its status should stay recorded as unresolved.
