# What the Shomorony et al. open question most plausibly denotes

_Status: independent source note, 2026-09-19. This note consolidates and
supersedes the scattered, unmerged source work on the referent of the 2016
open-question sentence (`shomorony-open-question-denotation.md`,
`ml-accepted-text-source-verification.md`, `ml-objective-candidate-class-resolution.md`)
after independently re-retrieving and reading the primary sources. It answers,
as far as the primary sources permit: which maximum-likelihood objective, which
candidate universe/length, which genome equivalence, and which tie semantics the
2016 sentence most plausibly denotes._

_It does not resolve the open problem and does not silently designate a single
formal target. Strictly as a **source fact**, the accepted 2016 text is
ambiguous; the ranking below is an explicit **source analysis / interpretation**.
The parallel variants must remain available per `../ml-formalization-contract.md`._

## 1. Question and method

Shomorony et al. (2016) end their Discussion by asking whether bridging
conditions guarantee "that the maximum-likelihood sequence is the true
sequence". The formulation is named only by a bibliography entry to Medvedev and
Brudno (2009), which contains several materially different maximum-likelihood
objects. This note asks: **if a single referent must be named, which one is the
most plausible?** and records separately what the sources do and do not fix
about the candidate universe, genome equivalence, and tie semantics.

Method: direct re-retrieval and end-to-end reading of the primary sources. No
claim below rests on a repository summary. Retrieved artifacts and their
identities are listed in §2; the load-bearing quotations were extracted from
those bytes.

## 2. Retrieval provenance (independently re-verified 2026-09-19)

| Source | Locator | Identity of retrieved artifact |
|---|---|---|
| Shomorony et al., publisher-formatted accepted article | <https://people.eecs.berkeley.edu/~courtade/pdfs/InfoOptimalAssy.pdf> | 9 pages; SHA-256 `ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043acfce3c4da` |
| Shomorony et al., author accepted manuscript | <https://people.eecs.berkeley.edu/~courtade/pdfs/NSG.pdf> | 8 pages; SHA-256 `daeb5b3163d92643affc2398a387217cb57e5e33ce0dd5ebbfccabf621454f2c` |
| Shomorony et al., earlier author-hosted preprint ("Optimal Sequence Assembly via Sparse Read-Overlap Graphs") | <https://web.stanford.edu/~gkamath/nsgIlan.pdf> | 23 pages; SHA-256 `f2a9f6a64f75cbf4c2cfaec6f794c779907f165c986261bec7a2aa72a3e6954a` |
| Medvedev & Brudno (2009) | <https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/> | full text retrieved via browser-rendered HTML (PMC blocks the plain `wget` path with a reCAPTCHA page) |
| Bresler, Bresler & Tse (2013) | <https://pmc.ncbi.nlm.nih.gov/articles/PMC3706340/> | full text retrieved via browser-rendered HTML |

The Oxford Academic publisher endpoints
(`https://academic.oup.com/bioinformatics/article/32/17/i494/2450650`, the
article PDF, and `btw450_supplement.zip` / the `oup.silverchair-cdn.com`
backfile path) still reject the available retrieval path. The accepted publisher
**supplement (Supplementary Material A–G) remains unretrieved** and is the one
unexamined primary-source artifact that could in principle change the ranking.

## 3. Source facts

### 3.1 The accepted 2016 open-question paragraph

`InfoOptimalAssy.pdf`, Section 5 (Discussion), final paragraph (the Discussion
begins on printed p. i501; the open-question sentence is on p. i501–i502), read
end to end:

> "Another direction for future work, from a more theoretical standpoint, is
> understanding whether, in information-feasible instances of the AP, the output
> of N OT-SO-GREEDY coincides with the solution of a combinatorial optimization
> problem. Notice that while Theorem 1 guarantees the reconstruction of the true
> sequence `s`, there is no guarantee that this sequence corresponds to the
> solution of an optimization-based formulation of the AP such as those
> considered by Nagarajan and Pop (2009) and Medvedev and Brudno (2009). As
> mentioned by Medvedev and Brudno (2009), parsimony-based formulations tend to
> encourage an over-collapsing of the repeats, and the optimal solution is in
> general different from the true underlying sequence. **The maximum-likelihood
> formulation of the AP (Medvedev and Brudno, 2009), on the contrary, seems to be
> robust to these issues, and thus a good candidate for the 'correct'
> formulation. Understanding whether bridging conditions can be used to
> guarantee that the maximum-likelihood sequence is the true sequence is
> currently an open question.**"

The author accepted manuscript (`NSG.pdf`, p. 7) carries the substantively
identical passage with only copy-editing differences ("maximum likelihood
formulation of the AP [8]", "maximum likelihood sequence"). "AP" is the paper's
own abbreviation for the assembly problem, defined in the Introduction.

A full-text scan of the accepted article finds only three occurrences of
`likelihood`: the two inside this paragraph and the Medvedev–Brudno reference
title. The accepted main text contains **no** `multinomial`, **no** `binomial`,
**no** copy-count/flow discussion, and no equation or section pointer into
Medvedev–Brudno.

### 3.2 The three Medvedev–Brudno objects

From `PMC3154397`, Section 6.1 (body text, read directly):

- **Exact global read-count likelihood.** "Let `D` be a circular genome of
  length `N(D)`, and let `d_i` denote the number of times the `k`-molecule `i`
  appears in `D`." A trial samples a start uniformly in `D` and yields type `i`
  with probability `d_i/N(D)`; the joint counts are multinomial with the
  constraint `N(D) = Σ_i d_i`. MB call the resulting function of the copy
  counts the **global read-count likelihood** and say "we attempt to assemble
  the genome with the maximum global read-count likelihood."
- **Binomial/separable approximation.** Immediately after: "Because the number
  of trials (sampled `k`-molecules) is typically large, we can **approximate**
  the multinomial distribution as the product of the individual binomial
  distributions of each `X_i`. Since in the binomial approximation the length of
  the genome `N(D)` is a constant that is independent of each `d_i`, we can
  replace it by `N`, which is the length of the actual genome from which the
  reads were sampled. … For our experiments, we assume that the genome size is
  known." This is a change of probability model, introduced explicitly for
  tractable convex flow.
- **Section 6.2 flow optimization.** The algorithm solves a convex min-cost
  biflow on the transitively reduced bidirected read-overlap graph with lower
  bound 1 on every read vertex, using the convex costs derived from the
  approximation: "Since any flow can be decomposed into a collection of walks,
  our flow represents a **(non-contiguous) assembly** of the genome."

MB's own description of the contribution (abstract) is a "maximum likelihood
framework for assembling the genome that is the most likely source of the
reads", contrasted with "the standard maximum parsimony approach".

### 3.3 The 2016 model fixes the true genome, not the competitor class

The accepted text's Preliminaries fix the *data-generating* model: the true
genome `s` has length `G`, `N` error-free reads of common length `L` are "drawn
independently and uniformly at random from the set of length-`L` substrings of
`s`", and `s` is circular. Theorem 1's conclusion is `st(c_s) = s` "up to cyclic
shifts", and the information-feasible set is

```text
I_s = { R : R covers s ; triple repeats in s are all-bridged ;
             interleaved repeats in s are bridged }.
```

This fixes the true `G`; it does not state a length or universe for a competing
genome in a maximum-likelihood comparison.

### 3.4 The earlier author-hosted preprint does not contain the open question

The 23-page preprint (`nsgIlan.pdf`, PDF creation date 2016-01-23) is an
**earlier version** and is not equivalent to the accepted article. Independently
re-read, its Introduction contains a sentence that is important corroborating
vocabulary:

> "To circumvent this issue, [8] proposed a maximum likelihood (ML) formulation
> for assembly. While such a formulation prevents the over-collapsing of
> repeats, devising algorithms to find the ML sequence given the read data is a
> daunting task, and existing approaches rely on the assumption of high
> coverage [8]."

Its Discussion (section 5) instead opens: "In this context, a natural question is
whether this approach is also solving some combinatorial optimization problem."
The phrases "open question" and the accepted open-question sentence do **not**
appear; the only likelihood claim in the document is the appended Bresler
same-likelihood theorem. This corrects a claim previously recorded in
`../literature/ml-tie-semantics.md` (see §6).

### 3.5 Bresler et al. (2013): same-length equal-likelihood competitors exist

`PMC3706340`, Theorem 1:

> "Given a DNA sequence `s` and a set of reads, if there is a pair of
> interleaved repeats or a triple repeat whose copies are all unbridged, then
> there is another sequence `s'` **of the same length** under which the
> likelihood of observing the reads is the same."

The bridging definition is the strict-extension one: "A subsequence `s_t^ℓ` is
bridged if and only if there exists at least one read which covers at least one
base on both sides of the subsequence." Bresler et al. also state that
reconstruction "contrasts with the many optimization-based formulations of
assembly, such as shortest common superstring (SCS), maximum-likelihood [6],
[7], and various graph-based formulations. When solving one of these alternative
formulations, there is no guarantee that the optimal solution is indeed the
original sequence." This is the exact gap the 2016 open question targets.

## 4. Determination: the most plausible referent (analysis)

**Most plausible: the exact global read-count likelihood of Section 6.1 —
multinomial read-type probabilities `d_i/N(D)` over circular candidate genomes
with candidate-dependent length (repository Variant E).**

Reasons, in order of weight:

1. **"Formulation" contrasts objectives, not algorithms.** The 2016 sentence
   opposes "parsimony-based formulations" to "the maximum-likelihood
   formulation". Both name objectives for the assembly problem. MB's exact
   global read-count likelihood is the objective; the binomial is labelled an
   approximation of it and §6.2 is the algorithm that optimizes the
   approximation.
2. **MB name the exact object as the target.** MB say their algorithm "finds the
   genome that maximizes the global read-count likelihood", and the §6.1
   definition uses the candidate's own `N(D)`. The approximation is introduced
   with the word "approximate".
3. **The same authors' earlier version separates formulation from algorithm.**
   The preprint says MB "proposed a maximum likelihood (ML) formulation for
   assembly" and then separately refers to "devising algorithms to find the ML
   sequence". The accepted phrase "the maximum-likelihood formulation of the AP"
   is a close paraphrase of that preprint sentence.
4. **The 2016 conclusion is about a sequence.** MB describe the §6.2 flow as a
   "(non-contiguous) assembly", which need not spell one sequence. That makes
   §6.2 an especially poor fit for "the maximum-likelihood *sequence* is the
   true sequence".

**Second most plausible: the binomial/separable approximation (Variant A).** A
reader who identifies "the MB formulation" with what MB's published algorithm
actually optimizes lands here, because §6.2 optimizes the approximation. This
reading is not excluded; it is weakened by MB's own use of the word
"approximate" and by the fixed external length it introduces.

**Least plausible: the Section 6.2 flow feasible set (Variant F).** It is an
algorithmic search space with read-vertex lower bounds and a non-contiguous
interpretation, and §6.2 is downstream of the approximation rather than a third
independent likelihood. It is not a formulation whose solution is a sequence.

**This ranking is an interpretation of a bare bibliographic citation, not a
source statement.** The accepted text names no formula, section, or equation
inside Medvedev–Brudno. Absent the accepted supplement or an author statement,
the honest source status remains a three-way disjunction.

## 5. Candidate universe, equivalence, and tie semantics

### 5.1 Candidate universe and length

- **Exact §6.1 objective:** candidate `D` is a circular genome with its own
  `N(D)`, and the likelihood is written as a function of the copy-count vector
  `(d_i)`, with the internal constraint `N(D) = Σ_i d_i`. The source does not
  state the competitor universe (all circular genomes? all realizable copy-count
  vectors?) and imposes **no fixed competitor length**.
- **Approximation:** the denominator is replaced by an external constant `N`
  (the true/estimated genome length). This is a change of the probability model;
  the source does not state that candidates must have length `N`.
- **§6.2 flow:** length is implicit in the read-overlap graph.
- **2016:** fixes the true `G`, not the competitors.

**Status: unresolved.** A fixed competitor length `|D| = G` is an additional
named restriction, not a default, and must be carried in the type/name of any
theorem that uses it.

### 5.2 Genome equivalence

- **Cyclic shift is required** by the 2016 circular exposition; Theorem 1 holds
  "up to cyclic shifts". **(Source fact.)**
- **Reverse complement is unresolved.** MB model double-stranded DNA with
  bidirected molecules; Bresler et al. handle double strands explicitly by
  mapping the problem to a length-`2G` concatenation of `u` and its reverse
  complement and doubling the reads, then looking for two Eulerian paths. The
  2016 exposition uses a single circular sequence. The sources therefore treat
  the second strand differently, and the 2016 sentence does not say whether the
  intended genome identity quotients reverse complement.

### 5.3 Tie and uniqueness semantics

- The 2016 sentence gives **no tie-break, no uniqueness claim, and no
  equivalence relation** under which uniqueness is intended. The singular "the
  maximum-likelihood sequence" cannot by itself distinguish a selected maximizer
  from a unique maximizer.
- Medvedev–Brudno give no tie rule either and state no uniqueness theorem.
- **Ties are real and source-demonstrated:** Bresler Theorem 1 constructs a
  distinct, same-length, equal-likelihood competitor from unbridged repeats.

Consequently these two conclusion schemas must stay distinct
(see `../ml-formalization-contract.md`):

```text
truthIsML     : ∀ D, L(D | reads) ≤ L(truth | reads)
mlIsTruthUpTo : truthIsML ∧ (∀ D, L(D | reads) = L(truth | reads) → D ≈ truth)
```

`truthIsML` is satisfied by a mere tie; `mlIsTruthUpTo` requires every
maximizer to be equivalent to the truth. A proof or counterexample of one must
not be advertised as settling the other.

## 6. Correction to an existing note

`../literature/ml-tie-semantics.md` previously stated that the author-hosted
manuscript "uses the same substantive open-question wording". Direct reading of
`nsgIlan.pdf` does not support this: that preprint predates and **lacks** the
accepted open-question sentence; its Discussion differs and the only
"likelihood" content is the appended Bresler theorem. The note has been
corrected accordingly. Its substantive conclusion (tie semantics unresolved)
is unchanged and is strengthened: neither version supplies a tie convention.

## 7. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| Accepted open-question sentence and full paragraph | **Source fact (re-verified)** | `InfoOptimalAssy.pdf` SHA-256 `ec17b16f…`; corroborated by `NSG.pdf` SHA-256 `daeb5b31…` |
| Accepted main text names MB only by bibliography; no formula/section/equation pointer | **Source fact** | Full-text scan: only three `likelihood` occurrences |
| §6.1 defines exact multinomial `d_i/N(D)` with `N(D)=Σd_i`, then a binomial approximation with external `N`, then §6.2 a read-overlap biflow | **Source fact** | Medvedev–Brudno §6.1–§6.2 |
| Preprint uses "ML formulation for assembly" / "algorithms to find the ML sequence" and lacks the accepted open question | **Source fact** | `nsgIlan.pdf` §1 and §5 |
| Bresler Theorem 1 yields a same-length equal-likelihood competitor | **Source fact** | Bresler et al. Theorem 1 |
| Exact multinomial (Variant E) is the most plausible referent | **Source analysis / interpretation** | §4 reasons 1–4 |
| Approximation (Variant A) is a weaker, non-excluded reading; §6.2 flow (Variant F) is least plausible | **Source analysis / interpretation** | §4 |
| Competitor universe/length not fixed; fixed length is a named restriction | **Unresolved source ambiguity** | §5.1 |
| Cyclic shift required; reverse-complement quotient unresolved | **Source fact / source analysis** | §5.2 |
| Tie/uniqueness convention absent; both conclusion schemas must remain | **Unresolved source ambiguity + modeling organization** | §5.3 |
| Accepted supplement contents | **Not retrieved (blocked)** | §2 |

## 8. Consequences and what would change the ranking

1. If the project names a single published referent, the exact global read-count
   multinomial over circular candidates with candidate-dependent length is the
   most defensible choice, **provided the note is labelled interpretation and the
   parallel variants stay available**.
2. Every concrete theorem must still name its ML layer, candidate universe,
   equivalence relation, and maximizer-versus-uniqueness conclusion, per
   `../ml-formalization-contract.md`.
3. Fixed competitor length, reverse-complement equivalence, and uniqueness are
   additional modeling choices; none follows from the 2016 sentence.
4. Recovering the accepted publisher supplement (sections A–G), or any later
   author statement identifying the exact versus approximation objective, would
   be the strongest reason to revise this ranking.

## References

1. I. Shomorony, S. H. Kim, T. A. Courtade, and D. N. C. Tse. "Information-optimal genome assembly via sparse read-overlap graphs." *Bioinformatics* 32(17):i494–i502, 2016. DOI <https://doi.org/10.1093/bioinformatics/btw450>.
2. P. Medvedev and M. Brudno. "Maximum Likelihood Genome Assembly." *Journal of Computational Biology* 16(8):1101–1116, 2009. DOI <https://doi.org/10.1089/cmb.2009.0047>. Full text <https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/>.
3. G. Bresler, M. Bresler, and D. Tse. "Optimal assembly for high throughput shotgun sequencing." *BMC Bioinformatics* 14(Suppl 5):S18, 2013. DOI <https://doi.org/10.1186/1471-2105-14-S5-S18>. Full text <https://pmc.ncbi.nlm.nih.gov/articles/PMC3706340/>.
4. Author-hosted earlier preprint, "Optimal Sequence Assembly via Sparse Read-Overlap Graphs." <https://web.stanford.edu/~gkamath/nsgIlan.pdf>.
