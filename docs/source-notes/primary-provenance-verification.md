# Independent primary-source verification: Shomorony open question and the Medvedev–Brudno ML objective

_Status: independent source verification, 2026-09-20. Re-retrieved every retrievable
primary artifact with a distinct toolchain (`urllib` + `pypdf`) and read the displayed
Medvedev–Brudno equations directly from the publisher's equation images rather than
trusting a transcription. Corroborates the accepted-main-text provenance recorded in
[`shomorony-ml-reference.md`](shomorony-ml-reference.md) and
[`ml-objective-candidate-class-resolution.md`](ml-objective-candidate-class-resolution.md),
and adds one new negative-evidence argument about the unretrieved publisher supplement.
It does not settle the published open problem._

## 0. Relation to existing notes

This note does not replace:

- [`shomorony-ml-reference.md`](shomorony-ml-reference.md) — accepted 2016 text names the
  ML referent only by bibliographic citation; publisher supplement unrecovered;
- [`ml-objective-candidate-class-resolution.md`](ml-objective-candidate-class-resolution.md)
  — exact vs. approximate vs. §6.2 flow; candidate length/tie/uniqueness unresolved;
- [`medvedev-brudno-candidate-class.md`](medvedev-brudno-candidate-class.md) — the three
  Medvedev–Brudno objects and their length semantics;
- [`docs/literature/ml-tie-semantics.md`](../literature/ml-tie-semantics.md) — tie semantics
  unresolved; two conclusion schemas must be kept distinct.

It independently reproduces the retrievals behind those notes with a different extraction
path and records four additions: (1) a byte-level artifact ledger, (2) direct visual
verification of the Medvedev–Brudno formulas from the publisher equation images, (3) a
negative-evidence argument about the publisher supplement's contents derived from the
accepted text's own cross-references, and (4) an explicit unresolved register.

## 1. Artifact ledger (independently retrieved this run)

| Artifact | URL | Pages | PDF CreationDate | SHA-256 |
|---|---|---|---|---|
| Published accepted article (OUP typeset, Berkeley mirror) | `https://people.eecs.berkeley.edu/~courtade/pdfs/InfoOptimalAssy.pdf` | 9 | `D:20180626171923Z` | `ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043acfce3c4da` |
| Accepted author manuscript | `https://people.eecs.berkeley.edu/~courtade/pdfs/NSG.pdf` | 8 | `D:20160506120616-07'00'` | `daeb5b3163d92643affc2398a387217cb57e5e33ce0dd5ebbfccabf621454f2c` |
| Earlier author-hosted preprint (with appended supplement) | `https://web.stanford.edu/~gkamath/nsgIlan.pdf` | 23 | `D:20160123235649-08'00'` | `f2a9f6a64f75cbf4c2cfaec6f794c779907f165c986261bec7a2aa72a3e6954a` |
| Medvedev–Brudno (2009) full text | `https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/` | HTML body | — | (HTML + GIF equation assets) |

All three SHA-256 values match the ledger recorded on the unmerged branches
`agent/source-provenance-0919c` and `agent/ml-layer-source-verification`, so the branches
are reading byte-identical artifacts. The published article's pages carry the OUP running
head `i494`–`i502` and the download stamp of the Oxford record.

## 2. Accepted 2016 open-question passage (verbatim)

From `InfoOptimalAssy.pdf` (Discussion, §5), and in substance from `NSG.pdf`:

> "Another direction for future work, from a more theoretical standpoint, is understanding
> whether, in information-feasible instances of the AP, the output of NOT-SO-GREEDY
> coincides with the solution of a combinatorial optimization problem. Notice that while
> Theorem 1 guarantees the reconstruction of the true sequence `s`, there is no guarantee
> that this sequence corresponds to the solution of an optimization-based formulation of
> the AP such as those considered by Nagarajan and Pop (2009) and Medvedev and Brudno
> (2009). As mentioned by Medvedev and Brudno (2009), parsimony-based formulations tend to
> encourage an over-collapsing of the repeats, and the optimal solution is in general
> different from the true underlying sequence. **The maximum-likelihood formulation of the
> AP (Medvedev and Brudno, 2009), on the contrary, seems to be robust to these issues, and
> thus a good candidate for the 'correct' formulation. Understanding whether bridging
> conditions can be used to guarantee that the maximum-likelihood sequence is the true
> sequence is currently an open question.**"

The quoted open-question sentence matches `docs/open-problem.md:9` at the wording level.

## 3. Accepted full-text scan (source fact)

Direct counts over the extracted text of `InfoOptimalAssy.pdf`:

- `open question`: 1 (the sentence above);
- `maximum-likelihood`: 2 and `maximum likelihood`: 1 — all three `likelihood` occurrences
  are the two inside this paragraph plus the Medvedev–Brudno bibliography entry;
- `multinomial`: 0; `binomial`: 0;
- no likelihood formula, no equation/section pointer into Medvedev–Brudno, no statement of a
  candidate-genome universe, no competitor-length restriction, no equivalence relation, and
  no tie rule.

The only substantive ML property claim is the qualitative "seems to be robust to these
issues." This independently confirms the `shomorony-ml-reference.md` conclusion: the
accepted main text does not select among the Medvedev–Brudno objects.

## 4. Version fork (source fact, independently confirmed)

Three distinct 2016 documents exist:

| Version | Date | `open question` | `maximum-likelihood sequence` |
|---|---|---|---|
| Preprint "Optimal Sequence Assembly…" (`nsgIlan.pdf`) | 2016-01-23 | 0 | 0 |
| Accepted manuscript (`NSG.pdf`) | 2016-05-06 | 1 | present (as "maximum likelihood") |
| Published typeset (`InfoOptimalAssy.pdf`) | OUP | 1 | present ("maximum-likelihood") |

The preprint's Discussion instead asks "whether this approach is also solving some
combinatorial optimization problem." Its appended supplement's only `likelihood` statement
is the Bresler equal-likelihood theorem (its Theorem 2: a sequence `s' ≠ s` of the same
likelihood). The preprint predates and lacks the accepted open-question sentence, so it is
earlier-version evidence, not a substitute for the accepted text.

## 5. Medvedev–Brudno exact objective and candidate class (source fact)

Directly read from `PMC3154397` §6.1. Body text:

> "Let D be a circular genome of length N(D), and let d_i denote the number of times the
> k-molecule i appears in D. … In each trial, a position is uniformly sampled from D and
> the outcome of the trial is the k-molecule beginning at that position. For a given i, the
> probability that the outcome of a single trial is i is simply `[d_i/N(D)]`. … There are
> 4^k such variables, and when considered independently of each other, they each follow the
> binomial distribution. When taken together, their joint distribution is exactly the
> multinomial distribution. … we can consider the likelihood of the parameters of the
> distribution (d_i) given the outcome of the trials (x_i), which we call the **global
> read-count likelihood**."

Displayed equations read directly from the equation images (not a transcription):

- `M26.gif`: `d_i / N(D)`
- `M27.gif`: `P[X_1 = x_1, X_2 = x_2, …, X_{4^k} = x_{4^k}] = n! / (∏_i x_i!) · ∏_i ( d_i / N(D) )^{x_i}`
- `M30.gif`: `N(D) = Σ_i d_i`

Three source facts about this exact objective:

1. the product ranges over all `4^k` read types (zero-count types are included);
2. the denominator is the candidate's own length `N(D)`, internally linked by `N(D) = Σ_i d_i`;
3. the likelihood is written as a function of the copy-count parameters `(d_i)`. The source
   does not state the universe of circular genomes realizing those counts, and imposes **no
   fixed competitor length** at this definition point.

## 6. Medvedev–Brudno approximation and §6.2 flow (source fact)

Same §6.1, second half:

> "Because the number of trials (sampled k-molecules) is typically large, we can approximate
> the multinomial distribution as the product of the individual binomial distributions of
> each X_i. Since in the binomial approximation the length of the genome N(D) is a constant
> that is independent of each d_i, we can replace it by N, which is the length of the actual
> genome from which the reads were sampled. … For our experiments, we assume that the genome
> size is known."

Displayed equations read directly:

- `M31.gif`: `L[d_1, …, d_{4^k} | x_1, …, x_{4^k}] ≈ ∏_i P[X_i = x_i] = ∏_i C(n, x_i) ( d_i / N )^{x_i} ( 1 − d_i / N )^{n − x_i}`
- `M32.gif`: `−log L = K · Σ_i c_i(d_i)`
- `M33.gif`: `c_i(d_i) = −( x_i log d_i ) − ( n − x_i ) log( N − d_i )`

The retained `(1 − d_i/N)^{n−x_i}` factor is direct evidence that the literal approximation
is not merely `∏_i d_i^{x_i}`. §6.2 then defines a convex min-cost biflow on the transitively
reduced read-overlap graph, where "Each vertex has a lower bound of 1" and "our flow
represents a (non-contiguous) assembly of the genome." Therefore the §6.2 feasible set is
not, without a correspondence argument, the §6.1 candidate universe.

## 7. Publisher supplement: retrieval status and content inventory (new)

### 7.1 Retrieval attempts this run

| Route | Result |
|---|---|
| `https://academic.oup.com/bioinformatics/article/32/17/i494/2450780` | HTTP 403 (Cloudflare) |
| OUP `article-pdf/.../bioinformatics_32_17_i494.pdf` | HTTP 403 |
| OUP `.../bioinformatics_32_17_i494_s1.zip` | HTTP 403 |
| `oup.silverchair-cdn.com/.../btw450_Supplementary_Data.zip` | HTTP 403 |
| Crossref `relation` for the DOI | empty (no supplement deposit) |
| Unpaywall / OpenAIRE DOI lookups | no supplement location |
| Wayback CDX (`bioinformatics_32_17_i494_s1*`, `*btw450*`, `*i494*2450780*`) | no snapshots |
| Authors' data repository `github.com/samhykim/nsg` | code and read/graph data only (13 files, no supplement) |

### 7.2 Negative-evidence argument from the accepted text's own cross-references

The accepted main text cites the publisher supplement by section letter. The referenced
sections and their described topics are:

- **A** — the greedy/overlap graph construction;
- **B** — proof of Lemma 1 (sparse graph under coverage + all-bridged triple repeats);
- **C** — proof of Theorem 1 (reconstruction under bridging);
- **E** — computation of effective overlaps;
- **F** — the Eulerian reduction / edge-multiplicity algorithm;
- **G** — the critical read length `ℓ_crit`.

No cross-reference points to a likelihood, objective, candidate-class, or tie-semantics
section. Section D is not referenced from the main text. Independently, the earlier
preprint's appended supplement was read end to end and contains no Medvedev–Brudno ML
definition (only the Bresler equal-likelihood theorem). **Inference (labelled):** the
accepted publisher supplement very likely contains no definition of the Medvedev–Brudno ML
objective, but this is not proved because the artifact itself remains uninspected.

## 8. Reconciliation with the tracked notes

| Tracked claim | This run |
|---|---|
| Accepted main text does not select an ML variant | Independently confirmed (§3) |
| Accepted main text names Medvedev–Brudno only by bibliography | Independently confirmed (§3) |
| Exact objective uses candidate-dependent `N(D)`, no fixed competitor length | Independently confirmed, formulas visually verified (§5) |
| Binomial approximation fixes the denominator to external `N` | Independently confirmed, formulas visually verified (§6) |
| §6.2 feasible objects are read-graph flows, not all genomes | Independently confirmed (§6) |
| Publisher supplement unretrieved | Confirmed; new content-inventory argument added (§7) |
| Preprint predates and lacks the accepted open-question sentence | Independently confirmed (§4) |

The `shomorony-ml-reference.md` and `ml-objective-candidate-class-resolution.md` caveats that
the accepted text "could not be re-fetched" are now superseded as a *retrieval* limitation by
the Berkeley mirror (which yields the publisher-typeset text), while the *publisher
supplement* limitation remains.

## 9. Unresolved register

1. **Which Medvedev–Brudno object the 2016 sentence intends:** exact multinomial (§6.1
   first half) vs. binomial approximation (§6.1 second half) vs. §6.2 flow set. The
   retrieved 2016 texts select none.
2. **Exact candidate universe / length:** §6.1 states no universe and no fixed competitor
   length; §6.2 is a genuine restriction. Unresolved.
3. **Reverse-complement equivalence:** cyclic shift is required by the 2016 circular model;
   whether the double-stranded Medvedev–Brudno model quotients reverse complement is not
   resolved by the 2016 text.
4. **Conclusion semantics and tie-breaking:** truth-is-a-maximizer vs.
   all-maximizers-are-truth; neither paper supplies a tie rule. Bresler's equal-likelihood
   competitor is same-length, so ties are a real phenomenon.
5. **Accepted publisher supplement contents:** still uninspected; §7 gives only
   negative-evidence inference.

## 10. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| Published article, accepted manuscript, preprint hashes and dates | source fact (verified) | direct retrieval; SHA-256 above |
| Accepted open-question sentence and surrounding paragraph | source fact | `InfoOptimalAssy.pdf` §5; `NSG.pdf` |
| Accepted main text names MB only by bibliography; no variant/formula pointer | source fact | full-text scan §3 |
| Exact multinomial with `d_i/N(D)`, product over `4^k` types, `N(D)=Σ d_i` | source fact | MB §6.1 body + images `M26/M27/M30` |
| Binomial approximation with external `N` and `(1−d_i/N)^{n−x_i}` | source fact | MB §6.1 body + images `M31/M32/M33` |
| §6.2 feasible objects are read-graph flows, not all genomes | source fact | MB §6.2 |
| §6.1 imposes no fixed competitor length | source reading (well supported) | §5; no restriction appears |
| Preprint lacks the accepted open-question sentence | source fact | `nsgIlan.pdf` scan |
| Publisher supplement remains unretrieved | fact about this run | §7.1 |
| Accepted supplement likely contains no MB ML definition | interpretation / negative-evidence inference | §7.2 |
| Tie semantics and referent unresolved | source-analysis | §9 |
