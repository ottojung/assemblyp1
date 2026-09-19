# Forward-citation audit: does post-2016 work settle the bridging→ML question?

_Status: independent literature audit, 2026-09-19. Read-only web/scholarly-API work; no Lean edits._

_Independent of, and complementary to, `docs/literature-status.md` (status checked 2026-09-17) and the unmerged search notes on branches `literature/ghodsi-truth-max-2026-09-19`, `agent/fixed-length-expanded-search`, and `analysis/parametric-fixed-length-formulas`. Those documents are cited below where they overlap; this note re-derives the citation universe from the primary-source DOIs rather than trusting their summaries._

## Question investigated

For the open sentence in Shomorony, Kim, Courtade, and Tse (2016),

> "Understanding whether bridging conditions can be used to guarantee that the
> maximum-likelihood sequence is the true sequence is currently an open
> question."

is there any **paper published after 2016** that *proves*, *refutes*, *narrows*,
or *reformulates* the implication under a source-faithful model? "Settlement"
here means a theorem or counterexample about the global likelihood comparison,
not an assembler that succeeds under bridging.

## Method and reproducible negative-search scope

Databases and endpoints queried on 2026-09-19:

| Source | Query | Result |
| --- | --- | --- |
| Semantic Scholar Graph API | `paper/DOI:10.1093/bioinformatics/btw450/citations`, fields title/year/venue/externalIds/abstract, limit 100 | returned **38** citing works (all years) |
| OpenAlex REST API | `works/doi:10.1093/bioinformatics/btw450` | work `W2515489235`, `cited_by_count` = **33** |
| OpenAlex REST API | `works?filter=cites:W2515489235,from_publication_date:2017-01-01` | **30** citing works since 2017 |
| Semantic Scholar Graph API | `paper/DOI:10.1089/cmb.2009.0047/citations` (Medvedev–Brudno), limit 100 (page 1 of >100) | forward chain scanned to 2016 |
| Semantic Scholar Graph API | `paper/DOI:10.1186/1471-2105-14-S5-S18/citations` (Bresler et al.), limit 100 | forward chain scanned |
| Web search | exact phrase `"maximum-likelihood sequence is the true sequence"` | no assembly hit; only signal-processing MLSE uses |
| Web search | `"bridged" repeats "maximum likelihood" genome assembly theorem proof unique reconstruction` | no bridging→ML theorem |
| Web search | combinations of `bridging`, `interleaved repeat`, `triple repeat`, `identifiability`, `safe assembly`, `shotgun sequencing channel`, `Supregraph`, `coverage diploid` | no bridging→ML theorem |

The 30 OpenAlex post-2017 citing works and the 38 Semantic Scholar citing works
were individually triaged by title/venue/year; the plausible candidates were then
read at abstract or full-text level in the primary source. The three independent
citation counts (33, 38, 30-post-2016) bound the citation universe checked; no
claim of exhaustiveness is made, since indexing differs and 2026 records are
still being added.

## Classification of the post-2016 citing works

### A. Prove or refute the exact implication

**None located.** No post-2016 citing work states a theorem that
\(\mathcal I_s\) (coverage + all-bridged triple repeats + bridged interleaved
repeats) forces the Medvedev–Brudno likelihood to be maximized at the true
genome, and no post-2016 citing work exhibits a published counterexample where
the bridging hypotheses hold and a distinct candidate has strictly greater
likelihood.

### B. Narrow the problem

1. **Mahajan, Jain, and Kashyap, "On the Coverage Required for Diploid Genome
   Assembly,"** ISIT 2024, arXiv:2405.05734v3 (rev. 2025-04-07); journal version
   *IEEE/ACM Trans. Comput. Biol. Bioinform.* 2025, DOI
   [10.1109/TCBBIO.2025.3594365](https://doi.org/10.1109/TCBBIO.2025.3594365).

   This is the most substantive post-2016 development in the Shomorony/Bresler
   line. It extends the repeat/bridging feasibility analysis from haploid to
   **diploid** genomes and computes the coverage and read-length required by
   greedy, de Bruijn, and overlap-graph algorithms. Its abstract states (source
   fact):

   > "Our results show that the coverage and read length requirements of the
   > assembly algorithms are considerably higher than the lower bound because both
   > algorithms require the double repeats in the genome to be bridged."

   It reuses the *equal-likelihood necessity* mechanism rather than proving a
   sufficiency direction. On the arXiv v3 full text, the word "likelihood"
   appears in the discussion of necessary conditions; the representative
   sentence is (source fact): "If Condition I2 is not satisfied, that is, neither
   of the double repeats is bridged, then the likelihood of observing the reads
   \(\mathcal R\) is the same for more than one genome; hence, correct
   reconstruction is not possible."

   **Epistemic classification:** this *narrows and reformulates* the setting
   (diploid, algorithm-specific necessary conditions) but does **not** prove
   bridging \(\Rightarrow\) ML, and it contains no ML sufficiency theorem. It
   reinforces that the established direction in this literature is still
   necessity-by-equal-likelihood.

2. **Luria and Weinberger, "Optimal Overlap Detection of Shotgun Reads,"** ISIT
   2025, arXiv:2502.13813; *IEEE Trans. Inf. Theory* 2026, DOI
   [10.1109/TIT.2026.3706236](https://doi.org/10.1109/TIT.2026.3706236).

   Characterizes the exact asymptotic Bayesian error probability for detecting
   whether two randomly located reads overlap, in noiseless and memoryless
   noisy settings. It is a **local** likelihood/hypothesis-testing result about
   pairwise overlap, not a global assembly-likelihood theorem, and it does not
   introduce bridging conditions. **Classification:** adjacent reformulation of
   one subroutine of the overlap-graph pipeline; not the open question.

### C. Reformulate the information layer (graph-representability)

1. **Bankevich, "Supregraph: Enabling Information-Optimal Assembly Graph
   Representation of a Read Set,"** arXiv:2604.21951, 2026. Introduces
   supregraphs, proves a correct error-free read-set representation exists, and
   argues they "provide a foundation for constructing theoretically optimal
   genome assemblies." The word "optimal" here refers to preserving read-set
   information in the graph, not to maximizing the Medvedev–Brudno likelihood;
   the abstract and framing concern graph representability. **Classification:**
   reformulates what "information-optimal" means at the graph layer; does not
   connect bridging to ML. Note the 2026 date and that the repository's other
   search notes reached the same scoping.

2. **Cairo et al. (hydrostructure, linear-time omnitigs) and Schmidt et al.
   (WABI 2024)** characterize sequences safe across *all graph-consistent*
   genomes. **Classification:** graph-consistency safety, a different predicate
   from global maximum probability. No likelihood theorem.

### D. Change the observation/information model

- **Shotgun-sequencing-channel line** (Ravi–Vahid–Shomorony, "Coded Shotgun
  Sequencing," JSAIT 2022, arXiv:2110.02868; "Capacity of the Shotgun
  Sequencing Channel," ISIT 2022; Ali et al., converse with erasures, ITW 2025;
  Grunbaum–Yaakobi, "General Coverage Models," ISIT 2026, arXiv:2510.25305).
  These characterize capacity or coverage-time under coding/erasure models.
  They do not use bridging conditions and do not pose an ML optimality question.
- **Mazooji–Santhanam, "Substring Density Estimation from Traces,"** IEEE Trans.
  Inf. Theory 2024. Trace/insertion-deletion model; different observation model.

**Classification:** genuine information-theoretic reformulations of "how much
data is needed", orthogonal to the bridging→ML comparison.

### E. Same authors / same line, explicit statements that the gap remains

- **HINGE (Kamath, Shomorony, Xia, Courtade, Tse), Genome Research 2017.** The
  paper that most develops bridging after 2016 explicitly defers the likelihood
  step: "Utilizing these small levels of divergence to phase or to score the
  different traversals of a repeat according to their likelihood is a future
  direction for improvement of the HINGE pipeline." This is a source fact that,
  as of 2017, the authors treated the likelihood connection as unfinished.
- **Medvedev, "Theoretical Analysis of Sequencing Bioinformatics Algorithms and
  Beyond," CACM 2023.** The Medvedev–Brudno co-author's survey does not record
  the bridging→ML question as resolved.
- **Salmela, "Sama," Algorithms Mol. Biol. 2025.** Cites the Shomorony
  correctness result and Medvedev–Brudno-style probabilistic assembly as
  separate lines.

## The one adjacent theorem-level find (cross-reference)

The Ghodsi et al. (2013) complete-data "true genome maximizes the likelihood"
proof (BMC Research Notes 6:334, DOI
[10.1186/1756-0500-6-334](https://doi.org/10.1186/1756-0500-6-334)) is an
important adjacent result, but it is **pre-2016** and therefore outside the
forward-citation scope of this audit. It was independently located and recorded
on the unmerged branch `literature/ghodsi-truth-max-2026-09-19`
(`docs/literature-search-ghodsi-truth-max-2026-09-19.md`); the careful
convention analysis there (complete tiling vs. finite random sample) is not
duplicated here. This audit's independent web search reached the same adjacent
result and confirms the same limitation: it does not apply to the finite-sample
2016 model.

## What would have counted, and was specifically searched for

The following were searched for and **not found**:

1. A post-2016 theorem: \(\mathcal I_s \Rightarrow L(s\mid R)\ge L(D\mid R)\) for
   all candidates \(D\).
2. A post-2016 theorem: \(\mathcal I_s \Rightarrow\) every ML genome is
   equivalent to \(s\) (uniqueness schema).
3. A published post-2016 counterexample: bridging hypotheses hold but some
   distinct \(D\) has strictly greater likelihood.
4. Any post-2016 paper explicitly citing the 2016 open-question sentence and
   claiming to settle it.

## What is directly sourced vs. inference

- **Source facts:** the titles, years, venues, DOIs, citation counts, and all
  quoted sentences above (recovered from the cited primary abstracts/full text
  and the two scholarly APIs).
- **Analysis:** the classification of each item as "narrows" / "reformulates" /
  "different model", and the claim that none settles the open question. These are
  judgments over the checked citation lists, not a proof of absence.

## Limitations

- Citation indexing is incomplete and 2026 records are still accruing; the
  Semantic Scholar count (38) and OpenAlex count (33, of which 30 post-2017)
  differ, so the examined universe is bounded but not exhaustive.
- Some items were triaged at abstract level; only the plausible candidates were
  read beyond the abstract. Mahajan et al. was checked at arXiv-v3 text level for
  the use of "likelihood"; the absence of an ML sufficiency theorem there is
  based on that text-level check plus the abstract, not a line-by-line proof.
- Paywalled journal versions (e.g., the 2025 TCBB version of Mahajan et al.,
  Luria–Weinberger TIT) were represented by their arXiv/preprint versions.

## Effect on `assemblyp1`

- **No change to the working conclusion:** the exact 2016 question remains
  unresolved in the located post-2016 literature (consistent with
  `docs/literature-status.md`).
- **The diploid extension is a durable new item** worth tracking for any future
  Diploid/coverage packet: Mahajan–Jain–Kashyap shows the field is still
  deriving *necessary* bridging conditions via equal-likelihood ambiguity, not
  *sufficient* ML optimality.
- **No change is forced on the Lean model or the theorem statement.** The
  post-2016 work does not disambiguate the Medvedev–Brudno objective, candidate
  class, or tie semantics; those remain source-ambiguous as documented in
  `docs/source-notes/shomorony-ml-reference.md` and
  `docs/literature/ml-tie-semantics.md`.

## References (new to this audit)

1. D. Mahajan, C. Jain, N. Kashyap. *On the Coverage Required for Diploid Genome
   Assembly.* ISIT 2024; *IEEE/ACM TCBB*, 2025.
   <https://arxiv.org/abs/2405.05734>.
2. N. Luria, N. Weinberger. *Optimal Overlap Detection of Shotgun Reads.* ISIT
   2025; *IEEE Trans. Inf. Theory*, 2026. <https://arxiv.org/abs/2502.13813>.
3. A. Bankevich. *Supregraph: Enabling Information-Optimal Assembly Graph
   Representation of a Read Set.* arXiv:2604.21951, 2026.
   <https://arxiv.org/abs/2604.21951>.
4. A. N. Ravi, A. Vahid, I. Shomorony. *Coded Shotgun Sequencing.* IEEE JSAIT
   3(1):147–159, 2022. <https://arxiv.org/abs/2110.02868>.
5. Y. Grunbaum, E. Yaakobi. *General Coverage Models: Structure, Monotonicity,
   and Shotgun Sequencing.* ISIT 2026. <https://arxiv.org/abs/2510.25305>.
6. M. Mazooji, N. Santhanam. *Substring Density Estimation from Traces.* IEEE
   Trans. Inf. Theory, 2024. DOI `10.1109/TIT.2024.3418377`.
