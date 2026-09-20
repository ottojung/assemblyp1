# Post-2016 follow-ups on the bridging→ML question: citation contexts and newly recorded adjacent results

_Search date: 2026-09-20._
_Scope: primary/reputable English-language work published after Shomorony et al. (2016) that
explicitly follows up on the repeat-bridging line, cites the 2016 paper, or reformulates the
Medvedev–Brudno (2009) maximum-likelihood objective. This note records only material **not already
present on `main`** in `docs/literature-status.md`, `docs/literature-search-*.md`,
`docs/literature/post2016-ml-likelihood-search-2026-09-20.md`,
`docs/literature/shomorony-group-post2016-identifiability-2026-09-20.md`,
`docs/literature/substring-spectrum-identifiability-2026-09-20.md`, or
`docs/literature/citation-context-and-referent-audit-2026-09-20.md`. Non-English sources,
including Russian-language sources, were excluded._

## Question investigated

Has any post-2016 primary work explicitly followed up on, quoted, proved, refuted, or materially
narrowed the open sentence in `docs/open-problem.md` (Shomorony–Kim–Courtade–Tse 2016): do the
repeat-bridging information-feasibility conditions guarantee that the true sequence is the
maximum-likelihood sequence under the Medvedev–Brudno (2009) read-count formulation?

## Method and instruments (all run 2026-09-20)

- Semantic Scholar Graph API: forward citations of Shomorony et al. 2016
  (`DOI:10.1093/bioinformatics/btw450`, 38 citing works) **with citation contexts**; forward
  citations of Medvedev–Brudno 2009 (`DOI:10.1089/cmb.2009.0047`) and Bresler et al. 2013
  (`DOI:10.1186/1471-2105-14-S5-S18`) with contexts.
- OpenAlex REST API: `cites:W2515489235` (Shomorony 2016), `cites:W2035596374` (Medvedev–Brudno
  2009), `cites:W2165847428` (Bresler 2013) since 2017; pairwise/triple citation intersections;
  topical `search=` queries.
- Europe PMC REST full-text search for the exact open-question phrase and bridging+ML combinations.
- arXiv API (`search_query`) for `"bridging conditions" AND assembly`, `"interleaved repeat"`,
  `"triple repeat" AND assembly`, `"maximum likelihood" AND "genome assembly" AND repeats`.
- Targeted live web search for the exact open-question wording.

## Headline result

**No located post-2016 work settles or explicitly addresses the exact 2016 implication.** This
packet reproduces the negative conclusion by a different instrument mix and adds the direct
citation-context check.

## 1. Explicit-follow-up / citation-context negative (source facts)

1. **No citing context mentions likelihood.** The Semantic Scholar forward-citation list of
   Shomorony et al. 2016 returned 38 citing works; for each returned `contexts` list, the
   sentences were scanned for `likelihood`/`maximum likelihood`/`ML`. No post-2016 citing context
   contains any of these terms. The 2016 "maximum-likelihood sequence is the true sequence"
   sentence is never quoted, paraphrased, or replied to. The dominant citation frames are
   information-feasibility / the "assembly limit" and NP-hardness of optimization formulations.
2. **Europe PMC full-text phrase search.** `"maximum-likelihood sequence is the true sequence"` →
   0 hits. `"bridging conditions" AND "maximum likelihood" AND "genome assembly"` → 0 hits. The
   only hit for `SHOMORONY AND "maximum likelihood"` is an unrelated 2024 multiple-sequence-
   alignment paper.
3. **arXiv API.** `all:"bridging conditions" AND all:assembly` → 0 entries;
   `all:"triple repeat" AND all:assembly` → 0; `all:"maximum likelihood" AND all:"genome assembly"
   AND all:repeats` → 0 (the single `"interleaved repeat"` hit is an unrelated computer-security
   paper).
4. **Citation intersection unchanged.** OpenAlex works citing **both** Shomorony 2016 and
   Medvedev–Brudno 2009 since 2017 are exactly Cairo et al. 2023 (`10.1145/3632176`) and the SAMA
   preprint/journal pair (`10.1101/2024.07.10.602853`, `10.1186/s13015-025-00280-y`). The triple
   intersection with Bresler 2013 is Cairo et al. alone. None contains a bridging⇒ML theorem.

## 2. Newly recorded adjacent results (not previously in the repository)

### 2.1 Hybrid-sequencing feasibility conditions — Chen–Ghaffari–Qian–Yoon (2017)

- **Citation:** C.-C. Chen, N. Ghaffari, X. Qian, B.-J. Yoon, "Optimal hybrid sequencing and
  assembly: Feasibility conditions for accurate genome reconstruction and cost minimization
  strategy," *Computational Biology and Chemistry* 69:153–163, 2017, DOI
  [`10.1016/j.compbiolchem.2017.03.016`](https://doi.org/10.1016/j.compbiolchem.2017.03.016).
  Thesis version: C.-C. Chen, "Emerging Topics in Genome Sequencing and Analysis," Texas A&M
  University, 2017.
- **Source fact (abstract/paper):** derives the conditions for whole-genome reconstruction from
  **multiple read sources** at a given confidence level and combines read sources by constrained
  discrete optimization to minimize sequencing cost; the feasibility conditions are the
  "coverage condition" together with **"bridging conditions"** for triple/interleaved/self repeats,
  with a critical read length `ℓ_crit = 1 + max{ℓ_inter, ℓ_triple, ℓ_self}`. It introduces an
  enhanced multi-bridging algorithm for hybrid read sets.
- **Relation to the open question (analysis):** this is the closest located **post-2016 explicit
  follow-up on the bridging conditions as hypotheses**. By the thesis's own summary it extends
  Bresler–Bresler–Tse (2013) "from a single read source" to hybrid sources, and the paper is
  explicitly about `ε`-feasible *complete reconstruction*. It does not engage the
  Medvedev–Brudno maximum-likelihood formulation. It therefore strengthens the hypothesis-side
  literature without touching the bridging⇒ML gap.

### 2.2 Safe and complete metagenomic assembly — Obscura Acosta–Mäkinen–Tomescu (2018)

- **Citation:** N. Obscura Acosta, V. Mäkinen, A. I. Tomescu, "A safe and complete algorithm for
  metagenomic assembly," *Algorithms for Molecular Biology* 13:3, 2018, DOI
  [`10.1186/s13015-018-0122-7`](https://doi.org/10.1186/s13015-018-0122-7).
- **Source fact (abstract):** characterizes the safe walks common to **all** metagenomic assembly
  solutions and gives a safe-and-complete polynomial algorithm, within the Tomescu–Medvedev
  safe-and-complete framework.
- **Relation (analysis):** a post-2016 extension of the safe-and-complete line from single genomes
  to multiple circular genomes. Its correctness predicate is graph-consistency safety across all
  solutions, which is logically distinct from global maximum-likelihood optimality (see
  `docs/literature-status.md` §11). It does not address the 2016 ML question.

### 2.3 Lower-venue identifiability extension (recorded with caveat)

- M. Herring, "A Probabilistic Analysis of Shotgun Sequencing for Metagenomics," *SIAM
  Undergraduate Research Online*, 2022, DOI
  [`10.1137/22s1472437`](https://doi.org/10.1137/22s1472437) (0 citations as of 2026-09-20).
- **Source fact (abstract):** analyzes, asymptotically in genome length, the identifiability of a
  collection of `M` genomes from shotgun reads, extending Bresler-style identifiability reasoning
  to metagenomes.
- **Relation (analysis):** an identifiability statement, not a likelihood statement; venue is a
  student research journal, so it is recorded only for completeness and carries no weight.

### 2.4 Already recorded elsewhere (no duplication)

- Y. Grunbaum, E. Yaakobi, "General Coverage Models: Structure, Monotonicity, and Shotgun
  Sequencing," ISIT 2026, arXiv:2510.25305, DOI `10.1109/ISIT62367.2026.11653923`, gives exact
  coverage-time results for cyclic/non-cyclic fixed-length window models. It is already recorded
  on unmerged branch `agent/literature-audit-0919b`
  (`docs/literature-audit-forward-citations-2026-09-19.md`) and branch
  `literature/ghodsi-truth-max-2026-09-19`; listed here only so a later reader does not
  re-record it.

## 3. Closest positive maximum-likelihood result remains non-transferable

The strongest post-2016 theorem of the shape "the maximum-likelihood object is the true object,
to the information limit" remains Bagaria–Ding–Tse–Wu–Xu, *Hidden Hamiltonian Cycle Recovery via
Linear Programming*, *Operations Research* 68(1):53–70, 2020 (already recorded in
`docs/literature/post2016-ml-likelihood-search-2026-09-20.md`). Its observation model (independent
pairwise contig-linking weights) is not the uniform length-`L` substring model, and it has no
repeat-bridging hypotheses, so it does not transfer to the 2016 implication.

## Epistemic classification

| Claim | Status |
|---|---|
| Citation counts, DOIs, venues, and citation-context scan | Source fact (S2/OpenAlex/Europe PMC/arXiv APIs, 2026-09-20) |
| Chen et al. 2017 feasibility/bridging conditions and hybrid multibridging | Source fact (abstract, publisher page, thesis) |
| Obscura Acosta et al. 2018 safe-and-complete metagenomic algorithm | Source fact (abstract) |
| Herring 2022 metagenomic identifiability | Source fact (abstract); low-venue caveat |
| No post-2016 work settles or explicitly addresses the 2016 implication | Source-analysis result, not a proof of absence |
| Each adjacent work does not resolve the question | Analysis unless a quoted sentence is given |

## Limitations

Citation indexing is incomplete and 2026 records are still accruing. Some works were triaged at
abstract level. Europe PMC and arXiv full-text coverage is partial. This is a bounded search, not
an exhaustive proof that no settlement exists.

## Effect on the repository and issue #36

1. Core status unchanged: the bridging→ML question appears open as of 2026-09-20.
2. New durable citations added to the record: Chen–Ghaffari–Qian–Yoon (2017); Obscura
   Acosta–Mäkinen–Tomescu (2018); Herring (2022, low-venue caveat).
3. No source disambiguates the Medvedev–Brudno referent, candidate class, or tie semantics; the
   four readings in issue #36 remain open.
4. No Lean-definition changes are forced.

## References (newly recorded here)

1. C.-C. Chen, N. Ghaffari, X. Qian, B.-J. Yoon. *Optimal hybrid sequencing and assembly:
   Feasibility conditions for accurate genome reconstruction and cost minimization strategy.*
   Computational Biology and Chemistry 69:153–163, 2017.
   <https://doi.org/10.1016/j.compbiolchem.2017.03.016>
2. N. Obscura Acosta, V. Mäkinen, A. I. Tomescu. *A safe and complete algorithm for metagenomic
   assembly.* Algorithms for Molecular Biology 13:3, 2018.
   <https://doi.org/10.1186/s13015-018-0122-7>
3. M. Herring. *A Probabilistic Analysis of Shotgun Sequencing for Metagenomics.* SIAM
   Undergraduate Research Online, 2022. <https://doi.org/10.1137/22s1472437>
