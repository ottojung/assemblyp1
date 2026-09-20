# Independent literature search (2026-09-20): settlement / citation trail for Shomorony bridging → ML

_Search date: 2026-09-20._
_Independent of `literature-status.md`, `literature-search-independent-2026-09-19.md`, and
`literature-search-citation-graph-2026-09-19.md`. This run used three separate bibliographic
indexes plus live web search, and deliberately re-derived the citation intersection rather than
trusting prior notes._

## Question

Does any primary or reputable work, especially post-2016, settle or materially narrow the
Shomorony–Kim–Courtade–Tse (2016) open question: do the repeat-bridging conditions that make a
read set information-feasible also guarantee that the true sequence is the maximum-likelihood
sequence under the Medvedev–Brudno (2009) read-count objective?

## Method and instruments

1. **Semantic Scholar Graph API** (`api.semanticscholar.org/graph/v1`): fetched the three
   foundational records and their complete forward-citation lists, then intersected them.
2. **OpenAlex API** (`api.openalex.org`): independent citation count and forward-citation list for
   the 2016 paper (`W2515489235`), a different index from Semantic Scholar.
3. **Europe PMC REST search**: reference-based search
   (`REF:"10.1093/bioinformatics/btw450"` combined with `"maximum likelihood"`) and exact-phrase
   full-text search.
4. **Live web search** for the exact open-question wording, the title/DOI with later-year terms,
   and the authors' later work.

All queries were run on 2026-09-20. Counts are as of that date.

## Reproduced citation facts

Source facts (index metadata):

- Semantic Scholar forward-citation counts: Shomorony 2016 = **38**, Medvedev–Brudno 2009 = **107**,
  Bresler–Bresler–Tse 2013 = **98**.
- OpenAlex forward citations of Shomorony 2016 = **33** (a narrower index; it omits some
  conference records that Semantic Scholar includes).
- Refetching the Semantic Scholar sets reproduced the prior intersection exactly:
  - `Shomorony2016 ∩ MedvedevBrudno2009` = **4**: Salmela (SAMA, 2025) and three
    Cairo et al. safe-and-complete records (hydrostructure / practice-to-theory family).
  - `Shomorony2016 ∩ MedvedevBrudno2009 ∩ Bresler2013` = **3**, all three being the Cairo et al.
    safe-and-complete records.
  - `Shomorony2016 ∩ Bresler2013` = **22**.
- Europe PMC `REF:"10.1093/bioinformatics/btw450"` + `"maximum likelihood"` = **2** records:
  SAMA 2025 and “Mechanisms for Hiding Sensitive Genotypes With Information-Theoretic Privacy”
  (2022). The second is unrelated to the assembly objective.

Source-analysis result: this independently reproduces the prior finding that the only works citing
both the bridging line and the ML line are the safe-and-complete graph-theory papers and SAMA
2025, none of which proves a bridging → global-ML implication.

### Caveat on full-text phrase search

Europe PMC `"maximum-likelihood sequence is the true sequence"` returned **0** hits. This is a
**weak** signal, not proof of absence: the 2016 paper is indexed by Europe PMC with abstract only
(no PMC full text record), and most IEEE/conference work is not in Europe PMC full text. The
reference-based query above is the meaningful part of the Europe PMC check.

## Forward citations observed here that were not recorded in prior notes

Source facts (index metadata; full text not read unless stated). These are recorded so a future run
does not have to rediscover them. None is asserted to resolve the question.

1. **Quantum-optimisation genome assembly (2026).** “Scaling Quantum Optimisation Beyond Hardware
   Limits for Real-World Scientific Workloads: Genome Assembly on Current Quantum Hardware,”
   2026, DOI `10.64898/2026.09.04.749434`; and N. G. Sankar, G. Miliotis, S. Caton,
   “Towards High Performance Quantum Computing (HPQ): Parallelisation of the Hamiltonian Auto
   Decomposition Optimisation Framework (HADOF),” arXiv:2604.27836, 2026. Returned in the
   Semantic Scholar forward list; not in OpenAlex. Analysis: quantum-computation framing of a
   genome-assembly workload; no evidence of engagement with the ML question. Metadata-only.
2. **C. Jain, “Coverage-preserving sparsification of overlap graphs for long-read assembly,”**
   *Bioinformatics*, 2023, DOI `10.1093/bioinformatics/btad124` (preprint
   `10.1101/2022.03.17.484715`). Full text checked: it cites Shomorony et al. as an overlap-graph
   sparsification prior, but explicitly notes that the Shomorony/Hui formulations
   “make a simplifying assumption that the input reads are long enough to avoid ambiguity caused
   by repeats,” and studies coverage preservation (whether chromosomes remain spellable as walks),
   not likelihood optimality. Does not mention the open question.
3. **RNA flow-decomposition safety (2022).** “Safety and Completeness in Flow Decompositions for
   RNA Assembly,” WABI 2022, DOI `10.1007/978-3-031-04749-7_11`; journal version “Improving RNA
   Assembly via Safety and Completeness in Flow Decompositions,” *J. Comput. Biol.*, 2022,
   DOI `10.1089/cmb.2022.0261`. Cites both Shomorony 2016 and Bresler 2013. Analysis: graph
   safety/completeness for flow decompositions; different predicate from global ML.
4. **“Optimal compressed representation of high throughput sequence data via light assembly,”**
   *Nature Communications* 9, 2018, DOI `10.1038/s41467-017-02480-6`. Cites Shomorony 2016.
   Analysis: compression/assembly-representation angle; no ML-settlement indication.
5. **“MOMS: A pipeline for scaffolding using multi-optical maps,”** *Molecular Ecology Resources*,
   2023, DOI `10.1111/1755-0998.13842`. Cites Shomorony 2016. Analysis: applied scaffolding
   pipeline; background citation.
6. **Deletion-channel ML/MAP reconstruction (2018–2020).** S. R. Srinivasavaradhan, M. Du,
   S. Diggavi, C. Fragouli: “On Maximum Likelihood Reconstruction over Multiple Deletion
   Channels,” ISIT 2018, DOI `10.1109/ISIT.2018.8437519`; “Symbolwise MAP for Multiple Deletion
   Channels,” ISIT 2019, DOI `10.1109/ISIT.2019.8849567`; “Algorithms for Reconstruction Over
   Single and Multiple Deletion Channels,” *IEEE Trans. Inf. Theory*, 2020,
   DOI `10.1109/TIT.2020.3033513`. Cite Shomorony 2016 and/or Bresler 2013. Analysis: ML/MAP for
   trace/deletion reconstruction; a different problem from global assembly likelihood.
7. **Genotype-privacy works (2022–2023).** B. Jiang, M. Seif, R. Tandon, M. Li, “Mechanisms for
   Hiding Sensitive Genotypes With Information-Theoretic Privacy,” *IEEE Trans. Inf. Theory*,
   2022, DOI `10.1109/TIT.2022.3156276`; “Answering Count Queries for Genomic Data With Perfect
   Privacy,” *IEEE Trans. Inf. Forensics Secur.*, 2023, DOI `10.1109/TIFS.2023.3288812`. Cite
   Shomorony 2016. Analysis: unrelated privacy use of the reference.
8. **“Shannon: An Information-Optimal de Novo RNA-Seq Assembler,”** bioRxiv 039230, 2016. Appears
   in `MedvedevBrudno2009 ∩ Bresler2013`. Analysis: adjacent information-optimal assembly line
   (metadata only); not a bridging → ML settlement.

## What was searched and not found

- No post-2016 work that proves the bridging hypotheses imply the truth is a global ML maximizer
  under the Medvedev–Brudno objective.
- No post-2016 work that proves the truth is the unique ML maximizer up to genome equivalence under
  those hypotheses.
- No published counterexample in which the bridging conditions hold and another candidate has
  strictly greater likelihood.
- No citing work that quotes or responds to the 2016 open-question sentence. The exact phrase
  search in Europe PMC is 0 hits (with the abstract-only caveat above), and web search for the
  sentence returns the 2016 paper itself.

## Epistemic status

- Citation counts, intersection membership, titles, years, and DOIs are **source facts** returned
  by the three index APIs and verified against publisher pages where possible.
- The conclusion that no intersected work settles the question is a **source-analysis result**
  over those facts, not a proof of absence.
- Statements that each adjacent work does not resolve the conjecture are **analysis** unless a
  quoted sentence is given.

## Effect on the repository

1. **The core conclusion is unchanged and now triple-index-confirmed as of 2026-09-20:** the
   bridging → ML question appears open; no settlement located.
2. **No Lean-definition changes** are forced by this run.
3. **Newly recorded adjacent citations** above should be treated as context, not as evidence for
   the conjecture; none supplies a missing implication.
4. The two-index citation-count discrepancy (Semantic Scholar 38 vs OpenAlex 33) is expected index
   coverage variation and is not evidence about the mathematics.

## References (newly recorded here)

1. N. G. Sankar, G. Miliotis, S. Caton. _Towards High Performance Quantum Computing (HPQ):
   Parallelisation of the Hamiltonian Auto Decomposition Optimisation Framework (HADOF)._
   arXiv:2604.27836, 2026. <https://doi.org/10.48550/arXiv.2604.27836>
2. _Scaling Quantum Optimisation Beyond Hardware Limits for Real-World Scientific Workloads:
   Genome Assembly on Current Quantum Hardware._ 2026. <https://doi.org/10.64898/2026.09.04.749434>
3. C. Jain. _Coverage-preserving sparsification of overlap graphs for long-read assembly._
   *Bioinformatics*, 2023. <https://doi.org/10.1093/bioinformatics/btad124>
4. _Safety and Completeness in Flow Decompositions for RNA Assembly._ WABI 2022.
   <https://doi.org/10.1007/978-3-031-04749-7_11>; journal version
   <https://doi.org/10.1089/cmb.2022.0261>
5. _Optimal compressed representation of high throughput sequence data via light assembly._
   *Nature Communications*, 2018. <https://doi.org/10.1038/s41467-017-02480-6>
6. _MOMS: A pipeline for scaffolding using multi-optical maps._ *Molecular Ecology Resources*,
   2023. <https://doi.org/10.1111/1755-0998.13842>
7. S. R. Srinivasavaradhan, M. Du, S. Diggavi, C. Fragouli. _On Maximum Likelihood Reconstruction
   over Multiple Deletion Channels._ ISIT 2018. <https://doi.org/10.1109/ISIT.2018.8437519>
8. B. Jiang, M. Seif, R. Tandon, M. Li. _Mechanisms for Hiding Sensitive Genotypes With
   Information-Theoretic Privacy._ *IEEE Trans. Inf. Theory*, 2022.
   <https://doi.org/10.1109/TIT.2022.3156276>
9. _Shannon: An Information-Optimal de Novo RNA-Seq Assembler._ bioRxiv 039230, 2016.
