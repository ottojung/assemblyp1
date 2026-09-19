# Literature-settlement audit: does any published work settle the bridging→ML question?

_Status: independent literature audit, 2026-09-19. Read-only web/scholarly work; no Lean edits._

_Independence: this note was produced from primary sources and the author-copy full texts, not by
trusting repository docs. It is deliberately scoped to **settlement** (a published proof,
counterexample, or equivalent theorem for the exact implication). It does not redo the
source-provenance reconciliation packet (candidate class, length semantics, tie semantics) or the
binomial kernel-check packet; where it touches those it only records the mismatch and points to
them._

_Complementary prior work in the repo: `docs/literature-status.md` (broad search, 2026-09-17) and the
unmerged forward-citation audit on `agent/literature-audit-0919b`. This audit independently recovered
the primary text and citation universes and adds a versioning finding and an adjacent-theorem
mismatch ledger; it reaches the same settlement verdict._

## Question investigated

The exact published sentence is:

> "Understanding whether bridging conditions can be used to guarantee that the
> maximum-likelihood sequence is the true sequence is currently an open question."

from Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, and David N. C. Tse,
"Information-optimal genome assembly via sparse read-overlap graphs," *Bioinformatics* 32(17),
2016, i494–i502, DOI [10.1093/bioinformatics/btw450](https://doi.org/10.1093/bioinformatics/btw450).

The question is whether there is a **published** proof, counterexample, or equivalent theorem for:

- **(P1, maximizer schema)** for every read set `R` and true circular sequence `s`,
  `R ∈ I_s ⇒ L(s | R) ≥ L(D | R)` for every candidate genome `D`;
- **(P2, uniqueness schema)** `R ∈ I_s ⇒` every maximizer of `L(· | R)` is equivalent to `s`
  (up to the congruence of the model).

"Equivalent theorem" means a theorem whose hypotheses are the source-faithful bridging conditions
and whose conclusion is one of P1/P2 under a source-faithful likelihood. It explicitly does **not**
mean an assembler that succeeds under bridging, nor a graph-consistency statement.

## Methods and reproducible search scope

Primary text was recovered from author copies and open full texts; scholarly APIs were queried
directly with Python `urllib` (no third-party script).

| Source | Endpoint / query | Result |
| --- | --- | --- |
| Shomorony author copy (accepted version, 9 pp.) | `http://people.eecs.berkeley.edu/~courtade/pdfs/InfoOptimalAssy.pdf` | full text recovered (pypdf) |
| Shomorony extended report (23 pp.) | `http://stanford.edu/~gkamath/nsgIlan.pdf` | full text recovered |
| Medvedev–Brudno | `https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/` and `http://www.cs.toronto.edu/~brudno/medvedev_MLA.pdf` | §6.1/§6.2 recovered |
| Bresler–Bresler–Tse | `https://pmc.ncbi.nlm.nih.gov/articles/PMC3706340/` | Theorem 1 and proof context recovered |
| Semantic Scholar Graph API | `paper/DOI:10.1093/bioinformatics/btw450/citations?fields=title,year,venue,externalIds,abstract,authors&limit=100` | 38 citing works |
| OpenAlex | `works/doi:10.1093/bioinformatics/btw450` | W2515489235, `cited_by_count` 33 |
| OpenAlex | `works?filter=cites:W2515489235,from_publication_date:2017-01-01&per-page=200` | 30 post-2017 citing works |
| OpenAlex | `works/doi:10.1089/cmb.2009.0047` + `cites:W2035596374,from_publication_date:2020-01-01` | 129 total; 15 since 2020 triaged |
| OpenAlex | `works/doi:10.1186/1471-2105-14-S5-S18` + `cites:W2165847428,from_publication_date:2020-01-01` | 95 total; 42 since 2020 triaged |
| Web search | exact phrase `"maximum-likelihood sequence is the true sequence"` (with/without `assembly`) | only signal-processing MLSE and the 2016 source |
| Web search | `bridging conditions maximum likelihood assembly open question`, plus terminology variants (`interleaved repeat`, `triple repeat`, `identifiability`, `safe assembly`, `shotgun sequencing channel`, `trace reconstruction`, `substring spectrum`) | no settlement hit |

Citation counts differ between indexes (33 vs 38) and 2026 records are still accreting, so the
universe examined is **bounded, not exhaustive**.

## Primary-source recovery (source facts)

### Shomorony et al. 2016

- **Model.** Circular sequence `s` of length `G`; `N` error-free reads of common length `L`, each
  drawn independently and uniformly from the `G` length-`L` circular substrings, with multiplicity.
- **Information-feasible set**, Eq. (1), p. i497:
  `I_s = { R : R covers s; triple repeats in s are all-bridged; interleaved repeats in s are bridged }`.
- **Reconstruction theorem**, Theorem 1 / Corollary 1: if `R ∈ I_s`, NOT-SO-GREEDY builds a
  read-overlap graph whose unique Eulerian cycle spells `s` up to cyclic shifts. This is an
  algorithmic reconstruction statement.
- **Open sentence location and immediate context** (Discussion, p. i501). The sentence closes this
  paragraph:

  > "Another direction for future work, from a more theoretical standpoint, is understanding whether,
  > in information-feasible instances of the AP, the output of NOT-SO-GREEDY coincides with the
  > solution of a combinatorial optimization problem. ... there is no guarantee that this sequence
  > corresponds to the solution of an optimization-based formulation of the AP such as those
  > considered by Nagarajan and Pop (2009) and Medvedev and Brudno (2009). As mentioned by Medvedev
  > and Brudno (2009), parsimony-based formulations tend to encourage an over-collapsing of the
  > repeats, and the optimal solution is in general different from the true underlying sequence.
  > The maximum-likelihood formulation of the AP ... seems to be robust to these issues, and thus a
  > good candidate for the 'correct' formulation. Understanding whether bridging conditions can be
  > used to guarantee that the maximum-likelihood sequence is the true sequence is currently an open
  > question."

  **Consequence (analysis):** the open question is not a standalone conjecture about `I_s`; it is the
  ML instance of a broader question about whether NOT-SO-GREEDY's unique recovery coincides with an
  optimization optimum. The likelihood objective and the candidate class are referenced only by
  citation, not restated in the sentence.

- **Versioning finding (new to this audit).**   The 23-page extended report
  (`nsgIlan.pdf`, "Optimal Sequence Assembly via Sparse Read-Overlap Graphs") mentions the
  maximum-likelihood formulation only in passing in its related-work introduction, and its
  Discussion **does not contain the phrase "open question"** and does not pose the ML implication.
  Instead it ends by replacing the ML avenue with a genie-aided formulation: "... consider a
  genie-aided formulation where the target genome length `G` is given ... provides a better setting
  to analyze the computational complexity ... of reconstructing the true sequence," then discusses
  GHC NP-hardness. The open sentence is therefore a feature of the accepted
  ISMB/*Bioinformatics* version, not of the extended technical report. A future statement must not
  silently attribute it to both versions.

### Medvedev–Brudno 2009

- **§6.1 exact objective.** `D` a circular genome of length `N(D)`, `d_i` the number of occurrences
  of `k`-molecule `i`, `x_i` observed counts from `n` independent uniform trials:
  `L(D | x) = n! / (∏ x_i!) · ∏ (d_i / N(D))^{x_i}`. This is the global read-count multinomial.
- **§6.2 approximation.** To make `−log L` separable they replace the multinomial by the product of
  individual binomial marginals and replace `N(D)` by an externally known length `N`. Their
  optimization then runs on a **transitively reduced bidirected overlap graph**; the flow is
  described as "a (non-contiguous) assembly." So the object actually optimized is neither the exact
  multinomial nor a circular genome in general.

### Bresler–Bresler–Tse 2013

- **Theorem 1 (necessity).** "Given a DNA sequence `s` and a set of reads, if there is a pair of
  interleaved repeats or a triple repeat whose copies are all unbridged, then there is another
  sequence `s'` of the same length under which the likelihood of observing the reads is the same."
  This gives a concrete non-identifiability mechanism of the form
  `unbridged-repeat pattern ⇒ ∃ s' ≠ s : L(s'|R) = L(s|R)`.
- It is a **lower-bound / necessity** statement; it does not show that satisfying the stronger
  all-bridged conditions makes `s` globally ML, and it does not exclude a competitor with strictly
  greater likelihood after bridging is imposed.

## Assumption-mismatch matrix

Cells are the source-faithful reading; "consequence" names why a result in that model does not
transfer to the target implication.

| Dimension | Shomorony et al. 2016 | Bresler et al. 2013 | Medvedev–Brudno 2009 | Consequence for settlement |
| --- | --- | --- | --- | --- |
| genome topology | circular, single strand | circular/long sequence | circular, double-stranded (bidirected) | MB equality is reverse-complement-aware; Shomorony uses cyclic shift |
| genome length | fixed `G` known to model | fixed true length | `N(D)` candidate-dependent in §6.1; external fixed `N` in §6.2 | P1 is sensitive to whether candidate length varies |
| read length | fixed `L` | fixed `L` | fixed `k` | compatible |
| read errors | none | none | none (assumed) | compatible |
| sampling | `N` iid uniform length-`L` reads with multiplicity | `N` iid uniform reads | `n` iid uniform `k`-molecules | compatible |
| multiplicity | retained in `R` | retained in `R` | retained via counts `x_i` | compatible, but graph algorithms may deduplicate |
| candidate class | arbitrary genomes compared against `s` (never enumerated by the paper) | arbitrary `s'` of the same length | §6.1 circular genomes; §6.2 integral flows over a read-derived bidirected overlap graph (non-contiguous) | **Largest mismatch:** the ML class intended by the sentence is unspecified |
| genome equivalence | cyclic shift | same length, exact sequence | reverse complement / bidirected | tie and uniqueness semantics differ |
| repeat definition | maximal repeated substrings; triple repeats; interleaved pairs | same (source) | `k`-molecule occurrence counts | repeat predicates do not map onto MB counts |
| bridging definition | a copy is bridged if some read strictly extends beyond it on both sides | same | absent | bridging is a property of latent read placement, not of observed counts |
| ML objective | referenced, not defined | "likelihood" used only in necessity | exact multinomial (§6.1) / binomial-marginal approximation (§6.2) | at least three inequivalent objectives are in scope |
| tie semantics | not specified | equal-likelihood competitor | maximization, ties possible | P1 vs P2 not disambiguated by source |

**Latent/observed caveat (analysis).** Bridging is defined via the realized start positions of the
true reads, while `L(D | R)` is a function of the observed read multiset. Any candidate comparison
must therefore keep the sequencing realization and the observable count vector distinct; otherwise
the likelihood estimator is given information it does not observe.

## Settlement search: results

### A. Post-2016 works citing the 2016 source

The 30 OpenAlex post-2017 and 38 Semantic Scholar citing works were triaged by title/venue/year and
read at abstract or full-text level where plausible. They fall into:

- **same information-feasibility line, still necessity-only:** Mahajan–Jain–Kashyap, "On the
  Coverage Required for Diploid Genome Assembly" (ISIT 2024; *IEEE/ACM TCBB* 2025). It extends the
  repeat/bridging analysis to diploid genomes and explicitly reuses equal-likelihood ambiguity
  ("... the likelihood of observing the reads is the same for more than one genome; hence, correct
  reconstruction is not possible"). No ML sufficiency theorem.
- **graph-representability / safe-and-complete:** supregraph (2026), hydrostructure, omnitig and
  WABI 2024 works. Safety across graph-consistent genomes is a different predicate from global
  maximum probability.
- **changed observation/coding model:** coded/shotgun-sequencing-channel, coverage-model, and
  substring-density-from-traces lines. These do not use bridging and ask capacity-type questions.
- **practical likelihood:** SAMA (2025), SWALO, GAML, CGAL. Likelihood is used as a score or
  heuristic; no bridging ⇒ ML theorem.
- **unrelated application:** light assembly, Skmer, privacy, scaffolding, quantum-assembly, etc.

**No work in this set proves, refutes, restates-and-settles, or claims to settle P1/P2.**

### B. Citation universes of the two foundational papers

Independently triaged recent citing works of Medvedev–Brudno (15 since 2020) and Bresler et al.
(42 since 2020). The only ML-adjacent items are "Accurate determination of node and arc
multiplicities in de Bruijn graphs using conditional random fields" (copy-count inference, not a
bridging implication), "Constructing a genome assembly that has the maximum likelihood"
(arXiv:1302.4391, below), and the safety/complexity lines. No bridging→ML theorem.

### C. Adjacent "equivalent theorem" candidates and why they are not equivalent

- **Complete/worst-case substring-spectrum reconstruction** (Ukkonen 1992; Pevzner 1995;
  Gabrys–Milenkovic; Marcovich–Yaakobi 2020; "Generalized Unique Reconstruction From Substrings",
  IEEE TIT 2023; "Multi-strand Reconstruction from Substrings"). These concern uniqueness from a
  complete (or adversarially damaged) `L`-multispectrum, not a finite iid sample, and conclude
  **spectrum equality**, not likelihood maximization. Different observation model → no equivalence.
- **Trace reconstruction / substring density from traces** (Mazooji–Santhanam; instance-based trace
  reconstruction 2024). Traces are subsequences, and the target is a rate/density, not assembly ML.
- **Shotgun sequencing channel capacity** (Ravi–Vahid–Shomorony, JSAIT 2022; ISIT 2022; converse
  with erasures ITW 2025). A **coded** setting with a codebook and ML decoding of a codeword, not
  the assembly ML over arbitrary genomes; bridging is not part of the model.
- **Multiple-sequence/metagenomic reconstruction** (Levick–Shomorony; Herring 2022). Identifiability
  thresholds for a collection of genomes; no bridging and no ML optimality.
- **Safe-and-complete contig assembly** (Tomescu–Medvedev; Rahmani–Medvedev). "Appears in every
  graph-consistent genome" ≠ "has greatest probability under the read model."
- **Eulerian/Hamiltonian pedagogy** (Medvedev–Pop, PLoS Comput Biol 2021). Explains why cycle
  finding is not the practical problem; does not address the ML question.
- **ML as an integer program/convex relaxation** (arXiv:1302.4391, "Constructing a genome assembly
  that has the maximum likelihood"). It states that the integer program "does not enforce global
  contiguity. Therefore the optimal solution is an upper bound on the probability for the optimal
  assembly," and rounds to Eulerian graphs. This is close to MB §6.2's non-contiguity phenomenon,
  but it has no bridging hypotheses and does not compare to the true sequence.
- **Phase transition in SCS complexity** (Fernández–Martín-Mayor–Yllanes, PRE 2024). About
  computational complexity, not likelihood-vs-truth.

None of these can be converted to P1/P2 without an additional equivalence lemma that no located
source proves (and several would be false as stated under the different observation models).

## Settlement ledger

| Candidate result | Exact proposition it would need to establish | Blocking assumption mismatch | Verdict |
| --- | --- | --- | --- |
| Bresler et al. Thm 1 (2013) | `I_s ⇒` P1/P2 | Only necessity (`all-unbridged ⇒ equal likelihood`); conclusion weaker than `I_s`; no sufficiency | Not a settlement |
| Shomorony et al. Thm 1/Cor 1 (2016) | `I_s ⇒` P1/P2 | Concludes unique Eulerian cycle, not global likelihood optimality | Not a settlement |
| MultiBridging Thm 6 | `I_s ⇒` P1/P2 | Algorithmic reconstruction guarantee | Not a settlement |
| HINGE (2017) | `I_s ⇒` P1/P2 | Repeat-resolution objective, no ML comparison | Not a settlement |
| Medvedev–Brudno (2009) | defines P1/P2 | Defines objective and notes parsimony≠truth; no bridging hypothesis; §6.1 vs §6.2 differ | Not a settlement (the statement is the question) |
| Diploid coverage (2024/2025) | `I_s ⇒` P1/P2 | Diploid model; necessity only | Not a settlement |
| Shotgun channel capacity (2022–2025) | `I_s ⇒` P1/P2 | Coded, ML-decoding of a codebook; no bridging | Not equivalent |
| Spectrum/multispectrum uniqueness | `I_s ⇒` P1/P2 | Complete/worst-case spectrum; equality not likelihood | Not equivalent |
| Safe-and-complete omnitigs | `I_s ⇒` P1/P2 | Graph consistency, not probability | Not equivalent |
| arXiv:1302.4391 ML IP/relaxation | `I_s ⇒` P1/P2 | Non-contiguous relaxation; no bridging | Not equivalent |

## Negative-result ledger (specifically searched for, not found)

1. A post-2016 theorem `R ∈ I_s ⇒ L(s|R) ≥ L(D|R)` for all candidates `D`.
2. A post-2016 theorem `R ∈ I_s ⇒` every ML maximizer is equivalent to `s`.
3. A published counterexample: `I_s` holds for a finite instance while a distinct `D` has strictly
   greater `L`.
4. Any post-2016 work citing the 2016 sentence and claiming to settle it.
5. Any source that disambiguates which Medvedev–Brudno objective (exact multinomial, fixed-length
   multinomial, or §6.2 binomial approximation) and which candidate class (circular genomes vs
   flow-feasible non-contiguous assemblies) the 2016 sentence intends.

## What would count as settlement (unchanged)

A positive settlement is a proof of a source-faithful P1 or P2 (with the objective, candidate class,
and equivalence convention justified from primary sources). A negative settlement is a finite
counterexample satisfying the faithfully formalized `I_s` hypotheses and violating the faithfully
formalized ML conclusion, with a kernel-checkable certificate. A finite computation is evidence
unless its completeness is proved.

## Effect on `assemblyp1`

- **No change to the working conclusion.** The exact 2016 sentence remains unresolved in the located
  literature. This audit independently reproduced the forward citation universe and adds the
  versioning finding; it does not upgrade or downgrade the open-problem status.
- **Durable new source-fidelity item:** the open sentence is present in the accepted
  *Bioinformatics* version and absent from the 23-page extended report, whose Discussion instead
  emphasizes a genie-aided fixed-length formulation. Any formal statement should cite the journal
  version and should not attribute the open question to the extended report.
- **No change forced on the Lean model.** The objective, candidate class, and tie-semantics
  ambiguities documented in `docs/source-notes/` and `docs/literature/ml-tie-semantics.md` remain;
  no located post-2016 work disambiguates them.

## Limitations

- Scholarly indexing is incomplete and 2026 records are still being added; counts differ across
  Semantic Scholar (38) and OpenAlex (33 / 30 post-2017). The examined set is bounded, not
  exhaustive.
- Paywalled journal versions were represented in some cases by author/preprint copies; the versioning
  finding was established from two author-hosted copies and should be re-checked against the
  publisher PDF if it becomes load-bearing.
- Several adjacent items were triaged at abstract/full-text level rather than line-by-line; the
  absence claims are negative search results, not proofs of non-existence.

## References (primary and directly read)

1. I. Shomorony, S. H. Kim, T. A. Courtade, D. N. C. Tse. *Information-optimal genome assembly via
   sparse read-overlap graphs.* Bioinformatics 32(17):i494–i502, 2016.
   <https://doi.org/10.1093/bioinformatics/btw450>. Accepted author copy:
   <http://people.eecs.berkeley.edu/~courtade/pdfs/InfoOptimalAssy.pdf>. Extended report:
   <http://stanford.edu/~gkamath/nsgIlan.pdf>.
2. P. Medvedev, M. Brudno. *Maximum Likelihood Genome Assembly.* J. Comput. Biol. 16(8):1101–1116,
   2009. <https://doi.org/10.1089/cmb.2009.0047>. Open text:
   <https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/>.
3. G. Bresler, M. Bresler, D. Tse. *Optimal assembly for high throughput shotgun sequencing.* BMC
   Bioinformatics 14(Suppl 5):S18, 2013. <https://doi.org/10.1186/1471-2105-14-S5-S18>. Open text:
   <https://pmc.ncbi.nlm.nih.gov/articles/PMC3706340/>.
4. G. M. Kamath, I. Shomorony, F. Xia, T. A. Courtade, D. N. Tse. *HINGE: long-read assembly
   achieves optimal repeat resolution.* Genome Research 27(5):747–756, 2017.
   <https://doi.org/10.1101/gr.216465.116>.
5. D. Mahajan, C. Jain, N. Kashyap. *On the Coverage Required for Diploid Genome Assembly.* ISIT
   2024; IEEE/ACM TCBB 2025. <https://arxiv.org/abs/2405.05734>.
6. S. Marcovich, E. Yaakobi. *Reconstruction of Strings From Their Substrings Spectrum.* IEEE Trans.
   Inf. Theory, 2020. <https://doi.org/10.1109/isit44484.2020.9174113> (see also the 2020/2023
   generalized-unique-reconstruction line).
7. P. Medvedev, M. Pop. *What do Eulerian and Hamiltonian cycles have to do with genome assembly?*
   PLoS Comput. Biol. 17(5):e1008928, 2021.
   <https://doi.org/10.1371/journal.pcbi.1008928>.
8. *Constructing a genome assembly that has the maximum likelihood.* arXiv:1302.4391.
   <https://arxiv.org/abs/1302.4391>.
9. L. A. Fernández, V. Martín-Mayor, D. Yllanes. *Phase transition in the computational complexity of
   the shortest common superstring and genome assembly.* Phys. Rev. E 109:014133, 2024.
   <https://doi.org/10.1103/physreve.109.014133>.
10. A. N. Ravi, A. Vahid, I. Shomorony. *Coded Shotgun Sequencing.* IEEE JSAIT 3(1):147–159, 2022.
    <https://arxiv.org/abs/2110.02868>.
