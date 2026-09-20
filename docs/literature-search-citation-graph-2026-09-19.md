# Independent citation-graph literature search: bridging → maximum-likelihood

_Search date: 2026-09-19._
_Independent of `literature-status.md`, `literature-search-2026-09-19.md`, and `literature-search-post2016-durable.md`; it was run as a separate desk search and reaches the same conclusion by a different route._

## Question investigated

Does any primary/reputable, English-language work (especially post-2016) settle or
materially narrow the Shomorony–Kim–Courtade–Tse (2016) open question: whether the
repeat-bridging conditions that make a read set information-feasible also guarantee
that the true sequence is the maximum-likelihood sequence under the
Medvedev–Brudno (2009) read-count objective?

## Method

This search deliberately did **not** rely on keyword matching alone. The main
instrument was the Semantic Scholar Graph API citation graph, which is
independently reproducible:

1. Forward-citation lists were pulled for the three foundational sources:
   - Shomorony, Kim, Courtade, Tse (2016), DOI `10.1093/bioinformatics/btw450`;
   - Medvedev, Brudno (2009), DOI `10.1089/cmb.2009.0047`;
   - Bresler, Bresler, Tse (2013), DOI `10.1186/1471-2105-14-S5-S18`.
2. The citing sets were intersected pairwise and as a triple. A work citing **both**
   the bridging/information-feasibility line and the maximum-likelihood formulation
   is the natural place a bridging→ML theorem would appear; the intersection is
   therefore a small, high-signal candidate set.
3. Candidate titles were then checked against publisher/arXiv pages and abstracts,
   and complementary web searches were run on the exact problem wording,
   terminology variants, and the authors' later work.

Databases/indexes used: Semantic Scholar Graph API (citation graph + abstracts),
arXiv, PubMed Central, publisher landing pages (Bioinformatics, Genome Research,
BMC Bioinformatics, IEEE, LIPIcs), and general web search. Non-English sources were
excluded. The search date is 2026-09-19; citation counts are as of that date.

## Direct result of the intersection

Citing sets at search time: Shomorony 2016 = 38, Medvedev–Brudno 2009 = 107,
Bresler et al. 2013 = 98.

- `Shomorony2016 ∩ MedvedevBrudno2009` = **4** Semantic Scholar records:
  - Cairo, Khan, Rizzi, Schmidt (2020), _Genome assembly, a universal theoretical
    framework: unifying and generalizing the safe and complete algorithms_
    (arXiv:2011.12635 family).
  - Cairo, Rizzi, Tomescu, Zirondelli (2020/2021), _Genome Assembly, from Practice to
    Theory: Safe, Complete and Linear-Time_, DOI `10.1145/3632176`.
  - Cairo, Khan, Rizzi, Schmidt, Tomescu, Zirondelli (2020), _The Hydrostructure: a
    Universal Framework for Safe and Complete Algorithms for Genome Assembly_,
    arXiv:2011.12635. (The two 2020 Cairo et al. records may be duplicate/version
    records of one line of work; the bibliographic distinction is not load-bearing
    for this search.)
  - Salmela (2025), _Sama: a contig assembler with correctness guarantee_,
    DOI `10.1186/s13015-025-00280-y`.
- `Shomorony2016 ∩ Bresler2013` = 22 papers (mostly the authors' own
  information-theory line plus the safe-and-complete line).
- `MedvedevBrudno2009 ∩ Bresler2013` = 14 papers.
- `Shomorony2016 ∩ MedvedevBrudno2009 ∩ Bresler2013` = **3**, all three of them the
  Cairo et al. safe-and-complete papers above.

**Source-analysis result.** The works that cite both the bridging line and the
maximum-likelihood line are exactly the safe-and-complete graph-theory papers and
SAMA 2025. None of them contains a theorem connecting the Shomorony bridging
hypotheses to global maximum-likelihood optimality; they either characterize
graph-consistent safety (omnitigs/hydrostructure) or bound local misassembly
probability (SAMA). This is a reproducible negative result, not a proof of absence.

## Newly recorded adjacent citations

These were not named in the existing repository literature notes. Each is adjacent
to the conjecture in model or objective, but none proved or disproved it. The
one-line relevance statements below are **analysis**, not assertions by the authors
unless quoted.

1. **J. Hui, I. Shomorony, K. Ramchandran, T. A. Courtade**, "Overlap-based genome
   assembly from variable-length reads," ISIT 2016, DOI `10.1109/ISIT.2016.7541453`.
   _Already in status docs; re-confirmed by the citation graph._

2. **K.-K. Lam, A. Khalak, D. Tse**, "Near-optimal assembly for shotgun sequencing
   with noisy reads," _BMC Bioinformatics_ 15(Suppl 9):S4, 2014,
   DOI `10.1186/1471-2105-15-S9-S4`.
   - Source fact (from cited context and abstract): extends the
     Bresler–Bresler–Tse bridging/information-feasibility analysis from error-free
     reads to noisy reads, giving near-optimality guarantees for a reconstruction
     algorithm.
   - Analysis: strengthens the _algorithmic reconstruction_ line, not the ML
     optimality line. It does not compare the truth to arbitrary candidates under a
     likelihood objective.

3. **A. S. Motahari, K. Ramchandran, D. Tse, N. Ma**, "Optimal DNA shotgun
   sequencing: noisy reads are as good as noiseless reads," ISIT 2013,
   arXiv:1304.2798.
   - Source fact: for the i.i.d. DNA model, noisy reads achieve the same
     read-length/coverage requirement as noiseless reads below an error threshold;
     the achievability scheme uses greedy assembly with a maximum-likelihood
     error-correction stage.
   - Analysis: uses ML only for base-level error correction, not as a global assembly
     objective; does not address the bridging→ML conjecture.

4. **A. N. Ravi, A. Vahid, I. Shomorony**, "Coded Shotgun Sequencing," _IEEE JSAIT_,
   2022, DOI `10.1109/JSAIT.2022.3151737`.
   - Analysis: coding-theoretic treatment of the shotgun-sequencing channel; about
     reliable information embedding/reconstruction rates, not the ML assembly
     objective. Same author group; no resolution.

5. **K. Mazooji, I. Shomorony**, "Substring Density Estimation From Traces,"
   ISIT 2022 (DOI `10.1109/ISIT54713.2023.10206758`); journal version _IEEE
   Transactions on Information Theory_, 2024,
   DOI `10.1109/TIT.2024.3418377`.
   - Analysis: estimation of substring multiplicities from noisy traces. Multiplicity
     estimation is mechanistically relevant to the Medvedev–Brudno read-count
     likelihood, but this work is about recovering densities under a trace model, not
     about proving that bridging forces the truth to maximize that likelihood.

6. **K. Mazooji, I. Shomorony**, "An Instance-Based Approach to the Trace
   Reconstruction Problem," CISS 2024, DOI `10.1109/CISS59072.2024.10480213`.
   - Analysis: instance-based trace reconstruction; different problem family.

7. **N. Luria, N. Weinberger**, "Optimal Overlap Detection of Shotgun Reads,"
   arXiv:2502.13813 (2025); _IEEE Transactions on Information Theory_, 2026,
   DOI `10.1109/TIT.2026.3706236`.
   - Source fact: characterizes the exact asymptotic Bayesian error probability of
     the optimal (MAP) detector for the overlap length of a pair of shot-gun reads,
     for stationary ergodic noiseless reads and for memoryless noisy reads.
   - Analysis: a distilled pairwise-alignment limit; it repeatedly cites Bresler
     et al. (2013) for the repeat-condition background but treats maximum likelihood
     only as a per-pair Bayesian detector. It does not state or resolve the global
     assembly bridging→ML question.

8. **M. Ali, H. Narayanan, P. Krishnan**, "A Converse For the Capacity of the
   Shotgun Sequencing Channel with Erasures," ITW 2025,
   DOI `10.1109/ITW62417.2025.11240437`; arXiv:2509.21216.
   - Analysis: information-theoretic converse for the erasure shotgun channel;
     capacity/setting differs from the error-free uniform-read model of the open
     question.

9. **Y. Yehezkeally, D. Bar-Lev, S. Marcovich, E. Yaakobi**, "Generalized Unique
   Reconstruction From Substrings," _IEEE Transactions on Information Theory_,
   2023, DOI `10.1109/TIT.2023.3269124`; arXiv:2210.04471.
   - Source fact: gives rate upper bounds and constructions for codes that guarantee
     unique reconstruction when consecutive substrings are read with some minimum
     overlap.
   - Analysis: concerns a complete/controlled substring-read model and code design,
     not a finite random shotgun sample and not a likelihood objective. Its
     "unique reconstruction" is a different predicate from "truth is the unique ML
     maximizer"; see the distinction already recorded in `literature-status.md` §11.

10. **M. Ghodsi**, "Constructing a genome assembly that has the maximum likelihood,"
    arXiv:1302.4391 (v1 2013; v3 2016).
    - Source fact: formulates assembly as maximizing the probability of the reads
      under a basic uniform, error-free, equal-length model. It assumes the genome
      length is known and states: "Note that the resulting Eulerian graph may have
      many tours, all of which will have equal likelihood. Therefore any final
      solution (assembled sequence) is, by itself, only one of many possible
      solutions."
    - Analysis: this is direct published acknowledgement that the ML assembly
      objective can have multiple tied optima, and it supports keeping the
      truth-is-a-maximizer and all-maximizers-are-truth schemas separate. It does
      not address bridging conditions or the 2016 question.

11. **Cairo, Khan, Rizzi, Schmidt** (2020), "Genome assembly, a universal theoretical
    framework: unifying and generalizing the safe and complete algorithms,"
    arXiv:2011.12635.
    - Analysis: unifies safe-and-complete graph theory. It is one of the few works
      citing both the bridging and ML lines, but it is about graph-consistency safety,
      not likelihood optimality.

12. **Y. Yang**, "Survey of Sequence Reconstruction Problems and Their Applications
    in DNA-Based Storage," _IEEE JSAIT_, 2025,
    DOI `10.1109/JSAIT.2025.3595457`.
    - Metadata as returned by the Semantic Scholar Graph API; the survey status is
      recorded for completeness. Analysis (tentative, pending full-text check): a
      reconstruction survey in the DNA-storage setting; not a bridging→ML result.

## Theorem/model correspondence summary

| Work | Model | Result type | Does it settle/narrow the 2016 question? |
| --- | --- | --- | --- |
| Shomorony et al. 2016 | circular genome, error-free uniform reads | algorithm-specific unique Eulerian reconstruction under bridging | States the question; does not answer it |
| Medvedev–Brudno 2009 | circular candidate, multinomial read-count likelihood (plus flow approximation) | defines ML objective; no uniqueness theorem | Defines the objective only |
| Bresler et al. 2013 | finite shotgun, likelihood | unbridged problematic repeats ⇒ equal-likelihood same-length competitor (necessity) | Necessary direction only |
| Lam, Khalak, Tse 2014 | noisy reads | near-optimal assembly algorithm | Algorithmic; not global ML |
| Motahari et al. 2013 | i.i.d. DNA, noisy reads | same thresholds as noiseless; ML used for base correction | Not global ML assembly |
| Mahajan, Jain, Kashyap 2024/25 | diploid | bridging conditions for reconstruction | Extends bridging; same gap |
| Safe-and-complete / hydrostructure (Cairo et al.) | assembly graph | graph-consistency safety and completeness | Different predicate from likelihood optimality |
| SAMA 2025 | de Bruijn graph | local misassembly-probability bounds | Different guarantee; cites both lines separately |
| Luria–Weinberger 2025/26 | pair of reads | exact MAP overlap-detection error | Pairwise detector, not global assembly ML |
| Yehezkeally et al. 2023 | controlled substring reads | unique-reconstruction codes | Different observation model |
| Ghodsi 2013 | basic uniform error-free, known length | ML formulation + note that many equal-likelihood tours can exist | Tie evidence, not bridging |

## What is directly sourced vs inference

- The citation counts, intersection membership, titles, years, venues, and DOIs are
  **source facts** returned by the Semantic Scholar Graph API and verified against
  author/publisher pages where possible.
- The conclusion that no intersected work resolves the question is a
  **source-analysis result** over those facts.
- The statements that each adjacent paper does not prove the conjecture are
  **analysis** unless a quoted sentence is given.

## Effect on the Lean model and theorem statement

1. **The problem remains open** as of 2026-09-19 by two independent search routes
   (keyword sweep in prior notes; citation-graph intersection here).
2. **No change to the required Lean definitions** is forced by these findings.
3. **Tie semantics gain an additional published witness.** Ghodsi (2013) explicitly
   notes multiple equal-likelihood ML tours. (Correction 2026-09-20: this note earlier
   said `docs/literature/ml-tie-semantics.md` “now cites this”; that file does not
   mention Ghodsi. The exact quotation, with provenance, is recorded in
   `docs/source-notes/ml-sequence-contemporary-denotation.md` §1.3.) The two
   conclusion schemas should remain separate.
4. **Multiplicity estimation (Mazooji–Shomorony) and pairwise overlap limit
   (Luria–Weinberger)** are mathematically adjacent tools that may supply lemmas
   about likelihood ratios, but neither is a source for the bridging hypotheses.

## References (newly recorded here)

1. K.-K. Lam, A. Khalak, D. Tse. _Near-optimal assembly for shotgun sequencing with
   noisy reads._ BMC Bioinformatics 15(Suppl 9):S4, 2014.
   <https://doi.org/10.1186/1471-2105-15-S9-S4>
2. A. S. Motahari, K. Ramchandran, D. Tse, N. Ma. _Optimal DNA shotgun sequencing:
   noisy reads are as good as noiseless reads._ ISIT 2013. arXiv:1304.2798.
3. A. N. Ravi, A. Vahid, I. Shomorony. _Coded Shotgun Sequencing._ IEEE JSAIT,
   2022. <https://doi.org/10.1109/JSAIT.2022.3151737>
4. K. Mazooji, I. Shomorony. _Substring Density Estimation From Traces._ IEEE
   Transactions on Information Theory, 2024.
   <https://doi.org/10.1109/TIT.2024.3418377>
5. K. Mazooji, I. Shomorony. _An Instance-Based Approach to the Trace Reconstruction
   Problem._ CISS 2024. <https://doi.org/10.1109/CISS59072.2024.10480213>
6. N. Luria, N. Weinberger. _Optimal Overlap Detection of Shotgun Reads._
   arXiv:2502.13813, 2025; IEEE Transactions on Information Theory, 2026.
   <https://doi.org/10.1109/TIT.2026.3706236>
7. M. Ali, H. Narayanan, P. Krishnan. _A Converse For the Capacity of the Shotgun
   Sequencing Channel with Erasures._ ITW 2025.
   <https://doi.org/10.1109/ITW62417.2025.11240437>; arXiv:2509.21216.
8. Y. Yehezkeally, D. Bar-Lev, S. Marcovich, E. Yaakobi. _Generalized Unique
   Reconstruction From Substrings._ IEEE Transactions on Information Theory,
   2023. <https://doi.org/10.1109/TIT.2023.3269124>
9. M. Ghodsi. _Constructing a genome assembly that has the maximum likelihood._
   arXiv:1302.4391, 2013/2016. <https://arxiv.org/abs/1302.4391>
10. M. Cairo, S. Khan, R. Rizzi, S. Schmidt. _Genome assembly, a universal
    theoretical framework: unifying and generalizing the safe and complete
    algorithms._ arXiv:2011.12635, 2020.
11. Y. Yang. _Survey of Sequence Reconstruction Problems and Their Applications in
    DNA-Based Storage._ IEEE JSAIT, 2025.
    <https://doi.org/10.1109/JSAIT.2025.3595457>
