# Post-2016 citation-chain audit: who answers, restates, or interprets Shomorony et al.'s bridging→ML question?

_Search/audit date: 2026-09-20._
_Scope: primary, English-language work published after Shomorony–Kim–Courtade–Tse (2016) that
either (a) answers, (b) explicitly restates, or (c) interprets the open question in
`docs/open-problem.md` — whether the repeat-bridging conditions guarantee that the
maximum-likelihood sequence is the true sequence under the Medvedev–Brudno (2009) formulation —
or that interprets the referenced MB09 objective in a way that constrains the referent of
issue #36. Russian-language material is excluded. General safe-and-complete / graph-theory
background is intentionally not re-recorded (see the existing literature notes)._

_This note records only material **not already present** in `docs/literature-status.md`,
`docs/literature-search-*.md`, `docs/literature/post2016-ml-likelihood-search-2026-09-20.md`,
`docs/literature/post2016-ml-assembly-citation-refresh-2026-09-20.md`,
`docs/literature/shomorony-group-post2016-identifiability-2026-09-20.md`,
`docs/literature/substring-spectrum-identifiability-2026-09-20.md`, or
`docs/literature/citation-context-and-referent-audit-2026-09-20.md`. Every substantive claim is
labelled **source fact**, **source-analysis**, or **analysis**._

## Question investigated

Has any post-2016 primary work explicitly answered, restated, or interpreted the Shomorony et al.
(2016) open sentence: do the information-feasibility repeat-bridging conditions force the true
sequence to be the maximum-likelihood sequence under the Medvedev–Brudno (2009) read-count
formulation? A secondary question, matching issue #36: does any post-2016 work independently
interpret what the referenced MB09 "maximum-likelihood formulation" means?

## Headline result

**No located post-2016 work answers or explicitly restates the exact 2016 open question.** This
audit reproduces the earlier negative result with a new, sharper instrument: a citation-chain
audit at the level of *post-2016 citation contexts and title/abstract intersections*. Two of the
new results are materially more precise than the prior record:

1. Among all **41 citation contexts of the 38 post-2016 citing works of Shomorony et al. (2016),
   zero contain the word "likelihood"** (fresh 2026-09-20 Semantic Scholar snapshot).
2. Among all **156 contexts of the 98 citing works of Bresler–Bresler–Tse (2013)** — the origin of
   the bridging framework — only two mention "likelihood", and **both citing works are pre-2016**
   (2014, 2015). Hence the post-2016 bridging literature never discusses likelihood at all.

A third, smaller finding bears on issue #36: several post-2016 primary works **do** restate the
MB09 objective, and every located restatement reads it as a *sequence/assembly-level likelihood of
the reads* (Sama 2025; SWALO 2016/2021; LOGAN 2017). None selects the exact-multinomial vs
fixed-`N` convention and none connects it to bridging. This is new citable support for the
sequence-level reading of the 2016 phrase, but it does not resolve the length/tie semantics.

## 1. Citation-context audit (source facts, all run 2026-09-20)

Instruments: Semantic Scholar (S2) Graph API `citations` with per-citation `contexts`; OpenAlex
REST `cites:` and `title_and_abstract.search` / `fulltext.search`; Europe PMC `fullTextXML`.
No API key was used.

| Instrument / query | Result |
| --- | --- |
| S2 `citations` of DOI `10.1093/bioinformatics/btw450` (Shomorony 2016) | 38 citing works, **41 contexts**, **0** contexts containing `likelihood`/`maximum likelihood` |
| S2 `citations` of DOI `10.1186/1471-2105-14-S5-S18` (Bresler 2013) | 98 citing works, 76 with contexts, **156 contexts**, **2** containing `likelihood`; both citing works are pre-2016 (2014, 2015) |
| OpenAlex `cites:W2515489235` (Shomorony 2016) | 33 works; diff against the S2 set yields only two `Faculty Opinions` recommendations of *Skmer* (non-scholarly), i.e. **no additional citing works** |
| OpenAlex `cites:W2515489235`, `title_and_abstract.search:"bridging"`, 2017+ | 2 hits, both Mahajan–Jain–Kashyap diploid (2024/2025) |
| OpenAlex `cites:W2515489235`, `title_and_abstract.search:"maximum likelihood"`, 2017+ | 2 hits, both multiple-deletion-channel reconstruction (2018, 2020), i.e. not the assembly model |
| OpenAlex `cites:W2035596374` (MB09), `title_and_abstract.search:"bridging"`, 2017+ | **0** |
| OpenAlex `cites:W2035596374`, `title_and_abstract.search:"maximum likelihood"`, 2017+ | 1 hit: SWALO (Rahman–Pachter) |
| OpenAlex `fulltext.search:"maximum-likelihood sequence is the true sequence"` (and hyphen-free variant) | **0** |
| Europe PMC full-text, same exact phrase | 0 (reproduces the earlier record) |

**Source-analysis.** The two scientific lines are not merely rarely combined; at the level of
citation contexts of the bridging origin (Bresler 2013) they are **disjoint post-2016**. The
"maximum likelihood" title/abstract hits that cite either line are all in other observation models
(deletion-channel trace reconstruction; scaffolding likelihood evaluation; diploid bridging).

The single post-2016 work that cites both Shomorony 2016 and MB09 and discusses an ML objective is
Sama (Salmela 2025), and it treats them as separate prior lines; its exact sentence is quoted in
§3 below.

## 2. No located explicit restatement or answer of the 2016 open question (source-analysis)

No located post-2016 work quotes, paraphrases, or replies to the 2016 discussion sentence, and none
proves or refutes the bridging⇒ML implication. This is a search conclusion, not a proof of absence.
The new context-level instruments above strengthen the earlier keyword/intersection evidence.

## 3. Post-2016 interpretations of the MB09 objective (source facts, relevant to issue #36)

These are the located post-2016 restatements of what MB09's maximum-likelihood assembly *is*.
They are interpretations of MB09, not of the Shomorony open question, and none discusses bridging.

### 3.1 Sama (Salmela 2025) — the only work citing both lines

- **Citation (source fact):** L. Salmela, "Sama: a contig assembler with correctness guarantee,"
  *Algorithms for Molecular Biology* 20:9, 2025, DOI `10.1186/s13015-025-00280-y`; PMC12135590.
- **Quoted (source fact, Europe PMC full text):**
  > "Medvedev and Brudno [6] and Myers [7] have proposed to report the sequence with maximum
  > likelihood given the reads as the assembled genome and Boža et al. [8] have developed a
  > probabilistic framework to produce an assembly with high likelihood using simulated annealing."
- **Relation to issue #36 (analysis):** this is an explicit post-2016 reading of MB09 as a
  **sequence-level** objective: "the sequence with maximum likelihood given the reads". It supports
  issue #36 readings (1)/(2)/(4) at the level of *object type* and gives a citable post-2016
  restatement, but it says nothing about the candidate-length convention, ties, or bridging, so it
  does not select among readings.

### 3.2 SWALO (Rahman–Pachter 2016/2021)

- **Citation (source fact):** A. Rahman, L. Pachter, "SWALO: scaffolding with assembly likelihood
  optimization," bioRxiv 2016, DOI `10.1101/081786`; published *Nucleic Acids Research* 49(17),
  2021, DOI `10.1093/nar/gkab717`.
- **Quoted context (source fact, S2 context of MB09):** "Thus, SWALO takes a step towards maximum
  likelihood genome assembly (53)."
- **Relation (analysis):** treats "maximum likelihood genome assembly" as an assembly-level target;
  no bridging, no length-convention discussion.

### 3.3 LOGAN (Bolger et al. 2017)

- **Citation (source fact):** A. M. Bolger, A. K. Denton, M. E. Bolger, B. Usadel, "LOGAN: A
  framework for LOssless Graph-based ANalysis of high throughput sequence data," bioRxiv 2017,
  DOI `10.1101/175976`.
- **Quoted context (source fact, S2 context of MB09):**
  > "We concur with Medvedev and Brudno (1) that the goal should be the set of contigs which best
  > explains the reads, given reasonable priors regarding their creation, thus aiming towards a
  > parsimonious result, rather than one of strictly minimal length."
- **Relation (analysis):** an independent reading of MB09 as "explain the reads" with a prior /
  parsimony flavour; no bridging or length convention.

### 3.4 Medvedev–Pop (2021) on non-uniqueness

- **Citation (source fact):** P. Medvedev, M. Pop, "What do Eulerian and Hamiltonian cycles have to
  do with genome assembly?" *PLOS Computational Biology* 17(5):e1008928, 2021,
  DOI `10.1371/journal.pcbi.1008928`; PMC8136698.
- **Quoted (source fact):** "The first is that a genome reconstruction is never unique and hence an
  algorithm for finding Eulerian or Hamiltonian cycles is not part of any assembly algorithm used
  in practice."
- **Source fact / analysis:** full text contains **zero** occurrences of `likelihood`. Authored by
  the MB09 co-author. It is negative evidence that MB09's author did not, by 2021, frame assembly
  correctness in likelihood terms; it is context for the uniqueness/tie-schema split (issue #36)
  but is not about bridging or the open question.

### 3.5 Already-recorded interpretation (not duplicated)

Medvedev, *Theoretical Analysis of Sequencing Bioinformatics Algorithms and Beyond*, CACM 66(7),
2023 (`10.1145/3571723`) is already on the repository record; its same-author separation of the
likelihood line from the reconstruction-condition line and its "I am not aware of any work that
attempted to use likelihood to theoretically predict algorithm performance" remain the strongest
negative evidence.

## 4. Epistemic classification

| Claim | Status |
| --- | --- |
| Citation counts, context counts, title/abstract intersection counts in §1 | Source fact (S2 and OpenAlex APIs, 2026-09-20) |
| `0` likelihood contexts among Shomorony-2016 citations; `2` (both pre-2016) among Bresler-2013 citations | Source fact (API `contexts`) |
| Exact phrase absent from OpenAlex fulltext and Europe PMC | Source fact (query results) |
| No located post-2016 answer/restatement of the 2016 open question | Source-analysis result (not absence) |
| Sama / SWALO / LOGAN / Medvedev–Pop quotations | Source fact (full text / API contexts) |
| Those restatements support a sequence-level reading of MB09 | Analysis |
| None resolves length/tie semantics or bridging⇒ML | Analysis |

## 5. Effect on the repository and issue #36

1. **Core conclusion unchanged:** no located post-2016 settlement of the bridging⇒ML question as of
   2026-09-20.
2. **Sharper negative:** the post-2016 bridging literature's citation contexts contain no
   likelihood discussion at all; the two lines are citation-disjoint at the context level. This can
   be cited instead of the earlier weaker "no citing context mentions ML" claim.
3. **Referent (issue #36):** the located post-2016 restatements of MB09 (Sama, SWALO, LOGAN) all
   read it as a sequence/assembly-level likelihood-of-reads objective. This is new independent
   support for the sequence-level reading already defended in
   `docs/source-notes/shomorony-ml-quantifier-sequence-resolution.md`, but it does not select
   exact-multinomial vs externally-fixed `N`, and it does not touch §6.2 feasibility.
4. **No Lean-definition changes are forced.**

## References (newly recorded here)

1. L. Salmela. *Sama: a contig assembler with correctness guarantee.* Algorithms for Molecular
   Biology 20:9, 2025. <https://doi.org/10.1186/s13015-025-00280-y> (PMC12135590).
2. A. Rahman, L. Pachter. *SWALO: scaffolding with assembly likelihood optimization.* bioRxiv 2016
   (`10.1101/081786`); Nucleic Acids Research 49(17), 2021 (`10.1093/nar/gkab717`).
3. A. M. Bolger, A. K. Denton, M. E. Bolger, B. Usadel. *LOGAN: A framework for LOssless
   Graph-based ANalysis of high throughput sequence data.* bioRxiv 2017 (`10.1101/175976`).
4. P. Medvedev, M. Pop. *What do Eulerian and Hamiltonian cycles have to do with genome assembly?*
   PLOS Computational Biology 17(5):e1008928, 2021. <https://doi.org/10.1371/journal.pcbi.1008928>.
