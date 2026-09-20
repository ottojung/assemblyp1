# Post-2016 results from the Shomorony group: identifiability and flow-decomposition limits

_Search date: 2026-09-20._
_Scope: primary results published after Shomorony et al. (2016) by the same group (and by
Medvedev–Brudno-adjacent authors) that concern substring/`k`-mer reconstruction
identifiability or flow-decomposition identifiability. This is an independent search supplementing
`docs/literature-search-post2016-durable.md`, `docs/literature-search-independent-2026-09-20.md`,
and `docs/literature/post2016-ml-likelihood-search-2026-09-20.md`. It records only material not
already present in those notes._

## Question investigated

Does any post-2016 primary work — especially by the Shomorony–Courtade–Tse group itself — settle,
narrow, or reformulate the open question in `docs/open-problem.md`: do the Shomorony–Kim–Courtade–Tse
repeat-bridging conditions (information feasibility) guarantee that the true sequence is the
maximum-likelihood sequence under the Medvedev–Brudno (2009) read-count objective?

## Headline result

**No.** The same group's post-2016 work continues to develop the **identifiability / information
feasibility** line (including an information-optimal flow-decomposition result), not the
likelihood-optimality line. These results are the nearest same-author follow-ups that a citation
intersection through the 2016 paper does **not** surface, because they do not cite it. They reinforce
that the group treated exact-reconstruction feasibility, not ML optimality, as the research frontier.

## Newly recorded same-group / adjacent primary results

### 1. Mazooji–Kannan–Noble–Shomorony, information-optimal flow decomposition (ISIT 2022)

- **Citation:** K. Mazooji, S. Kannan, W. S. Noble, I. Shomorony, "Fundamental Limits of Multi-Sample
  Flow Graph Decomposition," *2022 IEEE International Symposium on Information Theory (ISIT)*,
  pp. 2403–2408, DOI [`10.1109/ISIT50566.2022.9834518`](https://doi.org/10.1109/ISIT50566.2022.9834518).
  Long version: <https://ilanshom.github.io/papers/flow_decomposition_ISIT_long.pdf>.
- **Model (source fact):** a known DAG `G = (V,E)`; an unknown set `P` of source-to-sink paths; `T`
  independent samples, each sample a non-negative weighted flow on `G` induced by the paths in `P`
  (edge weight = sum of weights of paths through it). Goal: recover `P` and the per-sample weights.
- **Theorem 1 (source fact, quoted):** "Suppose `(G, P)` is such that all nodes are good. Then the
  Topological Decomposition algorithm (Algorithm 1) outputs `P̂ = P` with correct path weights for all
  samples **if and only if** the set of samples `T` reveals `P`." Here "good" is a node condition
  defined at the end of the paper; "reveals" means the samples unambiguously determine `P`.
- **Second result (source fact):** the necessary conditions plus a probabilistic sample model yield an
  upper and lower bound on the number `T*(ε)` of samples needed for unambiguous recovery, for the
  class where all nodes are good.
- **Relation to the open question (analysis):** this is a genuine information-optimal
  **flow-decomposition** theorem from the same lab and a post-2016 continuation of the 2016 paper's
  "partial assembly / flow" theme (cf. Shomorony et al., "Partial DNA Assembly: A Rate-Distortion
  Perspective," ISIT 2016). It establishes exact recovery of the true path set from flow
  observations, to the information limit, but its observation model (edge-weight flows) is not the
  uniform length-`L` substring sampling model, and it does not compare a candidate genome's
  likelihood against the truth. It therefore neither proves nor refutes the bridging→ML implication.

### 2. Levick–Shomorony, fundamental limits of reconstruction from substrings (ISIT 2023)

- **Citation:** K. Levick, I. Shomorony, "Fundamental Limits of Multiple Sequence Reconstruction from
  Substrings," *2023 IEEE International Symposium on Information Theory (ISIT)*, pp. 791–796,
  DOI [`10.1109/ISIT54713.2023.10206707`](https://doi.org/10.1109/ISIT54713.2023.10206707);
  preprint arXiv:2305.05820.
- **Model (source fact):** `m = n^α` i.i.d. source sequences of length `n`, each i.i.d. Bern(1/2);
  observe the union of their length-`k` substring sets, `k = β log n`; `Y` reconstructs `X` if `X` is
  the unique set of `m` length-`n` sequences (up to relabeling) generating `Y`.
- **Theorem 1 (source fact, quoted):** "`(α, β) ∈ F` if `β > max(2α + 1, α + 2)`; `(α, β) ∉ F` if
  `β < max(2α + 1, α + 3/2)`," where `F` is the feasibility region (pairs for which reconstruction
  succeeds with probability → 1). The region is thus characterized almost completely.
- **Qualitative finding (source fact):** "there are feasible `(α, β)` pairs where repeats across the
  source strings abound, and non-trivial reconstruction algorithms are needed to achieve the
  fundamental limit." Feasibility is established by analyzing the `k`-mer de Bruijn graph, whose
  edge-covering path set is unique; infeasibility is shown by exhibiting an explicit swap-based
  alternative reconstruction (an interleaved-repeat-style ambiguity).
- **Relation to the open question (analysis):** this is the same sampling substrate as the 2016 model
  (substrings of a random source, identifiability from their union) but it studies
  **exact uniqueness**, not the Medvedev–Brudno likelihood ranking, and it uses asymptotically growing
  `k` rather than a fixed-`L` finite sample. Its 17-item reference list (per Crossref) contains the
  Motahari/Bresler/Shomorony identifiability works but **not** Medvedev–Brudno (2009). It does not
  address the bridging→ML question.
- **Note:** the infeasibility witness (two strings `x_i, x_j` with repeated `k`-mers at equal gap,
  allowing a middle-segment swap) is the same combinatorial mechanism as the interleaved-repeat
  ambiguity and may be useful raw material for `mathematics/` analysis of competitor spectra.

### 3. Mazooji–Shomorony, substring density estimation from traces (TIT 2024)

- **Citation:** K. Mazooji, I. Shomorony, "Substring Density Estimation From Traces," *IEEE
  Transactions on Information Theory* 70(8):5782–5798, Aug. 2024, DOI
  [`10.1109/TIT.2024.3418377`](https://doi.org/10.1109/TIT.2024.3418377); ISIT 2023 companion (DOI
  `10.1109/ISIT54713.2023.10206758`).
- **Relation (analysis):** statistical estimation of substring densities from noisy traces; adjacent
  to read-multiplicity inference, but a different estimator/objective from global ML assembly. Not a
  settlement.
- **Source fact on citation separation:** the Crossref reference list for the TIT version cites **both**
  Shomorony et al. (2016) (`10.1093/bioinformatics/btw450`) and Bresler et al. (2013)
  (`10.1186/1471-2105-14-S5-S18`) but does **not** cite Medvedev–Brudno (2009). A same-group 2024
  paper thus still keeps the bridging/identifiability line and the ML-assembly line separate.

### 4. Ghodsi, "Constructing a genome assembly that has the maximum likelihood" (2013)

- **Citation:** M. Ghodsi, "Constructing a genome assembly that has the maximum likelihood,"
  arXiv:1302.4391, first posted 2013-02-18, last revised 2016-04-07.
- **Content (source fact):** formulates assembly as maximizing the likelihood of a candidate
  superstring given the reads; builds a complete "prefix graph" and relaxes an integer program to a
  convex program in vertex-flow variables `y_i = n_i/L`, with `z_i = log y_i`.
- **Relation (analysis):** pre-dates the 2016 question; a distinct ML-assembly formulation (a
  relaxation with an Eulerian-flow constraint). It is relevant context
  for the "flow-constrained likelihood" family but is neither a proof nor a counterexample for the
  bridging→ML implication. The v3 revision (April 2016) is roughly contemporaneous with the 2016
  paper and worth noting if authorship/provenance matters.
- **Correction (2026-09-20).** The earlier wording here said “no fixed candidate length.” That is
  wrong: Ghodsi §2 and Appendix B explicitly assume the genome/assembly length is known and constant in
  the optimization (with a scale-invariance justification), while eq. (1) writes the candidate
  length in the objective. See
  [`../source-notes/ml-sequence-contemporary-denotation.md`](../source-notes/ml-sequence-contemporary-denotation.md)
  §1.2, §5.

## What was searched and not found

- No post-2016 work by the 2016 authors that proves the bridging hypotheses imply truth is a global
  maximum-likelihood maximizer under the Medvedev–Brudno objective.
- No post-2016 work by the 2016 authors that states, quotes, or answers the 2016 Discussion's
  maximum-likelihood open question. The nearest same-lab post-2016 material is on identifiability
  thresholds and flow-decomposition information limits (items 1–3).
- No published counterexample where the bridging conditions hold but another candidate has strictly
  greater likelihood.

## Epistemic classification

| Claim | Status |
|---|---|
| Bibliographic data (authors, venue, pages, DOIs, theorem statements quoted above) | Source fact (Crossref / arXiv / IEEE pages, 2026-09-20) |
| Levick–Shomorony reference list omits Medvedev–Brudno 2009 | Source fact (Crossref reference items) |
| Mazooji et al. Theorem 1 and the `T*(ε)` result | Source fact (abstract + Theorem 1 statement read) |
| Each adjacent work does not resolve the bridging→ML conjecture | Analysis |
| No located settlement | Source-analysis result, not a proof of absence |

## Effect on the repository

1. Core conclusion unchanged: the bridging→ML question appears open as of 2026-09-20.
2. New durable citations to add to the literature record: Mazooji et al. (2022), Levick–Shomorony
   (2023), Mazooji–Shomorony (2024), Ghodsi (2013). These are same-lab / adjacent identifiability
   results that the citation intersection through the 2016 paper does not find.
3. The Levick–Shomorony infeasibility construction (equal-gap repeated `k`-mers enabling a swap) is
   recorded as potential raw material for competitor-spectrum analysis.
4. No Lean-definition changes are forced.

## References (newly recorded here)

1. K. Mazooji, S. Kannan, W. S. Noble, I. Shomorony. *Fundamental Limits of Multi-Sample Flow Graph
   Decomposition.* ISIT 2022, pp. 2403–2408.
   <https://doi.org/10.1109/ISIT50566.2022.9834518>
2. K. Levick, I. Shomorony. *Fundamental Limits of Multiple Sequence Reconstruction from Substrings.*
   ISIT 2023, pp. 791–796. <https://doi.org/10.1109/ISIT54713.2023.10206707> (arXiv:2305.05820).
3. K. Mazooji, I. Shomorony. *Substring Density Estimation From Traces.* IEEE Trans. Inf. Theory
   70(8):5782–5798, 2024. <https://doi.org/10.1109/TIT.2024.3418377>
4. M. Ghodsi. *Constructing a genome assembly that has the maximum likelihood.* arXiv:1302.4391,
   2013/2016. <https://arxiv.org/abs/1302.4391>
