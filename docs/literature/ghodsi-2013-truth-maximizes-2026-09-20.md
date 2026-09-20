# Ghodsi et al. (2013): the true genome maximizes the read-count likelihood, with ties characterized by the `L`-mer spectrum

_Search date: 2026-09-20._
_Scope: a post-2009 primary source that proves the "truth attains maximum likelihood"
half of the 2016 question in the same fixed-length, error-free, uniform-read model class
used by Medvedev–Brudno §6.1 and by Shomorony et al. (2016). This note records source
facts and their exact relation to the repository's objective; it does not restate the
Medvedev–Brudno candidate-class semantics, which live in
`docs/source-notes/ml-objective-candidate-class-resolution.md`._

## Why this source matters to the open question

The repository already records Ghodsi's arXiv manuscript (`arXiv:1302.4391`) for its
remark that maximum-likelihood assembly can have many equal-likelihood Eulerian tours
(`docs/literature/ml-tie-semantics.md`; `docs/literature-search-citation-graph-2026-09-19.md`).
The **peer-reviewed 2013 journal version** of the same line, which the earlier searches
did not record, contains an explicit *proof* of a stronger and more useful statement: in
the error-free model the likelihood is maximized by the true genome, and the optimum set
is exactly the set of candidate sequences inducing the observed read distribution.

This is directly relevant because "the true genome is a maximizer" is one of the two
conclusion schemas kept distinct in `docs/open-problem.md` and
`docs/literature/ml-tie-semantics.md`. The source pins down when that schema can hold and
what its exact failure mode (ties) looks like in the repository's model class.

## The source

- **Citation:** Mohammadreza Ghodsi, Christopher M. Hill, Irina Astrovskaya, Henry Lin,
  Dan D. Sommer, Sergey Koren, Mihai Pop, "De novo likelihood-based measures for comparing
  genome assemblies," *BMC Research Notes* 6:334, 2013.
  DOI `10.1186/1756-0500-6-334`; PMCID `PMC3765854`; PMID `23965294`.
  Open full text: <https://pmc.ncbi.nlm.nih.gov/articles/PMC3765854/>.
- The paper introduces the **LAP** ("Log Average Probability") assembly score, later
  distributed as the `assembly-eval` tool and cited as a reference-free evaluation method
  (e.g. by QUAST-LG). It is the journal counterpart of the manuscript referenced as
  `[1]` in Ghodsi's arXiv note.

## Exact theorem/model (source fact, quoted)

The Methods section, under the heading **"True genome obtains the maximum likelihood"**,
states and proves the following. Quotes are verbatim from the PMC full text.

- Objective and per-read probability:

  > "We define the quality of a sequence produced by an assembler as the conditional
  > probability of observing the sequenced reads from the assembled sequence. A key
  > property of our metric is that the true genome sequence maximizes the score."

  For a circular assembly of length `L`, the per-read probability is (their eq. (2)):

  > `p_r = n_r / 2L`

  "where `n_r` represents the number of places where the read occurs in the assembled
  sequence of length `L`. The factor 2 is due to the fact that reads are sampled with
  equal likelihood from both the forward and reverse strands… This formulation was
  previously used by Medvedev *et al.* [26] to define an objective function for genome
  assembly." (Reference `[26]` is Medvedev–Brudno 2009.)

- The model under which the theorem is stated:

  > "Assuming that we have a set of reads `R` from the true genome, produced by generating
  > exactly one single-end read from each location in the genome without errors and with a
  > fixed length. Given the set of reads `R`, the probability a particular read is
  > generated from the true genome is precisely the number of times the read occurs in `R`
  > divided by the size of `R`…"

- Their proof. With `N_s` the observed count of read type `s`, `q_s = N_s/|R|`, and `p_s`
  the candidate's induced probability of type `s`:

  > "Given assembly `A`, our likelihood score is then the product of `p_s^{N_s}` over all
  > sequences `s` in `S`, which can be rewritten as `∏_{s∈S} p_s^{q_s|R|} = (∏_{s∈S}
  > p_s^{q_s})^{|R|}`."

  > "`log(∏_{s∈S} p_s^{q_s}) = Σ_s q_s log p_s = Σ_s q_s log(p_s/q_s) + Σ_s q_s log q_s
  > = −D_KL(Q||P) − H(Q)`"

  > "Since the KL-divergence is always non-negative and only equal to 0 if and only if
  > `Q = P`, the average probability is maximized if the assembly is equal to the true
  > genome."

- The explicit tie statement (source fact, quoted):

  > "Even though the true genome does maximize the likelihood in this model, there may be
  > other assemblies that achieve the same optimal score as long as these assemblies yield
  > probabilities `p_s` which are equal to the probabilities `q_s` for every sequence `s`.
  > This can happen, for example, in the case of a misassembly that is nonetheless
  > consistent with the generated reads."

## Exact relation to the Medvedev–Brudno objective (analysis)

For a fixed-length, error-free model, Medvedev–Brudno §6.1 scores a circular candidate
`D` by the multinomial read-count likelihood with type probabilities `d_i/N(D)`. Ghodsi et
al.'s per-read product `∏_r p_r` is the same objective up to the multinomial coefficient,
with `p_s = n_s/2L` (the factor 2 is their double-stranded convention; `∑_s n_s = 2L`).
So the displayed KL identity is a statement about the **exact global read-count
likelihood** the repository has been formalizing.

Because the KL identity is unconditional in `Q`, the same derivation immediately
characterizes the whole maximizer set:

> For every observed count vector `x`, the read-count likelihood is maximized exactly by
> the candidates `D` whose induced read-type distribution `(d_i/N(D))_i` equals the
> empirical distribution `(x_i/∑x)_i`; its maximum value is `−H(empirical)` (as
> log-average-probability per read), independent of `D`.

This is mathematically the fixed-length characterization already derived in
`docs/fixed-length-ml-objective-analysis.md` §KL form and
`mathematics/fixed-length-exact-likelihood-characterization.md`; the 2013 paper is an
independent published proof of the same fact, with the double-stranded `2L` normalization
and a stated circular single-contig model.

### Bearing on the bridging→ML question (analysis, stated carefully)

- The paper's theorem is stated under **complete tiling** ("exactly one single-end read
  from each location"), where the empirical distribution `Q` *is* the true genome's
  read-type distribution. Under that assumption the true genome is a maximizer, and every
  candidate with the same read-type spectrum ties.
- In the repository's model the observation is a **finite uniform sample**, so `x/N` is
  the empirical distribution and generally differs from the true spectrum. The same KL
  identity then says the true genome is a maximizer **iff `x/N` equals the true genome's
  read-type distribution**. Bridging conditions constrain the true genome's repeat
  structure relative to the sampled read spans; they do not by themselves force the
  empirical distribution to equal the true spectrum. So the paper shows the
  "truth-is-a-maximizer" property is an equality-of-spectra statement, not a consequence
  of repeat-bridging alone, in the unrestricted finite-sample exact objective.
- This is consistent with, and gives a general source-backed form of, the repository's
  concrete finite counterexamples (`docs/fixed-length-counterexample-correction.md`,
  `mathematics/`). It **does not** settle the 2016 question, which may restrict the
  candidate class (e.g. to graph/flow-feasible genomes) or fix the candidate length; within
  such a restricted class the equality-of-spectra condition can still be non-vacuous and
  bridging may matter. The paper considers neither bridging nor a restricted candidate
  class.
- It also does not address the "all maximizers are truth" schema: the paper explicitly
  says equal-likelihood non-true candidates can exist.

## Adjacent 2013 primary source (not a theorem)

- Scott C. Clark, Rob Egan, Peter I. Frazier, Zhong Wang, "ALE: a generic assembly
  likelihood evaluation framework for assessing the accuracy of genome and metagenome
  assemblies," *Bioinformatics* 29(4):435–443, 2013, DOI `10.1093/bioinformatics/bts723`.
  ALE gives a Bayesian assembly score `P(R|S)P(S)` and reports that "the reference
  genomes are the best assemblies" on its datasets. This is an **empirical** claim on
  GAGE/Assemblathon data under a richer error/mate-pair model, not a theorem that the
  true genome maximizes the likelihood, and it does not address bridging or the 2016
  question. Recorded here only to distinguish it from the Ghodsi et al. proof.

## Epistemic classification

| Claim | Status |
|---|---|
| Quoted theorem statement, model assumptions, KL derivation, tie sentence | **Source fact** (BMC Res Notes 2013, PMC3765854) |
| `∏_r p_r` is the Medvedev–Brudno fixed-length exact objective up to the multinomial coefficient | **Analysis** (matching normalization and type-probability formulas) |
| Maximizer set = candidates with induced distribution equal to the empirical one | **Analysis / immediate corollary** of the quoted derivation; independently derived in `mathematics/fixed-length-exact-likelihood-characterization.md` |
| Truth is a maximizer iff empirical distribution equals true spectrum (finite sample) | **Analysis** (specialization of the corollary); not stated by the source |
| This does not settle the bridging→ML implication | **Source-analysis result** |
| ALE's "reference genomes are the best assemblies" | Source fact about ALE's reported experiments; not a theorem |

## Effect on the repository

1. Core conclusion unchanged: no located source settles the exact 2016 implication.
2. **New durable primary citation:** Ghodsi, Hill, Astrovskaya, Lin, Sommer, Koren, Pop,
   *BMC Research Notes* 6:334, 2013 (`10.1186/1756-0500-6-334`). This is the
   peer-reviewed, citable version of the model and the only located *proof* of the
   "truth is a maximizer" direction in the Medvedev–Brudno objective class.
3. The tie-semantics note should cite the journal version for the proof, not only the
   arXiv remark.
4. No Lean-definition changes are forced. The note supports keeping the
   truth-is-a-maximizer and all-maximizers-are-truth schemas distinct, and records that
   the first schema is equivalent to an empirical-spectrum equality in the unrestricted
   finite-sample exact objective.

## References (newly recorded here)

1. M. Ghodsi, C. M. Hill, I. Astrovskaya, H. Lin, D. D. Sommer, S. Koren, M. Pop.
   *De novo likelihood-based measures for comparing genome assemblies.* BMC Research
   Notes 6:334, 2013. <https://doi.org/10.1186/1756-0500-6-334>
   (PMCID PMC3765854).
2. S. C. Clark, R. Egan, P. I. Frazier, Z. Wang. *ALE: a generic assembly likelihood
   evaluation framework for assessing the accuracy of genome and metagenome assemblies.*
   Bioinformatics 29(4):435–443, 2013. <https://doi.org/10.1093/bioinformatics/bts723>
