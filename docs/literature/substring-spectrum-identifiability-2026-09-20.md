# Substring-spectrum identifiability: the known combinatorial half of the bridging→ML question

_Search date: 2026-09-20._
_Scope: post-2016 work on reconstructions from the multiset of fixed-length substrings (the
"substring / `L`-mer spectrum"), together with the classical characterization it rests on. This
note records only material not already present in `docs/literature-search-post2016-durable.md`,
`docs/literature-search-independent-2026-09-20.md`,
`docs/literature/post2016-ml-likelihood-search-2026-09-20.md`, or
`docs/literature/shomorony-group-post2016-identifiability-2026-09-20.md`._

> **Addendum 2026-09-21 (source-fidelity resolution).** The reconciliation below used
> Çelikkanat–Masegosa–Nielsen (2024, Theorem 3.1) as the primary anchor and left the
> step "`I_s` ⇔ absence of the obstruction, circularly" marked as unpinned analysis. That
> anchor is a *linear, non-maximal* restatement and was the reason for the caution. The
> correct anchor is **Bresler–Bresler–Tse 2013, Theorem 3** (`K`-mer graph from the
> `(K+1)`-spectrum; unique Eulerian cycle iff no triple or interleaved repeats of length
> `≥ K`), read with the **maximal-repeat** definitions that Shomorony et al. (2016)
> inherit and at `K = L−1`. Under those definitions `WEAK`/`P2` is literally "no triple or
> interleaved repeat of length at least `L−1`", so the inference
> `P2 ⇒ spectrum-uniqueness` is a published theorem. See
> [`circular-qgram-identifiability-and-Is-threshold-2026-09-21.md`](circular-qgram-identifiability-and-Is-threshold-2026-09-21.md),
> which supersedes the anchor choice in this note. The exhaustive 123 906-instance check
> remains valid corroboration (re-run 2026-09-21, 0 ambiguous). The finite-sample caveat
> in "Why this does not settle the 2016 open question" is unchanged.

## Why this line bears directly on the open question

The exact Medvedev–Brudno read-count likelihood (their §6.1, multinomial with
`d_i/N(D)` probabilities) depends on a candidate genome `D` **only through its multiset of
length-`L` substrings** (its `L`-mer spectrum), once the candidate length is fixed. Therefore:

- if two same-length candidates have the same `L`-mer spectrum, they tie for **every** sample;
- "the truth is the maximum-likelihood sequence" cannot hold unless the true spectrum is an
  optimal spectrum;
- "the maximum-likelihood sequence is the true sequence (uniquely)" cannot hold unless the
  `L`-mer spectrum **determines** the genome up to genome equivalence.

So the question in `docs/open-problem.md` contains a purely combinatorial sub-question —
*when does the `L`-mer spectrum determine the sequence?* — that is logically prior to the
statistical question. This sub-question turns out to be an old, fully characterized problem.

## The classical characterization (pre-2016, but decisive)

Two sequences over an alphabet are *`k`-equivalent* if they have the same `k`-mer profile
(multiset of length-`k` substrings). The classification of `k`-equivalence classes is:

- **E. Ukkonen**, "Approximate string-matching with `q`-grams and maximal matches,"
  *Theoretical Computer Science* 92(1):191–211, 1992 — introduced `q`-gram distance and
  conjectured that two strings with the same `q`-gram profile are related by a specific pair
  of transformations (a prefix–suffix shift, and a "swap" at a repeated `(q-1)`-mer).
- **P. A. Pevzner**, "DNA physical mapping and alternating Eulerian cycles in colored graphs,"
  *Algorithmica* 13(1–2):77–105, 1995 — proved the characterization (alternating Eulerian
  cycles in colored graphs).

**Post-2016 restatement with an explicit necessary-and-sufficient theorem.**
A. Çelikkanat, A. R. Masegosa, T. D. Nielsen, "Revisiting K-mer Profile for Effective and
Scalable Genome Representation Learning," *NeurIPS* 2024, pp. 118930–118952;
arXiv:2411.02125. Their **Theorem 3.1** states (quoted):

> Let `r` be a read of length `ℓ`. There exists no other distinct read having the same
> `k`-mer profile if and only if it does not satisfy any of the following conditions:
> 1. `r_1…r_{k−1} = r_{ℓ−k−2}…r_ℓ` and `r_i ≠ r_1` for some `1 < i < ℓ−k−2`.
> 2. `r_i…r_{i+k−2} = r_j…r_{j+k−2}` and `r_g…r_{g+k−2} = r_h…r_{h+k−2}` for some indices
>    `1 ≤ i < g < j < h ≤ ℓ−k+2` where `r_{i+k−1}…r_{g−1} ≠ r_{j+k−1}…r_{h−1}`.
> 3. `r_i…r_{i+k−2} = r_j…r_{j+k−2} = r_h…r_{h+k−2}` for some indices
>    `1 ≤ i < j < h ≤ ℓ−k+2` where `r_{i+k−1}…r_{j−1} ≠ r_{j+k−1}…r_{h−1}`.

Conditions (2) and (3) are exactly the **interleaved-repeat** and **triple-repeat** obstructions,
stated at the `(k−1)`-mer level. Condition (1) is a linear-string prefix–suffix (boundary)
obstruction with no circular analogue. The same paper attributes the underlying classification
to Ukkonen (conjecture) and Pevzner (proof), and quotes `[25]` = Ukkonen 1992 and
`[20]` = Pevzner 1995.

## Reconciliation with the repository's Conjecture 4

`mathematics/bridging-and-spectrum-uniqueness.md` (Conjecture 4) conjectures:

> If `S` is `I_s`-admissible, then any circular genome `D` with the same `L`-mer spectrum is a
> cyclic shift of `S`.

Read against Theorem 3.1 with profile length `k = L` (so the critical repeats are `(L−1)`-mers),
and after dropping the linear boundary condition (1) for the circular setting:

- Theorem 3.1 says the spectrum fails to determine the sequence **iff** there is an interleaved
  pair or a triple of `(L−1)`-mer repeats (with the stated maximality/disequality clauses).
- `I_s`-admissibility (per `docs/bridging-source-semantics.md` / the full-read reduction in
  `bridging-and-spectrum-uniqueness.md` §1) requires every triple repeat to have length
  `≤ L−2` and every interleaved maximal-repeat pair to have a constituent of length `≤ L−2`.
  Equivalently, it *excludes* triples and interleaved pairs of repeats of length `≥ L−1` —
  precisely the Theorem 3.1 obstructions.

**Consequence for epistemic status (analysis, pending a careful circular-indexing check):**
Conjecture 4 is very likely the circular special case of a **known theorem** (Ukkonen 1992 /
Pevzner 1995), not new mathematics. Its 123 906-instance computational evidence and the
"heuristic reduction" in the note are consistent with that. If confirmed, the combinatorial half
of the open question should be cited as classical rather than proved from scratch. This is a
genuine constraint on the research programme: it relocates the open content entirely to the
statistical layer.

_Status: **source-derived reconciliation, needs an explicit circular-state­ment check** against a
primary statement of the classical theorem. The linear Theorem 3.1 is quoted verbatim; the step
"`I_s` ⇔ no Theorem-3.1 obstruction, circularly" is the repository's analysis and is not yet
kernel-checked._

## Why this does **not** settle the 2016 open question

Spectrum identifiability is a statement about the **complete** `L`-mer multiset. The 2016
question instead observes a **finite random sample of reads**, summarized by the empirical
read-count vector `x`. In general `x` is not proportional to `d_S`; the exact objective is
`∏_w d_D(w)^{x_w}` (fixed length). The repository's own counterexample work
(`mathematics/`, Variant-E/F notes) shows the empirical optimum can differ from `d_S` without
any bridging violation. So:

- Theorem 3.1 (and Conjecture 4) control **ties/fibres** of the spectrum map, i.e. candidate
  *identity* at a given spectrum;
- the 2016 question asks whether bridging makes `d_S` beat *every other spectrum* on the
  observed sample — a different, sampling-fluctuation-sensitive statement;
- the classical theorem does not put `d_S` at the top of a finite-sample objective.

Consistent with this, the group's own post-2016 papers keep the two lines separate
(`docs/literature/shomorony-group-post2016-identifiability-2026-09-20.md`).

## Post-2016 continuation of the substring-spectrum line (not settlements)

These are the post-2016 primary works that continue the *multiset substring spectrum*
reconstruction problem. They study **partial / noisy / coded** spectra, not the finite uniform
read sample and not the Medvedev–Brudno objective.

1. **S. Marcovich, E. Yaakobi**, "Reconstruction of Strings from their Substrings Spectrum,"
   *IEEE Trans. Inf. Theory* 67(7):4369–4384, 2021; arXiv:1912.11108 (v1 2019, v2 2021).
   - Abstract (source fact): studies reconstruction under a **substrings spectrum** in which
     "not all substrings in the multispectrum are received," and also when "read substrings are
     not error free"; provides code constructions with efficient encoders/decoders and rates
     approaching 1, following the noisy model first studied by Gabrys–Milenkovic.
   - Model: complete-or-partial multiset of exact length-`k` substrings, with erasures/errors.
     Not a random shotgun sample; no likelihood ranking. Does not address bridging or the 2016
     question.
2. **R. Gabrys, S. Pattabiraman, O. Milenkovic**, "Unique Reconstruction of Coded Strings From
   Multiset Substring Spectra," *IEEE Trans. Inf. Theory* 65(12):7682–7696, 2019 (ISIT 2018
   preliminary); arXiv:1804.04548.
   - Source fact: characterizes/constructs **codebooks** of strings uniquely reconstructible
     from their multiset substring spectra; studies the equivalence classes and error
     correction. Codebook restriction is a different candidate class from the bridging-defined
     `C_det`/`C_spec` and from unbiased genomes.
3. **Z. Ye, O. Elishco**, "Reconstruction of a Single String From a Part of Its Composition
   Multiset," *IEEE Trans. Inf. Theory* 70(6):3922–3940, 2024; arXiv:2208.14963.
   - Model distinction: uses the **composition multiset** (unordered content of every
     substring), not the multiset of exact substrings. Different observation model; not the
     `L`-mer profile.
4. **U. Gupta, H. Mahdavifar**, "A New Algebraic Approach for String Reconstruction from
   Substring Compositions," *IEEE Trans. Inf. Theory* 71(1):125–137, 2025 (ISIT 2022);
   arXiv:2201.09955.
   - Same composition-multiset model; algebraic (bivariate polynomial) reconstruction.
5. (pre-2016 baseline for the composition model) **J. Acharya, H. Das, O. Milenkovic,
   A. Orlitsky, S. Pan**, "String Reconstruction from Substring Compositions," *SIAM J.
   Discrete Math.* 29(3):1340–1371, 2015; arXiv:1403.2439.

The `k`-deck (multiset of **subsequences**, not substrings) line, e.g. Golm–Nahvi–Gabrys–
Milenkovic, "The Gapped `k`-Deck Problem," arXiv:2201.12671, 2022, is a third, distinct model
and is not the `L`-mer profile.

## Assessment

| Claim | Status |
|---|---|
| Çelikkanat et al. Theorem 3.1 statement (quoted) | Source fact (arXiv HTML / NeurIPS 2024) |
| Attribution to Ukkonen 1992 (conjecture) and Pevzner 1995 (proof) | Source fact (as stated by Çelikkanat et al.) |
| Bibliographic data for Marcovich–Yaakobi 2021, Gabrys et al. 2019, Ye–Elishco 2024, Gupta–Mahdavifar 2025 | Source fact (arXiv / IEEE metadata) |
| `I_s`-admissibility ⇔ absence of the Theorem-3.1 circular obstructions | **Analysis** (needs circular-indexing verification) |
| Conjecture 4 is a known classical result | **Analysis** (strong, pending the check above) |
| No post-2016 work settles the statistical bridging→ML question | Source-analysis result (this search + prior notes) |
| The substring-spectrum line does not address bridging or global ML | Analysis, except where quoted |

## Effect on the repository

1. **Core conclusion unchanged:** no located settlement of the statistical 2016 question as of
   2026-09-20.
2. **New substantive constraint:** the `L`-mer-spectrum uniqueness half (repository Conjecture 4,
   and hence the "ties/fibres" analysis) should be treated as a consequence of the classical
   Ukkonen–Pevzner characterization, with a post-2016 citable restatement (Çelikkanat et al.
   2024, Thm 3.1). A future run should (a) pin a primary statement of the classical theorem for
   circular strings, (b) verify the exact `L−1` vs `L−2` threshold and the circular boundary,
   and (c) if confirmed, downgrade Conjecture 4 from "conjecture" to "known source theorem" in
   `mathematics/bridging-and-spectrum-uniqueness.md`.
3. **No Lean-definition changes are forced** by this run.
4. **New durable citations:** Ukkonen 1992; Pevzner 1995; Çelikkanat et al. 2024; Marcovich–
   Yaakobi 2021; Gabrys et al. 2019.

## References (newly recorded here)

1. E. Ukkonen. _Approximate string-matching with q-grams and maximal matches._ Theoretical
   Computer Science 92(1):191–211, 1992. <https://doi.org/10.1016/0304-3975(92)90143-4>
2. P. A. Pevzner. _DNA physical mapping and alternating Eulerian cycles in colored graphs._
   Algorithmica 13(1–2):77–105, 1995. <https://doi.org/10.1007/BF01188582>
3. A. Çelikkanat, A. R. Masegosa, T. D. Nielsen. _Revisiting K-mer Profile for Effective and
   Scalable Genome Representation Learning._ NeurIPS 2024; arXiv:2411.02125.
   <https://arxiv.org/abs/2411.02125>
4. S. Marcovich, E. Yaakobi. _Reconstruction of Strings from their Substrings Spectrum._
   IEEE Trans. Inf. Theory 67(7):4369–4384, 2021. <https://arxiv.org/abs/1912.11108>
5. R. Gabrys, S. Pattabiraman, O. Milenkovic. _Unique Reconstruction of Coded Strings From
   Multiset Substring Spectra._ IEEE Trans. Inf. Theory 65(12):7682–7696, 2019.
   <https://arxiv.org/abs/1804.04548>
6. Z. Ye, O. Elishco. _Reconstruction of a Single String From a Part of Its Composition
   Multiset._ IEEE Trans. Inf. Theory 70(6):3922–3940, 2024.
   <https://arxiv.org/abs/2208.14963>
7. U. Gupta, H. Mahdavifar. _A New Algebraic Approach for String Reconstruction from Substring
   Compositions._ IEEE Trans. Inf. Theory 71(1):125–137, 2025.
   <https://arxiv.org/abs/2201.09955>
