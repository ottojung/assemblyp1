# Candidate-genome class and length semantics: source-fidelity resolution

_Status: source-fidelity result, 2026-09-19. Resolves the candidate-genome
class and length semantics attributable to the primary sources and records the
consequences for the repository's finite counterexamples. It does not claim to
settle which Medvedev–Brudno layer the 2016 sentence intends, and it does not
select an equivalence relation by fiat._

## Questions addressed

1. In the exact Medvedev–Brudno §6.1 likelihood, is a competing genome's length
   fixed to an external constant, or is it candidate-intrinsic?
2. In the §6.1 product-of-binomial-marginals approximation, which quantity is
   fixed?
3. What genome equivalence follows from the primary sources: cyclic shift only,
   or cyclic shift plus reverse complement?
4. Does the published 2016 maximum-likelihood claim quantify over all sequence
   lengths?

## Primary sources and independent verification

- Paul Medvedev and Michael Brudno, "Maximum Likelihood Genome Assembly,"
  *Journal of Computational Biology* 16(8), 2009, 1101–1116, DOI
  <https://doi.org/10.1089/cmb.2009.0047>, full text
  [PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/). Section 6.1
  body text was independently re-retrieved and read on 2026-09-19. The displayed
  equations are images in the HTML (`M26`–`M33`); the claims below use only the
  body text plus the elementary multinomial normalization.
- Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, and David N. C. Tse,
  "Information-optimal genome assembly via sparse read-overlap graphs,"
  *Bioinformatics* 32(17), 2016, i494–i502, DOI
  <https://doi.org/10.1093/bioinformatics/btw450>. The publisher endpoint
  returns HTTP 403, so the accepted main text was read from the author-hosted
  accepted PDF <https://people.eecs.berkeley.edu/~courtade/pdfs/InfoOptimalAssy.pdf>
  (SHA-256 `ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043acfce3c4da`).
  The Discussion passage was re-verified verbatim.
- Guy Bresler, Ma'ayan Bresler, and David Tse, "Optimal assembly for high
  throughput shotgun sequencing," *BMC Bioinformatics* 14(Suppl 5):S18, 2013,
  DOI <https://doi.org/10.1186/1471-2105-14-S5-S18> (for the equal-likelihood
  obstruction and its same-length competitor).

## 1. Exact §6.1 objective: candidate-intrinsic length

The §6.1 body text defines the candidate and the probability model as:

> "Let `D` be a circular genome of length `N(D)`, and let `di` denote the number
> of times the `k`-molecule `i` appears in `D`."

> "In each trial, a position is uniformly sampled from `D` and the outcome of
> the trial is the `k`-molecule beginning at that position. For a given `i`, the
> probability that the outcome of a single trial is `i` is simply `di/N(D)`."

The joint count distribution is "exactly the multinomial distribution," and the
likelihood of the copy-count vector `(di)` is called the **global read-count
likelihood**. The multinomial normalization gives the internal constraint

```text
N(D) = Σ_i d_i .
```

**Source facts.**

- A candidate is a circular genome whose length `N(D)` is an intrinsic property,
  not an externally supplied parameter.
- The per-trial probability of read type `i` is its occurrence multiplicity
  divided by the candidate's own length.
- The source does **not** state that all competitors share one fixed length, and
  it does not state that competitors have the true genome's length.
- The source does not explicitly enumerate the competitor universe either. The
  strongest defensible reading is that the objective is defined on every
  nonempty circular candidate (equivalently, every de Bruijn-realizable
  copy-count vector with `N(D) = Σ_i d_i`).

## 2. Approximation: an external length in the denominator

The §6.1 body text then introduces the separable approximation:

> "Since in the binomial approximation the length of the genome `N(D)` is a
> constant that is independent of each `di`, we can replace it by `N`, which is
> the length of the actual genome from which the reads were sampled."

**Source facts.**

- The approximation replaces the candidate-dependent `N(D)` by a fixed external
  constant `N` (the actual or estimated genome length).
- This is an explicitly labeled approximation, not the exact global likelihood.
- The approximation is still a function of the free variables `(di)`. It does
  not impose `Σ_i d_i = N`, and it does not impose a single candidate length on
  the competitors. Its literal domain requires `0 ≤ d_i ≤ N` for the binomial
  factors `(1 - d_i/N)^{n - x_i}` to be probabilities; a candidate with some
  `d_i > N` falls outside the domain for a reason unrelated to its length.

## 3. Circular equivalence

- Shomorony et al. work with a circular true sequence and state their
  reconstruction conclusion up to cyclic shift. Cyclic-shift equivalence is
  therefore source-required for the circular-string model.
- Medvedev and Brudno model double-stranded DNA with unordered reverse-
  complement molecules and bidirected graphs. In that model a molecule and its
  reverse complement are not distinguished. The 2016 open-question text does not
  restate this and does not say whether the maximum-likelihood competitor
  identity is cyclic shift only or cyclic shift plus reverse complement.
- **Resolution:** cyclic shift is a source fact; reverse-complement
  identification is a source fork that must remain an explicit parameter. It
  does not affect the maximizer-only schema, which contains no equivalence
  relation; it can affect the uniqueness schema.

## 4. Does the published claim quantify over all sequence lengths?

The 2016 sentence is, verbatim from the accepted Discussion:

> "Understanding whether bridging conditions can be used to guarantee that the
> maximum-likelihood sequence is the true sequence is currently an open
> question."

It is preceded by the observation that Theorem 1 reconstructs `s` but does not
guarantee that `s` solves an optimization-based formulation, and by the naming
of "The maximum-likelihood formulation of the AP (Medvedev and Brudno, 2009)"
as "a good candidate for the 'correct' formulation." Shomorony et al. fix the
true sequence's length `G` for the data-generating model but never state a
length constraint on maximum-likelihood competitors, and the main text contains
no likelihood formula.

**Resolution.**

- If "the maximum-likelihood formulation" means the exact §6.1 global
  read-count likelihood, then its candidate length is intrinsic and no fixed
  competitor length is imposed. The claim therefore quantifies over circular
  candidates of arbitrary nonempty length unless a restriction is added.
- If it means the §6.1 binomial approximation, `N` is an external scoring
  constant; the candidates are still free count vectors and again no fixed
  candidate length is imposed.
- Under either literal reading, restricting competitors to the true length `G`
  or to a fixed external `N` is an **additional, unstated modeling decision**
  and must be named as a restriction rather than assumed as a default.

## 5. Consequences for the repository's known counterexamples

The repository's finite witnesses were re-checked with exact rational
arithmetic on 2026-09-19. The point below is which reading each one bears on.

| Witness | Objective / candidate universe | Source admissibility | Consequence |
|---|---|---|---|
| `ACGT` vs `ACACGT`, reads `{AC,AC,GT}`, bridging vacuous (`docs/exact-variant-e-counterexample.md`) | Exact §6.1 multinomial, candidate length intrinsic | Admissible: `ACACGT` is a nonempty circular candidate of length 6 ≠ `G = 4`, and §6.1 imposes no fixed length | Refutes the truth-is-a-maximizer and uniqueness schemas for the **literal unrestricted-length exact §6.1** reading. `L(ACGT)=3/64`, `L(ACACGT)=1/18`, difference `5/576 > 0`. Kernel-checked in `AssemblyP1/ExactVariantECounterexample.lean` |
| `AAABB` vs `AAAAB`, `G = 5` (`docs/fixed-length-exact-counterexample.md`) | Exact §6.1 multinomial with all candidates restricted to length `G` | Uses a restriction the source does not state | Refutes the exact objective **when the unstated fixed-length restriction is imposed**. `L` ratio `2`. Kernel-checked in `AssemblyP1/FixedLengthExactCounterexample.lean` |
| `AAACC` vs `AAAAC`, `N = 5`, reads `{AAA,AAC,CAA}` (`docs/fixed-length-binomial-counterexample.md`) | Literal §6.1 product-of-binomial-marginals, fixed external `N = 5` | Literal approximation; same-length competitor keeps `Σ d_i = N` | Refutes truth-is-a-maximizer for the **literal separable approximation**. Ratio `1125/512 > 1`; arithmetic independently reproduced (not yet kernel-checked) |

The first row is decisive for the length question: because the exact §6.1
objective does not fix competitor length, the existing kernel-checked
`ACGT`/`ACACGT` instance is a legitimate counterexample to the maximizer claim
under that reading, not an artifact of an inadmissible competitor. The strict
inequality also means the refutation does not depend on the genome-equivalence
convention.

## 6. Net frontier

- The candidate-genome class for the exact §6.1 objective is circular genomes of
  arbitrary nonempty length; length is intrinsic, `N(D) = Σ_i d_i`.
- Fixed competitor length is not source-justified for §6.1; it must be carried
  as a named restriction.
- The published 2016 sentence, read as the literal exact §6.1 objective, is
  refuted (negatively settled) by the existing finite counterexample.
- The question can remain open only under a restricted candidate class, a
  different objective layer (external-`N` separable approximation or the §6.2
  flow feasible set), or a different genome/likelihood convention. Of these, the
  separable approximation is also refuted for same-length competitors in the
  repository's arithmetic; the least-tested object nearest the citation is the
  §6.2 read-derived flow feasible set (`Variant F`), which has not been
  identified with the §6.1 candidate universe and for which no bridging-to-ML
  statement has been proved or refuted.

## Epistemic classification

| Claim | Class | Basis |
|---|---|---|
| §6.1 candidate is circular with intrinsic `N(D)`; probability `d_i/N(D)`; `N(D)=Σ_i d_i` | Source fact | Medvedev–Brudno §6.1 body text (re-read 2026-09-19) |
| §6.1 states no fixed competitor length | Source fact (absence) | Full §6.1 text |
| §6.1 candidate universe is all nonempty circular genomes | Source reading (well-supported) | Definition of `D` plus absence of any restriction |
| Approximation replaces `N(D)` by external `N` and is distinct from the exact objective | Source fact | Medvedev–Brudno §6.1 body text |
| Cyclic shift required; reverse complement unresolved | Source fact + source analysis | Shomorony circular reconstruction; Medvedev–Brudno double-stranded molecules |
| Literal exact §6.1 maximizer claim is false | Mathematical consequence of kernel-checked witness | `AssemblyP1.ExactVariantECounterexample` |
| Which 2009 layer the 2016 sentence intends | Unresolved | [`shomorony-ml-reference.md`](shomorony-ml-reference.md); accepted main text selects none |

## Related notes

- [`medvedev-brudno-candidate-class.md`](medvedev-brudno-candidate-class.md)
- [`shomorony-ml-reference.md`](shomorony-ml-reference.md)
- [`../ml-formalization-contract.md`](../ml-formalization-contract.md)
- [`../exact-variant-e-counterexample.md`](../exact-variant-e-counterexample.md)
- [`../fixed-length-exact-counterexample.md`](../fixed-length-exact-counterexample.md)
- [`../fixed-length-binomial-counterexample.md`](../fixed-length-binomial-counterexample.md)
- [`../literature-status.md`](../literature-status.md)
