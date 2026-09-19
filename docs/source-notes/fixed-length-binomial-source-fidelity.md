# Fixed-length vs. binomial: source fidelity of the Medvedev–Brudno §6.1 objective and the scope of the 2016 open question

_Status: independent source note, 2026-09-19. Records newly retrieved primary-source
provenance and a terminology correction. Does not change the kernel-checked work for
issue #31/#33 or the issue #32 counterexample arithmetic; it only labels the objective
more precisely and distinguishes source fact from interpretation._

Companion notes:

- [`medvedev-brudno-candidate-class.md`](medvedev-brudno-candidate-class.md)
- [`shomorony-ml-reference.md`](shomorony-ml-reference.md)
- [`../fixed-length-binomial-counterexample.md`](../fixed-length-binomial-counterexample.md)
- [`../ml-formalization-contract.md`](../ml-formalization-contract.md)

## 0. Summary

1. **Provenance closed (main text).** The accepted 2016 text was retrieved from an
   author-hosted copy and the open-question sentence matches the repository's quotation
   verbatim. This removes the "accepted text not independently re-fetched" limitation for
   the main-text sentence.
2. **Formula verified independently.** The literal §6.1 product-of-binomial-marginals
   objective was re-read from the primary displayed equations and its ratio in the
   repository's witness was re-derived (`1125/512`).
3. **One conflation to fix in wording, not in mathematics.** "Fixed external `N`" (a change
   of the per-trial probability model) is not the same claim as "competitors are restricted
   to length `N`" (a restriction of the candidate universe). Medvedev–Brudno §6.1 does the
   former and does not state the latter. The phrase "fixed-length binomial objective" in the
   repository fuses the two. The mathematics of the existing counterexample is unaffected;
   only its name/description should be disambiguated.

## 1. Accepted 2016 text: independent retrieval and verbatim verification

Retrieved artifact (author-hosted copy on the corresponding author's Berkeley page):

- URL: <https://people.eecs.berkeley.edu/~courtade/pdfs/InfoOptimalAssy.pdf>
- size `715274` bytes; SHA-256
  `ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043ac3fce3c4da`;
  9 pages.
- Title and author list match the published article. Every page footer reads
  `Downloaded from https://academic.oup.com/bioinformatics/article-abstract/32/17/i494/2450780
  by UNIVERSITY OF CALIFORNIA, Berkeley user on 26 June 2018`, i.e. this is the published
  article PDF, not the earlier Stanford preprint.

The open-question sentence is on PDF page 9 of 9 (printed page i502), Section 5
(Discussion), in the final paragraph before *Acknowledgements*.

**Source fact (verbatim, the repository's target sentence).**

> "Understanding whether bridging conditions can be used to guarantee that the
> maximum-likelihood sequence is the true sequence is currently an open question."

This is exactly the sentence quoted in [`../open-problem.md`](../open-problem.md) and
`docs/literature-status.md`.

**Source fact (immediately preceding scope context, same paragraph).**

> "Another direction for future work, from a more theoretical standpoint, is understanding
> whether, in information-feasible instances of the AP, the output of NOT-SO-GREEDY
> coincides with the solution of a combinatorial optimization problem. Notice that while
> Theorem 1 guarantees the reconstruction of the true sequence s, there is no guarantee that
> this sequence corresponds to the solution of an optimization-based formulation of the AP
> such as those considered by Nagarajan and Pop (2009) and Medvedev and Brudno (2009). …
> The maximum-likelihood formulation of the AP (Medvedev and Brudno, 2009), on the contrary,
> seems to be robust to these issues, and thus a good candidate for the 'correct'
> formulation."

The same page defines the hypotheses the open question attaches to, numbered equation (1):

> `I_s = { R : R covers s, triple repeats in s are all-bridged, interleaved repeats in s are bridged }`

So the repository's description of `I_s` in [`../open-problem.md`](../open-problem.md)
(coverage plus all-bridged triple repeats plus bridged interleaved repeats) is
source-faithful. Note also that Theorem 1 itself is stated for coverage plus all-bridged
triple repeats; the interleaved-repeats clause is part of `I_s` and is used for the
Eulerian reduction (Corollary 1).

**Scope consequences (source reading).**

- The open question is asked about **information-feasible instances** (the paper's `I_s`
  region), and asks whether the ML sequence **coincides with** the true sequence.
- The paper names the Medvedev–Brudno *formulation* only by bibliography. It does not
  reproduce the likelihood, does not mention the binomial approximation, does not mention
  the §6.2 flow set, and   does not say competitors have the true length. This is independent
  confirmation of the unresolved variant choice recorded in
  [`medvedev-brudno-candidate-class.md`](medvedev-brudno-candidate-class.md) §4 and in
  [`shomorony-ml-reference.md`](shomorony-ml-reference.md).

**Provenance limitation that remains.** The publisher's accepted *supplementary* archive
(`bioinformatics_32_17_i494_s1.zip`) is still not independently inspected. This note
concerns the accepted main text only.

## 2. Literal §6.1 binomial objective: independent formula check

Primary text: Medvedev–Brudno (2009), `PMC3154397`, §6.1 "Maximizing the global read-count
likelihood". Body text (source fact):

> "Since in the binomial approximation the length of the genome `N(D)` is a constant that
> is independent of each `d_i`, we can replace it by `N`, which is the length of the actual
> genome from which the reads were sampled." … "For our experiments, we assume that the
> genome size is known."

The displayed equations are images; they were fetched directly from the NCBI CDN and read
(hashes for reproducibility):

| Asset | bytes | SHA-256 (first 16) | content |
|---|---|---|---|
| `M30.gif` | 943 | `af197c7ca67bac0a` | exact multinomial constraint `N(D) = Σ_i d_i` |
| `M31.gif` | 4157 | `3376d93729edf8b6` | `L[d_1,…,d_{4^k}\|x_1,…,x_{4^k}] ≈ ∏_i P[X_i=x_i] = ∏_i C(n,x_i)(d_i/N)^{x_i}(1-d_i/N)^{n-x_i}` |
| `M32.gif` | 1243 | `bf4726b65c2d4546` | separability identity `-log L = K·Σ_i c_i(d_i)` |
| `M33.gif` | 2047 | `d1cff9e91b8d79cb` | `c_i(d_i) = -(x_i log d_i) - (n-x_i) log(N-d_i)` |

**Source facts.**

- The product runs over all `4^k` read types and retains the zero-count factors
  `(1-d_i/N)^{n-x_i}`; it is not merely `∏_i d_i^{x_i}`.
- The denominator is the **external true length `N`**, not the candidate-dependent `N(D)`.
- The likelihood is written as a function of the copy-count vector `(d_1,…,d_{4^k})` with
  `N` fixed. There is no candidate-length coordinate in the formula.

**Independent arithmetic re-derivation of the repository witness.** For the witness in
[`../fixed-length-binomial-counterexample.md`](../fixed-length-binomial-counterexample.md)
(true `S=AAACC`, competitor `D=AAAAC`, `N=5`, `n=3`, observed `AAA,AAC,CAA` once each), the
literal product gives

- `L_A(S) = 27·(1/5)^3·(4/5)^12 = 452984832 / 30517578125`;
- `L_A(D) = 7962624 / 244140625`;
- `L_A(D)/L_A(S) = 1125/512 > 1`.

This reproduces the existing note's arithmetic. It is a computation, not an independent
kernel check; the kernel check for this objective remains an issue #32 concern.

## 3. The source-fidelity point: two independent axes

The repository sometimes writes "fixed-length binomial approximation". That phrase fuses
two logically independent modeling choices. They are not the same, and only one of them is
present in the primary source.

| Axis | What it fixes | Medvedev–Brudno §6.1 |
|---|---|---|
| A. Denominator/length **parameter** | Replaces candidate-dependent `N(D)` by the external true length `N` in each binomial success probability | **Stated** (source fact) |
| B. Candidate **universe** | Restricts competitors to circular genomes with `|D| = N` (or `|D| = G`) | **Not stated** (source fact) |

Reasons B does not follow from A (source reading):

1. The exact multinomial requires the coupling `Σ_i d_i = N(D)` (`M30.gif`), which is exactly
   what makes `-log L` non-separable; the approximation drops that coupling to get independent
   binomials. Once dropped, `(d_i)` is a free copy-count vector, not a fixed-length genome.
2. The approximation's domain is the set of `(d_i)` with `0 ≤ d_i ≤ N` (so that each factor is a
   valid binomial probability). A candidate longer or shorter than `N` remains in the domain
   whenever all its type-multiplicities satisfy `d_i ≤ N`.
3. A candidate `D` is still a circular genome realizing `(d_i)`; nothing in the passage makes
   `|D| = N` a definitional requirement.

The main-branch note that already separates these objects is
[`medvedev-brudno-candidate-class.md`](medvedev-brudno-candidate-class.md) §2–§3
(exact likelihood with candidate intrinsic length; approximation with an externally supplied
constant; §6.2 flow set as a distinct object). Several exploratory, non-`main` notes instead
say the binomial approximation "fixes length"; those should be read as an over-reading of
axis A.

**Consistency check at same length.** Even when `|D| = N`, the binomial objective is *not*
the fixed-length exact multinomial: the exact objective's per-candidate factor is
`N^{-n}·∏_i d_i^{x_i}`, while the binomial objective additionally retains
`∏_i (1-d_i/N)^{n-x_i}`. The witness ratio is `1125/512` under the binomial objective versus
`2` under the fixed-length exact multinomial — two different numbers for the same
equality-pattern instance. So "fixed-length" does not collapse Variant A into Variant E.

## 4. Terminology correction proposal (no mathematics changes)

The file name and content of
[`../fixed-length-binomial-counterexample.md`](../fixed-length-binomial-counterexample.md)
describe a counterexample whose competitor happens to be **same-length**, evaluated under
the **fixed-external-`N`** binomial approximation. Recommended disambiguation, in-place and
minimal:

- title: "Same-length competitor counterexample for the binomial approximation" (or
  "Fixed-external-`N` binomial-approximation counterexample"); and
- replace "this fixed-length literal Section 6.1 binomial-approximation objective" with
  "this literal Section 6.1 binomial-approximation objective, evaluated at the explicit
  same-length competitor".

This is wording only. It does not affect the arithmetic, the bridging certificate, or the
kernel-check boundary recorded for issue #32.

## 5. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| Accepted main-text open-question sentence is verbatim as quoted | Source fact | Author-hosted accepted PDF, SHA-256 above, p.9 |
| Open question is scoped to `I_s` information-feasible instances and asks coincidence with truth | Source fact | Same paragraph and eq. (1) |
| 2016 text does not select exact vs approximate vs flow, nor fix competitor length | Source fact | Full Discussion read; no passage does so |
| Literal §6.1 marginal retains `(1-d_i/N)^{n-x_i}` over all `4^k` types | Source fact | `M31.gif`, `M33.gif` |
| Binomial approximation replaces `N(D)` by external `N` | Source fact | §6.1 body text |
| §6.1 does **not** restrict competitors to length `N` | Source reading | No restriction appears; coupling dropped for separability |
| "Fixed-length binomial objective" conflates axes A and B | Source analysis | This note, §3 |
| Witness ratio `L_A(D)/L_A(S) = 1125/512` | Reproduced | §2 arithmetic |
| Accepted supplementary archive inspected | Not done | Out of scope here |

## 6. Handoff

- If issue #32's kernel worker names its objective, prefer "fixed-external-`N` binomial
  approximation" over "fixed-length binomial", so the formal statement's candidate universe
  stays recoverable from its type.
- If the repository later restricts Variant A to `|D| = N`, that restriction must be a named
  hypothesis, not read out of §6.1.
- [`../open-problem.md`](../open-problem.md) may now cite the accepted main-text sentence as
  independently retrieved; the accepted supplementary check remains open.
