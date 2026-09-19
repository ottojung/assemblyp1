# End-to-end independent audit of issue #32 (Medvedev–Brudno §6.1 binomial approximation)

_Status: independent primary-source + exact-rational audit, 2026-09-19. Scope is
the literal §6.1 product-of-binomial-marginals approximation ("Variant A") and
the `AAACC` / `AAAAC` witness. It does **not** settle the source-ambiguous
Shomorony et al. (2016) open question, and it does not touch the exact
fixed-length multinomial (issue #31 / PR #33) or the §6.2 flow feasible set except
to note the distinction._

This note is independent of, and in one place corrects/qualifies,
`docs/audit-binomial-marginals-issue32.md` (branch `audit/issue32-binomial-marginals`).
The raw arithmetic there reproduces exactly; the candidate-universe reading in
its §4 is narrowed below.

## 1. Primary source, re-fetched and re-read

- Paul Medvedev and Michael Brudno, "Maximum Likelihood Genome Assembly,"
  *Journal of Computational Biology* 16(8), 2009, 1101–1116,
  DOI [10.1089/cmb.2009.0047](https://doi.org/10.1089/cmb.2009.0047),
  full text [PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/).

Fetched fresh in this audit (not reused from an earlier run). The displayed
formulas are images in the PMC HTML; the image assets were downloaded and read
directly:

| Asset | SHA-256 (this fetch) | Content |
|-------|----------------------|---------|
| `M26.gif` | `d7488abb…ca13371` | per-trial probability `d_i/N(D)` |
| `M27.gif` | `74f8e68f…eca46276` | exact multinomial `P[X_1=x_1,…,X_{4^k}=x_{4^k}] = n!/(∏x_i!) ∏_i (d_i/N(D))^{x_i}` |
| `M30.gif` | `af197c7c…3c89e362` | constraint `N(D) = Σ_i d_i` |
| `M31.gif` | `3376d937…54b0b34a` | binomial approximation (below) |
| `M33.gif` | `d1cff9e9…830dea5` | convex cost `c_i(d_i) = -(x_i log d_i) - (n-x_i) log(N-d_i)` |

Reading `M31.gif` directly gives the literal formula:

```text
L[d_1, ..., d_{4^k} | x_1, ..., x_{4^k}]
    ≈ ∏_i P[X_i = x_i]
    = ∏_i C(n, x_i) (d_i / N)^{x_i} (1 - d_i / N)^{n - x_i} .
```

The surrounding prose (same fetch) reads, verbatim in relevant part:

> "There are `4^k` such variables, and when considered independently of each
> other, they each follow the binomial distribution."
>
> "…we can approximate the multinomial distribution as the product of the
> individual binomial distributions of each `X_i`. **Since in the binomial
> approximation the length of the genome `N(D)` is a constant that is
> independent of each `d_i`, we can replace it by `N`, which is the length of
> the actual genome from which the reads were sampled.** … For our experiments,
> we assume that the genome size is known."

**Source fact.** The formula in `docs/audit-binomial-marginals-issue32.md` §1 is
a faithful transcription: the product ranges over all `4^k` read types, uses one
fixed external `N`, retains the binomial coefficients `C(n,x_i)` and the
zero-count factors `(1-d_i/N)^{n-x_i}`, and the negative log matches `M33` after
dropping candidate-independent constants. The claim that the zero-count factors
are part of the literal objective is directly supported by `M33`.

## 2. Witness recomputation over the full `4^3` type space

Instance (DNA relabeling `B→C` of the issue #31 `AAABB` / `AAAAB` instance):

- truth `S = AAACC`, length `5`;
- competitor `D = AAAAC`, length `5`;
- read length `k = 3`, number of reads `n = 3`;
- realized starts `0, 1, 4` → observed types `AAA, AAC, CAA`, once each;
- fixed external `N = 5`.

Circular `3`-mer spectra (recomputed):

```text
S = AAACC : {AAA:1, AAC:1, ACC:1, CCA:1, CAA:1}   (5 distinct types)
D = AAAAC : {AAA:2, AAC:1, ACA:1, CAA:1}
observed  : {AAA:1, AAC:1, CAA:1}
```

Independent exact-rational evaluation with a from-scratch script
(`scripts/audit_issue32_end_to_end.py`) over all `4^3 = 64` DNA read types:

```text
L_A(S) = 452984832 / 30517578125   ≈ 0.014843406974976
L_A(D) = 7962624 / 244140625       ≈ 0.032614907904
L_A(D) / L_A(S) = 1125 / 512       ≈ 2.197265625  > 1
```

The issue #32 values and the ratio `1125/512` reproduce exactly. Additional
checks:

- dropping the observation-only coefficients `C(n,x_i)` leaves the ratio
  `1125/512` (they are candidate-independent for fixed `x`);
- dropping the zero-count factors `(1-d_i/N)^{n-x_i}` instead changes the ratio
  to exactly `2`, confirming that the literal and simplified objectives differ;
- the exact fixed-length multinomial (issue #31 objective) gives ratio `2` on the
  same instance;
- the source convex-cost identity `L = K · ∏_i d_i^{x_i} (N-d_i)^{n-x_i}` holds
  exactly for both `S` and `D`.

**Verified.** The computational core of issue #32 is correct.

## 3. The candidate-universe / fixed-`N` question

The issue asks whether the candidate-universe / fixed-external-`N`
interpretation used is source-faithful. The answer is narrower than
`docs/audit-binomial-marginals-issue32.md` §4 states.

**Source facts.** In the exact model the candidate `D` is a circular genome
with its *own* length `N(D) = Σ_i d_i`, and the per-trial probability is
`d_i/N(D)`. The binomial approximation then proceeds by declaring the length
"a constant that is independent of each `d_i`" and replacing `N(D)` by the
external `N`, "the length of the actual genome"; the paper adds that "we assume
that the genome size is known."

**Source reading (well-supported).** That replacement is the definition of a
*fixed-length* approximation: it takes every candidate's length to equal the
known true length `N`, i.e. it restricts the copy-count vector to
`Σ_i d_i = N`. This is what makes each factor `Binomial(n, d_i/N)` a genuine
marginal and what makes the product a coherent approximation of the candidate's
multinomial. For a candidate of length `M ≠ N`, the candidate's own per-trial
probability is `d_i/M`, not `d_i/N`; the product of `Binomial(n, d_i/N)` terms is
then neither the candidate's multinomial nor a normalized distribution (the
success probabilities `d_i/N` do not sum to `1`). So the external `N` is not
merely a free denominator: it encodes the candidate length.

**Consequence for the existing audit.** The statement in
`docs/audit-binomial-marginals-issue32.md` §4 that candidates with `d_i ≤ N` but
length `≠ N` (e.g. `AAAAAC`) are "admissible for the literal objective" is an
extension of the displayed product beyond its derivation. It is not directly
supported by the source, and it should not be presented as a source reading.
What the source supports is:

- the approximation's candidate universe is length-`N` circular genomes
  (`Σ_i d_i = N`, which automatically gives `d_i ≤ N`); and
- the source does not *explicitly* reassure the reader about competitors of
  other lengths, and its §6.2 implementation optimizes an unconstrained
  bidirected flow, so the competitor set is at least under-specified.

**The witness is unaffected.** `S` and `D` both have length `N = 5`
(`Σ_i d_i = 5`), so the counterexample lies inside the fixed-length-`N`
universe. It is therefore robust to this interpretation question: it refutes
the fixed-length binominate approximation whether fixed-`N` is read as a length
constraint or as a bare denominator.

**Repository conflict to surface.** `docs/source-notes/candidate-genome-class-resolution.md`
§2.2 and its variant table state that the binomial approximation "fixes length to
`N`." The existing issue #32 audit §4 asserts the opposite. These two current
repository statements conflict and should be reconciled to the fixed-length
reading above.

## 4. Relation to the issue #31 certificate

The witness is the exact `B→C` relabeling of the issue #31 instance, whose
`I_s` certificate (coverage; the maximal length-1 triple repeat on `A` at starts
`0,1,2`, all-bridged by reads at `4,0,1`; no interleaved pair requiring a
bridge) is kernel-checked by
`AssemblyP1.FixedLengthExactCounterexample.fixed_length_exact_counterexample`
and documented in `docs/fixed-length-exact-counterexample.md`. The relabeling
preserves the repeat/bridging structure, so the same `I_s` certificate applies.
This audit recomputes only the likelihood comparison; it does not re-formalize
`I_s`.

## 5. Epistemic classification

| Claim | Status |
|-------|--------|
| `M31` literal product includes `C(n,x_i)` and `(1-d_i/N)^{n-x_i}` over all `4^k` types | **Source fact** (fresh fetch, `M31`/`M33`) |
| `L_A(S)=452984832/30517578125`, `L_A(D)=7962624/244140625`, ratio `1125/512>1` | **Verified**, independent exact rationals |
| Dropping zero-count factors changes the ratio to `2` | **Verified** |
| `L = K ∏ d_i^{x_i}(N-d_i)^{n-x_i}` matches source `c_i` | **Verified** |
| Literal binomial ratio `1125/512` differs from fixed-length exact ratio `2` | **Verified** |
| The approximation fixes candidate length to the known true `N` (`Σd_i=N`) | **Source reading** (from the "constant independent of each `d_i`" / "length of the actual genome" justification) |
| Candidates of length `≠ N` are admissible | **Not source-supported**; extension beyond the derivation |
| `S` and `D` both have length `N=5`, so the witness is inside the fixed-length universe | **Verified** |
| Shomorony et al. intended this approximation | **Unresolved source ambiguity** — not claimed |
| §6.2 flow feasible set | **Out of scope** — not claimed |

## 6. Reproduce

```text
python3 scripts/audit_issue32_end_to_end.py
python3 scripts/audit_binomial_marginals_issue32.py
```

Both scripts assert the exact values above and print the length/domain check.
The two scripts were written independently and agree.

## 7. What this does and does not claim

It independently confirms the literal §6.1 formula and the `AAACC`/`AAAAC`
exact-rational counterexample, and it corrects the candidate-universe reading to
the fixed-length-`N` interpretation while noting that the source nowhere states
the approximation's competitor universe explicitly. It does **not** identify
which Medvedev–Brudno layer the Shomorony et al. sentence intends, does not
resolve equality/tie semantics, and does not settle the published open problem.
