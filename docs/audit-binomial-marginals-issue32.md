# Independent audit: issue #32 literal product-of-binomial-marginals objective

_Status: independent exact-rational audit, 2026-09-19. Scope limited to the
literal Medvedev–Brudno §6.1 separable/binomial approximation ("Variant A").
Does not touch PR #33 or Section 6.2. Does not settle the source-ambiguous
Shomorony et al. open question._

## 1. Scope and primary source

The objective audited here is the one the issue calls the **literal
product-of-binomial-marginals approximation** from Medvedev–Brudno (2009),
"Maximum Likelihood Genome Assembly", J. Comput. Biol. 16(8), §6.1.

Primary-source formula (PMC3154397, §6.1, displayed equation after the
multinomial; recovered from the publisher-rendered display graphic `M31.gif`):

```text
L[d_1,...,d_{4^k} | x_1,...,x_{4^k}]
    ~= prod_i P[X_i = x_i]
     = prod_i C(n, x_i) (d_i / N)^{x_i} (1 - d_i / N)^{n - x_i}.
```

The surrounding prose states: "There are `4^k` such variables, and when
considered independently of each other, they each follow the binomial
distribution"; "we can approximate the multinomial distribution as the product
of the individual binomial distributions of each `X_i`"; "in the binomial
approximation the length of the genome `N(D)` is a constant that is independent
of each `d_i`, we can replace it by `N`, which is the length of the actual
genome from which the reads were sampled"; "For our experiments, we assume that
the genome size is known."

The immediately following convex-cost display (`M33.gif`) is

```text
c_i(d_i) = -(x_i log d_i) - (n - x_i) log(N - d_i),
```

which is exactly the negative log of the marginal binomial **retaining** the
`(1 - d_i/N)` factor and dropping only terms independent of `d_i`. This is
direct source evidence that the `(1 - d_i/N)^{n - x_i}` factors are part of the
literal objective and are not meant to be discarded from it.

### Source-fact vs. interpretation

- **Source fact:** the product is over all `4^k` read types, uses one fixed
  external `N` (the true genome length) in every factor, and includes both the
  binomial coefficients `C(n, x_i)` and the zero-count factors
  `(1 - d_i/N)^{n - x_i}`.
- **Source ambiguity (unchanged):** Shomorony et al. (2016) cite the
  Medvedev–Brudno ML formulation by bare bibliography and do not say whether
  their open question intends this approximation, the exact multinomial, or the
  §6.2 flow feasible set. This note does not resolve that.

## 2. Witness

DNA relabeling (`B -> C`) of the issue #31 / #32 witness:

- truth `S = AAACC`, length `5`;
- read length `k = 3`, number of reads `n = 3`;
- realized starts `0, 1, 4`, so observed types are `AAA, AAC, CAA`, once each;
- same-length competitor `D = AAAAC`, length `5`;
- fixed external `N = 5`.

Circular 3-mer multiplicities:

```text
S = AAACC : {AAA:1, AAC:1, ACC:1, CCA:1, CAA:1}
D = AAAAC : {AAA:2, AAC:1, ACA:1, CAA:1}
observed  : {AAA:1, AAC:1, CAA:1}
```

`S` is repeat-free in 3-mers; `D` doubles `d(AAA)` from `1` to `2` while keeping
the observed types positive.

## 3. Exact-rational recomputation

Computed with Python `fractions.Fraction` over the full `4^3 = 64` type space
(script: `scripts/audit_binomial_marginals_issue32.py`).

**Literal full marginal-binomial PMF** (all 64 factors, including binomial
coefficients and zero-count factors):

```text
L_A(S) = 452984832 / 30517578125   ~= 0.014843406974976
L_A(D) = 7962624 / 244140625       ~= 0.032614907904
L_A(D) / L_A(S) = 1125 / 512       ~= 2.197265625  > 1
```

The values match issue #32 exactly. The ratio `1125/512 > 1` reproduces.

**Factor separation.** Dropping the observation-only binomial coefficients
`C(n, x_i)` leaves the ratio unchanged at `1125/512` (they cancel in the
candidate comparison). Dropping the zero-count factors `(1 - d_i/N)^{n-x_i}`
instead changes the ratio to exactly `2`:

```text
L_A(D)/L_A(S) with zero-count factors    = 1125/512  > 1
L_A(D)/L_A(S) without zero-count factors = 2         > 1
```

Thus the literal objective and its simplified version give **different ratios**
even though both orderings happen to agree on this instance. This confirms the
issue's warning that dropping the zero-count factors gives a different
objective, and shows the difference is quantitatively material.

**Source convex-cost identity.** The exact identity

```text
L = K · prod_i d_i^{x_i} (N - d_i)^{n - x_i},
    K = prod_i C(n, x_i) / N^{n·4^k},
```

is verified exactly for both `S` and `D`, matching the source's `c_i` form.

## 4. Fixed external `N` is not a candidate-length constraint

> **Qualification (2026-09-19, end-to-end audit).** The reading in this section
> is narrowed by [`docs/audit-issue32-end-to-end.md`](audit-issue32-end-to-end.md)
> §3. The §6.1 replacement of `N(D)` by `N` is justified in the source by
> declaring the candidate length "a constant … the length of the actual
> genome"; the source-faithful reading therefore restricts the approximation to
> length-`N` candidates (`Σ_i d_i = N`), which automatically gives `d_i <= N`.
> The length-`≠N` admissibility claimed below is an extension of the bare
> displayed product beyond its derivation and is **not source-supported**.
> The witness itself has `|S| = |D| = N = 5`, so its conclusion is unaffected.
> `docs/source-notes/candidate-genome-class-resolution.md` §2.2 states the
> fixed-length reading; the conflict should be resolved toward that reading.

The literal objective uses `N` only as a probability denominator. Nothing in the
formula restricts the candidate `D` to length `N`. The only domain requirement
is that each factor be a valid binomial probability, i.e. `0 <= d_i/N <= 1`, so
the objective is well-defined precisely when `d_i <= N` for every type `i`.

Consequences:

- A candidate of length `5` (`D = AAAAC`) is admissible, as used here.
- A candidate of length `6` can also be admissible (e.g. `AAAAAC` has
  `max d_i = 3 <= 5`), even though its length differs from the external `N`.
- A candidate can fall **outside the approximation domain** when some type
  occurs more than `N` times (e.g. `AAAAAA`, `max d_i = 6 > 5`), since
  `(1 - d_i/N)^{n-x_i}` is then not a probability. This is a domain artifact of
  the fixed-`N` approximation, not a length restriction.

So the correct reading of the issue's "fixed external `N`" is: `N` is the
source genome's length, supplied externally and used as the binomial success
denominator. It does **not** fix the candidate universe to length-`N` strings.
In particular, the product over the full `4^k` type space naturally includes
read types absent from `D` (`d_i = 0`, contributing `1` for `x_i = 0` and `0`
for `x_i > 0`), which is why the zero-count factors are essential.

## 5. Distinctness from the fixed-length exact multinomial

For the same instance, the exact multinomial at common length `G = 5` gives

```text
L_exact(D|x) / L_exact(S|x) = 2.
```

So the literal binomial approximation (`1125/512`) and the fixed-length exact
multinomial (`2`) are genuinely different objectives with different numerical
ratios on the same data. This is the separation issue #32 and #31 were meant to
maintain.

## 6. Relation to existing Variant A statements

Exploratory repository analyses often characterize the binomial approximation
as `L ∝ prod_i d_i^{x_i}` (for example the fixed-length objective analysis and
the Eulerian/edge-count formulation note).

That characterization is **correct only for the zero-count-dropped simplified
objective** (the `2` branch above), not for the literal product in the source,
which retains `(1 - d_i/N)^{n-x_i}`. The conclusion those analyses draw — that
Variant A admits a counterexample — is unaffected and in fact holds for both
versions, but the stated objective is imprecise. Downstream work that needs the
literal source objective (including any future kernel check of this instance)
should use the full product. This note is deliberately independent of those
exploratory artifacts and rests only on the primary source and the exact
computation in `scripts/audit_binomial_marginals_issue32.py`.

## 7. Epistemic status

| Claim | Status |
|-------|--------|
| Source §6.1 product includes binomial coefficients and `(1 - d_i/N)^{n-x_i}` over all `4^k` types | **Source fact** (displayed equation + `c_i` form, PMC3154397) |
| `L_A(S) = 452984832/30517578125`, `L_A(D) = 7962624/244140625`, ratio `1125/512 > 1` | **Verified** exact rationals, independently reproduced |
| Dropping zero-count factors changes the ratio to `2` | **Verified** exact rationals |
| `L = K · prod d_i^{x_i}(N-d_i)^{n-x_i}` with source `c_i` | **Verified** exact identity |
| Fixed external `N` is a denominator, not a length constraint; domain is `d_i <= N` | **Source reading** supported by the formula; interpretation |
| Literal binomial ratio differs from fixed-length exact multinomial ratio | **Verified** exact rationals (`1125/512` vs `2`) |
| Shomorony et al. intended this objective | **Unresolved source ambiguity** — not claimed |
| Section 6.2 flow feasibility | **Out of scope** — not claimed |

## 8. Reproduce

```text
python3 scripts/audit_binomial_marginals_issue32.py
```

The script asserts the issue's values, the `1125/512` ratio, the `2` ratio for
the zero-count-dropped objective, the source convex-cost identity, and prints
the candidate-universe/domain check.
