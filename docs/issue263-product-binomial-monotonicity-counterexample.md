# The MB09 §6.1 product-binomial is not coordinatewise monotone (board #263)

_Status: kernel-checked Lean counterexample
(`AssemblyP1/ProductBinomialMonotonicityCounterexample.lean`, axiom audit in
`AssemblyP1/ProductBinomialMonotonicityCounterexampleAudit.lean`), imported by
`AssemblyP1.lean`. No `sorry` / `admit` / `axiom` / `native_decide`._

This is a bounded, independent increment on the issue-#263 frontier. It
kernel-checks the small finite counterexample that **separates a
coordinatewise-monotone separable Graver optimality certificate from the
Medvedev–Brudno 2009 §6.1 product-of-binomials objective**. It does **not**
touch #257's integer-kernel conformal decomposition, #261's signed-graph
adapter, or `Section62BinomialCriterion`.

## The model it settles

Medvedev–Brudno 2009, §6.1 (PMC3154397) score a candidate circular genome by
the product of per-read-type **binomial marginals** with a fixed external genome
size `N`. For one read type with `n` reads and `x` observed copies, the marginal
is `(d / N)^x (1 - d / N)^(n - x)`, where `d` is the candidate copy count. The
Lean definition `binomKernel N n x d = d^x * (N - d)^(n - x)` is the integer
numerator; the denominator `N^n` is candidate-independent, so all comparisons
are unchanged.

The kernel is the product of an **increasing** factor `d^x` and a **decreasing**
factor `(N - d)^(n - x)`, hence **nonmonotone** in `d`. The coordinatewise
nonmonotonicity is **not new here**: it is already kernel-checked as
`AssemblyP1.GeneralBidirectedFlowML.binomial_not_coordinatewise` (truth `(1, 2)`,
candidate `(1, 1)`, external `N = 3`, sample `(2, 1)`, core `8 > 4`; see
[`docs/issue261-general-bidirected-flow-ml.md`](issue261-general-bidirected-flow-ml.md)),
and the earlier "0 and `N-d` factors are nonmonotone" attribution to the board is
corrected accordingly. The genuinely new content of this module is the failure of
the **single-coordinate sign-compatible Positive Sum Property** (`HasPSS`), the
one-dimensional superadditivity step of a monotone separable Graver certificate,
which the coordinatewise failure alone does not establish.

## The theorem(s) and the exact ratio

Instance: `N = 12`, `n = 3`, `x = 1`.

| theorem | statement |
|---|---|
| `binomKernel_eight_lt_four` | `P(8) = 8 · 4² = 128 < 256 = 4 · 8² = P(4)` with `4 ≤ 8`; exact ratio `P(4) / P(8) = 2`. |
| `binomKernel_not_coordMono` | the §6.1 objective is **not** coordinatewise monotone (`¬ CoordMono`); re-instantiation of the already-merged `AssemblyP1.GeneralBidirectedFlowML.binomial_not_coordinatewise`. |
| `binomKernel_pss_fails` | on the sign-compatible path `4 → 6 → 8`, `P(8) − P(4) = −128 < −80 = 2·(P(6) − P(4))`; the sign-compatible Positive Sum Property **fails**. |
| `binomKernelTwo_dominance_fails` | on two types, the dominated spectrum `(4, 4)` beats the dominating spectrum `(8, 8)` (`256² = 65536 > 16384 = 128²`). |
| `binomKernel_zero`, `binomKernel_at_N` | boundary kernels vanish (`P(0) = P(12) = 0`), so the true extended-real negative log is `+∞` there. |
| `product_binomial_separation` | combined separation: `¬ CoordMono ∧ ¬ HasPSS`. |
| `id_coordMono`, `id_hasPSS` | the coordinatewise-monotone separable domain is nonempty (`f d = d`). |

The two **domain hypotheses** are made explicit as `CoordMono` (coordinatewise
monotonicity / dominance) and `HasPSS` (sign-compatible Positive Sum Property,
the one-dimensional superadditivity step). The §6.1 product-binomial satisfies
neither, so a Graver certificate that assumes either does **not** transfer to it.

## What the correct certificate uses instead

The separable-convex Graver certificate
([`docs/issue263-separable-convex-graver-certificate.md`](issue263-separable-convex-graver-certificate.md))
requires **discrete convexity** of the one-coordinate cost
(`AssemblyP1.SeparableConvexGraver.DiscConvOn`), not monotonicity. The §6.1
negative-log cost is discretely convex in the candidate copy count `d` on the
**open interior** `0 < d < N`
(`AssemblyP1.SeparableConvexGraver.binomTerm_discConvOn`), where
`−log P(d) = −x log d − (n − x) log(N − d) + n log N`. It is *not* the raw
likelihood kernel, and at a zero-probability boundary (`d = 0` with `x > 0`, or
`d = N` with `n − x > 0`) the true cost is `+∞`; the finite full-box treatment
is a separately-documented regularized extension, not the genuine ML objective.

## Scope

This is a statement about the §6.1 **product-binomial surrogate** in the
candidate copy count. It makes no claim about the exact joint multinomial law,
about §6.2 bidirected flows, about which feasible flows spell genomes, or about
the historical candidate adapter (all deliberately left to their own fronts).
