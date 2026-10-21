# Exact support-restricted Graver optimality certificate (issue #263)

This note documents the kernel-checked Lean artifact
[`AssemblyP1/ExactSupportRestrictedGraver.lean`](../AssemblyP1/ExactSupportRestrictedGraver.lean)
and its axiom audit
[`AssemblyP1/ExactSupportRestrictedGraverAudit.lean`](../AssemblyP1/ExactSupportRestrictedGraverAudit.lean).

## Why this increment exists

The merged separable-convex Graver certificate
`AssemblyP1.SeparableConvexGraver.graver_optimal_iff_no_improving` (PR #305)
and its exact-ML optimizer-preservation transfer
`AssemblyP1.ExactMLOptimizerTransfer` (PR #357) are conditional: the transfer
from the finite secant-slope affine-tail *surrogate* to the genuine
extended-real ML objective needs the certified minimizer to lie in the positive
interior of the box, and that hypothesis is **not** established.  The
one-dimensional witness `N = 3, n = 2, x = 1` shows the surrogate over-admits:
the exact likelihoods are `(0, 2/9, 2/9, 0)` so the exact ML maximizers are
`{1, 2}`, while `affineExtend` is constant on `{0,1,2,3}` and therefore
certifies all four candidates, including the impossible `d = 0` and `d = 3`.

This module removes the surrogate entirely.  The genuine extended-real cost
`⊤` at a zero-likelihood endpoint is used honestly, and the optimization is
restricted to the **support-restricted admissible box** where every marginal
likelihood is strictly positive.

## The support-restricted admissible box

For a finite read-class type `E`, external total `N`, observed counts `x`, and
read total `n` (`0 ≤ x ≤ n`), the admissible box is

```
lowOf x e  = if 0 < x e       then 1 else 0
highOf N n x e = if 0 < n e - x e then N e - 1 else N e
```

A candidate `z` is **admissible** when `lowOf x e ≤ z e ≤ highOf N n x e` for
all `e`.  This is exactly the set of candidates whose per-class binomial
marginal likelihood is strictly positive:

* `z e ≥ 1` whenever `x e > 0` — a positive observation forces a positive copy
  count;
* `z e ≤ N e - 1` whenever `n e - x e > 0` — an unobserved copy forces a
  non-full count.

The admissible box lies inside the ambient box `[0, N]`, so no candidate outside
`[0, N]` is considered.

## T1: excluded (zero-likelihood) candidates cannot minimize

`excluded_binom_exact_eq_top` / `excluded_multinomial_exact_eq_top`: a candidate
that violates the support restriction has a zero-likelihood marginal, hence
`binomExact` / `multinomialExact` is `⊤` (`+∞` negative log) there and the
separable objective is `⊤`.

`excluded_binom_not_minimizer` / `excluded_multinomial_not_minimizer`: given at
least one admissible candidate `w`, an excluded candidate `z` satisfies
`exactObj w < exactObj z = ⊤`, so `z` is **not** a global exact-ML minimizer.
This is the "excluded candidates cannot maximize the exact objective"
statement, in the minimization form of the negative-log objective.

## T2: optimizer preservation on the admissible box

`admissible_binomExact_eq_coe` / `admissible_multinomialExact_eq_coe`: on the
admissible box the exact extended-real objective agrees pointwise with the
honest finite interior cost `binomCost` (resp. `multinomialCost`), so
`exactObj = ↑(sepObj cost)`.

`admissible_binom_exact_le_iff_cost_le` /
`admissible_multinomial_exact_le_iff_cost_le`: two admissible candidates are
ordered by the exact objective exactly when they are ordered by the finite cost.
Hence the exact-ML minimizer over the admissible box coincides with the
minimizer of the finite cost over the same box.

`binomCost_admissible_discConvOn` / `multinomialCost_admissible_discConvOn`:
the honest finite cost is **discretely convex on the admissible box**, in all
four sign patterns of `x` and `n - x`:

| pattern | box | convexity source |
| --- | --- | --- |
| `x > 0`, `n - x > 0` | `[1, N-1]` | `SeparableConvexGraver.binomTerm_discConvOn` |
| `x > 0`, `n - x = 0` | `[1, N]` | `negLog_discConvOn` (composition with `log N`) |
| `x = 0`, `n - x > 0` | `[0, N-1]` | `negLog_sub_discConvOn_zero` (reflection of `-log d`) |
| `x = 0`, `n - x = 0` | `[0, N]` | constant `0` |

The left endpoint `d = 0` in the third row is honest because `x = 0` makes the
`-x·log(d/N)` term vanish; `negLog_sub_discConvOn_zero` is the reflection
`(fun d => -log d).comp_sub (c := N)`, which is discretely convex on
`[0, N-1]`.

## The exact-ML Graver certificate without the surrogate

`binom_exact_optimal_admissible` / `multinomial_exact_optimal_admissible`:
on the support-restricted integer affine fiber with box
`(lowOf x, highOf N n x)` (resp. `(lowOf x, G)`), a point `z` minimizes the
**exact** extended-real ML objective over the whole admissible box iff no
feasible Graver move `z + g` strictly improves the honest finite interior cost.
The proof instantiates the merged `graver_optimal_iff_no_improving` with
`binomCost` / `multinomialCost` on the admissible box and then applies the T2
agreement; **no affine-tail surrogate is used**.

## Relation to neighbouring fronts

* **#305 / #357** (`SeparableConvexGraver`, `ExactMLOptimizerTransfer`): reused
  verbatim.  This module does not restate `graver_optimal_iff_no_improving`,
  `binomTerm_discConvOn`, `negLog_discConvOn`, `negLog_sub_discConvOn`, the
  `DiscConvOn` closure lemmas, or the exact extended-real cost definitions; it
  consumes them.  It closes the interior-minimizer hypothesis of PR #357 by
  working on the exact objective directly.
* **#259 / #261 / #258** (`Section62BinomialCriterion`, `FixedXExactML`,
  `GeneralBidirectedFlowML`): the exact finite likelihood and zero-likelihood
  candidate treatment are already kernel-checked there; this module does not
  reprove "positive observations require positive multiplicity".
* **#257 / #264** (`GraverRigidity`): the integer-kernel conformal Graver
  decomposition is consumed as the abstract `HasGraverDecomposition` hypothesis;
  this module does not duplicate its existence proof.
* **#331** (`ProductBinomialMonotonicityCounterexample`): the raw §6.1 kernel is
  not coordinatewise monotone and fails the sign-compatible Positive Sum
  Property; the correct certificate applies to the negative-log cost, which is
  what is done here.

## Boundary honesty

`Real.log 0 = 0` by the totalized definition, so the naive everywhere-real
negative log would report a false finite value at impossible candidates.  This
module never evaluates the log at an impossible argument: the admissible box
excludes `d ≤ 0` with `x > 0` and `d ≥ N` with `n - x > 0`, and the exact
objective is `⊤` outside it.

## Open / deferred

* The direct discharge of `HasGraverDecomposition` from
  `AssemblyP1.GraverRigidity.graver_decomposition` in the augmented
  `[A 0; -T I]` flow/throughput setting (#259/#261 bridge) remains **OPEN**; the
  certificate here is conditional on it, exactly as `SeparableConvexGraver` is.
* The #261 historical signed-graph candidate adapter is separately **OPEN**.
* No claim is made about polynomial-time Graver augmentation or about which
  feasible flows spell genomes.
