# Separable-convex Graver optimality certificate (issue #263)

This note documents the kernel-checked Lean artifact
[`AssemblyP1/SeparableConvexGraver.lean`](../AssemblyP1/SeparableConvexGraver.lean)
and its axiom audit
[`AssemblyP1/SeparableConvexGraverAudit.lean`](../AssemblyP1/SeparableConvexGraverAudit.lean).

## What is proved

The file formalizes the **convex-objective half** of the Graver optimality
certificate for a separable convex integer program.  The endpoint is the
conditional necessary-and-sufficient theorem

```
graver_optimal_iff_no_improving :
  (∀ w, Feasible w → F z ≤ F w) ↔
  (∀ g, Graver g → Feasible (z + g) → F z ≤ F (z + g))
```

for a separable discrete-convex objective `F z = ∑ e, f e (z e)` on an
integer affine fiber `lin z = b` with coordinatewise box `l ≤ z ≤ u`, under
two explicit hypotheses:

* `hker : Graver g → lin g = 0` — Graver moves lie in the kernel;
* `HasGraverDecomposition` — every feasible displacement `y - z` is a `List`
  of coordinatewise sign-compatible Graver moves summing to `y - z`.

The inequality direction is the **minimization** form `F z ≤ F (z + g)`; this
is the direction that a discrete optimality certificate requires.  It is *not*
the continuous KKT stationarity condition: a discrete minimizer need not be a
stationary point of the real relaxation.

Supporting results:

* `inc_mono` — monotonicity of finite differences under discrete convexity.
* `quad_pos`, `quad_neg` — the two-step discrete-convex quadrangle inequality.
* `superadd_list` — the one-dimensional Positive Sum Property.
* `superadd_separable_list` — the separable Positive Sum Property.
* `multiplier_improving` — if the integer Graver ray `α • g` (`α ≥ 1`) strictly
  improves over `z` while the path stays in the box, then the unit step `g`
  already strictly improves.
* `negLog_discConvOn`, `negLog_sub_discConvOn`, `multinomialTerm_discConvOn`,
  `binomTerm_discConvOn` — the source likelihood costs are discretely convex in
  the **candidate copy count** `d` on the positive interior.
* `affineExtend`, `affineExtend_discConvOn`, `inc_affineExtend` — the
  **secant-slope affine-tail extension** of an interval-convex cost to the whole
  integer line, discretely convex on any enclosing interval.
* `multinomialTerm_ext_discConvOn`, `binomTerm_ext_discConvOn`,
  `binomTerm_degenerate_discConvOn` — the source likelihood costs extended to
  the **full** candidate box, including the boundary candidates `d = 0` and
  `d = N`.

## Mathematical source

* Hunkenschröder, Koutecký, Levin, Vu, *(Near)-Optimal algorithms for sparse
  separable convex integer programs*, Mathematical Programming (2026):
  **Proposition 1** is the separable-convex superadditivity for same-orthant
  increments, and **Proposition 3** is the conformal positive-sum decomposition
  of integer kernel moves into Graver elements,
  <https://link.springer.com/article/10.1007/s10107-026-02341-5>.
* Hemmecke, Onn, Weismantel, *A polynomial oracle-time algorithm for convex
  integer minimization*, <https://arxiv.org/abs/0710.3003> (Mathematical
  Programming 126, 2011).
* The standard Graver optimality certificate (Onn; De Loera–Oebelein–Onn).

## Relation to the neighbouring fronts

* **#257 / #264** (`AssemblyP1/GraverRigidity.lean`): that front proves the
  integer-kernel conformal decomposition
  `graver_decomposition`, which returns exactly a `List` of Graver moves each
  conformal to the total displacement.  This file does **not** duplicate that
  existence proof; it consumes the decomposition as the explicit
  `HasGraverDecomposition` hypothesis.  A `List` (rather than a `Finset`) is
  essential because a conformal decomposition may repeat a Graver move, and a
  `Finset` silently loses multiplicities.
* **#259 / #261**: those fronts concern likelihood maximizers and exact finite
  binomial comparisons.  Here the objective is a **cost to be minimized**
  (`F = -log-likelihood` on the interior), and the certificate is stated for
  the generic separable convex objective; the finite likelihood costs are
  provided as convexity instantiations, not as an optimality claim about a
  specific historical candidate set.

## Boundary honesty

`Real.log 0 = 0` by the totalized definition, so the naive everywhere-real
negative-log-likelihood would report a false finite value at impossible
boundary candidates (copy count `0` with a positive observed count, or copy
count `N` with a positive missing count).  The instantiation lemmas therefore
restrict to the positive interior (`d ∈ [1, hi]` for the fixed-total
multinomial term, `d ∈ [1, N-1]` for the product-binomial term), where the
source formulas are honest.  The abstract certificate `graver_optimal_iff_no_improving`
carries the box `l ≤ z ≤ u` explicitly, so any boundary policy is a modelling
choice made by the caller, not an implicit assumption of the theorem.

To apply the certificate on the **whole** box — including the boundary
candidates `d = 0` and `d = N` — the cost must be a *globally* discretely convex
function on that box.  The naive totalized extension `d ↦ -x · log(max d 1 / G)`
is **not** discretely convex at the boundary: its slope on `[0,1]` is `0`
(because `max 0 1 = max 1 1`) while its slope on `[1,2]` is negative, so the
discrete second difference at `d = 1` is **negative** (the extension is concave
there).  The
correct minimal extension is the **secant-slope affine tail**
`affineExtend f L U`: exact on `[L, U]` and affine outside `[L, U]` with the
boundary secant slopes `f(L+1) - f(L)` (below `L`) and `f(U) - f(U-1)` (above
`U`).  Because those slopes coincide with the first interior differences
`inc f L` and `inc f (U-1)`, and `inc f` is nondecreasing, `affineExtend f L U`
is discretely convex on any interval enclosing `[L, U]` (`affineExtend_discConvOn`,
via the first-difference identity `inc_affineExtend`).  Instantiating this:

* `multinomialTerm_ext_discConvOn` proves discrete convexity on the full box
  `[0, G]` for `G ≥ 2`, with the boundary candidate `d = 0` taking the finite
  secant value `x · log (2G)`;
* `binomTerm_ext_discConvOn` proves discrete convexity on the full box `[0, N]`
  for `N ≥ 3`, with `d = 0` and `d = N` taking the secant values;
* `binomTerm_degenerate_discConvOn` records the degenerate totals `N ≤ 2`, where
  the strict interior `0 < d < N` has at most the single point `d = 1`, so there
  is no interior second difference and the constant extension is already
  discretely convex.

These are the minimal honest finite convex extensions; they are a modelling
choice about the boundary, not an implicit assumption of the abstract theorem.

## Penalized solver cost vs pure ML

The instantiated costs are the **pure maximum-likelihood** (negative-log)
terms. A penalized solver cost `F_ML + P` — the likelihood plus a sparsity,
balance, or other regularization penalty — is a *different objective*: the
certificate `graver_optimal_iff_no_improving` applies to it only when the
full penalized objective is itself discretely convex on the box. That must be
verified for the specific penalty `P`; for a separable convex penalty the
closure lemmas `DiscConvOn.add` / `DiscConvOn.const_mul` compose it with the
pure-ML convexity proved here, but a non-separable or non-convex penalty is
not covered. The pure-ML convexity lemmas certify the likelihood terms only
and make no claim about penalized solver costs in general.

## Open / deferred

* The direct discharge of `HasGraverDecomposition` from
  `AssemblyP1.GraverRigidity.graver_decomposition` in the augmented
  `[A 0; -T I]` flow/throughput setting (the #259/#261 vertex-throughput
  bridge) is deliberately **left open**; this issue closes as the conditional
  core convex theorem.
* No claim is made about polynomial-time Graver augmentation or about which
  feasible flows spell genomes.
