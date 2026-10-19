# Exact-ML optimizer preservation for the affine-tail Graver certificate (issue #263)

This note documents the kernel-checked Lean artifact
[`AssemblyP1/ExactMLOptimizerTransfer.lean`](../AssemblyP1/ExactMLOptimizerTransfer.lean)
and its axiom audit
[`AssemblyP1/ExactMLOptimizerTransferAudit.lean`](../AssemblyP1/ExactMLOptimizerTransferAudit.lean),
with an independent numerical/exact-rational cross-check
[`scripts/verify_issue263_exact_ml_optimizer_transfer.py`](../scripts/verify_issue263_exact_ml_optimizer_transfer.py).

## The gap that this file closes

The merged separable-convex Graver certificate
`AssemblyP1.SeparableConvexGraver.graver_optimal_iff_no_improving` (PR #305/#331)
certifies a minimizer of the **finite secant-slope affine-tail extension**
`affineExtend f 1 (N-1)` of the source negative-log-likelihood cost on the full
candidate box `[0, N]`.  That extension is a *regularized surrogate*: at a
zero-probability endpoint (`d = 0` with `x > 0`, or `d = N` with `n - x > 0`)
the genuine extended-real negative log is `+∞`, while `affineExtend` assigns a
finite secant value.  As recorded in
[`docs/issue263-separable-convex-graver-certificate.md`](issue263-separable-convex-graver-certificate.md)
under "Source-fidelity caveat", the transfer of optimality from the extension to
the **true extended-real maximum-likelihood objective** was left explicitly
OPEN.

This file closes that gap **conditionally**, under the single explicit
optimizer-preservation hypothesis that the certified minimizer lies in the
positive interior of the box.

## The transfer, in one line

For every feasible candidate `w` and an interior certified minimizer `z` of the
extension,

```text
exact(w)  ≥  extension(w)  ≥  extension(z)  =  exact(z).
```

* `extension(w) ≥ extension(z)` is the merged Graver criterion applied to the
  **extension** over the full box (`graver_optimal_iff_no_improving` with
  `f = binomExt`), i.e. the "no improving feasible Graver move" certificate.
* `exact(w) ≥ extension(w)` is the honest pointwise domination: at a
  zero-likelihood endpoint `exact(w) = ⊤`; at a positive-likelihood endpoint the
  secant tail lies below the convex interior cost; on the interior the two
  coincide.
* `exact(z) = extension(z)` holds because `z` is interior.

## What is proved

* `exact_minimizer_of_ext_minimizer` — the generic transfer.  Let `P` be a
  feasible set inside the box `l ≤ · ≤ u`, `f` a finite separable objective, and
  `g` an extended-real separable objective with `↑(f e d) ≤ g e d` on the box
  and `g e (z e) = ↑(f e (z e))` at interior points.  If `z` is interior and
  minimizes `f` over `P`, then `z` minimizes `g` over `P`.
* `graver_exact_optimal_of_no_improving` — the same, with "minimizes `f`"
  supplied by the merged `graver_optimal_iff_no_improving`; the conclusion is
  stated for the exact extended-real objective `exactObj g`.
* `binomExt_discConvOn`, `multinomialExt_discConvOn` — discrete convexity of the
  affine-tail extensions on the full boxes `[0, N]` / `[0, G]`, reused verbatim
  from `binomTerm_ext_discConvOn` / `multinomialTerm_ext_discConvOn`.
* `binomExact_dom_ext`, `multinomialExact_dom_ext` — pointwise domination
  `↑extension ≤ exact` on the full box.
* `binomExact_eq_ext`, `multinomialExact_eq_ext` — interior agreement.
* `log_one_sub_two_le` — the single elementary logarithm inequality
  `log(1 - 2/N) ≤ 2 log(1 - 1/N)` (`N ≥ 3`), equivalent to
  `N (N - 2) ≤ (N - 1)²`, from which both endpoint dominations follow
  (`binomExt_zero_le`, `binomExt_N_le`).
* `binom_separable_exact_optimal` — the separable fixed-external-`N`
  product-binomial instantiation.
* `binom_exact_optimal_flow` — the concrete edge-flow instantiation, with the
  `HasGraverDecomposition` hypothesis discharged by the merged
  `AssemblyP1.GraverThroughputBridge.hasGraverDecomposition_flow` (#343).

## Exact extended-real objective

The exact objective is `WithTop ℝ`-valued:
`binomExact N x n d = ⊤` at a zero-probability endpoint and
`↑(binomCost N x n d)` otherwise, where
`binomCost N x n d = -x·log(d/N) - (n-x)·log(1 - d/N)` is the finite
negative log.  The fixed-total multinomial analogue is `multinomialExact`.
Minimizing the negative log is maximizing the likelihood; the
candidate-independent constant (the multinomial coefficient / the common
`N^{-n}` factor) is dropped, which does not move the minimizer.  This is the
**pure maximum-likelihood** objective, not a penalized solver cost: a penalty
`P` must be separately shown discretely convex before the certificate applies
(see the "Penalized solver cost vs pure ML" section of the certificate note).

## Boundary honesty

`Real.log 0 = 0` by the totalized definition, so a naive everywhere-real
negative log reports a false finite value at impossible boundary candidates.
The exact objective here is instead `⊤` there, and the finite surrogate
`affineExtend` is only used as a **lower bound** at the positive-likelihood
endpoints.  The domination is exactly the content of `log_one_sub_two_le`:
for `N ≥ 3`, `N (N - 2) ≤ (N - 1)²`, so the secant tail cannot exceed the
convex interior cost at `d = 0` or `d = N`.

## Remaining open gap

The hypothesis that the affine-tail minimizer is **interior** is *not*
established here.  The extension may be minimized only at a zero-probability
endpoint (the one-dimensional example `N = 3`, `n = 2`, `x = 1`, where the
extension is constant while the exact objective is `+∞` at `d = 0` and `d = 3`,
exhibits exactly this over-admission).  In that case no interior optimizer
exists and this transfer does not apply; conversely, an interior extension
minimizer is a genuine exact-ML optimizer by the results above.  Determining
when the extension has an interior minimizer — equivalently, excluding
over-admission of boundary minimizers — is a separate question, deliberately
left OPEN.  The direct historical candidate adapter (#261) and the genuine
vertex-throughput `T`-sign-compatible Graver decomposition also remain OPEN.

## Relation to neighbouring fronts

* Consumes, without reproving, the merged
  `AssemblyP1.SeparableConvexGraver` endpoints
  (`graver_optimal_iff_no_improving`, `binomTerm_ext_discConvOn`,
  `multinomialTerm_ext_discConvOn`, `affineExtend*`) and the merged
  `AssemblyP1.GraverThroughputBridge` endpoints
  (`flowLin`, `Graver`, `flowLin_add`, `graver_flowLin_eq_zero`,
  `hasGraverDecomposition_flow`).
* Does not duplicate #257's integer-kernel conformal-minimal existence, #261's
  historical signed-graph adapter, or #331's product-binomial monotonicity
  counterexample.
* The source-oriented exact finite multinomial / fixed-external-`N`
  product-binomial costs and the discrete-convexity lemmas are those of
  `AssemblyP1.SeparableConvexGraver`.
