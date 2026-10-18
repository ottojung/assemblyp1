import Mathlib

set_option autoImplicit false

/-!
# The MB09 §6.1 product-binomial objective is not coordinatewise monotone
(board issue #263)

This file kernel-checks the **small finite counterexample** that separates a
*coordinatewise-monotone separable* Graver optimality certificate from the
Medvedev–Brudno 2009 §6.1 fixed-external-`N` **product-of-binomials** objective.
It is a bounded, independent increment on the issue-#263 frontier; it does **not**
duplicate #257's integer-kernel conformal decomposition, #261's signed-graph
adapter, or `Section62BinomialCriterion`.

## The two domains being separated

A Graver optimality certificate for a separable objective
`F z = ∑_e f_e (z_e)` reduces global optimality to the absence of a single
improving Graver move by using a *monotonicity / superadditivity* property of the
one-coordinate cost `f_e`.  Two such properties are

* **coordinatewise monotonicity** (`CoordMono`): `a ≤ b → f a ≤ f b`, and
* the sign-compatible **Positive Sum Property** (`HasPSS`):
  `f (z + g + h) - f z ≥ (f (z + g) - f z) + (f (z + h) - f z)` for `g, h ≥ 0`.

For a genuinely monotone separable objective (e.g. `f d = d`) both hold, and
"coordinatewise dominance" of one candidate spectrum over another immediately
transfers to the objective.  The separable-convex certificate of
`AssemblyP1.SeparableConvexGraver` replaces `CoordMono` by discrete convexity
(`DiscConvOn`), for which `HasPSS` is `superadd_list`.

## The counterexample

The MB09 §6.1 marginal for one read type, with external genome size `N`, `n`
reads and `x` observed copies, is the binomial kernel
`P(d) = (d / N)^x (1 - d / N)^(n - x)`, whose numerator is
`binomKernel N n x d = d^x (N - d)^(n - x)`.  This is a product of the
*increasing* factor `d^x` and the *decreasing* factor `(N - d)^(n - x)`, hence
**nonmonotone** in `d`: the board's "8-vs-4" example.  With `N = 12`, `n = 3`,
`x = 1`,

```text
P(8) = 8 · 4² = 128   <   256 = 4 · 8² = P(4),       4 ≤ 8,
```

an exact ratio `P(4) / P(8) = 256 / 128 = 2`.  On the sign-compatible path
`4 → 6 → 8` the Positive Sum Property also fails:

```text
P(8) - P(4) = -128   <   -80 = 2 · (P(6) - P(4)).
```

Hence neither the coordinatewise-dominance argument nor the sign-compatible
superadditivity step of a monotone separable Graver certificate transfers to the
§6.1 product-binomial objective.  The correct certificate applies to the
*negative log* cost (discretely convex on the open interior `0 < d < N`, see
`AssemblyP1.SeparableConvexGraver.binomTerm_discConvOn`), **not** to the raw
likelihood kernel; and at the zero-probability boundary `d = 0` (for `x > 0`) or
`d = N` (for `n - x > 0`) the kernel vanishes and the true extended-real cost is
`+∞`.

## Scope

The counterexample is a statement about the §6.1 **product-binomial surrogate**
in the candidate copy count `d`; it makes no claim about the exact joint
multinomial law, about §6.2 bidirected flows, or about which feasible flows spell
genomes.  No `sorry`, `admit`, `axiom`, or `native_decide` is used.
-/

namespace AssemblyP1.ProductBinomialMonotonicityCounterexample

/-- The Medvedev–Brudno 2009 §6.1 fixed-external-`N` product-binomial **integer
numerator** for a single read type, as a function of the candidate copy count
`d`: `d ^ x * (N - d) ^ (n - x)`.

The full §6.1 marginal `(d / N) ^ x * (1 - d / N) ^ (n - x)` is this quantity
divided by the candidate-independent constant `N ^ n`, so comparisons between
candidates are unchanged by working with the numerator.  The intended domain is
`x ≤ n` and `0 ≤ d ≤ N`; outside it the integer factors are not the source
likelihood. -/
def binomKernel (N n x : ℕ) (d : ℕ) : ℤ :=
  (d : ℤ) ^ x * ((N : ℤ) - (d : ℤ)) ^ (n - x)

/-- The §6.1 product-binomial kernel on a two-type read universe, as a function
of the two candidate copy counts: `binomKernel N n x₀ d₀ * binomKernel N n x₁ d₁`.
This is the product of the per-type §6.1 marginals (up to the constant `N ^ n`),
so it is the multi-type object whose coordinatewise monotonicity the "coordinatewise
dominance" argument for flow objectives would need. -/
def binomKernelTwo (N n x₀ x₁ d₀ d₁ : ℕ) : ℤ :=
  binomKernel N n x₀ d₀ * binomKernel N n x₁ d₁

/-- Coordinatewise monotonicity of a single-coordinate objective: increasing the
candidate copy count never decreases the value.  This is the monotonicity
hypothesis underlying the naive coordinatewise-dominance Graver argument for
separable monotone flow objectives. -/
def CoordMono (f : ℕ → ℤ) : Prop := ∀ a b : ℕ, a ≤ b → f a ≤ f b

/-- The sign-compatible **Positive Sum Property** for a single-coordinate
objective `f`: for nonnegative increments `g`, `h`, the increment over the whole
step dominates the sum of the two one-step increments.  This is the
one-dimensional superadditivity step of the separable Graver optimality
certificate (compare `AssemblyP1.SeparableConvexGraver.superadd_list`, which
proves the same shape from discrete convexity). -/
def HasPSS (f : ℕ → ℤ) : Prop :=
  ∀ z g h : ℕ, f (z + g + h) - f z ≥ (f (z + g) - f z) + (f (z + h) - f z)

/-! ## The "8-vs-4" kernel -/

/-- The §6.1 product-binomial kernel at copy count `8` is strictly **below** its
value at copy count `4` (external `N = 12`, `n = 3` reads, `x = 1` observed),
even though `4 ≤ 8`: `8 · 4² = 128 < 256 = 4 · 8²`.  The increasing `d^x` factor
is defeated by the decreasing `(N - d)^(n - x)` factor.  Exact ratio
`P(4) / P(8) = 2`. -/
theorem binomKernel_eight_lt_four :
    binomKernel 12 3 1 8 < binomKernel 12 3 1 4 := by
  norm_num [binomKernel]

/-- The §6.1 product-binomial objective is **not** coordinatewise monotone: the
copy count `4` strictly beats the larger copy count `8`. -/
theorem binomKernel_not_coordMono :
    ¬ CoordMono (binomKernel 12 3 1) := by
  intro h
  have hle := h 4 8 (by norm_num)
  rw [show binomKernel 12 3 1 8 = 128 by norm_num [binomKernel],
      show binomKernel 12 3 1 4 = 256 by norm_num [binomKernel]] at hle
  omega

/-- The §6.1 product-binomial objective **fails** the sign-compatible Positive
Sum Property: at `z = 4` with `g = h = 2` (path `4 → 6 → 8` inside `[0, 12]`),
`P(8) - P(4) = -128 < -80 = 2 · (P(6) - P(4))`.  Hence the superadditivity step
of a monotone separable Graver certificate does not transfer to the raw
likelihood kernel. -/
theorem binomKernel_pss_fails :
    ¬ HasPSS (binomKernel 12 3 1) := by
  intro h
  have hinst := h 4 2 2
  rw [show binomKernel 12 3 1 8 = 128 by norm_num [binomKernel],
      show binomKernel 12 3 1 4 = 256 by norm_num [binomKernel],
      show binomKernel 12 3 1 6 = 216 by norm_num [binomKernel]] at hinst
  norm_num at hinst

/-- At the zero-copy boundary the §6.1 kernel vanishes (`x = 1 > 0`), so the true
extended-real negative log is `+∞`.  The interior `8`-vs-`4` drop already
exhibits the nonmonotonicity strictly inside the box `[0, N]`. -/
theorem binomKernel_zero : binomKernel 12 3 1 0 = 0 := by
  norm_num [binomKernel]

/-- At the full-copy boundary `d = N` the §6.1 kernel vanishes
(`n - x = 2 > 0`), again giving the true extended-real cost `+∞`. -/
theorem binomKernel_at_N : binomKernel 12 3 1 12 = 0 := by
  norm_num [binomKernel]

/-! ## Multi-type coordinatewise dominance also fails -/

/-- On the two-type §6.1 product-binomial, the dominated spectrum `(4, 4)` beats
the dominating spectrum `(8, 8)` (`256² = 65536 > 16384 = 128²`).  So
"coordinatewise dominance" of one candidate spectrum over another does not imply
a larger objective value. -/
theorem binomKernelTwo_dominance_fails :
    binomKernelTwo 12 3 1 1 8 8 < binomKernelTwo 12 3 1 1 4 4 := by
  norm_num [binomKernelTwo, binomKernel]

/-! ## The separated domains -/

/-- The coordinatewise-monotone separable domain is nonempty: the identity
objective `f d = d` is coordinatewise monotone. -/
theorem id_coordMono : CoordMono (fun d : ℕ => (d : ℤ)) := by
  intro a b hab
  exact Int.ofNat_le.mpr hab

/-- The identity objective satisfies the sign-compatible Positive Sum Property
(with equality). -/
theorem id_hasPSS : HasPSS (fun d : ℕ => (d : ℤ)) := by
  intro z g h
  push_cast
  omega

/-- **Separation theorem (board #263).** The MB09 §6.1 product-binomial objective
violates both hypotheses of the coordinatewise-monotone separable Graver
certificate on the explicit instance `N = 12`, `n = 3`, `x = 1`: it is not
coordinatewise monotone (the `8`-vs-`4` kernel) and it fails the sign-compatible
Positive Sum Property on the path `4 → 6 → 8`.  Exact ratio `P(4) / P(8) = 2`.

The domain hypotheses are therefore explicit: a certificate that assumes
`CoordMono` (coordinatewise dominance) or `HasPSS` (sign-compatible
superadditivity) of the objective does **not** apply to the §6.1
product-of-binomials objective.  The separable-convex certificate instead
requires discrete convexity of the negative-log cost on `0 < d < N`. -/
theorem product_binomial_separation :
    ¬ CoordMono (binomKernel 12 3 1) ∧ ¬ HasPSS (binomKernel 12 3 1) :=
  ⟨binomKernel_not_coordMono, binomKernel_pss_fails⟩

end AssemblyP1.ProductBinomialMonotonicityCounterexample
