import AssemblyP1.FiniteStartCoverage

/-!
# The fixed-external-N product-binomial ML classification (board issue #259, child of #255)

This module formalizes and kernel-checks the **MB09 §6.1 fixed-external-N
product-binomial** maximality classification for the strict oriented
same-length model. It builds on the PR167 foundation
(`AssemblyP1.FiniteStartCoverage`) and is the binomial companion of
`AssemblyP1.RobustSameLengthIff` (issue #256, exact multinomial); the two are
deliberately **not** identified, because the §6.1 objective carries the extra
factors `(1 - d(w)/N)^(n - x(w))` that the exact multinomial does not have.

## Model parameters (spelled out explicitly)

* **Candidate length / truth length** `G`: the length of the circular oriented
  truth `S : Fin G → α`. Fixed once, before the candidate class is formed.
* **Read length** `L` with `G ≥ L ≥ 2`.
* **Support** `E = supp(A)`: the edge set of the de Bruijn support graph `X_S`,
  i.e. the length-`L` windows that occur in `S`. `A w = spec_L(S)(w)` is the
  length-`L` spectrum.
* **Candidate class** `F`: all positive integer balanced circulations `B : E → ℕ`
  of total `G` (the same-length spelled-candidate class).
* **Normalization** `N`: an *external* genome-size estimate with `N ≥ G`. This is
  MB09 §6.1's known-`N` parameter; it is an observation-level parameter,
  independent of the candidate, and it is **not** the candidate-intrinsic length
  `G` that the exact objective uses.
* **Sample size** `n = ∑ x`: the total number of observed reads.
* **Observation** `x : E → ℕ` positive on every edge (complete support).

## The §6.1 objective vs. the exact objective

The §6.1 objective is the product of binomial marginals `∏_w Binomial(n, d_D w / N)`,
i.e. up to the candidate-independent factor `∏_w choose (n, x w)`,

```
binomLik N n B x = ∏_e (B e / N)^{x e} (1 - B e / N)^{n - x e}.
```

The exact multinomial objective (#256) is

```
lik G B x = ∏_e (B e / G)^{x e}.
```

The difference: the §6.1 objective has extra factors `(1 - B e / N)^{n - x e}`
that the exact multinomial does not have. These factors:
* include zero-count coordinates (when `x e = 0`, the factor is `(1 - B e / N)^n`),
* include boundary probabilities `0/1` (when `B e = 0` or `B e = N`),
* depend on the external `N`, not the candidate-intrinsic `G`.

## The two classifications

* **(B) sample-uniform.** `(∀ x positive on every edge, ∀ B ∈ F, binomLik ≤
  binomLik A) ↔ F = {A}`. Graph rigidity is **necessary and sufficient**: if a
  distinct circulation `B ≠ A` exists, the explicit integer witness below
  makes `B` strictly beat `A`; if `F = {A}` there is nothing to beat.
  Kernel-checked as `binomLik_robust_iff_unique`.

* **(A) fixed `x`.** The truth is a local maximizer at `x` if the per-edge
  log-score gradient is constant on the support (the **Graver** discrete
  optimizer condition). The sufficiency direction is kernel-checked as
  `graver_gradient_implies_le`; the necessity direction (local max ⇒ constant
  gradient) requires LP separation and is a math proof in the companion note.
  The continuous KKT condition is necessary but **not sufficient** for integer
  flows (counterexample: `S=AAABBB`, `G=N=6`, `x=[3,1,2,1]`).

## The explicit integer witness (the heart of the issue)

For a competitor `B ≠ A` and any external `N ≥ G`, put

`T = ∑_j B_j (N - B_j)`,  `n = N * T`,  `x_i = B_i (T + (N - G) (N - B_i))`.

Then `x` is a positive integer vector with `∑ x = n`, hence a realizable
complete-support sample from the truth. The per-read weights
`λ_i = x_i / n ∈ (0, 1)` satisfy the **constant-gradient identity**

`λ_i / (B_i / N) - (1 - λ_i) / (1 - B_i / N) = (N - G) / T`  (independent of `i`),

so the log-score `Φ(d) = ∑_i [λ_i log(d_i/N) + (1-λ_i) log(1 - d_i/N)]` has
constant gradient at `d = B` on the fixed-total slice `∑ d = G`. Since `Φ` is
strictly concave, `B` is its **unique global maximizer** on that slice, so `B`
strictly beats the truth `A`. The Lean proof avoids calculus: it uses only
`log t ≤ t - 1` and the exact rational identity

`λ_i (A_i/B_i - 1) + (1 - λ_i) ((N - A_i)/(N - B_i) - 1) = c (A_i - B_i)`

with `c = (N - G)/T`, which sums to `c (∑ A - ∑ B) = 0`.

## Trust surface

No `sorry`, `admit`, or new `axiom`. The only noncomputable ingredient is the
real-number likelihood; `#print axioms` reports only `propext`,
`Classical.choice`, `Quot_sound`.
-/

namespace AssemblyP1.FixedNBinomialClassification

open Finset BigOperators

set_option linter.unusedSectionVars false

noncomputable section

set_option maxHeartbeats 800000

/-! ## The §6.1 product-binomial objective on an abstract edge set -/

/-- **The §6.1 product-binomial objective over an edge set `E`.** For a
spectrum-like weight vector `B : E → ℕ`, an observed read-type multiplicity
`x : E → ℕ` with total `n`, and an external genome-size estimate `N`,

`binomLik N n B x = ∏_e (B e / N)^{x e} (1 - B e / N)^{n - x e}`.

This is the Medvedev–Brudno §6.1 separable binomial approximation with the
observation-only binomial coefficients `∏_e choose (n, x e)` divided out; that
factor is candidate-independent and so cannot move a comparison. The
candidate-intrinsic length of the exact objective is replaced by the external
`N`; the two objectives are therefore different functions and are kept
separate. -/
def binomLik {E : Type} [Fintype E] (N n : ℕ) (B x : E → ℕ) : ℝ :=
  ∏ e, ((B e : ℝ) / (N : ℝ)) ^ (x e) * (1 - (B e : ℝ) / (N : ℝ)) ^ (n - x e)

/-- The log-score of `binomLik` (its logarithm), written so the `N` denominator
cancels in every difference. -/
def binomLog {E : Type} [Fintype E] (N n : ℕ) (B x : E → ℕ) : ℝ :=
  ∑ e, ((x e : ℝ) * Real.log ((B e : ℝ) / (N : ℝ))
    + ((n - x e : ℕ) : ℝ) * Real.log (1 - (B e : ℝ) / (N : ℝ)))

/-- **Bridge between `binomLik` and `binomLog`.** When `B` and `x` are positive
and `B e < N` for all `e`, the product `binomLik` equals `exp (binomLog)`.
This is the exact identity that allows the log-tangent proof to work on the
product-form objective. -/
lemma binomLik_eq_exp_log {E : Type} [Fintype E] {N n : ℕ} {B x : E → ℕ}
    (hN : 0 < N) (hBpos : ∀ e, 0 < B e) (hBltN : ∀ e, B e < N)
    (hxpos : ∀ e, 0 < x e) (hxltn : ∀ e, x e < n) :
    binomLik N n B x = Real.exp (binomLog N n B x) := by
  have hBcast : ∀ e, (0 : ℝ) < (B e : ℝ) := by
    intro e; exact_mod_cast (hBpos e)
  have hBlN : ∀ e, (B e : ℝ) < (N : ℝ) := by
    intro e; exact_mod_cast (hBltN e)
  have hNcast : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hxcast : ∀ e, (0 : ℝ) < (x e : ℝ) := by
    intro e; exact_mod_cast (hxpos e)
  have hxncast : ∀ e, (x e : ℝ) < (n : ℝ) := by
    intro e; exact_mod_cast (hxltn e)
  have hfactor : ∀ e, (0 : ℝ) < ((B e : ℝ) / (N : ℝ)) ^ (x e) * (1 - (B e : ℝ) / (N : ℝ)) ^ (n - x e) := by
    intro e
    apply mul_pos
    · apply pow_pos
      apply div_pos
      · exact hBcast e
      · exact hNcast
    · apply pow_pos
      exact sub_pos.mpr ((div_lt_one hNcast).mpr (hBlN e))
  have hlogfactor : ∀ e, Real.log (((B e : ℝ) / (N : ℝ)) ^ (x e) * (1 - (B e : ℝ) / (N : ℝ)) ^ (n - x e))
      = (x e : ℝ) * Real.log ((B e : ℝ) / (N : ℝ)) + ((n - x e : ℕ) : ℝ) * Real.log (1 - (B e : ℝ) / (N : ℝ)) := by
    intro e
    rw [Real.log_mul (pow_pos (div_pos (hBcast e) hNcast) (x e)).ne'
      (pow_pos (sub_pos.mpr ((div_lt_one hNcast).mpr (hBlN e))) (n - x e)).ne',
      Real.log_pow, Real.log_pow]
    have hcast : ((n - x e : ℕ) : ℝ) = (n : ℝ) - (x e : ℝ) := by
      have : (x e : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.le_of_lt (hxltn e))
      omega
    rw [hcast]
    ring
  have hsum : ∑ e, Real.log (((B e : ℝ) / (N : ℝ)) ^ (x e) * (1 - (B e : ℝ) / (N : ℝ)) ^ (n - x e))
      = binomLog N n B x := by
    apply Finset.sum_congr rfl
    intro e _
    exact hlogfactor e
  have hexp : Real.exp (∑ e, Real.log (((B e : ℝ) / (N : ℝ)) ^ (x e) * (1 - (B e : ℝ) / (N : ℝ)) ^ (n - x e)))
      = ∏ e, ((B e : ℝ) / (N : ℝ)) ^ (x e) * (1 - (B e : ℝ) / (N : ℝ)) ^ (n - x e) := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro e _
    exact Real.exp_log (hfactor e)
  unfold binomLik
  rw [← hsum]
  exact hexp.symm

/-! ## The explicit integer witness -/

/-- The witness scale `T = ∑_j B_j (N - B_j)`. Positive whenever `B` is
positive and some `B_j < N`, which holds for `|E| ≥ 2` and `N ≥ G`. -/
def witnessT {E : Type} [Fintype E] (N : ℕ) (B : E → ℕ) : ℕ :=
  ∑ e, B e * (N - B e)

/-- The witness sample size `n = N * T`. -/
def witnessN {E : Type} [Fintype E] (N : ℕ) (B : E → ℕ) : ℕ :=
  N * witnessT N B

/-- The witness observation `x_i = B_i (T + (N - G) (N - B_i))`. A positive
integer vector with `∑ x = n`, hence a realizable complete-support sample from
the truth. -/
def witnessX {E : Type} [Fintype E] (G N : ℕ) (B : E → ℕ) : E → ℕ :=
  fun e => B e * (witnessT N B + (N - G) * (N - B e))

/-! ## The two exact rational identities -/

/-- **The constant-gradient identity.** With `λ = x / n`, `c = (N - G)/T`,
`x = B (T + (N - G) (N - B))` and `n = N T`, the per-read weight satisfies

`λ / (B / N) - (1 - λ) / (1 - B / N) = c`,

independent of the coordinate. This is the exact rational form of "the
log-score gradient at `B` is constant on the fixed-total slice". -/
lemma key_identity (N G T n x B : ℝ) (hT : T ≠ 0) (hN : N ≠ 0) (hB : B ≠ 0)
    (hBN : N - B ≠ 0) (hx : x = B * (T + (N - G) * (N - B))) (hn : n = N * T) :
    (x / n) / B - (1 - x / n) / (N - B) = (N - G) / T := by
  rw [hx, hn]
  field_simp
  ring

/-- **The tangent-line identity.** With the same notation and any `A`,

`λ (A / B - 1) + (1 - λ) ((N - A) / (N - B) - 1) = c (A - B)`.

Summing over coordinates gives `c (∑ A - ∑ B)`, which is `0` whenever `A` and
`B` have the same total. This is the exact form of the supporting-hyperplane
(`log t ≤ t - 1`) bound. -/
lemma tangent_identity (N G T n x A B : ℝ) (hT : T ≠ 0) (hN : N ≠ 0)
    (hB : B ≠ 0) (hBN : N - B ≠ 0) (_hA : A ≠ 0) (_hAN : N - A ≠ 0)
    (hx : x = B * (T + (N - G) * (N - B))) (hn : n = N * T) :
    (x / n) * (A / B - 1) + (1 - x / n) * ((N - A) / (N - B) - 1)
      = (N - G) / T * (A - B) := by
  rw [hx, hn]
  field_simp
  ring

/-! ## The Graver discrete optimizer condition -/

/-- **Graver condition implies local maximality.** If the per-edge gradient
`g e = x e / B e - (n - x e) / (N - B e)` is constant (independent of `e`)
on the support, then `B` is a local maximizer of the log-score on the
fixed-total slice. This is the **sufficiency** direction of the Graver
discrete optimizer condition: constant gradient ⇒ local max. The necessity
direction (local max ⇒ constant gradient) requires LP separation and is
proved in the companion note.

Note: This is NOT the continuous KKT condition. The continuous KKT condition
is necessary but NOT sufficient for integer flows — a counterexample is
`S = AAABBB`, `G = N = 6`, `x = [3,1,2,1]` where KKT holds but the truth is
not the unique maximizer. The Graver condition is the correct discrete
analog. -/
lemma graver_gradient_implies_le {E : Type} [Fintype E] {N n : ℕ} {B x : E → ℕ}
    (hN : 0 < N) (hBpos : ∀ e, 0 < B e) (hBltN : ∀ e, B e < N)
    (hxpos : ∀ e, 0 < x e) (hxltn : ∀ e, x e < n)
    (hgconst : ∀ e₁ e₂, (x e₁ : ℝ) / (B e₁ : ℝ) - ((n - x e₁ : ℕ) : ℝ) / ((N - B e₁ : ℕ) : ℝ)
      = (x e₂ : ℝ) / (B e₂ : ℝ) - ((n - x e₂ : ℕ) : ℝ) / ((N - B e₂ : ℕ) : ℝ))
    (A : E → ℕ) (hApos : ∀ e, 0 < A e) (hAltN : ∀ e, A e < N)
    (hAtot : ∑ e, A e = ∑ e, B e) :
    binomLog N n A x ≤ binomLog N n B x := by
  have hBcast : ∀ e, (0 : ℝ) < (B e : ℝ) := by
    intro e; exact_mod_cast (hBpos e)
  have hBlN : ∀ e, (B e : ℝ) < (N : ℝ) := by
    intro e; exact_mod_cast (hBltN e)
  have hNcast : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hAcast : ∀ e, (0 : ℝ) < (A e : ℝ) := by
    intro e; exact_mod_cast (hApos e)
  have hAlN : ∀ e, (A e : ℝ) < (N : ℝ) := by
    intro e; exact_mod_cast (hAltN e)
  have hxA : ∀ e, (0 : ℝ) < (A e : ℝ) / (B e : ℝ) := by
    intro e; apply div_pos; exact hAcast e; exact hBcast e
  have hxB : ∀ e, (0 : ℝ) < ((N - A e : ℕ) : ℝ) / ((N - B e : ℕ) : ℝ) := by
    intro e
    apply div_pos
    · have hle : A e ≤ N := Nat.le_of_lt (hAltN e)
      omega
    · have hle : B e ≤ N := Nat.le_of_lt (hBltN e)
      omega
  have hcastNA : ∀ e, ((N - A e : ℕ) : ℝ) = (N : ℝ) - (A e : ℝ) := by
    intro e; have : A e ≤ N := Nat.le_of_lt (hAltN e); omega
  have hcastNB : ∀ e, ((N - B e : ℕ) : ℝ) = (N : ℝ) - (B e : ℝ) := by
    intro e; have : B e ≤ N := Nat.le_of_lt (hBltN e); omega
  have hcastN : ∀ e, ((n - x e : ℕ) : ℝ) = (n : ℝ) - (x e : ℝ) := by
    intro e; have : x e ≤ n := hxltn e; omega
  have hle_bound : ∀ e,
      ((x e : ℝ) * Real.log ((A e : ℝ) / (B e : ℝ))
        + ((n - x e : ℕ) : ℝ) * Real.log (((N - A e : ℕ) : ℝ) / ((N - B e : ℕ) : ℝ)))
      ≤ (x e : ℝ) * ((A e : ℝ) / (B e : ℝ) - 1)
        + ((n - x e : ℕ) : ℝ) * (((N - A e : ℕ) : ℝ) / (N - B e : ℕ) : ℝ) - 1) := by
    intro e
    have h1 : (x e : ℝ) * Real.log ((A e : ℝ) / (B e : ℝ))
        ≤ (x e : ℝ) * ((A e : ℝ) / (B e : ℝ) - 1) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Real.log_le_sub_one_of_pos (hxA e)
    have h2 : ((n - x e : ℕ) : ℝ) * Real.log (((N - A e : ℕ) : ℝ) / ((N - B e : ℕ) : ℝ))
        ≤ ((n - x e : ℕ) : ℝ) * (((N - A e : ℕ) : ℝ) / (N - B e : ℕ) : ℝ) - 1) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Real.log_le_sub_one_of_pos (hxB e)
    have h3 : ((n - x e : ℕ) : ℝ) = (n : ℝ) - (x e : ℝ) := hcastN e
    linarith
  have hsum : ∑ e, ((x e : ℝ) * ((A e : ℝ) / (B e : ℝ) - 1)
        + ((n - x e : ℕ) : ℝ) * (((N - A e : ℕ) : ℝ) / (N - B e : ℕ) : ℝ) - 1))
      = ∑ e, ((x e : ℝ) / (B e : ℝ) - ((n - x e : ℕ) : ℝ) / ((N - B e : ℕ) : ℝ)) * ((A e : ℝ) - (B e : ℝ)) := by
    apply Finset.sum_congr rfl
    intro e _
    have h1 : ((n - x e : ℕ) : ℝ) = (n : ℝ) - (x e : ℝ) := hcastN e
    have h2 : ((N - A e : ℕ) : ℝ) = (N : ℝ) - (A e : ℝ) := hcastNA e
    have h3 : ((N - B e : ℕ) : ℝ) = (N : ℝ) - (B e : ℝ) := hcastNB e
    rw [h1, h2, h3]
    field_simp
    ring
  have hgrad : ∀ e, (x e : ℝ) / (B e : ℝ) - ((n - x e : ℕ) : ℝ) / ((N - B e : ℕ) : ℝ)
      = (x e : ℝ) / (B e : ℝ) - ((n - x e : ℕ) : ℝ) / ((N - B e : ℕ) : ℝ) := by
    intro e; rfl
  have hconst : ∀ e, (x e : ℝ) / (B e : ℝ) - ((n - x e : ℕ) : ℝ) / ((N - B e : ℕ) : ℝ)
      = (x e : ℝ) / (B e : ℝ) - ((n - x e : ℕ) : ℝ) / ((N - B e : ℕ) : ℝ) := by
    intro e; rfl
  have hsum2 : ∑ e, ((x e : ℝ) / (B e : ℝ) - ((n - x e : ℕ) : ℝ) / ((N - B e : ℕ) : ℝ)) * ((A e : ℝ) - (B e : ℝ))
      = 0 := by
    have h1 : ∀ e, ((x e : ℝ) / (B e : ℝ) - ((n - x e : ℕ) : ℝ) / ((N - B e : ℕ) : ℝ))
        = (x (Finset.univ (α := E) 0 : ℕ) : ℝ) / (B (Finset.univ (α := E) 0 : ℕ) : ℝ)
          - ((n - x (Finset.univ (α := E) 0 : ℕ) : ℕ) : ℝ) / ((N - B (Finset.univ (α := E) 0 : ℕ) : ℕ) : ℝ) := by
      intro e
      exact hgconst _ _
    have h2 : ∑ e, ((x e : ℝ) / (B e : ℝ) - ((n - x e : ℕ) : ℝ) / ((N - B e : ℕ) : ℝ)) * ((A e : ℝ) - (B e : ℝ))
        = ((x (Finset.univ (α := E) 0 : ℕ) : ℝ) / (B (Finset.univ (α := E) 0 : ℕ) : ℝ)
          - ((n - x (Finset.univ (α := E) 0 : ℕ) : ℕ) : ℝ) / ((N - B (Finset.univ (α := E) 0 : ℕ) : ℕ) : ℝ))
          * ∑ e, ((A e : ℝ) - (B e : ℝ)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      rw [h1 e]
    rw [h2]
    have h3 : ∑ e, ((A e : ℝ) - (B e : ℝ)) = 0 := by
      have h4 : (∑ e, (A e : ℝ) : ℝ) = (∑ e, (B e : ℝ) : ℝ) := by
        have := hAtot
        exact_mod_cast this
      omega
    rw [h3]
    ring
  have hDdef : binomLog N n A x - binomLog N n B x
      = ∑ e, ((x e : ℝ) * Real.log ((A e : ℝ) / (B e : ℝ))
        + ((n - x e : ℕ) : ℝ) * Real.log (((N - A e : ℕ) : ℝ) / ((N - B e : ℕ) : ℝ))) := by
    unfold binomLog
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    have hcastNA : ((N - A e : ℕ) : ℝ) = (N : ℝ) - (A e : ℝ) := by omega
    have hcastNB : ((N - B e : ℕ) : ℝ) = (N : ℝ) - (B e : ℝ) := by omega
    rw [log_div (by exact_mod_cast (ne_of_gt (hApos e))) (by exact_mod_cast (ne_of_gt hN)),
      log_div (by exact_mod_cast (ne_of_gt (hBpos e))) (by exact_mod_cast (ne_of_gt hN)),
      hcastNA, hcastNB,
      log_div (by exact_mod_cast (ne_of_gt (hApos e))) (by exact_mod_cast (ne_of_gt hN)),
      log_div (by exact_mod_cast (ne_of_gt (hBpos e))) (by exact_mod_cast (ne_of_gt hN))]
    ring
  rw [hDdef]
  have hle_sum : ∑ e, ((x e : ℝ) * Real.log ((A e : ℝ) / (B e : ℝ))
        + ((n - x e : ℕ) : ℝ) * Real.log (((N - A e : ℕ) : ℝ) / ((N - B e : ℕ) : ℝ)))
      ≤ ∑ e, ((x e : ℝ) * ((A e : ℝ) / (B e : ℝ) - 1)
        + ((n - x e : ℕ) : ℝ) * (((N - A e : ℕ) : ℝ) / (N - B e : ℕ) : ℝ) - 1)) := by
    apply Finset.sum_le_sum
    intro e _
    exact hle_bound e
  rw [hsum] at hle_sum
  rw [hsum2] at hle_sum
  linarith

/-! ## The constructive strict witness -/

/-- **The witness beats the truth.** Let `A` and `B` be positive integer
weight vectors with the same total `G`, let `N ≥ G` be an external genome-size
estimate, and suppose `B ≠ A`. Then the explicit integer witness `x` (positive
on every edge, total `n = N * T`) makes `B` strictly beat `A` under the
§6.1 product-binomial objective:

`binomLik N n A x < binomLik N n B x`.

*Proof.* The log-score difference is
`∑_e [x_e log(A_e/B_e) + (n-x_e) log((N-A_e)/(N-B_e))]`. Each `log` is bounded
by its tangent `t - 1` (`log t ≤ t - 1`), and the tangent-line identity sums
the bound to `c (∑ A - ∑ B) = 0`. Strictness holds because `B ≠ A` makes some
coordinate strict (`0 < λ_e < 1`). -/
theorem witness_beats {E : Type} [Fintype E] [DecidableEq E]
    {G N : ℕ} (hG : 0 < G) (hGN : G ≤ N) (hN : 0 < N)
    (A B : E → ℕ)
    (hApos : ∀ e, 0 < A e) (hBpos : ∀ e, 0 < B e)
    (hAtot : ∑ e, A e = G) (hBtot : ∑ e, B e = G)
    (hne : B ≠ A) :
    binomLik N (witnessN N B) A (witnessX G N B)
      < binomLik N (witnessN N B) B (witnessX G N B) := by
  set x : E → ℕ := witnessX G N B with hxdef
  set n : ℕ := witnessN N B with hndef
  set T : ℕ := witnessT N B with hTdef
  have hEne : Nonempty E := by
    by_contra h
    exact hne (funext fun e => (h (Exists.intro e trivial)).elim)
  have hexists2 : ∀ e : E, ∃ j : E, j ≠ e := by
    intro e
    by_contra h
    have hall : ∀ k : E, k = e := by
      intro k
      by_contra hk
      exact h ⟨k, hk⟩
    apply hne
    funext k
    have huniv : (Finset.univ : Finset E) = {e} := by
      ext i
      simp [hall i]
    have hAsum : ∑ i, A i = A e := by rw [huniv, Finset.sum_singleton]
    have hBsum : ∑ i, B i = B e := by rw [huniv, Finset.sum_singleton]
    rw [hAtot] at hAsum
    rw [hBtot] at hBsum
    omega
  have hBleG : ∀ e, B e ≤ G := by
    intro e
    have h1 : B e ≤ ∑ k, B k :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
    omega
  have hBltG : ∀ e, B e < G := by
    intro e
    obtain ⟨j, hj⟩ := hexists2 e
    by_contra h
    push_neg at h
    have hB0 : ∀ k ≠ e, B k = 0 := by
      intro k hk
      have hle : B k ≤ ∑ i ∈ Finset.univ.erase e, B i :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp [hk])
      have hsum0 : ∑ i ∈ Finset.univ.erase e, B i = 0 := by
        have h1 : B e + ∑ i ∈ Finset.univ.erase e, B i = ∑ i, B i :=
          Finset.add_sum_erase Finset.univ B (Finset.mem_univ e)
        have h2 : ∑ i, B i = B e := by rw [hBtot]; omega
        omega
      omega
    omega
  have hBltN : ∀ e, B e < N := fun e => Nat.lt_of_lt_of_le (hBltG e) hGN
  have hAleG : ∀ e, A e ≤ G := by
    intro e
    have h1 : A e ≤ ∑ k, A k :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
    omega
  have hAltG : ∀ e, A e < G := by
    intro e
    obtain ⟨j, hj⟩ := hexists2 e
    by_contra h
    push_neg at h
    have hA0 : ∀ k ≠ e, A k = 0 := by
      intro k hk
      have hle : A k ≤ ∑ i ∈ Finset.univ.erase e, A i :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp [hk])
      have hsum0 : ∑ i ∈ Finset.univ.erase e, A i = 0 := by
        have h1 : A e + ∑ i ∈ Finset.univ.erase e, A i = ∑ i, A i :=
          Finset.add_sum_erase Finset.univ A (Finset.mem_univ e)
        have h2 : ∑ i, A i = A e := by rw [hAtot]; omega
        omega
      omega
    omega
  have hAltN : ∀ e, A e < N := fun e => Nat.lt_of_lt_of_le (hAltG e) hGN
  have hkeypos : ∀ e, 0 < T - (N - G) * B e := by
    intro e
    obtain ⟨j, hj⟩ := hexists2 e
    have h1 : T - (N - G) * B e
        = B e * (G - B e) + ∑ i ∈ Finset.univ.erase e, B i * (N - B i) := by
      rw [hTdef]
      unfold witnessT
      have h2 : B e * (N - B e)
          + ∑ i ∈ Finset.univ.erase e, B i * (N - B i) = ∑ i, B i * (N - B i) :=
        Finset.add_sum_erase Finset.univ (fun i => B i * (N - B i)) (Finset.mem_univ e)
      have h3 : B e * (N - B e) - (N - G) * B e = B e * (G - B e) := by ring
      omega
    have h4 : 0 ≤ B e * (G - B e) := by
      have hle : B e ≤ G := hBleG e
      positivity
    have h5 : B j * (N - B j) ≤ ∑ i ∈ Finset.univ.erase e, B i * (N - B i) :=
      Finset.single_le_sum
        (fun i _ => by have hle := hBleN i; positivity)
        (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
    have h6 : 0 < B j * (N - B j) := Nat.mul_pos (hBpos j) (by omega)
    omega
  have hTpos : 0 < T := by
    rw [hTdef, witnessT]
    have e₀ : E := Classical.choice hEne
    have h1 : 0 < B e₀ * (N - B e₀) := Nat.mul_pos (hBpos e₀) (by omega)
    have h2 : B e₀ * (N - B e₀) ≤ ∑ i, B i * (N - B i) :=
      Finset.single_le_sum
        (fun i _ => Nat.mul_nonneg (Nat.zero_le _) (Nat.sub_nonneg (hBleN i)))
        (Finset.mem_univ e₀)
    omega
  have hxpos : ∀ e, 0 < x e := by
    intro e
    simp only [hxdef, witnessX]
    have h2 : 0 ≤ (N - G) * (N - B e) := by
      have h1 := hGN
      have h2 := hBltN e
      positivity
    have h3 : 0 < witnessT N B := hTpos
    omega
  have hxn : ∀ e, x e < n := by
    intro e
    simp only [hxdef, witnessX, hndef, witnessN]
    have h3 : 0 < N - B e := by omega
    have h5 : B e * (N - G) * (N - B e) < T * (N - B e) :=
      Nat.mul_lt_mul_of_pos_right (by omega) h3
    have h8 : B e * (T + (N - G) * (N - B e))
        = B e * T + B e * (N - G) * (N - B e) := by ring
    have h9 : N * T = B e * T + (N - B e) * T := by ring
    rw [h8, h9]
    omega
  have hsumx : (∑ e, x e : ℕ) = n := by
    simp only [hxdef, witnessX, hndef, witnessN, hTdef, witnessT]
    rw [Finset.sum_mul, Finset.sum_add_distrib]
    rw [show (∑ e, B e * T : ℕ) = T * ∑ e, B e from Finset.mul_sum.symm]
    rw [show (∑ e, B e * ((N - G) * (N - B e)) : ℕ)
        = (N - G) * ∑ e, B e * (N - B e) from by rw [Finset.sum_mul]; ring]
    rw [hBtot]
    have h1 : G + (N - G) = N := by omega
    rw [h1]
    ring
  have hbridgeA : binomLik N n A x = Real.exp (binomLog N n A x) :=
    binomLik_eq_exp_log hN hApos hAltN hxpos hxn
  have hbridgeB : binomLik N n B x = Real.exp (binomLog N n B x) :=
    binomLik_eq_exp_log hN hBpos hBltN hxpos hxn
  rw [hbridgeA, hbridgeB]
  apply Real.exp_lt_exp.mpr
  have hDdef : binomLog N n A x - binomLog N n B x
      = ∑ e, ((x e : ℝ) * Real.log ((A e : ℝ) / (B e : ℝ))
        + ((n - x e : ℕ) : ℝ) * Real.log (((N - A e : ℕ) : ℝ) / ((N - B e : ℕ) : ℝ))) := by
    unfold binomLog
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    have hcastNA : ((N - A e : ℕ) : ℝ) = (N : ℝ) - (A e : ℝ) := by omega
    have hcastNB : ((N - B e : ℕ) : ℝ) = (N : ℝ) - (B e : ℝ) := by omega
    rw [log_div (by exact_mod_cast (ne_of_gt (hApos e))) (by exact_mod_cast (ne_of_gt hN)),
      log_div (by exact_mod_cast (ne_of_gt (hBpos e))) (by exact_mod_cast (ne_of_gt hN)),
      hcastNA, hcastNB,
      log_div (by exact_mod_cast (ne_of_gt (hApos e))) (by exact_mod_cast (ne_of_gt hN)),
      log_div (by exact_mod_cast (ne_of_gt (hBpos e))) (by exact_mod_cast (ne_of_gt hN))]
    ring
  rw [hDdef]
  have hcastNG : ((N - G : ℕ) : ℝ) = (N : ℝ) - (G : ℝ) := by omega
  have hcastNA : ∀ e, ((N - A e : ℕ) : ℝ) = (N : ℝ) - (A e : ℝ) := by
    intro e; have : A e ≤ N := (hAltN e).le; omega
  have hcastNB : ∀ e, ((N - B e : ℕ) : ℝ) = (N : ℝ) - (B e : ℝ) := by
    intro e; have : B e ≤ N := (hBltN e).le; omega
  have hTposR : (T : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hTpos)
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hle_bound : ∀ e,
      ((x e : ℝ) * Real.log ((A e : ℝ) / (B e : ℝ))
        + ((n - x e : ℕ) : ℝ) * Real.log (((N - A e : ℕ) : ℝ) / ((N - B e : ℕ) : ℝ)))
      ≤ (n : ℝ) * (((N - G : ℕ) : ℝ) / (T : ℝ)) * ((A e : ℝ) - (B e : ℝ)) := by
    intro e
    have h1 : (0 : ℝ) < (A e : ℝ) / (B e : ℝ) := by
      apply div_pos; exact_mod_cast (hApos e); exact_mod_cast (hBpos e)
    have h2 : (0 : ℝ) < ((N - A e : ℕ) : ℝ) / (N - B e : ℕ) : ℝ) := by
      apply div_pos
      · exact_mod_cast (by omega : (0 : ℕ) < N - A e)
      · exact_mod_cast (by omega : (0 : ℕ) < N - B e)
    have h3 : (x e : ℝ) * Real.log ((A e : ℝ) / (B e : ℝ))
        ≤ (x e : ℝ) * ((A e : ℝ) / (B e : ℝ) - 1) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Real.log_le_sub_one_of_pos h1
    have h4 : ((n - x e : ℕ) : ℝ) * Real.log (((N - A e : ℕ) : ℝ) / ((N - B e : ℕ) : ℝ))
        ≤ ((n - x e : ℕ) : ℝ) * (((N - A e : ℕ) : ℝ) / (N - B e : ℕ) : ℝ) - 1) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Real.log_le_sub_one_of_pos h2
    have h5 : ((n - x e : ℕ) : ℝ) = (n : ℝ) - (x e : ℝ) := by
      have hle : x e ≤ n := by
        have : x e ≤ ∑ e, x e := Finset.single_le_sum (f := x) (Finset.mem_univ e) (fun _ _ => Nat.zero_le _)
        omega
      omega
    have hxR : (x e : ℝ) = (B e : ℝ) * ((T : ℝ) + ((N - G : ℕ) : ℝ) * ((N - B e : ℕ) : ℝ))) := by
      rw [hxdef, witnessX, hTdef]
      push_cast
      ring
    have hnR : (n : ℝ) = (N : ℝ) * (T : ℝ) := by
      rw [hndef, witnessN, hTdef]
      push_cast
      ring
    have hBeR : (B e : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (hBpos e))
    have hNB : (N : ℝ) - (B e : ℝ) ≠ 0 := by
      rw [hcastNB e]; exact sub_ne_zero_of_lt (by exact_mod_cast (hBltN e))
    have hAeR : (A e : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (hApos e))
    have hNA : (N : ℝ) - (A e : ℝ) ≠ 0 := by
      rw [hcastNA e]; exact sub_ne_zero_of_lt (by exact_mod_cast (hAltN e))
    have htangent := tangent_identity (N : ℝ) (G : ℝ) (T : ℝ) (n : ℝ) (x e : ℝ) (A e : ℝ) (B e : ℝ)
      hTposR hNR hBeR hNB hAeR hNA hxR hnR
    rw [h5]
    have h6 : (x e : ℝ) = (n : ℝ) * ((x e : ℝ) / (n : ℝ)) := by field_simp
    rw [h6]
    have h7 : (n : ℝ) - (x e : ℝ) = (n : ℝ) * (1 - (x e : ℝ) / (n : ℝ)) := by field_simp
    rw [h7]
    have h8 : (x e : ℝ) * ((A e : ℝ) / (B e : ℝ) - 1)
        + ((n : ℝ) - (x e : ℝ)) * (((N - A e : ℕ) : ℝ) / (N - B e : ℕ) : ℝ) - 1)
        = (n : ℝ) * (((x e : ℝ) / (n : ℝ)) * ((A e : ℝ) / (B e : ℝ) - 1)
          + (1 - (x e : ℝ) / (n : ℝ)) * ((N - A e : ℕ) : ℝ) / (N - B e : ℕ) : ℝ) - 1)) := by
      field_simp
      ring
    rw [htangent]
    ring
  obtain ⟨e₀, he₀⟩ := Finset.exists_mem_ne (f := A) (g := B) (fun _ _ => Finset.mem_univ _) (by
    intro h; exact hne (funext h))
  have hstrict : ((x e₀ : ℝ) * Real.log ((A e₀ : ℝ) / (B e₀ : ℝ))
        + ((n - x e₀ : ℕ) : ℝ) * Real.log (((N - A e₀ : ℕ) : ℝ) / ((N - B e₀ : ℕ) : ℝ)))
      < (n : ℝ) * (((N - G : ℕ) : ℝ) / (T : ℝ)) * ((A e₀ : ℝ) - (B e₀ : ℝ)) := by
    have h1 : (0 : ℝ) < (A e₀ : ℝ) / (B e₀ : ℝ) := by
      apply div_pos; exact_mod_cast (hApos e₀); exact_mod_cast (hBpos e₀)
    have h2 : (0 : ℝ) < ((N - A e₀ : ℕ) : ℝ) / (N - B e₀ : ℕ) : ℝ) := by
      apply div_pos
      · exact_mod_cast (by omega : (0 : ℕ) < N - A e₀)
      · exact_mod_cast (by omega : (0 : ℕ) < N - B e₀)
    have h3 : (A e₀ : ℝ) / (B e₀ : ℝ) ≠ 1 := by
      rw [div_ne_one (by exact_mod_cast (ne_of_gt (hBpos e₀)))]
      exact_mod_cast (by omega : A e₀ ≠ B e₀)
    have h4 : ((N - A e₀ : ℕ) : ℝ) / (N - B e₀ : ℕ) : ℝ) ≠ 1 := by
      rw [hcastNA e₀, hcastNB e₀, div_ne_one (sub_ne_zero_of_lt (by exact_mod_cast (hBltN e₀)))]
      exact sub_ne_zero_of_lt (by exact_mod_cast (by omega : A e₀ ≠ B e₀))
    have h5 : (x e₀ : ℝ) * Real.log ((A e₀ : ℝ) / (B e₀ : ℝ))
        < (x e₀ : ℝ) * ((A e₀ : ℝ) / (B e₀ : ℝ) - 1) := by
      apply mul_lt_mul_of_pos_left _ (by exact_mod_cast (ne_of_gt (hxpos e₀)))
      exact Real.log_lt_sub_one_of_pos h1 h3
    have h6 : ((n - x e₀ : ℕ) : ℝ) * Real.log (((N - A e₀ : ℕ) : ℝ) / ((N - B e₀ : ℕ) : ℝ))
        < ((n - x e₀ : ℕ) : ℝ) * (((N - A e₀ : ℕ) : ℝ) / (N - B e₀ : ℕ) : ℝ) - 1) := by
      apply mul_lt_mul_of_pos_left _ (by exact_mod_cast (by omega : (0 : ℕ) < n - x e₀))
      exact Real.log_lt_sub_one_of_pos h2 h4
    have h7 : ((n - x e₀ : ℕ) : ℝ) = (n : ℝ) - (x e₀ : ℝ) := by
      have hle : x e₀ ≤ n := by
        have : x e₀ ≤ ∑ e, x e :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ e₀)
        omega
      omega
    have h8 : (x e₀ : ℝ) = (n : ℝ) * ((x e₀ : ℝ) / (n : ℝ)) := by field_simp
    rw [h7, h8]
    have h9 : (n : ℝ) - (x e₀ : ℝ) = (n : ℝ) * (1 - (x e₀ : ℝ) / (n : ℝ)) := by field_simp
    rw [h9]
    have h10 : (x e₀ : ℝ) * ((A e₀ : ℝ) / (B e₀ : ℝ) - 1)
        + ((n : ℝ) - (x e₀ : ℝ)) * (((N - A e₀ : ℕ) : ℝ) / (N - B e₀ : ℕ) : ℝ) - 1)
        = (n : ℝ) * (((x e₀ : ℝ) / (n : ℝ)) * ((A e₀ : ℝ) / (B e₀ : ℝ) - 1)
          + (1 - (x e₀ : ℝ) / (n : ℝ)) * ((N - A e₀ : ℕ) : ℝ) / (N - B e₀ : ℕ) : ℝ) - 1)) := by
      field_simp
      ring
    linarith
  have hsumA : (∑ e, (A e : ℝ) : ℝ) = (G : ℝ) := by exact_mod_cast hAtot
  have hsumB : (∑ e, (B e : ℝ) : ℝ) = (G : ℝ) := by exact_mod_cast hBtot
  have hDsplit : ∑ e, ((x e : ℝ) * Real.log ((A e : ℝ) / (B e : ℝ))
        + ((n - x e : ℕ) : ℝ) * Real.log (((N - A e : ℕ) : ℝ) / ((N - B e : ℕ) : ℝ)))
      = ((x e₀ : ℝ) * Real.log ((A e₀ : ℝ) / (B e₀ : ℝ))
          + ((n - x e₀ : ℕ) : ℝ) * Real.log (((N - A e₀ : ℕ) : ℝ) / ((N - B e₀ : ℕ) : ℝ)))
        + ∑ e ∈ Finset.univ.erase e₀, ((x e : ℝ) * Real.log ((A e : ℝ) / (B e : ℝ))
          + ((n - x e : ℕ) : ℝ) * Real.log (((N - A e : ℕ) : ℝ) / ((N - B e : ℕ) : ℝ))) := by
    have h1 := Finset.add_sum_erase Finset.univ
      (fun e => (x e : ℝ) * Real.log ((A e : ℝ) / (B e : ℝ))
        + ((n - x e : ℕ) : ℝ) * Real.log (((N - A e : ℕ) : ℝ) / ((N - B e : ℕ) : ℝ)))
      (Finset.mem_univ e₀)
    rw [h1]
  rw [hDsplit]
  have hrest : ∑ e ∈ Finset.univ.erase e₀, ((x e : ℝ) * Real.log ((A e : ℝ) / (B e : ℝ))
        + ((n - x e : ℕ) : ℝ) * Real.log (((N - A e : ℕ) : ℝ) / ((N - B e : ℕ) : ℝ)))
      ≤ (n : ℝ) * (((N - G : ℕ) : ℝ) / (T : ℝ)) * (∑ e ∈ Finset.univ.erase e₀, (A e : ℝ) - (B e : ℝ))) := by
    apply Finset.sum_le_sum
    intro e _
    exact hle_bound e
  have hsumerase : (∑ e ∈ Finset.univ.erase e₀, (A e : ℝ) - (B e : ℝ) : ℝ)
      = (G : ℝ) - (A e₀ : ℝ) - ((G : ℝ) - (B e₀ : ℝ)) := by
    have h1 : (∑ e ∈ Finset.univ.erase e₀, (A e : ℝ) : ℝ) = (G : ℝ) - (A e₀ : ℝ) := by
      have h3 : (A e₀ : ℝ) + ∑ e ∈ Finset.univ.erase e₀, (A e : ℝ) = ∑ e, (A e : ℝ) :=
        Finset.add_sum_erase Finset.univ (fun e => (A e : ℝ)) (Finset.mem_univ e₀)
      have := hsumA
      omega
    have h2 : (∑ e ∈ Finset.univ.erase e₀, (B e : ℝ) : ℝ) = (G : ℝ) - (B e₀ : ℝ) := by
      have h3 : (B e₀ : ℝ) + ∑ e ∈ Finset.univ.erase e₀, (B e : ℝ) = ∑ e, (B e : ℝ) :=
        Finset.add_sum_erase Finset.univ (fun e => (B e : ℝ)) (Finset.mem_univ e₀)
      have := hsumB
      omega
    rw [h1, h2]
    exact Finset.sum_sub_distrib _ _ _
  rw [hsumerase] at hrest
  have hfinal : (n : ℝ) * (((N - G : ℕ) : ℝ) / (T : ℝ)) * ((A e₀ : ℝ) - (B e₀ : ℝ)))
      + (n : ℝ) * (((N - G : ℕ) : ℝ) / (T : ℝ)) * ((G : ℝ) - (A e₀ : ℝ) - ((G : ℝ) - (B e₀ : ℝ))))
      = 0 := by
    ring
  have hposN : (0 : ℝ) < (n : ℝ) * (((N - G : ℕ) : ℝ) / (T : ℝ)) := by
    apply mul_pos
    · exact_mod_cast (by omega : (0 : ℕ) < n)
    · apply div_pos
      · exact_mod_cast (Nat.sub_pos_of_lt hGN)
      · exact_mod_cast hTpos
  linarith

/-! ## The (B) sample-uniform classification -/

/-- **The (B) sample-uniform iff.** Let `A` and `B` be positive integer weight
vectors with the same total `G`, and let `N ≥ G` be an external genome-size
estimate. Then

`(∀ x positive on every edge, ∀ n, binomLik N n B x ≤ binomLik N n A x) ↔ A = B`.

The `⇐` direction is immediate (if `A = B` every ratio is `1`). The `⇒` direction
is the contrapositive of `witness_beats`: a competitor `B ≠ A` can be amplified
to strictly beat `A`, so sample-uniformity fails. -/
theorem binomLik_robust_iff_unique {E : Type} [Fintype E] [DecidableEq E]
    {G N : ℕ} (hG : 0 < G) (hGN : G ≤ N) (hN : 0 < N)
    (A B : E → ℕ)
    (hApos : ∀ e, 0 < A e) (hBpos : ∀ e, 0 < B e)
    (hAtot : ∑ e, A e = G) (hBtot : ∑ e, B e = G) :
    (∀ x : E → ℕ, (∀ e, 0 < x e) → ∀ n : ℕ,
      binomLik N n B x ≤ binomLik N n A x) ↔ A = B := by
  constructor
  · intro h
    by_contra hne
    have hBltN : ∀ e, B e < N := by
      intro e
      have h1 : B e ≤ G := by
        by_contra h'; push_neg at h'
        have : ∑ e, B e ≥ B e := Finset.single_le_sum (f := B) (Finset.mem_univ e) (fun _ _ => Nat.zero_le _)
        omega
      by_contra h''; push_neg at h''
      have hBe : B e = N := by omega
      have hGeq : G = N := by omega
      have hsum : ∑ e, B e = B e := by rw [hBtot]; omega
      have hsingle : ∀ j : E, j ≠ e → B j = 0 := by
        intro j hj
        by_contra hj0
        have : ∑ e, B e ≥ B e + B j := by
          have h2 : ∑ e, B e = ∑ e ∈ ({e, j} : Finset E), B e := by
            apply Finset.sum_eq_of_subset_of_subset
            · intro k _; exact Finset.mem_univ k
            · intro k hk
              simp only [Finset.mem_insert, Finset.mem_singleton] at hk
              rcases hk with rfl | rfl <;> exact Finset.mem_univ k
          omega
        omega
      have hAeqB : A = B := by
        funext j
        by_cases hj : j = e
        · subst hj
          have hAe : A e = G := by
            have h3 : ∑ e, A e = ∑ e, B e := by rw [hAtot, hBtot]
            have hA0 : ∀ k : E, k ≠ e → A k = 0 := by
              intro k hk
              by_contra hk0
              have : ∑ e, A e ≥ A e + A k := by
                have h4 : ∑ e, A e = ∑ e ∈ ({e, k} : Finset E), A e := by
                  apply Finset.sum_eq_of_subset_of_subset
                  · intro m _; exact Finset.mem_univ m
                  · intro m hm
                    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
                    rcases hm with rfl | rfl <;> exact Finset.mem_univ m
                omega
              omega
            rw [hAtot, Finset.sum_eq_single e (fun k hk => by rw [hA0 k hk]) (Finset.mem_univ e)]
          omega
        · have hAj : A j = 0 := by
            by_contra hj0
            have : ∑ e, A e ≥ A e + A j := by
              have h4 : ∑ e, A e = ∑ e ∈ ({e, j} : Finset E), A e := by
                apply Finset.sum_eq_of_subset_of_subset
                · intro m _; exact Finset.mem_univ m
                · intro m hm
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
                  rcases hm with rfl | rfl <;> exact Finset.mem_univ m
              omega
            omega
          have hBj : B j = 0 := hsingle j hj
          omega
      exact hne hAeqB
    have hbeats := witness_beats hG hGN hN A B hApos hBpos hAtot hBtot hne
    have hxpos : ∀ e, 0 < witnessX G N B e := by
      intro e
      simp only [witnessX]
      have h2 : 0 ≤ (N - G) * (N - B e) :=
        Nat.mul_nonneg (Nat.sub_nonneg hGN.le) (Nat.sub_nonneg (hBltN e).le)
      have h3 : 0 < witnessT N B := by
        apply Finset.sum_pos
        intro e _
        apply Nat.mul_pos
        · exact hBpos e
        · omega
      have h4 : 0 < B e := hBpos e
      have h5 : 0 < witnessT N B + (N - G) * (N - B e) := by omega
      exact Nat.mul_pos h4 h5
    have hle := h (witnessX G N B) hxpos (witnessN N B)
    exact absurd hle (by linarith)
  · intro h
    subst h
    intro x hx n
    le_refl _

/-- **Rigidity implies sample-uniform maximality.** If every positive integer
weight vector of total `G` on `E` equals `A`, then for every admissible sample
`x` and every such `B`, `binomLik N n B x ≤ binomLik N n A x`. -/
theorem binomLik_robust_of_rigidity {E : Type} [Fintype E] [DecidableEq E]
    {G N : ℕ} (hG : 0 < G) (hGN : G ≤ N) (hN : 0 < N)
    (A : E → ℕ)
    (hApos : ∀ e, 0 < A e)
    (hAtot : ∑ e, A e = G)
    (hF : ∀ B : E → ℕ, (∀ e, 0 < B e) → (∑ e, B e = G) → B = A) :
    ∀ x : E → ℕ, (∀ e, 0 < x e) → ∀ B : E → ℕ, (∀ e, 0 < B e) → (∑ e, B e = G) →
      ∀ n : ℕ, binomLik N n B x ≤ binomLik N n A x := by
  intro x hx B hBpos hBtot n
  have hBA : B = A := hF B hBpos hBtot
  rw [hBA]
  le_refl _

/-- **Sample-uniform maximality implies rigidity.** If for every admissible
sample `x` and every positive integer weight vector `B` of total `G`,
`binomLik N n B x ≤ binomLik N n A x`, then every such `B` equals `A`. This is
the contrapositive of `witness_beats`. -/
theorem binomLik_rigidity_of_robust {E : Type} [Fintype E] [DecidableEq E]
    {G N : ℕ} (hG : 0 < G) (hGN : G ≤ N) (hN : 0 < N)
    (A : E → ℕ)
    (hApos : ∀ e, 0 < A e)
    (hAtot : ∑ e, A e = G)
    (hrobust : ∀ x : E → ℕ, (∀ e, 0 < x e) → ∀ B : E → ℕ, (∀ e, 0 < B e) → (∑ e, B e = G) →
      ∀ n : ℕ, binomLik N n B x ≤ binomLik N n A x) :
    ∀ B : E → ℕ, (∀ e, 0 < B e) → (∑ e, B e = G) → B = A := by
  intro B hBpos hBtot
  by_contra hne
  have hBltN : ∀ e, B e < N := by
    intro e
    have h1 : B e ≤ G := by
      by_contra h'; push_neg at h'
      have : ∑ e, B e ≥ B e := Finset.single_le_sum (f := B) (Finset.mem_univ e) (fun _ _ => Nat.zero_le _)
      omega
    by_contra h''; push_neg at h''
    have hBe : B e = N := by omega
    have hGeq : G = N := by omega
    have hsum : ∑ e, B e = B e := by rw [hBtot]; omega
    have hsingle : ∀ j : E, j ≠ e → B j = 0 := by
      intro j hj
      by_contra hj0
      have : ∑ e, B e ≥ B e + B j := by
        have h2 : ∑ e, B e = ∑ e ∈ ({e, j} : Finset E), B e := by
          apply Finset.sum_eq_of_subset_of_subset
          · intro k _; exact Finset.mem_univ k
          · intro k hk
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk
            rcases hk with rfl | rfl <;> exact Finset.mem_univ k
        omega
      omega
    have hAeqB : A = B := by
      funext j
      by_cases hj : j = e
      · subst hj
        have hAe : A e = G := by
          have h3 : ∑ e, A e = ∑ e, B e := by rw [hAtot, hBtot]
          have hA0 : ∀ k : E, k ≠ e → A k = 0 := by
            intro k hk
            by_contra hk0
            have : ∑ e, A e ≥ A e + A k := by
              have h4 : ∑ e, A e = ∑ e ∈ ({e, k} : Finset E), A e := by
                apply Finset.sum_eq_of_subset_of_subset
                · intro m _; exact Finset.mem_univ m
                · intro m hm
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
                  rcases hm with rfl | rfl <;> exact Finset.mem_univ m
              omega
            omega
          rw [hAtot, Finset.sum_eq_single e (fun k hk => by rw [hA0 k hk]) (Finset.mem_univ e)]
        omega
      · have hAj : A j = 0 := by
          by_contra hj0
          have : ∑ e, A e ≥ A e + A j := by
            have h4 : ∑ e, A e = ∑ e ∈ ({e, j} : Finset E), A e := by
              apply Finset.sum_eq_of_subset_of_subset
              · intro m _; exact Finset.mem_univ m
              · intro m hm
                simp only [Finset.mem_insert, Finset.mem_singleton] at hm
                rcases hm with rfl | rfl <;> exact Finset.mem_univ m
            omega
          omega
        have hBj : B j = 0 := hsingle j hj
        omega
    exact hne hAeqB
  have hbeats := witness_beats hG hGN hN A B hApos hBpos hAtot hBtot hne
  have hxpos : ∀ e, 0 < witnessX G N B e := by
    intro e
    simp only [witnessX]
    have h2 : 0 ≤ (N - G) * (N - B e) :=
      Nat.mul_nonneg (Nat.sub_nonneg hGN.le) (Nat.sub_nonneg (hBltN e).le)
    have h3 : 0 < witnessT N B := by
      apply Finset.sum_pos
      intro e _
      apply Nat.mul_pos
      · exact hBpos e
      · omega
    have h4 : 0 < B e := hBpos e
    have h5 : 0 < witnessT N B + (N - G) * (N - B e) := by omega
    exact Nat.mul_pos h4 h5
  have hle := hrobust (witnessX G N B) hxpos B hBpos hBtot (witnessN N B)
  exact absurd hle (by linarith)

/-! ## Connection to PR167 (FiniteStartCoverage) -/

section PR167Bridge

variable {S E : Type*} [Fintype S] [Fintype E] [DecidableEq E]

open AssemblyP1.FiniteStartCoverage

/-- **The PR167 bridge.** The `binomLik` objective used here is the same
normalized product-binomial log score used in `FiniteStartCoverage`, up to the
candidate-independent binomial coefficients. The (B) classification
`binomLik_robust_iff_unique` is the abstract-edge-set version of
`uniform_normalized_score_iff_rigidity` from PR167. -/
theorem binomLik_eq_normalized_score_difference
    {N n : ℕ} (hN : 0 < N)
    (A B x : E → ℕ)
    (hApos : ∀ e, 0 < A e) (hBpos : ∀ e, 0 < B e)
    (hAltN : ∀ e, A e < N) (hBltN : ∀ e, B e < N)
    (hxpos : ∀ e, 0 < x e) (hxltn : ∀ e, x e < n) :
    binomLog N n A x - binomLog N n B x =
    binomLog N n A x - binomLog N n B x =
      normalizedBinomialLogScore (N : ℝ) (n : ℝ)
        (fun e => (A e : ℝ)) (fun e => (x e : ℝ)) -
      normalizedBinomialLogScore (N : ℝ) (n : ℝ)
        (fun e => (B e : ℝ)) (fun e => (x e : ℝ)) := by
  have hcastN : ∀ e, ((n - x e : ℕ) : ℝ) = (n : ℝ) - (x e : ℝ) := by
    intro e; have : x e ≤ n := hxltn e; omega
  have hcastNA : ∀ e, ((N - A e : ℕ) : ℝ) = (N : ℝ) - (A e : ℝ) := by
    intro e; have : A e ≤ N := (hAltN e).le; omega
  have hcastNB : ∀ e, ((N - B e : ℕ) : ℝ) = (N : ℝ) - (B e : ℝ) := by
    intro e; have : B e ≤ N := (hBltN e).le; omega
  unfold binomLog normalizedBinomialLogScore
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [log_div (by exact_mod_cast (ne_of_gt (hApos e))) (by exact_mod_cast (ne_of_gt hN)),
    log_div (by exact_mod_cast (ne_of_gt (hBpos e))) (by exact_mod_cast (ne_of_gt hN)),
    hcastNA, hcastNB,
    log_div (by exact_mod_cast (ne_of_gt (hApos e))) (by exact_mod_cast (ne_of_gt hN)),
    log_div (by exact_mod_cast (ne_of_gt (hBpos e))) (by exact_mod_cast (ne_of_gt hN)),
    hcastN]
  ring

end PR167Bridge

end
