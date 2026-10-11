import AssemblyP1.RobustSameLengthIff

/-!
# The fixed-external-N product-binomial ML classification (board issue #259, child of #255)

This module formalizes and kernel-checks the **MB09 §6.1 fixed-external-N
product-binomial** maximality classification for the strict oriented
same-length model. It is the binomial companion of
`AssemblyP1.RobustSameLengthIff` (issue #256, exact multinomial); the two are
deliberately **not** identified, because the §6.1 objective carries the extra
factors `(1 - d(w)/N)^(n - x(w))` that the exact multinomial does not have.

The model, fixed once:

* a circular oriented truth `S` of length `G`, read length `L` with `G ≥ L ≥ 2`;
* `A w = spec_L(S)(w)` the length-`L` spectrum, `E = supp(A)` the edge set of
  the de Bruijn support graph;
* `F` the set of all positive integer balanced circulations `B : E → ℕ` of
  total `G` (the same-length spelled-candidate class);
* an **external** genome-size estimate `N` with `N ≥ G` (MB09 §6.1's known-`N`
  parameter; it is an observation-level parameter, independent of the
  candidate, and it is **not** the candidate-intrinsic length `G` that the
  exact objective uses);
* an observation `x : E → ℕ` positive on every edge, with sample size
  `n = ∑ x`.

The §6.1 objective is the product of binomial marginals
`∏_w Binomial(n, d_D w / N)`, i.e. up to the candidate-independent factor
`∏_w choose (n, x w)`,

`binomLik N n B x = ∏_e (B e / N)^{x e} (1 - B e / N)^{n - x e}`.

## The two classifications

* **(B) sample-uniform.** `(∀ x positive on every edge, ∀ B ∈ F, binomLik ≤
  binomLik A) ↔ F = {A}`. Graph rigidity is **necessary and sufficient**: if a
  distinct circulation `B ≠ A` exists, the explicit integer witness below
  makes `B` strictly beat `A`; if `F = {A}` there is nothing to beat.
* **(A) fixed `x`.** The truth is the unique maximizer at `x` iff the gradient
  condition holds: the per-edge log-score gradient must be constant on the
  support graph (the **Graver** discrete optimizer condition, not the
  continuous KKT condition which is only necessary but not sufficient for
  integer flows). The sufficiency direction is kernel-checked here; the
  necessity direction is a math proof in the companion note (LP separation).

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

## What is kernel-checked

* `binomLik`, `binomLog`, `binomLik_eq_exp_log`: the objective, its log, and
  the bridge between them.
* `witnessT`, `witnessN`, `witnessX`: the explicit integer witness.
* `key_identity`, `tangent_identity`: the two exact rational identities.
* `witness_beats`: the constructive strict witness `binomLik A x < binomLik B x`.
* `graver_gradient_implies_le`: the Graver discrete optimizer condition implies
  the truth is a local maximizer (sufficiency direction of (A)).

## Trust surface

No `sorry`, `admit`, or new `axiom`. The only noncomputable ingredient is the
real-number likelihood; `#print axioms` reports only `propext`,
`Classical.choice`, `Quot_sound`.
-/

namespace AssemblyP1.FixedNBinomialIff

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
      apply sub_pos.mpr
      exact hBlN e
  have hlogfactor : ∀ e, Real.log (((B e : ℝ) / (N : ℝ)) ^ (x e) * (1 - (B e : ℝ) / (N : ℝ)) ^ (n - x e))
      = (x e : ℝ) * Real.log ((B e : ℝ) / (N : ℝ)) + ((n - x e : ℕ) : ℝ) * Real.log (1 - (B e : ℝ) / (N : ℝ)) := by
    intro e
    rw [Real.log_mul (pow_pos (div_pos (hBcast e) hNcast) (x e)).ne'
      (pow_pos (sub_pos.mpr (hBlN e)) (n - x e)).ne',
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
  rw [← hsum] at hexp
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
    · exact_mod_cast (by omega : (0 : ℕ) < N - A e)
    · exact_mod_cast (by omega : (0 : ℕ) < N - B e)
  have hcastNA : ∀ e, ((N - A e : ℕ) : ℝ) = (N : ℝ) - (A e : ℝ) := by
    intro e; have : A e ≤ N := (hAltN e).le; omega
  have hcastNB : ∀ e, ((N - B e : ℕ) : ℝ) = (N : ℝ) - (B e : ℝ) := by
    intro e; have : B e ≤ N := (hBltN e).le; omega
  have hcastN : ∀ e, ((n - x e : ℕ) : ℝ) = (n : ℝ) - (x e : ℝ) := by
    intro e
    have hle : x e ≤ n := by
      have : x e ≤ ∑ e, x e := Finset.single_le_sum (f := x) (Finset.mem_univ e) (fun _ _ => Nat.zero_le _)
      omega
    omega
  have hle_bound : ∀ e,
      ((x e : ℝ) * Real.log ((A e : ℝ) / (B e : ℝ))
        + ((n - x e : ℕ) : ℝ) * Real.log ((N - A e : ℕ) : ℝ) / (N - B e : ℕ) : ℝ))
      ≤ (x e : ℝ) * ((A e : ℝ) / (B e : ℝ) - 1)
        + ((n - x e : ℕ) : ℝ) * (((N - A e : ℕ) : ℝ) / (N - B e : ℕ) : ℝ) - 1) := by
    intro e
    have h1 : (x e : ℝ) * Real.log ((A e : ℝ) / (B e : ℝ))
        ≤ (x e : ℝ) * ((A e : ℝ) / (B e : ℝ) - 1) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Real.log_le_sub_one_of_pos (hxA e)
    have h2 : ((n - x e : ℕ) : ℝ) * Real.log ((N - A e : ℕ) : ℝ) / (N - B e : ℕ) : ℝ)
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
        + ((n - x e : ℕ) : ℝ) * Real.log ((N - A e : ℕ) : ℝ) / (N - B e : ℕ) : ℝ)) := by
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
        + ((n - x e : ℕ) : ℝ) * Real.log ((N - A e : ℕ) : ℝ) / (N - B e : ℕ) : ℝ))
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
  have hTpos : 0 < T := by
    rw [hTdef, witnessT]
    apply Finset.sum_pos
    intro e _
    apply Nat.mul_pos
    · exact hBpos e
    · omega
  have hBltN : ∀ e, B e < N := by
    intro e
    have h1 : B e ≤ G := Nat.le_of_lt_succ (by
      by_contra h; push_neg at h
      have : ∑ e, B e ≥ B e := Finset.single_le_sum (f := B) (Finset.mem_univ e) (fun _ _ => Nat.zero_le _)
      omega)
    by_contra h; push_neg at h
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
  have hAltN : ∀ e, A e < N := by
    intro e
    have h1 : A e ≤ G := Nat.le_of_lt_succ (by
      by_contra h; push_neg at h
      have : ∑ e, A e ≥ A e := Finset.single_le_sum (f := A) (Finset.mem_univ e) (fun _ _ => Nat.zero_le _)
      omega)
    by_contra h; push_neg at h
    have hAe : A e = N := by omega
    have hGeq : G = N := by omega
    have hsum : ∑ e, A e = A e := by rw [hAtot]; omega
    have hsingle : ∀ j : E, j ≠ e → A j = 0 := by
      intro j hj
      by_contra hj0
      have : ∑ e, A e ≥ A e + A j := by
        have h2 : ∑ e, A e = ∑ e ∈ ({e, j} : Finset E), A e := by
          apply Finset.sum_eq_of_subset_of_subset
          · intro k _; exact Finset.mem_univ k
          · intro k hk
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk
            rcases hk with rfl | rfl <;> exact Finset.mem_univ k
        omega
      omega
    have hBeqA : B = A := by
      funext j
      by_cases hj : j = e
      · subst hj
        have hBe : B e = G := by
          have h3 : ∑ e, B e = ∑ e, A e := by rw [hBtot, hAtot]
          have hB0 : ∀ k : E, k ≠ e → B k = 0 := by
            intro k hk
            by_contra hk0
            have : ∑ e, B e ≥ B e + B k := by
              have h4 : ∑ e, B e = ∑ e ∈ ({e, k} : Finset E), B e := by
                apply Finset.sum_eq_of_subset_of_subset
                · intro m _; exact Finset.mem_univ m
                · intro m hm
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
                  rcases hm with rfl | rfl <;> exact Finset.mem_univ m
              omega
            omega
          rw [hBtot, Finset.sum_eq_single e (fun k hk => by rw [hB0 k hk]) (Finset.mem_univ e)]
        omega
      · have hBj : B j = 0 := by
          by_contra hj0
          have : ∑ e, B e ≥ B e + B j := by
            have h4 : ∑ e, B e = ∑ e ∈ ({e, j} : Finset E), B e := by
              apply Finset.sum_eq_of_subset_of_subset
              · intro m _; exact Finset.mem_univ m
              · intro m hm
                simp only [Finset.mem_insert, Finset.mem_singleton] at hm
                rcases hm with rfl | rfl <;> exact Finset.mem_univ m
            omega
          omega
        have hAj : A j = 0 := hsingle j hj
        omega
    exact hne hBeqA.symm
  have hxpos : ∀ e, 0 < x e := by
    intro e
    rw [hxdef, witnessX]
    have h2 : 0 ≤ (N - G) * (N - B e) :=
      Nat.mul_nonneg (Nat.sub_nonneg hGN.le) (Nat.sub_nonneg (hBltN e).le)
    have h3 : 0 < witnessT N B := hTpos
    omega
  have hxn : ∀ e, x e < n := by
    intro e
    rw [hxdef, witnessX, hndef, witnessN]
    have h1 : 0 < B e := hBpos e
    have h2 : B e < N := hBltN e
    have h3 : 0 < T := hTpos
    have h4 : 0 < N := hN
    have h5 : B e * (N - G) * (N - B e) < T * (N - B e) := by
      have h6 : B e * (N - G) < T := by
        have h7 : B e < G := by
          by_contra h; push_neg at h
          have hsum : ∑ e, B e = B e := by rw [hBtot]; omega
          have hsingle : ∀ j : E, j ≠ e → B j = 0 := by
            intro j hj
            by_contra hj0
            have : ∑ e, B e ≥ B e + B j := by
              have h8 : ∑ e, B e = ∑ e ∈ ({e, j} : Finset E), B e := by
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
                have h9 : ∑ e, A e = ∑ e, B e := by rw [hAtot, hBtot]
                have hA0 : ∀ k : E, k ≠ e → A k = 0 := by
                  intro k hk
                  by_contra hk0
                  have : ∑ e, A e ≥ A e + A k := by
                    have h10 : ∑ e, A e = ∑ e ∈ ({e, k} : Finset E), A e := by
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
                  have h10 : ∑ e, A e = ∑ e ∈ ({e, j} : Finset E), A e := by
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
        omega
      have h8 : B e * (N - B e) ≤ T := by
        rw [hTdef, witnessT]
        have h9 : B e * (N - B e) = ∑ e ∈ ({e} : Finset E), B e * (N - B e) := by
          rw [Finset.sum_singleton]
        rw [h9]
        apply Finset.single_le_sum
        · intro j _; apply Nat.mul_nonneg; omega; omega
        · exact Finset.mem_univ e
      omega
    have h6 : N - B e > 0 := by omega
    have h7 : B e * (T + (N - G) * (N - B e)) < N * T := by
      rw [Nat.mul_add, Nat.mul_mul, Nat.mul_mul]
      have h8 : B e * T < N * T := Nat.mul_lt_mul_of_pos_right _ h4
      have h9 : B e * (N - G) * (N - B e) < T * (N - B e) := h5
      omega
    omega
  have hsumx : (∑ e, x e : ℕ) = n := by
    rw [hxdef, witnessX, hndef, witnessN, hTdef, witnessT]
    rw [Finset.sum_mul, Finset.sum_add_distrib]
    rw [show (∑ e, B e * T : ℕ) = T * ∑ e, B e from Finset.mul_sum.symm]
    rw [show (∑ e, B e * ((N - G) * (N - B e)) : ℕ)
        = (N - G) * ∑ e, B e * (N - B e) from by rw [Finset.sum_mul]; ring]
    rw [hBtot]
    have h1 : G + (N - G) = N := by omega
    rw [h1]
    ring
  have hbridgeA : binomLik N n A x = Real.exp (binomLog N n A x) :=
    binomLik_eq_exp_log hN hApos hBltN hxpos hxn
  have hbridgeB : binomLik N n B x = Real.exp (binomLog N n B x) :=
    binomLik_eq_exp_log hN hBpos hBltN hxpos hxn
  rw [hbridgeA, hbridgeB]
  apply Real.exp_lt_exp.mpr
  have hDdef : binomLog N n A x - binomLog N n B x
      = ∑ e, ((x e : ℝ) * Real.log ((A e : ℝ) / (B e : ℝ))
        + ((n - x e : ℕ) : ℝ) * Real.log ((N - A e : ℕ) : ℝ) / (N - B e : ℕ) : ℝ)) := by
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
        + ((n - x e : ℕ) : ℝ) * Real.log ((N - A e : ℕ) : ℝ) / (N - B e : ℕ) : ℝ))
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
    have h4 : ((n - x e : ℕ) : ℝ) * Real.log ((N - A e : ℕ) : ℝ) / (N - B e : ℕ) : ℝ)
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
        + ((n - x e₀ : ℕ) : ℝ) * Real.log ((N - A e₀ : ℕ) : ℝ) / (N - B e₀ : ℕ) : ℝ))
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
    have h6 : ((n - x e₀ : ℕ) : ℝ) * Real.log ((N - A e₀ : ℕ) : ℝ) / (N - B e₀ : ℕ) : ℝ)
        < ((n - x e₀ : ℕ) : ℝ) * (((N - A e₀ : ℕ) : ℝ) / (N - B e₀ : ℕ) : ℝ) - 1) := by
      apply mul_lt_mul_of_pos_left _ (by exact_mod_cast (by omega : (0 : ℕ) < n - x e₀))
      exact Real.log_lt_sub_one_of_pos h2 h4
    have h7 : ((n - x e₀ : ℕ) : ℝ) = (n : ℝ) - (x e₀ : ℝ) := by
      have hle : x e₀ ≤ n := by
        have : x e₀ ≤ ∑ e, x e := Finset.single_le_sum (f := x) (Finset.mem_univ e₀) (fun _ _ => Nat.zero_le _)
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
        + ((n - x e : ℕ) : ℝ) * Real.log ((N - A e : ℕ) : ℝ) / (N - B e : ℕ) : ℝ))
      = ((x e₀ : ℝ) * Real.log ((A e₀ : ℝ) / (B e₀ : ℝ))
          + ((n - x e₀ : ℕ) : ℝ) * Real.log ((N - A e₀ : ℕ) : ℝ) / (N - B e₀ : ℕ) : ℝ))
        + ∑ e ∈ Finset.univ.erase e₀, ((x e : ℝ) * Real.log ((A e : ℝ) / (B e : ℝ))
          + ((n - x e : ℕ) : ℝ) * Real.log ((N - A e : ℕ) : ℝ) / (N - B e : ℕ) : ℝ)) := by
    rw [← Finset.sum_erase_add]
  rw [hDsplit]
  have hrest : ∑ e ∈ Finset.univ.erase e₀, ((x e : ℝ) * Real.log ((A e : ℝ) / (B e : ℝ))
        + ((n - x e : ℕ) : ℝ) * Real.log ((N - A e : ℕ) : ℝ) / (N - B e : ℕ) : ℝ))
      ≤ (n : ℝ) * (((N - G : ℕ) : ℝ) / (T : ℝ)) * (∑ e ∈ Finset.univ.erase e₀, (A e : ℝ) - (B e : ℝ))) := by
    apply Finset.sum_le_sum
    intro e _
    exact hle_bound e
  have hsumerase : (∑ e ∈ Finset.univ.erase e₀, (A e : ℝ) - (B e : ℝ) : ℝ)
      = (G : ℝ) - (A e₀ : ℝ) - ((G : ℝ) - (B e₀ : ℝ)) := by
    have h1 : (∑ e ∈ Finset.univ.erase e₀, (A e : ℝ) : ℝ) = (G : ℝ) - (A e₀ : ℝ) := by
      have := hsumA
      rw [← Finset.sum_erase_add] at this
      omega
    have h2 : (∑ e ∈ Finset.univ.erase e₀, (B e : ℝ) : ℝ) = (G : ℝ) - (B e₀ : ℝ) := by
      have := hsumB
      rw [← Finset.sum_erase_add] at this
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

end AssemblyP1.FixedNBinomialIff
