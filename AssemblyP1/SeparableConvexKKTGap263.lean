import Mathlib

/-!
# Exact-rational KKT-gap witness for issue #263 (AAABBB, `G = N = 6`, `x = [3,1,2,1]`)

This file kernel-checks the two exact facts behind the board #259 comment recorded in
`docs/remaining-open-matrix-255.md` ("#259 recovered WIP's fixed-x iff continuous KKT:
FALSE for integer flows"):

* **Discrete unique maximality.**  At the fixed-external-`N` product-binomial likelihood
  of MB09 §6.1 (per-type `Binom(n, cᵢ / N)` with `N = n = 6`, observed `x = [3,1,2,1]`),
  the AAABBB truth spectrum `d = [2,1,2,1]` (spectra `B1` of `FixedXExactML.lean`, in
  `AA, AB, BB, BA` order) is the **unique** maximizer over the *entire* sum-6 count fiber
  `{c ∈ {0,…,6}⁴ : ∑ cᵢ = 6}` — hence in particular over the four balanced spectra
  `{B1, B2, B3, B4}` of `docs/fixed-x-exact-ml-258.md`.  The comparison uses only natural
  numbers: with `S(c) = ∏ᵢ cᵢ ^ xᵢ * (N - cᵢ) ^ (n - xᵢ)` (the `c`-dependent part of the
  product-binomial likelihood; the `c`-independent binomial coefficients and `N⁻⁶`
  factors cancel), `S(B1) = 5120000000000` strictly exceeds every other fiber value.
  All exponents are positive here (`x = [3,1,2,1]`, `n - x = [3,5,4,5]`), so no `0 ^ 0`
  convention is ever needed and `0 ^ (positive) = 0` correctly scores unsupported
  candidates.
* **Nonzero KKT residual.**  The formal partial derivatives of the log-likelihood term
  `xᵢ * log (cᵢ / N) + (n - xᵢ) * log (1 - cᵢ / N)` at `c = d` are
  `gᵢ = xᵢ / dᵢ - (n - xᵢ) / (N - dᵢ) = [3/4, 0, 0, 0]` (elementary calculus:
  `d/dc [x * log (c/N)] = x / c`; cf. Mathlib `HasDerivAt.log`, not re-proved here).
  KKT stationarity for maximizing this concave likelihood over the continuous simplex
  relaxation would force all four partials to be equal on the support; instead
  `g AA = 3/4 ≠ 0 = g AB`.  Equivalently, along the mass-preserving integer direction
  `v = (1, 0, -1, 0)` (which also preserves the de Bruijn balance, since `AA` and `BB`
  are loops at distinct nodes) the directional derivative is `3 / 4 ≠ 0`.

**Epistemic boundary (honest):** kernel-checked below are the unique-maximality fact
(`kktGap_uniqueMax`, by `decide` over the `7⁴ = 2401`-element box) and the exact
stationarity-vector values (`stationarity_vals`, `no_equal_multiplier`,
`directional_nonzero`).  The *interpretation* — that this refutes necessity of
continuous KKT stationarity for the integer problem — is documented here, not
kernel-checked (it is the standard Lagrange/KKT consequence for concave maximization
over an affine simplex).  This is exactly why the discrete Graver certificate of
`AssemblyP1.SeparableConvexGraver` (`graver_optimal_iff_no_improving`) is the correct
optimality tool: it is necessary **and** sufficient on the integer fiber and never
asks for a vanishing gradient.

**Scope:** no duplication of #257's integer-kernel conformal-minimal existence proof,
of #261's historical signed-graph adapter, or of #258's feasible-set enumeration
(`FixedXExactML.lean`, imported nowhere here); the AAABBB spectrum values are restated
as literals with their provenance cited above.  The historical candidate adapter stays
OPEN.
-/

namespace AssemblyP1.KKTGap263

open Finset BigOperators

/-- The observed read-count vector `x = [3,1,2,1]` (board #259 comment), in
`AA, AB, BB, BA` order. -/
def obs : Fin 4 → ℕ := ![3, 1, 2, 1]

/-- The AAABBB truth spectrum `d = [2,1,2,1]` (`B1` of `FixedXExactML.lean`). -/
def truth : Fin 4 → ℕ := ![2, 1, 2, 1]

/-- The truth spectrum as box elements. -/
def truthFin : Fin 4 → Fin 7 := ![2, 1, 2, 1]

/-- External read count `N = 6` (= genome length `G`). -/
def N : ℕ := 6

/-- Per-type trial count `n = 6`. -/
def n : ℕ := 6

/-- The `c`-dependent part of the fixed-external-`N` product-binomial likelihood
`∏ᵢ C(n, xᵢ) * (cᵢ/N)^xᵢ * (1 - cᵢ/N)^(n-xᵢ)`, as an exact natural number. -/
def score (c : Fin 4 → ℕ) : ℕ :=
  ∏ i, (c i) ^ (obs i) * (N - c i) ^ (n - obs i)

/-- The truth scores `S(B1) = 5120000000000`. -/
theorem score_truth : score truth = 5120000000000 := by decide

set_option maxRecDepth 100000 in
/-- **Discrete unique maximality (issue #263/259 witness).**  Over the whole sum-6
count fiber in the `{0,…,6}⁴` box, the truth uniquely maximizes `score`. -/
theorem kktGap_uniqueMax :
    ∀ c : Fin 4 → Fin 7, (∑ i, (c i : ℕ)) = 6 →
      score (fun i => (c i : ℕ)) ≤ score truth ∧
        (score (fun i => (c i : ℕ)) = score truth → c = truthFin) := by
  decide

/-- Residual numerators `rᵢ = xᵢ * (N - dᵢ) - (n - xᵢ) * dᵢ` of the stationarity vector
at the truth (common denominator `dᵢ * (N - dᵢ)` per coordinate). -/
def resid : Fin 4 → ℤ := fun i => (obs i : ℤ) * ((N : ℤ) - (truth i : ℤ))
  - (((n : ℤ) - (obs i : ℤ)) * (truth i : ℤ))

/-- The residual numerators at the truth are `[6, 0, 0, 0]`. -/
theorem resid_vals : resid = ![6, 0, 0, 0] := by decide

/-- The exact stationarity vector `gᵢ = rᵢ / (dᵢ * (N - dᵢ))` at the truth. -/
def statVec : Fin 4 → ℚ := ![3 / 4, 0, 0, 0]

/-- The stationarity vector equals the residual-over-denominator formula. -/
theorem statVec_vals : ∀ i, statVec i
    = (resid i : ℚ) / ((truth i : ℚ) * ((N : ℚ) - (truth i : ℚ))) := by
  intro i
  fin_cases i <;> norm_num [statVec, resid, obs, truth, N, n]

/-- No Lagrange multiplier fits: the partials are not all equal, so continuous KKT
stationarity fails at the discrete unique maximizer. -/
theorem no_equal_multiplier : ¬ ∃ lam : ℚ, ∀ i, statVec i = lam := by
  rintro ⟨lam, h⟩
  have h0 := h 0
  have h1 := h 1
  norm_num [statVec] at h0 h1
  linarith

/-- A mass-preserving integer direction. -/
def dirV : Fin 4 → ℤ := ![1, 0, -1, 0]

/-- The direction preserves total mass. -/
theorem dirV_sum : ∑ i, dirV i = 0 := by decide

/-- The directional derivative along `dirV` is `3 / 4 ≠ 0`. -/
theorem directional_nonzero : ∑ i, (dirV i : ℚ) * statVec i = 3 / 4 := by
  simp only [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, dirV, statVec]
  norm_num

end AssemblyP1.KKTGap263
