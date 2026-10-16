import Mathlib
import AssemblyP1.Section62BinomialRealGenomeInversion

/-!
# Power monotonicity of the exact-iid vs §6.1 ranking inversion (#259)

The merged witness `AssemblyP1.Section62BinomialRealGenomeInversion` shows that
at sample size `n = 1` (a single `00` read) the exact iid/multinomial likelihood
and MB09 §6.1's product of marginal binomial likelihoods rank two genuine
circular genomes of equal fixed length `N = 100` differently:

* `A = 0^51 1^49` has oriented circular two-read counts `(50, 1, 1, 48)`;
* `B = 0^50 1^18 (01)^16` has oriented circular two-read counts
  `(49, 17, 17, 17)`.

The exact probability of the single read `00` is `50 / 100` under `A` and
`49 / 100` under `B`, so the exact likelihood favors `A`.  The full four-word
§6.1 product-binomial score keeps the three zero-count factors
`(1 - d_i / N)` and gives `50 * 99 * 99 * 52 / 100 ^ 4 = 25482600 / 100 ^ 4`
under `A` versus `49 * 83 ^ 3 / 100 ^ 4 = 28017563 / 100 ^ 4` under `B`, so
the surrogate favors `B`.

This module proves the **power-monotonicity corollary** recorded by the
research assistant on 2026-10-15T04:08Z: the inversion is not confined to
`n = 1`.  For *every* sample size `n ≥ 1` consisting of `n` identical `00`
reads:

* the exact iid/multinomial likelihood still favors `A`, because
  `(50 / 100) ^ n > (49 / 100) ^ n`;
* the full-alphabet §6.1 product-binomial surrogate still favors `B`, because
  `(25482600 / 100 ^ 4) ^ n < (28017563 / 100 ^ 4) ^ n`.

Both are stated as exact rational comparisons over `ℚ`.  The per-read base
inequalities are the merged kernel-checked facts `exact_prefers_A` and
`surrogate_prefers_B`; the `n`-read statements are their strict power
monotonicity.

## What is *not* claimed

This is a statement about the two **base inequalities**, not about typical
samples.  A sample consisting of `n` identical `00` reads has probability
`(1/2) ^ n` under `A`, so it is exponentially rare: the corollary does **not**
assert that the §6.1 surrogate misranks `A` and `B` on typical high-coverage
data, only that the ranking reversal persists at every nominal sample size on
this explicit family.  The surrogate remains deliberately distinct from the
exact joint read law (#256) and from the §6.2 bidirected flows (#260/#261).
-/

namespace AssemblyP1.Section62BinomialPowerMonotonicity

open AssemblyP1.Section62BinomialRealGenomeInversion

/-- Exact iid probability that `n` independent reads from genome `A` are all
the oriented word `00`.  Because the observed count vector `(n, 0, 0, 0)`
concentrates on a single read type, this equals the exact joint multinomial
probability of that count vector. -/
noncomputable def exactIidA (n : ℕ) : ℚ :=
  (exactNumA : ℚ) ^ n / (100 : ℚ) ^ n

/-- Exact iid probability that `n` independent reads from genome `B` are all
the oriented word `00`. -/
noncomputable def exactIidB (n : ℕ) : ℚ :=
  (exactNumB : ℚ) ^ n / (100 : ℚ) ^ n

/-- Full-alphabet MB09 §6.1 product-of-marginal-binomials score for the count
vector `(n, 0, 0, 0)` under genome `A`.  The score is the `n`-th power of the
single-read score `surrogateNumA / 100 ^ 4`, because every read contributes the
same `00` factor `p_00` and the same three zero-count factors `(1 - p_i)`. -/
noncomputable def surrogateA (n : ℕ) : ℚ :=
  (surrogateNumA : ℚ) ^ n / (100 : ℚ) ^ (4 * n)

/-- Full-alphabet MB09 §6.1 product-of-marginal-binomials score for the count
vector `(n, 0, 0, 0)` under genome `B`. -/
noncomputable def surrogateB (n : ℕ) : ℚ :=
  (surrogateNumB : ℚ) ^ n / (100 : ℚ) ^ (4 * n)

/-- The single-read scores agree with the merged witness: `exactIidA 1` is
`50 / 100` and `exactIidB 1` is `49 / 100`. -/
theorem exactIidA_one : exactIidA 1 = (50 : ℚ) / 100 := by
  norm_num [exactIidA, exactNumA]

theorem exactIidB_one : exactIidB 1 = (49 : ℚ) / 100 := by
  norm_num [exactIidB, exactNumB]

/-- The single-read §6.1 scores agree with the merged integer numerators. -/
theorem surrogateA_one : surrogateA 1 = (25482600 : ℚ) / 100 ^ 4 := by
  norm_num [surrogateA, surrogateNumA]

theorem surrogateB_one : surrogateB 1 = (28017563 : ℚ) / 100 ^ 4 := by
  norm_num [surrogateB, surrogateNumB]

/-- **Exact iid power monotonicity.**  For every `n ≥ 1` the exact iid
likelihood of `n` identical `00` reads is strictly larger under `A` than under
`B`.  The proof is strict power monotonicity of the merged base inequality
`exactNumB < exactNumA`. -/
theorem exact_prefers_A_all_n (n : ℕ) (hn : 1 ≤ n) : exactIidB n < exactIidA n := by
  unfold exactIidB exactIidA
  rw [div_lt_div_iff_of_pos_right (by positivity)]
  gcongr
  decide

/-- **§6.1 product-binomial power monotonicity.**  For every `n ≥ 1` the
full-alphabet MB09 §6.1 product-binomial score of `n` identical `00` reads is
strictly smaller under `A` than under `B`.  The proof is strict power
monotonicity of the merged base inequality
`surrogateNumA < surrogateNumB`, keeping the three zero-count factors. -/
theorem surrogate_prefers_B_all_n (n : ℕ) (hn : 1 ≤ n) : surrogateA n < surrogateB n := by
  unfold surrogateA surrogateB
  rw [div_lt_div_iff_of_pos_right (by positivity)]
  gcongr
  decide

/-- **Ranking inversion at every sample size.**  For every `n ≥ 1`, `n`
identical `00` reads make the exact iid/multinomial likelihood favor the true
circular genome `A` while the full-alphabet §6.1 product-binomial surrogate
favors the competitor `B`. -/
theorem ranking_inversion_all_n (n : ℕ) (hn : 1 ≤ n) :
    exactIidB n < exactIidA n ∧ surrogateA n < surrogateB n :=
  ⟨exact_prefers_A_all_n n hn, surrogate_prefers_B_all_n n hn⟩

/-- The `n = 1` case of the corollary is exactly the merged witness. -/
theorem ranking_inversion_one :
    exactIidB 1 < exactIidA 1 ∧ surrogateA 1 < surrogateB 1 :=
  ranking_inversion_all_n 1 le_rfl

/-- Exact iid likelihood ratio: the exact score ratio is `(50 / 49) ^ n > 1`,
so the exact model's preference for `A` strengthens (in ratio) with `n`. -/
theorem exact_ratio_gt_one (n : ℕ) (hn : 1 ≤ n) : 1 < exactIidA n / exactIidB n := by
  have hB : 0 < exactIidB n := by
    unfold exactIidB
    exact div_pos (pow_pos (by norm_num [exactNumB]) n) (by positivity)
  rw [one_lt_div hB]
  exact exact_prefers_A_all_n n hn

end AssemblyP1.Section62BinomialPowerMonotonicity
