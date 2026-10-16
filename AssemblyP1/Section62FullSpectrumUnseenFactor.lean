import Mathlib

/-!
# §6.1 full-spectrum likelihood: the unobserved-molecule factor (#284)

Medvedev–Brudno, *Maximum Likelihood Genome Assembly* (2009), §6.1 defines the
global read-count likelihood as the multinomial over **all `4^k` k-molecule
outcomes**, then approximates it by the product of the individual per-molecule
binomials

    L ≈ ∏_i C(n, x_i) (d_i / N)^{x_i} (1 − d_i / N)^{n − x_i},

where `x_i` is the observed count of molecule `i`, `d_i` its copy count in the
candidate genome `D`, `N = N(D)` the (known) genome length, and `n` the number of
reads.  Crucially the product ranges over *all* molecule classes, including the
unobserved ones (`x_i = 0`).  For such a class with `0 < d_i < N` the factor

    (1 − d_i / N)^n < 1

is a **strict penalty**, so a surrogate that drops unobserved classes overstates
the candidate's likelihood.

The `Section62NonSpelledFlow` non-spellable flow countermodel of `#214` exploits
exactly this gap: its circuit `AAA → AAA → AAT → TAA → AAA` spells the circular
genome `D = AAATA`, whose complete length-3 spectrum contains the *unobserved*
molecule `ATA` once.  The flow's observed-vertex surrogate omits `ATA`'s penalty.

This module kernel-checks the exact algebra for that instance.  With the four
length-3 binary molecule classes `AAA, AAT, ATA, TAA`, genome length `N = 5`,
`n = 4` reads, and sample `x = (AAA:2, AAT:1, ATA:0, TAA:1)`:

* truth `S = AAATT` has spectrum `dS = (1, 2, 0, 2)`;
* the non-spellable candidate `D = AAATA` has spectrum `dD = (2, 1, 1, 1)`.

Then, with constants (the binomial coefficients `C(n, x_i)`) dropped, which
cancel in a ratio,

* observed-vertex surrogate ratio `L_obs(D)/L_obs(S) = 256/81 > 1`;
* unobserved-`ATA` factor ratio `= (1 − 1/5)^4 = 256/625 < 1`;
* **full** §6.1 ratio `L(D)/L(S) = (256/81) · (256/625) = 65536/50625 > 1`.

So the non-spellable candidate still beats the truth under the *full-spectrum*
§6.1 objective, but by a different margin than the observed-vertex surrogate:
the unobserved molecule's penalty is a real, quantified correction.  This is the
explicit full §6.1 unseen-factor identity requested for `#284`; the general
RC/oriented indexing question (`4^k` k-mers versus reverse-complement classes)
is recorded as open in the accompanying note and is **not** silently resolved.
-/

namespace AssemblyP1.Section62FullSpectrumUnseenFactor

/-- The per-molecule §6.1 binomial factor with the binomial coefficient `C(n, x)`
dropped (it cancels in every ratio).  `N` is the candidate genome length, `n` the
number of reads, `x` the observed count and `d` the candidate copy count. -/
def factor (N n x d : ℕ) : ℚ :=
  ((d : ℚ) / N) ^ x * (1 - (d : ℚ) / N) ^ (n - x)

/-- The four length-3 binary molecule classes `AAA, AAT, ATA, TAA`, indexed
`0, 1, 2, 3`. -/
abbrev Mol := Fin 4

/-- Truth `S = AAATT`: complete length-3 spectrum `(AAA:1, AAT:2, ATA:0, TAA:2)`. -/
def dS : Mol → ℕ := ![1, 2, 0, 2]

/-- Non-spellable candidate `D = AAATA`: spectrum `(AAA:2, AAT:1, ATA:1, TAA:1)`. -/
def dD : Mol → ℕ := ![2, 1, 1, 1]

/-- Observed sample `x = (AAA:2, AAT:1, ATA:0, TAA:1)`. -/
def x : Mol → ℕ := ![2, 1, 0, 1]

/-- The full §6.1 surrogate over the four classes (constants dropped). -/
def surrogate (N n : ℕ) (x d : Mol → ℕ) : ℚ :=
  factor N n (x 0) (d 0) * factor N n (x 1) (d 1) *
    factor N n (x 2) (d 2) * factor N n (x 3) (d 3)

/-- The observed-vertex surrogate: the same product restricted to the classes with
`x_i > 0` (`AAA, AAT, TAA`). -/
def surrogateObs (N n : ℕ) (x d : Mol → ℕ) : ℚ :=
  factor N n (x 0) (d 0) * factor N n (x 1) (d 1) * factor N n (x 3) (d 3)

/-- The observed-vertex surrogate ratio `L_obs(D)/L_obs(S) = 256/81`. -/
theorem observed_ratio : surrogateObs 5 4 x dD / surrogateObs 5 4 x dS = 256 / 81 := by
  norm_num [surrogateObs, factor, dS, dD, x]

/-- The unobserved-`ATA` factor ratio `(1 − 1/5)^4 / (1 − 0/5)^4 = 256/625`. -/
theorem unseen_factor_ratio : factor 5 4 (x 2) (dD 2) / factor 5 4 (x 2) (dS 2) = 256 / 625 := by
  norm_num [factor, dS, dD, x]

/-- The unobserved factor is a strict contraction: `(1 − 1/5)^4 = 256/625 < 1`. -/
theorem unseen_factor_lt_one : factor 5 4 (x 2) (dD 2) / factor 5 4 (x 2) (dS 2) < 1 := by
  rw [unseen_factor_ratio]; norm_num

/-- **The explicit full §6.1 identity for the instance.**  The full-spectrum
likelihood ratio factors as the observed-vertex surrogate ratio times the
unobserved-`ATA` factor ratio. -/
theorem full_eq_observed_mul_unseen :
    surrogate 5 4 x dD / surrogate 5 4 x dS =
      (surrogateObs 5 4 x dD / surrogateObs 5 4 x dS) *
        (factor 5 4 (x 2) (dD 2) / factor 5 4 (x 2) (dS 2)) := by
  norm_num [surrogate, surrogateObs, factor, dS, dD, x]

/-- **The full §6.1 ratio.**  `L(D)/L(S) = 65536/50625`. -/
theorem full_ratio : surrogate 5 4 x dD / surrogate 5 4 x dS = 65536 / 50625 := by
  norm_num [surrogate, factor, dS, dD, x]

/-- The non-spellable candidate strictly beats the truth under the **full** §6.1
objective, with the unobserved-molecule penalty included. -/
theorem full_ratio_gt_one : 1 < surrogate 5 4 x dD / surrogate 5 4 x dS := by
  rw [full_ratio]; norm_num

/-- The observed-vertex surrogate **overstates** the candidate relative to the
full-spectrum objective: the full ratio is strictly smaller than the
observed-only ratio. -/
theorem full_ratio_lt_observed_ratio :
    surrogate 5 4 x dD / surrogate 5 4 x dS <
      surrogateObs 5 4 x dD / surrogateObs 5 4 x dS := by
  rw [full_ratio, observed_ratio]
  norm_num

/-- The exact correction factor `65536/50625 ÷ (256/81) = 256/625`. -/
theorem correction_factor :
    (65536 / 50625 : ℚ) / (256 / 81) = 256 / 625 := by
  norm_num

/-! ## A general contraction lemma for the unobserved factor

For any genome length `N`, candidate copy count `d` with `0 < d < N`, and `n > 0`
reads, the unobserved-class factor `(1 − d/N)^n` is strictly below `1`.  This is
the general reason an observed-vertex surrogate overstates a candidate that
introduces a new unobserved molecule class. -/

theorem unseen_factor_contract {N d n : ℕ} (hd : 0 < d) (hdN : d < N) (hn : 0 < n) :
    (1 - (d : ℚ) / N) ^ n < 1 := by
  have hNpos : (0 : ℚ) < N := by
    have : 0 < N := lt_of_lt_of_le hd (le_of_lt hdN)
    exact_mod_cast this
  have hdN' : (d : ℚ) < N := by exact_mod_cast hdN
  have hbase_nonneg : (0 : ℚ) ≤ 1 - (d : ℚ) / N := by
    rw [sub_nonneg]
    exact div_le_one_of_le₀ (by linarith) (le_of_lt hNpos)
  have hbase_lt : 1 - (d : ℚ) / N < 1 := by
    rw [sub_lt_self_iff]
    exact div_pos (by exact_mod_cast hd) hNpos
  calc
    (1 - (d : ℚ) / N) ^ n < 1 ^ n :=
      pow_lt_pow_left₀ hbase_lt hbase_nonneg (Nat.pos_iff_ne_zero.mp hn)
    _ = 1 := one_pow n

#print axioms observed_ratio
#print axioms unseen_factor_ratio
#print axioms unseen_factor_lt_one
#print axioms full_eq_observed_mul_unseen
#print axioms full_ratio
#print axioms full_ratio_gt_one
#print axioms full_ratio_lt_observed_ratio
#print axioms unseen_factor_contract

end AssemblyP1.Section62FullSpectrumUnseenFactor
