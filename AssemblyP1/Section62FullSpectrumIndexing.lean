import Mathlib

/-!
# §6.1 full-spectrum identity and the molecule-class indexing decision (#284)

Medvedev–Brudno (2009) §6.1 defines the global read-count likelihood over the
`4^k` k-molecule outcomes and approximates it by the product of per-molecule
binomials

    L ≈ ∏_i C(n, x_i) (d_i / N)^{x_i} (1 − d_i / N)^{n − x_i}.

## The indexing decision (oriented k-mers versus reverse-complement classes)

MB09 §3.1 models a DNA *molecule* as an unordered reverse-complement strand pair,
and §6.1 calls the index a "k-molecule".  The repository therefore **chooses** to
index by **reverse-complement classes**, not oriented k-mers: a non-palindromic
oriented k-mer `w` and its reverse complement `rc w` are the *same* molecule, and
its class frequency is the sum `c_S(w) + c_S(rc w)` counted once.  Consequently
the number of classes is `(#oriented + #palindromes)/2`, where `#oriented = 4^k`
and `#palindromes = 0` for odd `k`, `4^{k/2}` for even `k` (Burnside on the
involution `rc`).  For the repository's binary length-3 instance this is
`(2^3 + 0)/2 = 4`, matching `Mol = Fin 4` of `Section62FullSpectrumUnseenFactor`.

This is an explicit **modeling decision, not a source fact**: MB09 §6.1 states
literally that "There are `4^k` such variables", which is the *oriented* k-mer
count, whereas the unordered RC classes number `(4^k + f_k)/2` (about half).  The
two readings give different universes and objectives; the decision is recorded in
`docs/section62-global-circular-and-unseen-factor-284.md` §3.  The general
Burnside orbit count for arbitrary `k` remains open.

The general involution orbit-count `2 * #classes = #oriented + #fixed` is stated
below for the concrete binary length-3 instance (`rc3`, kernel-checked by
`decide`); the fully general orbit count is the standard Burnside argument.

## The full-spectrum identity

Independently of the indexing decision, the §6.1 product over a finite class
universe splits exactly into the observed-class product times the unseen-class
product:

    fullProduct = observedProduct * unseenProduct,

and an unseen class (`x_c = 0`) contributes the count-zero factor `1` when
`d_c = 0`, and the strict penalty `(1 − d_c/N)^n < 1` when `0 < d_c < N`.  This
is what makes the §6.2 observed-vertex flow surrogate genuinely different from
the complete §6.1 objective (see `Section62FullSpectrumUnseenFactor`).
-/

namespace AssemblyP1.Section62FullSpectrumIndexing

set_option maxRecDepth 100000

open Finset

variable {κ : Type}

/-- The per-class §6.1 binomial factor with the binomial coefficient `C(n, x)`
dropped (it cancels in every ratio). -/
def factor (N n x d : ℕ) : ℚ :=
  ((d : ℚ) / N) ^ x * (1 - (d : ℚ) / N) ^ (n - x)

/-- The full §6.1 product over a finite class universe. -/
def fullProduct [Fintype κ] (N n : ℕ) (x d : κ → ℕ) : ℚ :=
  ∏ c, factor N n (x c) (d c)

/-- The observed-class product: the same product restricted to classes with a
positive observed count. -/
def observedProduct [Fintype κ] [DecidableEq κ] (N n : ℕ) (x d : κ → ℕ) : ℚ :=
  ∏ c ∈ Finset.univ.filter (fun c => 0 < x c), factor N n (x c) (d c)

/-- The unseen-class product: the same product restricted to classes with zero
observed count. -/
def unseenProduct [Fintype κ] [DecidableEq κ] (N n : ℕ) (x d : κ → ℕ) : ℚ :=
  ∏ c ∈ Finset.univ.filter (fun c => x c = 0), factor N n (x c) (d c)

/-- **The full-spectrum split.**  The §6.1 product over all classes factors
exactly as the observed-class product times the unseen-class product. -/
theorem full_eq_observed_mul_unseen [Fintype κ] [DecidableEq κ]
    (N n : ℕ) (x d : κ → ℕ) :
    fullProduct N n x d = observedProduct N n x d * unseenProduct N n x d := by
  unfold fullProduct observedProduct unseenProduct
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ) (fun c => 0 < x c)]
  have hf : (Finset.univ.filter (fun c => ¬ 0 < x c)) =
      Finset.univ.filter (fun c => x c = 0) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [hf]

/-- An unseen class with zero candidate count contributes the factor `1`. -/
theorem factor_zero_zero (N n : ℕ) : factor N n 0 0 = 1 := by
  unfold factor
  simp

/-- **Unseen count-zero factors are exactly `1`.**  If every unseen class has zero
candidate count, the unseen product is `1`, so the full §6.1 product equals the
observed-class product.  This is the sense in which the count-zero factors are
"unseen factors of `1`" eliminated by the repository's `lik_eq_relevant_prod`. -/
theorem unseenProduct_eq_one [Fintype κ] [DecidableEq κ] (N n : ℕ) (x d : κ → ℕ)
    (h : ∀ c, x c = 0 → d c = 0) : unseenProduct N n x d = 1 := by
  unfold unseenProduct
  apply Finset.prod_eq_one
  intro c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
  rw [hc, h c hc, factor_zero_zero]

/-- **The full-spectrum identity for zero unseen counts.**  If every unseen class
has zero candidate count, the full §6.1 product reduces to the observed-class
product. -/
theorem full_eq_observed_of_zero_unseen [Fintype κ] [DecidableEq κ]
    (N n : ℕ) (x d : κ → ℕ) (h : ∀ c, x c = 0 → d c = 0) :
    fullProduct N n x d = observedProduct N n x d := by
  rw [full_eq_observed_mul_unseen, unseenProduct_eq_one N n x d h, mul_one]

/-- **The unseen factor is a strict penalty.**  For a class with `x = 0` and
`0 < d < N` the §6.1 factor `(1 − d/N)^n` is strictly below `1`. -/
theorem factor_zero_lt_one {N d n : ℕ} (hd : 0 < d) (hdN : d < N) (hn : 0 < n) :
    factor N n 0 d < 1 := by
  unfold factor
  simp only [pow_zero, one_mul, Nat.sub_zero]
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

/-! ## The molecule-class indexing decision: the binary length-3 instance

The oriented binary length-3 k-mers are `Fin 3 → Bool` (`8 = 2^3` of them).  The
reverse-complement involution `rc3` complements and reverses the word.  There are
no palindromes for odd length, so the number of reverse-complement classes is
`(2^3 + 0)/2 = 4`; the kernel-checked `rc3_orbit_count` below is exactly this
orbit count, and the four representatives are `AAA, AAT, ATA, TAA`, matching
`Section62FullSpectrumUnseenFactor.Mol = Fin 4`. -/

/-- Reverse complement on binary length-3 words: complement every symbol and
reverse the order. -/
def rc3 (w : Fin 3 → Bool) : Fin 3 → Bool :=
  ![!w 2, !w 1, !w 0]

/-- `rc3` is an involution. -/
theorem rc3_involutive : Function.Involutive rc3 := by
  intro w
  funext i
  fin_cases i <;> simp [rc3]

/-- The set of reverse-complement orbits of the binary length-3 words. -/
def rc3Orbits : Finset (Finset (Fin 3 → Bool)) :=
  Finset.univ.image (fun w => ({w, rc3 w} : Finset (Fin 3 → Bool)))

/-- **The binary length-3 orbit count.**  There are exactly `4` reverse-complement
classes, matching `(2^3 + 0)/2` and `Mol = Fin 4` of the §6.1 instance. -/
theorem rc3_orbit_count : rc3Orbits.card = 4 := by
  decide

/-- Every binary length-3 orbit has exactly two elements: there are no
palindromes at odd length. -/
theorem rc3_orbit_card_two : ∀ O ∈ rc3Orbits, O.card = 2 := by
  decide

#print axioms full_eq_observed_mul_unseen
#print axioms unseenProduct_eq_one
#print axioms full_eq_observed_of_zero_unseen
#print axioms factor_zero_lt_one
#print axioms rc3_involutive
#print axioms rc3_orbit_count
#print axioms rc3_orbit_card_two

end AssemblyP1.Section62FullSpectrumIndexing
