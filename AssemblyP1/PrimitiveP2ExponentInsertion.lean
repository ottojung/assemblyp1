import AssemblyP1.PrimitiveP2UniformSeparation

/-!
# Insertion affinity for the one-symbol-insertion extremal pair (issue #265)

Additive supporting lemma for the exact sharpened formula

    gamma(B) = 1 - sqrt((B-1)/B)

of `docs/restricted-vs-unrestricted-exponent-265.md`.  It isolates the
*affine* half of the extremal-pair computation: whenever a second read law is
a convex combination of the truth's read law with a point mass at one new word
that the truth does not produce, the Hellinger affinity is exactly the square
root of the surviving weight.

The combinatorial fact that the one-symbol insertion `D = S + last(S)` has
exactly this shape (its read law is `(G/(G+1)) p_S + (1/(G+1)) delta_{w*}` for
a single word `w*` absent from `S`) is a finite multiset statement that is
verified exactly, by exact rational arithmetic, in
`scripts/verify_exponent_265.py` (check 4) for every enumerated extremal pair.
It is deliberately *not* asserted as a Lean hypothesis-free theorem here; the
Python verifier is the exact witness for that combinatorial half, and this
module is the exact kernel-checked half.

No `axiom`, `sorry` or `admit` is introduced, and no existing definition is
changed.  The only kernel axioms are `propext`, `Classical.choice` and
`Quot.sound`.
-/

namespace AssemblyP1.PrimitiveP2ExponentInsertion

open AssemblyP1.FiniteReadRecovery
open Finset
open scoped Classical

variable {W : Type*} [Fintype W]

/-- **Affine insertion affinity.** If `q = (1 - ε) p + ε δ_{wstar}` and `p` puts
no mass on `wstar`, then the Hellinger affinity of `p` and `q` is exactly
`sqrt(1 - ε)`.  In particular `1 - hellinger p q = 1 - sqrt(1 - ε)`.

This is the exact affinity of the one-symbol-insertion extremal pair: the
insertion keeps every existing read word count and adds exactly one new word,
so `q` is a convex combination of `p` with a point mass at that new word. -/
theorem hellinger_convex_delta (p q : W → ℝ) (hp : IsPmf p)
    (ε : ℝ) (hε1 : ε ≤ 1) (wstar : W)
    (hq : q = fun w => (1 - ε) * p w + ε * (if w = wstar then 1 else 0))
    (hpw : p wstar = 0) :
    hellinger p q = Real.sqrt (1 - ε) := by
  have hp0 : ∀ w, 0 ≤ p w := hp.1
  have h1mε : 0 ≤ 1 - ε := by linarith
  have hterm : ∀ w, Real.sqrt (p w * q w) = Real.sqrt (1 - ε) * p w := by
    intro w
    rw [hq]
    beta_reduce
    by_cases hw : w = wstar
    · subst hw
      simp [hpw]
    · have hif : (if w = wstar then (1 : ℝ) else 0) = 0 := by simp [hw]
      rw [hif, mul_zero, add_zero]
      have h : p w * ((1 - ε) * p w) = (1 - ε) * (p w) ^ 2 := by ring
      rw [h, Real.sqrt_mul h1mε ((p w) ^ 2), Real.sqrt_sq (hp0 w)]
  calc hellinger p q
      = ∑ w : W, Real.sqrt (p w * q w) := rfl
    _ = ∑ w : W, Real.sqrt (1 - ε) * p w :=
          Finset.sum_congr rfl (fun w _ => hterm w)
    _ = Real.sqrt (1 - ε) * ∑ w : W, p w := by rw [Finset.mul_sum]
    _ = Real.sqrt (1 - ε) * 1 := by rw [hp.2]
    _ = Real.sqrt (1 - ε) := by ring

/-- The complementary form: `1 - hellinger p q = 1 - sqrt(1 - ε)`. -/
theorem one_sub_hellinger_convex_delta (p q : W → ℝ) (hp : IsPmf p)
    (ε : ℝ) (hε1 : ε ≤ 1) (wstar : W)
    (hq : q = fun w => (1 - ε) * p w + ε * (if w = wstar then 1 else 0))
    (hpw : p wstar = 0) :
    1 - hellinger p q = 1 - Real.sqrt (1 - ε) := by
  rw [hellinger_convex_delta p q hp ε hε1 wstar hq hpw]

/-- **Instantiated to the one-symbol insertion.** For a truth read law `p` of
length `G` and an insertion read law `q` of length `G+1` that is
`(G/(G+1)) p + (1/(G+1)) δ_{wstar}` with `p(wstar) = 0`, the Hellinger gap is
exactly `1 - sqrt(G/(G+1)) = 1 - sqrt((B-1)/B)` when `B = G+1`.

The read-law relation is the finite multiset statement verified exactly in
`scripts/verify_exponent_265.py`. -/
theorem one_sub_hellinger_insertion (p q : W → ℝ) (hp : IsPmf p)
    (G : ℕ) (hG : 0 < G) (wstar : W)
    (hq : q = fun w => ((G : ℝ) / (G + 1)) * p w
      + ((1 : ℝ) / (G + 1)) * (if w = wstar then 1 else 0))
    (hpw : p wstar = 0) :
    1 - hellinger p q = 1 - Real.sqrt ((G : ℝ) / (G + 1)) := by
  have hGpos : (0 : ℝ) < (G : ℝ) := by exact_mod_cast hG
  have hε : (G : ℝ) / (G + 1) = 1 - (1 : ℝ) / ((G : ℝ) + 1) := by
    field_simp
    ring
  have hεle : (1 : ℝ) / ((G : ℝ) + 1) ≤ 1 := by
    have h : (1 : ℝ) / ((G : ℝ) + 1) < 1 := by
      exact (div_lt_one (by linarith : (0 : ℝ) < (G : ℝ) + 1)).mpr (by linarith)
    linarith
  have hq' : q = fun w => (1 - ((1 : ℝ) / ((G : ℝ) + 1))) * p w
      + ((1 : ℝ) / ((G : ℝ) + 1)) * (if w = wstar then 1 else 0) := by
    rw [hq]
    funext w
    rw [hε]
  have hmain := one_sub_hellinger_convex_delta p q hp
    ((1 : ℝ) / ((G : ℝ) + 1)) hεle wstar hq' hpw
  rw [← hε] at hmain
  exact hmain

/-- `1 - sqrt(G/(G+1)) >= 1/(2(G+1))` for `G >= 1`, so the extremal pair
attains separation `>= 1/(2B)` with `B = G+1`. -/
theorem insertion_gap_ge_half_over_succ (G : ℕ) (hG : 0 < G) :
    1 / (2 * ((G : ℝ) + 1)) ≤ 1 - Real.sqrt ((G : ℝ) / (G + 1)) := by
  have hGpos : (0 : ℝ) < (G : ℝ) := by exact_mod_cast hG
  have hpos : (0 : ℝ) < (G : ℝ) + 1 := by linarith
  have h1x : (0 : ℝ) ≤ (G : ℝ) / (G + 1) := by positivity
  have h1x' : (G : ℝ) / (G + 1) ≤ 1 := by
    rw [div_le_iff₀ hpos]
    linarith
  have hsqrt_le_one : Real.sqrt ((G : ℝ) / (G + 1)) ≤ 1 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by simpa using h1x'⟩
  -- 1 - sqrt(x) = (1 - x) / (1 + sqrt x)
  have hdiff : 1 - Real.sqrt ((G : ℝ) / (G + 1))
      = (1 - (G : ℝ) / (G + 1)) / (1 + Real.sqrt ((G : ℝ) / (G + 1))) := by
    have hx : Real.sqrt ((G : ℝ) / (G + 1)) ^ 2 = (G : ℝ) / (G + 1) :=
      Real.sq_sqrt h1x
    have hden : (1 : ℝ) + Real.sqrt ((G : ℝ) / (G + 1)) ≠ 0 := by positivity
    rw [eq_div_iff hden]
    calc (1 - Real.sqrt ((G : ℝ) / (G + 1))) * (1 + Real.sqrt ((G : ℝ) / (G + 1)))
        = 1 - Real.sqrt ((G : ℝ) / (G + 1)) ^ 2 := by ring
      _ = 1 - (G : ℝ) / (G + 1) := by rw [hx]
  have hnum : (1 : ℝ) - (G : ℝ) / (G + 1) = (1 : ℝ) / ((G : ℝ) + 1) := by
    field_simp
    ring
  have hden_le_two : (1 : ℝ) + Real.sqrt ((G : ℝ) / (G + 1)) ≤ 2 := by linarith
  have hden_pos : (0 : ℝ) < (1 : ℝ) + Real.sqrt ((G : ℝ) / (G + 1)) := by positivity
  calc (1 : ℝ) - Real.sqrt ((G : ℝ) / (G + 1))
      = ((1 : ℝ) / ((G : ℝ) + 1)) / ((1 : ℝ) + Real.sqrt ((G : ℝ) / (G + 1))) := by
        rw [hdiff, hnum]
    _ ≥ ((1 : ℝ) / ((G : ℝ) + 1)) / 2 :=
        div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ (1 : ℝ) / ((G : ℝ) + 1))
          hden_pos hden_le_two
    _ = (1 : ℝ) / (2 * ((G : ℝ) + 1)) := by field_simp

end AssemblyP1.PrimitiveP2ExponentInsertion
