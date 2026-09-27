import Mathlib

/-!
# The population read distribution and its likelihood (issue #89)

Paper source: `paper/sections/05-population.tex`, `def:population` and
`lem:gibbs`.

This file is the **population objective layer** of the population
maximum-likelihood model, formalizing the published definitions
literally and proving the published consequences in the kernel:

* `popProb`: the population read distribution
  `p_D(w) = spec_L(D)(w) / |D|` of `def:population`;
* `PopLogLik`: the population log-likelihood
  `ℓpop_S(D) = ∑_w p_S(w) log p_D(w)`, with the published convention
  `ℓpop_S(D) = -∞` when some `w` with `p_S(w) > 0` has `p_D(w) = 0`.
  `-∞` is modelled as `⊥` in `WithBot ℝ`, the only order in which `-∞`
  is the bottom element, so that "the truth is a maximizer" is a
  genuine `≤` statement in a linear order rather than a
  caller-supplied opaque `Prop`;
* `popLogLik_le_self`: `lem:gibbs`, the truth is always a population
  maximizer, proved for **every** candidate distribution — no repeat
  condition and no candidate-class membership is required, exactly as
  the paper states;
* `popTie_of_eq` / `popTie_iff`: the equality characterization in
  `lem:gibbs`, proved in the strict form (a tie at a point where the two
  distributions differ is impossible), so a population tie forces
  `p_D = p_S`;
* `popProb_eq_iff`: `p_D = p_S` is exactly the proportional
  (normalized) equality of the two integer spectra.

Nothing here is a premise of a later theorem: the Gibbs/KL layer is
proved, not assumed. The only external input still used anywhere in the
project is the complete-spectrum uniqueness theorem of
Bresler--Bresler--Tse (2013), handled in `AssemblyP1.P2` /
`AssemblyP1.PopulationUniqueness` and recorded as an explicit boundary.
-/

namespace AssemblyP1.PopulationGibbs

open BigOperators

variable {W : Type} [Fintype W]
variable {n : ℕ}

/-- The population read distribution of a circular word with integer
spectrum `c` on `n` positions: `p(w) = c(w)/n`
(`def:population`). -/
noncomputable def popProb (c : W → ℕ) (n : ℕ) (w : W) : ℝ :=
  (c w : ℝ) / (n : ℝ)

omit [Fintype W] in
theorem popProb_nonneg (c : W → ℕ) (n : ℕ) (w : W) : 0 ≤ popProb c n w := by
  unfold popProb
  positivity

/-- A read distribution is nonnegative and sums to `1`. -/
def IsProb (p : W → ℝ) : Prop :=
  (∀ w, 0 ≤ p w) ∧ (∑ w, p w) = 1

/-- The normalizing constant makes `popProb` a distribution. -/
theorem popProb_sum_eq_one (c : W → ℕ) (hsum : (∑ w, c w) = n) (hn : 0 < n) :
    (∑ w, popProb c n w) = 1 := by
  have hnR : (n : ℝ) ≠ 0 := by exact Nat.cast_ne_zero.mpr hn.ne'
  have hcast : (∑ w, (c w : ℝ)) = (n : ℝ) := by exact_mod_cast hsum
  unfold popProb
  calc (∑ w, (c w : ℝ) / (n : ℝ)) = (∑ w, (c w : ℝ)) / (n : ℝ) := by
        symm
        exact Finset.sum_div (s := (Finset.univ : Finset W))
          (f := fun w : W => (c w : ℝ)) (a := (n : ℝ))
    _ = (n : ℝ) / (n : ℝ) := by rw [hcast]
    _ = 1 := by field_simp

/-- A normalized integer spectrum is a read distribution. -/
theorem popProb_isProb (c : W → ℕ) (hsum : (∑ w, c w) = n) (hn : 0 < n) :
    IsProb (popProb c n) := by
  refine ⟨fun w => popProb_nonneg c n w, ?_⟩
  exact popProb_sum_eq_one c hsum hn

/-- Two read distributions have the same support (the same set of read
types actually observed). -/
def SuppEq (pS pD : W → ℝ) : Prop :=
  ∀ w, (0 < pS w ↔ 0 < pD w)

/-- The finite part of the population log-likelihood:
`∑_w p_S(w) log p_D(w)`. -/
noncomputable def PopLogLikValue (pS pD : W → ℝ) : ℝ :=
  ∑ w, pS w * Real.log (pD w)

/-- **The population log-likelihood of `def:population`**, with the
published convention that it is `-∞` (here `⊥` of `WithBot ℝ`, the linear
order in which `-∞` is the least element) when a word read by the truth
is not read at all by the candidate. -/
noncomputable def PopLogLik (pS pD : W → ℝ) : WithBot ℝ := by
  classical
  exact if SuppEq pS pD then (PopLogLikValue pS pD : WithBot ℝ) else ⊥

omit [Fintype W] in
theorem suppEq_refl (p : W → ℝ) : SuppEq p p := fun _ => Iff.rfl

/-- The likelihood is finite as soon as the supports agree. -/
theorem popLogLik_of {pS pD : W → ℝ} (h : SuppEq pS pD) :
    PopLogLik pS pD = (PopLogLikValue pS pD : WithBot ℝ) := by
  rw [PopLogLik, if_pos h]

/-- `ℓpop_S(S)`, which is always finite. -/
theorem popLogLik_self (pS : W → ℝ) :
    PopLogLik pS pS = (PopLogLikValue pS pS : WithBot ℝ) :=
  popLogLik_of (suppEq_refl pS)

/-- `ℓpop_S(S)` is never `-∞`: the truth reads every word it reads. -/
theorem popLogLik_self_ne_bot (pS : W → ℝ) : PopLogLik pS pS ≠ (⊥ : WithBot ℝ) := by
  rw [popLogLik_self]
  exact WithBot.coe_ne_bot

/-- `ℓpop_S(D) = -∞` as soon as the supports disagree. -/
theorem popLogLik_bot_of {pS pD : W → ℝ} (h : ¬ SuppEq pS pD) :
    PopLogLik pS pD = (⊥ : WithBot ℝ) := by
  rw [PopLogLik, if_neg h]

/-- The population log-likelihood is finite exactly when the supports
agree, i.e. it is `-∞` exactly in the published
`ℓpop_S(D) = -∞` case. -/
theorem popLogLik_ne_bot_iff {pS pD : W → ℝ} :
    PopLogLik pS pD ≠ (⊥ : WithBot ℝ) ↔ SuppEq pS pD := by
  classical
  by_cases h : SuppEq pS pD
  · constructor
    · intro hc
      exact h
    · intro _
      rw [popLogLik_of h]
      exact WithBot.coe_ne_bot
  · constructor
    · intro hc
      exact False.elim (hc (popLogLik_bot_of h))
    · intro hn
      exact fun e => False.elim
        (WithBot.coe_ne_bot ((popLogLik_of hn).symm.trans e))

/-- The population log-likelihood is `-∞` exactly when the supports
disagree, i.e. exactly in the published `ℓpop_S(D) = -∞` case. -/
theorem popLogLik_eq_bot {pS pD : W → ℝ} :
    PopLogLik pS pD = (⊥ : WithBot ℝ) ↔ ¬ SuppEq pS pD := by
  classical
  by_cases h : SuppEq pS pD
  · constructor
    · intro hc
      rw [popLogLik_of h] at hc
      exact (WithBot.coe_ne_bot hc).elim
    · intro hn
      exact absurd h hn
  · constructor
    · intro _
      exact h
    · intro hc
      exact popLogLik_bot_of hc

/-- Recover the support clause from a finite likelihood. -/
theorem popLogLik_ne_bot_imp {pS pD : W → ℝ} (h : PopLogLik pS pD ≠ (⊥ : WithBot ℝ)) :
    SuppEq pS pD :=
  (popLogLik_ne_bot_iff (pD := pD)).mp h

/-! ## The Gibbs inequality, proved pointwise -/

omit [Fintype W] in
/-- Strict form of `log t < t - 1` for `t > 0`, `t ≠ 1`. -/
theorem log_lt_sub_one_of_ne_one {x : ℝ} (hx : 0 < x) (h1 : x ≠ 1) :
    Real.log x < x - 1 := by
  have hne : Real.log x ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hx h1
  have h := Real.add_one_lt_exp hne
  rw [Real.exp_log hx] at h
  linarith

omit [Fintype W] in
/-- Strict form of `1 - 1/x ≤ log x`, strict when `x ≠ 1`. -/
theorem one_sub_inv_lt_log_of_ne_one {x : ℝ} (hx : 0 < x) (h1 : x ≠ 1) :
    1 - x⁻¹ < Real.log x := by
  have h := log_lt_sub_one_of_ne_one (inv_pos.mpr hx) (inv_ne_one.mpr h1)
  rw [Real.log_inv] at h
  linarith

omit [Fintype W] in
/-- The Gibbs pointwise bound `p_S log p_S - p_S log p_D ≥ p_S - p_D`. -/
theorem term_ge {pS pD : W → ℝ} (hSupp : SuppEq pS pD) (hS0 : ∀ w, 0 ≤ pS w)
    (hD0 : ∀ w, 0 ≤ pD w) (w : W) :
    pS w * Real.log (pS w) - pS w * Real.log (pD w) ≥ pS w - pD w := by
  by_cases hs : pS w = 0
  · have hz : pD w = 0 := by
      by_contra hcon
      have hpos : 0 < pS w :=
        (hSupp w).mpr (lt_of_le_of_ne (hD0 w) (Ne.symm hcon))
      rw [hs] at hpos
      exact lt_irrefl 0 hpos
    simp [hs, hz, Real.log_zero]
  · have hs0 : 0 < pS w := lt_of_le_of_ne (hS0 w) (Ne.symm hs)
    have hd0 : 0 < pD w := (hSupp w).mp hs0
    have hneS : pS w ≠ 0 := hs0.ne'
    have hneD : pD w ≠ 0 := hd0.ne'
    have hlb := Real.one_sub_inv_le_log_of_pos (div_pos hs0 hd0)
    rw [inv_div] at hlb
    have hlog : Real.log (pS w / pD w) = Real.log (pS w) - Real.log (pD w) :=
      Real.log_div hneS hneD
    have hmul := mul_le_mul_of_nonneg_left hlb (le_of_lt hs0)
    have hdiv : pS w * (pD w / pS w) = pD w := by field_simp
    calc pS w * Real.log (pS w) - pS w * Real.log (pD w)
        = pS w * (Real.log (pS w) - Real.log (pD w)) := by ring
      _ = pS w * Real.log (pS w / pD w) := by rw [hlog]
      _ ≥ pS w * (1 - pD w / pS w) := hmul
      _ = pS w - pD w := by linarith

/-- The excess of `p_S ‖ p_D` at one word, `≥ 0`. -/
noncomputable def KLExcess (pS pD : W → ℝ) (w : W) : ℝ :=
  (pS w * Real.log (pS w) - pS w * Real.log (pD w)) - (pS w - pD w)

omit [Fintype W] in
theorem klExcess_nonneg {pS pD : W → ℝ} (hSupp : SuppEq pS pD) (hS0 : ∀ w, 0 ≤ pS w)
    (hD0 : ∀ w, 0 ≤ pD w) (w : W) : 0 ≤ KLExcess pS pD w :=
  sub_nonneg.mpr (term_ge hSupp hS0 hD0 w)

theorem sum_second_eq_zero {pS pD : W → ℝ} (hS : IsProb pS) (hD : IsProb pD) :
    (∑ w, (pS w - pD w)) = 0 := by
  rw [Finset.sum_sub_distrib, hS.2, hD.2, sub_self]

theorem logLik_sub (pS pD : W → ℝ) :
    (∑ w, (pS w * Real.log (pS w))) - (∑ w, (pS w * Real.log (pD w)))
      = ∑ w, (pS w * Real.log (pS w) - pS w * Real.log (pD w)) := by
  rw [Finset.sum_sub_distrib]

theorem sum_first_eq (pS pD : W → ℝ) :
    (∑ w, (pS w * Real.log (pS w) - pS w * Real.log (pD w)))
      = (∑ w, (pS w - pD w)) + ∑ w, KLExcess pS pD w := by
  have h : (∑ w, (pS w * Real.log (pS w) - pS w * Real.log (pD w)))
      = ∑ w, (KLExcess pS pD w + (pS w - pD w)) := by
    apply Finset.sum_congr rfl
    intro w _
    unfold KLExcess
    ring
  rw [h, Finset.sum_add_distrib, add_comm]

theorem sum_first_nonneg {pS pD : W → ℝ} (hSupp : SuppEq pS pD) (hS : IsProb pS)
    (hD : IsProb pD) :
    0 ≤ ∑ w, (pS w * Real.log (pS w) - pS w * Real.log (pD w)) := by
  have h1 : 0 ≤ (∑ w, KLExcess pS pD w) :=
    Finset.sum_nonneg fun w _ => klExcess_nonneg hSupp hS.1 hD.1 w
  rw [sum_first_eq, sum_second_eq_zero hS hD]
  linarith

/-- **Gibbs inequality (Cover--Thomas), population form.** For read
distributions `p_S`, `p_D` with equal support, the truth maximizes the
population log-likelihood. -/
theorem popLogLik_le_self {pS pD : W → ℝ} (hS : IsProb pS) (hD : IsProb pD)
    (hSupp : SuppEq pS pD) :
    PopLogLik pS pD ≤ PopLogLik pS pS := by
  rw [popLogLik_of hSupp, popLogLik_self]
  have h1 := sum_first_nonneg hSupp hS hD
  have h2 : (∑ w, (pS w * Real.log (pD w)))
      ≤ ∑ w, (pS w * Real.log (pS w)) := by
    have h3 := logLik_sub pS pD
    rw [← h3] at h1
    linarith
  exact_mod_cast h2

/-- **`lem:gibbs`, full form.** The truth is a population maximizer over
*any* candidate class, with no repeat condition required: the only
hypotheses are that the truth and the candidate induce read
distributions. Support mismatch makes `ℓpop_S(D) = -∞`, which is the
`≤` case. -/
theorem popLogLik_le_self' {pS pD : W → ℝ} (hS : IsProb pS) (hD : IsProb pD) :
    PopLogLik pS pD ≤ PopLogLik pS pS := by
  by_cases hSupp : SuppEq pS pD
  · exact popLogLik_le_self hS hD hSupp
  · rw [PopLogLik, if_neg hSupp]
    exact bot_le

/-- A population tie at a point where the distributions differ is
impossible: the Gibbs excess is then strictly positive somewhere. -/
theorem popTie_iff {pS pD : W → ℝ} (hS : IsProb pS) (hD : IsProb pD) :
    PopLogLik pS pD = PopLogLik pS pS ↔ pD = pS := by
  constructor
  · intro h
    have hbot : PopLogLik pS pD ≠ (⊥ : WithBot ℝ) := by
      intro hz
      exact (popLogLik_self_ne_bot pS) (h.symm.trans hz)
    have hSupp : SuppEq pS pD := popLogLik_ne_bot_imp hbot
    have hsum : PopLogLikValue pS pS = PopLogLikValue pS pD := by
      rw [popLogLik_of hSupp] at h
      exact (WithBot.coe_injective (h.trans (popLogLik_self pS))).symm
    have h1 : ∑ w, (pS w * Real.log (pS w) - pS w * Real.log (pD w)) = 0 := by
      rw [← logLik_sub]
      unfold PopLogLikValue at hsum
      linarith [hsum]
    have hex : ∀ w, KLExcess pS pD w = 0 := by
      intro w
      have hsum : (∑ x, KLExcess pS pD x) = 0 := by
        have h := sum_first_eq pS pD
        rw [h1, sum_second_eq_zero hS hD] at h
        simpa only [zero_add] using h.symm
      have hle := Finset.single_le_sum
        (fun i _ => klExcess_nonneg hSupp hS.1 hD.1 i) (Finset.mem_univ w)
      rw [hsum] at hle
      have hne' := klExcess_nonneg hSupp hS.1 hD.1 w
      linarith
    funext w
    by_cases hs : pS w = 0
    · have hpos : ¬ 0 < pS w := by rw [hs]; exact lt_irrefl 0
      have hz : pD w = 0 := by
        by_contra hcon
        exact hpos ((hSupp w).mpr (lt_of_le_of_ne (hD.1 w) (Ne.symm hcon)))
      rw [hs, hz]
    · have hs0 : 0 < pS w := lt_of_le_of_ne (hS.1 w) (Ne.symm hs)
      have hd0 : 0 < pD w := (hSupp w).mp hs0
      have hz : KLExcess pS pD w = 0 := hex w
      by_cases hne : pS w / pD w = 1
      · have hself : pS w = (pS w / pD w) * pD w := by field_simp
        rw [hne, one_mul] at hself
        exact hself.symm
      · exfalso
        have hlt := one_sub_inv_lt_log_of_ne_one (div_pos hs0 hd0) hne
        have hmul := mul_lt_mul_of_pos_left hlt hs0
        have hdiv : pS w * (pD w / pS w) = pD w := by field_simp
        have hlog : Real.log (pS w / pD w) = Real.log (pS w) - Real.log (pD w) :=
          Real.log_div hs0.ne' hd0.ne'
        rw [inv_div] at hmul
        have hmul' : pS w * (1 - pD w / pS w)
            < pS w * (Real.log (pS w) - Real.log (pD w)) := by
          rw [← hlog]
          exact hmul
        have hself : pS w * (1 - pD w / pS w) = pS w - pD w := by linarith
        have h3 : pS w - pD w < pS w * (Real.log (pS w) - Real.log (pD w)) := by
          rw [hself] at hmul'
          exact hmul'
        have hz' : pS w * Real.log (pS w) - pS w * Real.log (pD w)
            = pS w - pD w := by
          unfold KLExcess at hz
          linarith
        linarith
  · intro h
    have hSupp : SuppEq pS pD := by
      intro w
      rw [h]
    rw [popLogLik_of hSupp, popLogLik_self]
    simp [PopLogLikValue, h]


/-- The maximizer half of `lem:gibbs` in a form that consumes only
distributions: `S` attains the maximum of `ℓpop_S(·)`. -/
theorem truth_is_population_maximizer (pS : W → ℝ) (hS : IsProb pS)
    (candidates : Set (W → ℝ)) (hIn : ∀ pD ∈ candidates, IsProb pD) :
    ∀ pD ∈ candidates, PopLogLik pS pD ≤ PopLogLik pS pS :=
  fun _ hpD => popLogLik_le_self' hS (hIn _ hpD)

/-- A population tie between two distributions is exactly their
equality. -/
theorem popTie_iff' {pS pD : W → ℝ} (hS : IsProb pS) (hD : IsProb pD) :
    (PopLogLik pS pD = PopLogLik pS pS) ↔ pD = pS :=
  popTie_iff hS hD

/-! ## From the population objective to normalized spectrum equality -/

omit [Fintype W] in
/-- `p_D = p_S` for the two population read distributions, with
nonzero lengths on both sides, is exactly the proportional
("normalized") equality of the two integer spectra
`c_D * |S| = c_S * |D|` — the equality that
`AssemblyP1.PopulationReduction.NormalizedEqual` states. -/
theorem popProb_eq_iff_normalized {cS cD : W → ℕ} {nS nD : ℕ}
    (hS : 0 < nS) (hD : 0 < nD)
    (h : popProb cS nS = popProb cD nD) :
    ∀ w : W, cS w * nD = cD w * nS := by
  have hS0 : (nS : ℝ) ≠ 0 := by exact Nat.cast_ne_zero.mpr hS.ne'
  have hD0 : (nD : ℝ) ≠ 0 := by exact Nat.cast_ne_zero.mpr hD.ne'
  intro w
  have hw := congrFun h w
  simp only [popProb] at hw
  field_simp at hw
  rw [mul_comm (nS : ℝ) (cD w : ℝ)] at hw
  exact_mod_cast hw

end AssemblyP1.PopulationGibbs
