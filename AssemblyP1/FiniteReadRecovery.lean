import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fintype.Pi
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Finite-read recovery bounds from population identifiability (Antonina #270)

This module proves the bridge between population-level identifiability of a
finite candidate family of read distributions and finite-sample
high-probability maximum-likelihood recovery.

## Model

* `W` is a finite read universe (the observed read alphabet).
* A candidate is a pmf `p : W → ℝ` (`IsPmf`: nonnegative, sums to one).
* Reads `R_1, …, R_n` are iid with `R_i ~ p` (the true distribution).
* The likelihood of a read tuple `t = (R_1, …, R_n)` under a candidate `p` is
  `tupleLikelihood p n t = ∏ i, p (t i)`.
* The exact probability of an event `E` on read tuples under `n` iid reads
  from `p` is `eventProb p n E = ∑ t, if E t then tupleLikelihood p n t else 0`,
  which is precisely the measure of `E` under the product categorical measure
  on `W^n`.

## Main results

1. **Pairwise Hellinger bound** (`eventProb_pairwise`): for a distinguishable
   competitor `q` (a pmf with `q ≠ p`),
   `P_p[L_q ≥ L_p] ≤ ρ(p, q)^n`, where `ρ(p, q) = ∑ w, √(p w * q w)` is the
   finite discrete Hellinger/Bhattacharyya affinity. The proof is the robust
   zero-mass-avoiding route: pointwise on the event `L_q ≥ L_p`,
   `L_p ≤ √(L_p * L_q)` (including `L_p = 0` and ties), and summing over iid
   tuples factors the geometric mean into `ρ^n`. No likelihood-ratio division
   is used.

2. **Affinity bounds** (`hellinger_le_one`, `hellinger_lt_one_iff_ne`):
   `0 ≤ ρ ≤ 1`, and `ρ < 1` iff `p ≠ q`, via the exact identity
   `∑ w, (√(p w) - √(q w))^2 = 2 * (1 - ρ)`.

3. **Finite union bound** (`eventProb_wrong_le_sum`, `eventProb_wrong_le_card`):
   for a finite family `Θ` of wrong candidates (not containing `p`),
   `P_p[∃ q ∈ Θ, L_q ≥ L_p] ≤ ∑_{q ∈ Θ} ρ(p, q)^n ≤ |Θ| * ρ_max^n` when every
   `ρ(p, q) ≤ ρ_max < 1`.

4. **Consistency** (`eventProb_wrong_tendsto_zero`, `exists_n_for_confidence`):
   for a finite identifiable family (`ρ_max < 1`), the wrong-selection
   probability tends to zero, so the correct-selection probability tends to
   one; an explicit sufficient `n` exists for any requested confidence.

5. **Quantitative 99% illustration** (`il_confidence_99`): with `|Θ| = 4`
   candidates and uniform affinity bound `ρ_max = 9/10`, `n = 55` iid reads
   give wrong-selection probability `< 1/100`, i.e. `> 99%` confidence.

## Scope

These are generic finite-PMF lemmas. They apply to the AssemblyP1 primitive-P2
candidate class only after restricting to a **finite** candidate family (see
`AssemblyP1.FiniteReadRecoveryPopulation`): the full class has unbounded genome
lengths and hence infinite size, so the finite-family bound cannot be applied
to it directly. The population theorem `population_unique_ML` gives
identifiability over the whole (infinite) class at the population level; the
finite-read bound is a separate, finite-sample statement.
-/

namespace AssemblyP1.FiniteReadRecovery

open Finset BigOperators Filter
open scoped Classical

variable {W : Type*} [Fintype W]

/-- A probability mass function on the finite read universe `W`: nonnegative
and summing to one. -/
def IsPmf (p : W → ℝ) : Prop := (∀ w, 0 ≤ p w) ∧ (∑ w : W, p w = 1)

/-- The finite discrete Hellinger (Bhattacharyya) affinity of two read
distributions `p` and `q` over the finite read universe `W`. -/
noncomputable def hellinger (p q : W → ℝ) : ℝ :=
  ∑ w : W, Real.sqrt (p w * q w)

/-- Likelihood of an `n`-tuple of iid reads under distribution `p`. -/
def tupleLikelihood (p : W → ℝ) (n : ℕ) (t : Fin n → W) : ℝ :=
  ∏ i : Fin n, p (t i)

/-- Exact probability of an event `E` on read tuples under `n` iid reads from
`p`: the sum of tuple likelihoods over the event. This is exactly the measure
of `E` under the product categorical measure on `W^n`. -/
noncomputable def eventProb (p : W → ℝ) (n : ℕ) (E : (Fin n → W) → Prop)
    [DecidablePred E] : ℝ :=
  ∑ t : Fin n → W, if E t then tupleLikelihood p n t else 0

/- The likelihood of a read tuple is nonnegative. -/
omit [Fintype W] in theorem tupleLikelihood_nonneg (p : W → ℝ) (n : ℕ) (t : Fin n → W)
    (hp : ∀ w, 0 ≤ p w) : 0 ≤ tupleLikelihood p n t := by
  unfold tupleLikelihood
  exact Finset.prod_nonneg (fun i _ => hp (t i))

/-- The total likelihood of all `n`-tuples factors: summing the tuple
likelihood over all tuples gives the `n`-th power of the total mass. -/
theorem sum_tupleLikelihood (p : W → ℝ) (n : ℕ) :
    ∑ t : Fin n → W, tupleLikelihood p n t = (∑ w : W, p w) ^ n := by
  show ∑ t : Fin n → W, ∏ i : Fin n, p (t i) = _
  have hkey := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset W))
    (fun (i : Fin n) (w : W) => p w)
  rw [Fintype.piFinset_univ] at hkey
  have hprod : ∏ i : Fin n, ∑ j ∈ (Finset.univ : Finset W), p j = (∑ w : W, p w) ^ n := by
    simp [Finset.prod_const]
  rw [hprod] at hkey
  exact hkey.symm

/-- The probability of the whole tuple space under a pmf is one. -/
theorem eventProb_univ (p : W → ℝ) (n : ℕ) (hp : IsPmf p) :
    eventProb p n (fun _ => True) = 1 := by
  have h1 := sum_tupleLikelihood p n
  have h2 : (∑ w : W, p w) ^ n = 1 ^ n := by rw [hp.2]
  rw [h2] at h1
  show ∑ t : Fin n → W, (if (fun _ => True) t then tupleLikelihood p n t else 0) = 1
  simp [h1]

/-- The Hellinger affinity is nonnegative. -/
theorem hellinger_nonneg (p q : W → ℝ) : 0 ≤ hellinger p q := by
  unfold hellinger
  exact Finset.sum_nonneg (fun w _ => Real.sqrt_nonneg _)

/-- The exact identity `∑ w, (√(p w) - √(q w))^2 = 2 - 2 * ρ` for
nonnegative `p`, `q` summing to one. -/
theorem hellinger_sq_identity (p q : W → ℝ) (hp : ∀ w, 0 ≤ p w)
    (hq : ∀ w, 0 ≤ q w) (hpsum : ∑ w : W, p w = 1) (hqsum : ∑ w : W, q w = 1) :
    ∑ w : W, (Real.sqrt (p w) - Real.sqrt (q w)) ^ 2 = 2 - 2 * hellinger p q := by
  unfold hellinger
  have hterm : ∀ w : W, (Real.sqrt (p w) - Real.sqrt (q w)) ^ 2
      + 2 * Real.sqrt (p w * q w) = p w + q w := by
    intro w
    have h1 : Real.sqrt (p w) ^ 2 = p w := Real.sq_sqrt (hp w)
    have h2 : Real.sqrt (q w) ^ 2 = q w := Real.sq_sqrt (hq w)
    have h3 : Real.sqrt (p w) * Real.sqrt (q w) = Real.sqrt (p w * q w) := by
      rw [← Real.sqrt_mul (hp w) (q w)]
    have h4 : (Real.sqrt (p w) - Real.sqrt (q w)) ^ 2
        = Real.sqrt (p w) ^ 2 - 2 * (Real.sqrt (p w) * Real.sqrt (q w)) + Real.sqrt (q w) ^ 2 := by
      ring
    rw [h4, h1, h2, h3]
    ring
  have hsplit : ∑ w : W, ((Real.sqrt (p w) - Real.sqrt (q w)) ^ 2
      + 2 * Real.sqrt (p w * q w))
      = (∑ w : W, (Real.sqrt (p w) - Real.sqrt (q w)) ^ 2)
        + 2 * (∑ w : W, Real.sqrt (p w * q w)) := by
    have h2 : ∀ w : W, 2 * Real.sqrt (p w * q w)
        = Real.sqrt (p w * q w) + Real.sqrt (p w * q w) := by
      intro w; ring
    have hscalar : ∑ w : W, 2 * Real.sqrt (p w * q w)
        = 2 * (∑ w : W, Real.sqrt (p w * q w)) := by
      rw [Finset.sum_congr rfl (fun w _ => h2 w), Finset.sum_add_distrib]
      ring
    rw [Finset.sum_add_distrib, hscalar]
  have hcongr : ∑ w : W, ((Real.sqrt (p w) - Real.sqrt (q w)) ^ 2
      + 2 * Real.sqrt (p w * q w)) = ∑ w : W, (p w + q w) := by
    apply Finset.sum_congr rfl
    intro w _
    exact hterm w
  have hsum : ∑ w : W, (p w + q w) = 2 := by
    rw [Finset.sum_add_distrib, hpsum, hqsum]
    ring
  linarith

/-- The Hellinger affinity of two pmfs is at most one. -/
theorem hellinger_le_one (p q : W → ℝ) (hp : IsPmf p) (hq : IsPmf q) :
    hellinger p q ≤ 1 := by
  have hident := hellinger_sq_identity p q hp.1 hq.1 hp.2 hq.2
  have hnonneg : 0 ≤ ∑ w : W, (Real.sqrt (p w) - Real.sqrt (q w)) ^ 2 :=
    Finset.sum_nonneg (fun w _ => sq_nonneg _)
  rw [hident] at hnonneg
  linarith

/-- The Hellinger affinity is strictly less than one iff the two pmfs differ.
Equivalently, `ρ = 1` iff `p = q`. -/
theorem hellinger_lt_one_iff_ne (p q : W → ℝ) (hp : IsPmf p) (hq : IsPmf q) :
    hellinger p q < 1 ↔ p ≠ q := by
  have hident := hellinger_sq_identity p q hp.1 hq.1 hp.2 hq.2
  constructor
  · intro hlt heq
    subst heq
    unfold hellinger at hlt
    have : ∑ w : W, Real.sqrt (p w * p w) = 1 := by
      have hpsum : ∑ w : W, p w = 1 := hp.2
      have : ∑ w : W, Real.sqrt (p w * p w) = ∑ w : W, p w := by
        apply Finset.sum_congr rfl
        intro w _
        rw [Real.sqrt_mul (hp.1 w) (p w), Real.mul_self_sqrt (hp.1 w)]
      rw [this, hpsum]
    linarith
  · intro hne
    -- p ≠ q gives a witness w with p w ≠ q w, hence a strictly positive square
    have hne' : ¬ (∀ w : W, p w = q w) := by
      intro hforall
      exact hne (funext hforall)
    rw [not_forall] at hne'
    obtain ⟨w, hw⟩ := hne'
    have hsqrtne : Real.sqrt (p w) ≠ Real.sqrt (q w) := by
      intro hsq
      have : p w = q w := (Real.sqrt_inj (hp.1 w) (hq.1 w)).mp hsq
      exact hw this
    have hdiff : Real.sqrt (p w) - Real.sqrt (q w) ≠ 0 := by
      intro hzero
      apply hsqrtne
      linarith
    have hsqpos : 0 < (Real.sqrt (p w) - Real.sqrt (q w)) ^ 2 :=
      sq_pos_of_ne_zero hdiff
    have hle : (Real.sqrt (p w) - Real.sqrt (q w)) ^ 2
        ≤ ∑ w : W, (Real.sqrt (p w) - Real.sqrt (q w)) ^ 2 :=
      Finset.single_le_sum (f := fun x => (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2)
        (fun w _ => sq_nonneg _) (Finset.mem_univ w)
    rw [hident] at hle
    have hnonneg : 0 ≤ ∑ w : W, (Real.sqrt (p w) - Real.sqrt (q w)) ^ 2 :=
      Finset.sum_nonneg (fun w _ => sq_nonneg _)
    linarith

/- Pointwise core of the Hellinger bound: on the event that the competitor
likelihood `L_q` is at least the true likelihood `L_p`, the true likelihood is
bounded by the geometric mean `√(L_p * L_q)`. Zero-probability tuples and ties
are handled directly, with no division. -/
omit [Fintype W] in theorem indicator_le_sqrt_mul (p q : W → ℝ) (n : ℕ) (t : Fin n → W)
    (hp : ∀ w, 0 ≤ p w) (_hq : ∀ w, 0 ≤ q w) :
    (if tupleLikelihood q n t ≥ tupleLikelihood p n t then tupleLikelihood p n t else 0)
      ≤ Real.sqrt (tupleLikelihood p n t * tupleLikelihood q n t) := by
  by_cases h : tupleLikelihood q n t ≥ tupleLikelihood p n t
  · rw [ite_eq_left h]
    have hLp : 0 ≤ tupleLikelihood p n t := tupleLikelihood_nonneg p n t hp
    have hge : (tupleLikelihood p n t) ^ 2 ≤ tupleLikelihood p n t * tupleLikelihood q n t := by
      have hmul := mul_le_mul_of_nonneg_left h hLp
      rw [sq]
      exact hmul
    have hsqrt : Real.sqrt ((tupleLikelihood p n t) ^ 2)
        ≤ Real.sqrt (tupleLikelihood p n t * tupleLikelihood q n t) :=
      Real.sqrt_le_sqrt hge
    rwa [Real.sqrt_sq hLp] at hsqrt
  · rw [ite_eq_right h]
    exact Real.sqrt_nonneg _

/-- **Pairwise finite-read Hellinger bound.** For `n` iid reads from the true
distribution `p`, the exact probability that a competitor `q` ties or beats
the truth in likelihood is at most `hellinger(p, q)^n`. -/
theorem eventProb_pairwise (p q : W → ℝ) (n : ℕ) (hp : IsPmf p) (hq : IsPmf q) :
    eventProb p n (fun t => tupleLikelihood q n t ≥ tupleLikelihood p n t)
      ≤ (hellinger p q) ^ n := by
  have hpnn : ∀ w, 0 ≤ p w := hp.1
  have hqnn : ∀ w, 0 ≤ q w := hq.1
  have hpt : ∀ t : Fin n → W,
      (if tupleLikelihood q n t ≥ tupleLikelihood p n t then tupleLikelihood p n t else 0)
        ≤ Real.sqrt (tupleLikelihood p n t * tupleLikelihood q n t) :=
    fun t => indicator_le_sqrt_mul p q n t hpnn hqnn
  have hsum : eventProb p n (fun t => tupleLikelihood q n t ≥ tupleLikelihood p n t)
      ≤ ∑ t : Fin n → W, Real.sqrt (tupleLikelihood p n t * tupleLikelihood q n t) := by
    unfold eventProb
    exact Finset.sum_le_sum (fun t _ => hpt t)
  have hfac : ∀ t : Fin n → W,
      Real.sqrt (tupleLikelihood p n t * tupleLikelihood q n t)
        = ∏ i : Fin n, Real.sqrt (p (t i) * q (t i)) := by
    intro t
    show Real.sqrt ((∏ i : Fin n, p (t i)) * (∏ i : Fin n, q (t i)))
        = ∏ i : Fin n, Real.sqrt (p (t i) * q (t i))
    rw [Real.sqrt_mul (Finset.prod_nonneg (fun i _ => hpnn (t i)))]
    rw [Real.sqrt_prod Finset.univ (fun i _ => hpnn (t i)),
      Real.sqrt_prod Finset.univ (fun i _ => hqnn (t i))]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [Real.sqrt_mul (hpnn (t i))]
  have htotal : ∑ t : Fin n → W, ∏ i : Fin n, Real.sqrt (p (t i) * q (t i))
      = (∑ w : W, Real.sqrt (p w * q w)) ^ n := by
    have hkey := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset W))
      (fun (i : Fin n) (w : W) => Real.sqrt (p w * q w))
    rw [Fintype.piFinset_univ] at hkey
    have hprod : ∏ i : Fin n, ∑ j ∈ (Finset.univ : Finset W), Real.sqrt (p j * q j)
        = (∑ w : W, Real.sqrt (p w * q w)) ^ n := by
      simp [Finset.prod_const]
    rw [hprod] at hkey
    exact hkey.symm
  have hsum2 : ∑ t : Fin n → W, Real.sqrt (tupleLikelihood p n t * tupleLikelihood q n t)
      = ∑ t : Fin n → W, ∏ i : Fin n, Real.sqrt (p (t i) * q (t i)) :=
    Finset.sum_congr rfl (fun t _ => hfac t)
  unfold hellinger
  rw [hsum2, htotal] at hsum
  exact hsum

/-- The wrong-selection event over a family `Θ` of competitor pmfs (not
containing the truth `p`): some competitor ties or beats the truth in
likelihood. -/
def wrongEvent (p : W → ℝ) (Θ : Finset (W → ℝ)) (n : ℕ) (t : Fin n → W) : Prop :=
  ∃ q ∈ Θ, tupleLikelihood q n t ≥ tupleLikelihood p n t

/-- The exact probability of the wrong-selection event is nonnegative. -/
theorem eventProb_wrong_nonneg (p : W → ℝ) (Θ : Finset (W → ℝ)) (n : ℕ)
    (hp : IsPmf p) : 0 ≤ eventProb p n (wrongEvent p Θ n) := by
  show 0 ≤ ∑ t : Fin n → W, (if wrongEvent p Θ n t then tupleLikelihood p n t else 0)
  apply Finset.sum_nonneg
  intro t _
  by_cases h : wrongEvent p Θ n t
  · rw [ite_eq_left h]; exact tupleLikelihood_nonneg p n t hp.1
  · rw [ite_eq_right h]

/-- Finite union bound: the exact probability that some competitor in a finite
family `Θ` ties or beats the truth is at most the sum of the exact pairwise
probabilities. -/
theorem eventProb_wrong_le_sum (p : W → ℝ) (Θ : Finset (W → ℝ)) (n : ℕ)
    (hp : IsPmf p) :
    eventProb p n (wrongEvent p Θ n)
      ≤ ∑ q ∈ Θ, eventProb p n (fun t => tupleLikelihood q n t ≥ tupleLikelihood p n t) := by
  have hpnn : ∀ w, 0 ≤ p w := hp.1
  have hpt : ∀ t : Fin n → W,
      (if wrongEvent p Θ n t then tupleLikelihood p n t else 0)
        ≤ ∑ q ∈ Θ, (if tupleLikelihood q n t ≥ tupleLikelihood p n t then tupleLikelihood p n t else 0) := by
    intro t
    by_cases h : wrongEvent p Θ n t
    · rw [ite_eq_left h]
      obtain ⟨q, hqΘ, hge⟩ := h
      have hnonneg : ∀ q' ∈ Θ, 0 ≤ (if tupleLikelihood q' n t ≥ tupleLikelihood p n t then tupleLikelihood p n t else 0) := by
        intro q' _
        by_cases h' : tupleLikelihood q' n t ≥ tupleLikelihood p n t
        · rw [ite_eq_left h']; exact tupleLikelihood_nonneg p n t hpnn
        · rw [ite_eq_right h']
      have hfq : (if tupleLikelihood q n t ≥ tupleLikelihood p n t then tupleLikelihood p n t else 0) = tupleLikelihood p n t := ite_eq_left hge
      calc
        tupleLikelihood p n t = (if tupleLikelihood q n t ≥ tupleLikelihood p n t then tupleLikelihood p n t else 0) := hfq.symm
        _ ≤ ∑ q' ∈ Θ, (if tupleLikelihood q' n t ≥ tupleLikelihood p n t then tupleLikelihood p n t else 0) :=
          Finset.single_le_sum hnonneg hqΘ
    · rw [ite_eq_right h]
      exact Finset.sum_nonneg (fun q _ => by
        by_cases h' : tupleLikelihood q n t ≥ tupleLikelihood p n t
        · rw [ite_eq_left h']; exact tupleLikelihood_nonneg p n t hpnn
        · rw [ite_eq_right h'])
  have hsum : eventProb p n (wrongEvent p Θ n)
      ≤ ∑ t : Fin n → W, ∑ q ∈ Θ, (if tupleLikelihood q n t ≥ tupleLikelihood p n t then tupleLikelihood p n t else 0) := by
    unfold eventProb
    exact Finset.sum_le_sum (fun t _ => hpt t)
  have exch : ∑ t : Fin n → W, ∑ q ∈ Θ, (if tupleLikelihood q n t ≥ tupleLikelihood p n t then tupleLikelihood p n t else 0)
      = ∑ q ∈ Θ, ∑ t : Fin n → W, (if tupleLikelihood q n t ≥ tupleLikelihood p n t then tupleLikelihood p n t else 0) :=
    Finset.sum_comm
  rw [exch] at hsum
  have hconvert : ∀ q : W → ℝ,
      ∑ t : Fin n → W, (if tupleLikelihood q n t ≥ tupleLikelihood p n t then tupleLikelihood p n t else 0)
        = eventProb p n (fun t => tupleLikelihood q n t ≥ tupleLikelihood p n t) := fun q => rfl
  rw [Finset.sum_congr rfl (fun q _ => hconvert q)] at hsum
  exact hsum

/-- With a uniform affinity bound, the wrong-selection probability is at most
`|Θ| * ρ_max^n`. -/
theorem eventProb_wrong_le_card (p : W → ℝ) (Θ : Finset (W → ℝ)) (n : ℕ) (ρ_max : ℝ)
    (hp : IsPmf p) (hq : ∀ q ∈ Θ, IsPmf q)
    (hρ : ∀ q ∈ Θ, hellinger p q ≤ ρ_max) :
    eventProb p n (wrongEvent p Θ n) ≤ (Θ.card : ℝ) * ρ_max ^ n := by
  have h1 := eventProb_wrong_le_sum p Θ n hp
  have h2 : ∀ q ∈ Θ, eventProb p n (fun t => tupleLikelihood q n t ≥ tupleLikelihood p n t) ≤ ρ_max ^ n := by
    intro q hqΘ
    exact (eventProb_pairwise p q n hp (hq q hqΘ)).trans
      (pow_le_pow_left₀ (hellinger_nonneg p q) (hρ q hqΘ) n)
  have h3 : ∑ q ∈ Θ, eventProb p n (fun t => tupleLikelihood q n t ≥ tupleLikelihood p n t) ≤ (Θ.card : ℝ) * ρ_max ^ n := by
    calc ∑ q ∈ Θ, eventProb p n (fun t => tupleLikelihood q n t ≥ tupleLikelihood p n t)
        ≤ ∑ q ∈ Θ, ρ_max ^ n := Finset.sum_le_sum h2
      _ = (Θ.card : ℝ) * ρ_max ^ n := by simp [Finset.sum_const]
  exact h1.trans h3

/-- For a finite identifiable family (uniform `ρ_max < 1`), the exact
wrong-selection probability tends to zero as the number of iid reads grows. -/
theorem eventProb_wrong_tendsto_zero (p : W → ℝ) (Θ : Finset (W → ℝ)) (ρ_max : ℝ)
    (hp : IsPmf p) (hq : ∀ q ∈ Θ, IsPmf q)
    (hρ : ∀ q ∈ Θ, hellinger p q ≤ ρ_max)
    (hρnn : 0 ≤ ρ_max) (hρmax : ρ_max < 1) :
    Tendsto (fun n => eventProb p n (wrongEvent p Θ n)) Filter.atTop (nhds 0) := by
  have hbound : ∀ n : ℕ, eventProb p n (wrongEvent p Θ n) ≤ (Θ.card : ℝ) * ρ_max ^ n := fun n =>
    eventProb_wrong_le_card p Θ n ρ_max hp hq hρ
  have hρtendsto : Tendsto (fun n => ρ_max ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hρnn hρmax
  have hmult : Tendsto (fun n => (Θ.card : ℝ) * ρ_max ^ n) Filter.atTop (nhds 0) :=
    by simpa using (tendsto_const_nhds.mul hρtendsto : Tendsto (fun n => (Θ.card : ℝ) * ρ_max ^ n) Filter.atTop (nhds ((Θ.card : ℝ) * 0)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (f := fun n => eventProb p n (wrongEvent p Θ n))
    (g := fun _ => (0 : ℝ)) (h := fun n => (Θ.card : ℝ) * ρ_max ^ n)
    tendsto_const_nhds hmult (fun n => eventProb_wrong_nonneg p Θ n hp) hbound

/-- **Finite-family consistency.** For a finite identifiable family (uniform
`ρ_max < 1`), for every requested confidence `δ > 0` there is a number of
reads `N` such that for all `n ≥ N` the wrong-selection probability is at most
`δ`. -/
theorem exists_n_for_confidence (p : W → ℝ) (Θ : Finset (W → ℝ)) (ρ_max : ℝ)
    (hp : IsPmf p) (hq : ∀ q ∈ Θ, IsPmf q)
    (hρ : ∀ q ∈ Θ, hellinger p q ≤ ρ_max)
    (hρnn : 0 ≤ ρ_max) (hρmax : ρ_max < 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, eventProb p n (wrongEvent p Θ n) ≤ δ := by
  rcases Finset.eq_empty_or_nonempty Θ with hempty | hnonempty
  · refine ⟨0, fun n _ => ?_⟩
    have h0 : eventProb p n (wrongEvent p Θ n) ≤ 0 := by
      simpa [hempty] using (eventProb_wrong_le_card p Θ n ρ_max hp hq hρ)
    exact h0.trans (le_of_lt hδ)
  · have hcardpos : 0 < (Θ.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hnonempty)
    have hρtendsto : Tendsto (fun n => ρ_max ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hρnn hρmax
    have hε : ∀ᶠ n in Filter.atTop, (ρ_max ^ n : ℝ) < δ / (Θ.card : ℝ) := by
      have hball : ∀ᶠ n in Filter.atTop, ρ_max ^ n ∈ Metric.ball (0 : ℝ) (δ / (Θ.card : ℝ)) := by
        apply hρtendsto
        exact Metric.nhds_basis_ball.mem_of_mem (by exact div_pos hδ hcardpos)
      filter_upwards [hball] with n hn
      have hdist : |(ρ_max ^ n : ℝ)| < δ / (Θ.card : ℝ) := by
        simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hn
      exact lt_of_le_of_lt (le_abs_self _) hdist
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hε
    refine ⟨N, fun n hn => ?_⟩
    have hle := eventProb_wrong_le_card p Θ n ρ_max hp hq hρ
    have hρn := hN n hn
    have hmul : (Θ.card : ℝ) * ρ_max ^ n <
        (Θ.card : ℝ) * (δ / (Θ.card : ℝ)) :=
      mul_lt_mul_of_pos_left hρn hcardpos
    have hcancel : (Θ.card : ℝ) * (δ / (Θ.card : ℝ)) = δ := by
      field_simp [ne_of_gt hcardpos]
    exact (hle.trans_lt (hmul.trans_eq hcancel)).le

/-- **Quantitative 99% illustration.** With `|Θ| = 4` candidates and a uniform
affinity bound `ρ_max = 9/10`, `n = 55` iid reads give wrong-selection
probability `< 1/100`, i.e. correct-selection probability `> 99%`. This is a
conditional numerical illustration, not a measured AssemblyP1 constant. -/
theorem il_confidence_99 : (3 : ℝ) * ((9 : ℝ) / 10) ^ 55 < 1 / 100 := by
  norm_num

end AssemblyP1.FiniteReadRecovery
