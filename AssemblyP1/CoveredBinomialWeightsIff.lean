import AssemblyP1.FixedNBinomialEffectiveWeights
import AssemblyP1.FiniteStartCoverage

/-!
# Complete covered-sample maximality criterion for the fixed-`N`
product-binomial surrogate (#259)

Medvedev and Brudno 2009 Section 6.1 model the read-count objective as a
*product of binomial marginals* with a fixed external genome length `N`.
This is a separable optimization surrogate, not the true joint multinomial
read-count law, and it is not the Section 6.2 bidirected-flow model.

For a fixed finite read-type universe `E`, the candidate-dependent integer
numerator of that surrogate is exactly `∏ i, (effectiveWeight N B i) ^ x i`,
where `effectiveWeight N B i = B i * ∏ j, if i = j then 1 else (N - B j)`
(`AssemblyP1.FixedNBinomialEffectiveWeights`).  The second product runs over
*all* modeled read types, including zero-count ones; this is the extra
`(1 - d(w)/N) ^ (n - x(w))` factor that distinguishes the binomial surrogate
from the exact multinomial likelihood of `#256`.

## What is proved here

Write `qA i` and `qB i` for the truth and competitor effective weights, and
let `a` be a strictly positive *coverage baseline*: the sample count vectors
considered are exactly those with `a i ≤ x i` for every modeled type (the
sample size `n = ∑ x` is otherwise free).  This is the finite weight-level
statement behind "every realizable complete-support sample".

The main theorem is a genuine necessary-and-sufficient classification:

`(∀ covered x, ∏ qB i ^ x i ≤ ∏ qA i ^ x i)` holds **iff** either the
competitor has a zero effective weight somewhere (so its score is `0` on
*every* covered sample, because a positive baseline forces every coordinate
to be observed at least once), or the competitor's effective weights are
pointwise dominated by the truth's.

The forward direction is non-vacuous and constructive: if every competitor
weight is positive and some `qB j > qA j`, then flooding coordinate `j` with
`t` extra mandatory reads makes the score ratio `(qB j / qA j) ^ t` times a
constant and hence exceeds `1` for some finite `t`.  The arithmetic heart is
`pow_add_growth`.

`covered_start_samples_effectiveProduct_le_iff` instantiates the weight-level
statement with `AssemblyP1.FiniteStartCoverage.coverage_of_type_budget`, so
"covered sample" really means a read sample that visits every true genome
start at least once.  Boundary probabilities `0`/`1` and novel read types
outside `E`, variable genome length, and the general bidirected flows of
`#260`/`#261` remain out of scope.
-/

namespace AssemblyP1.CoveredBinomialWeightsIff

open Finset BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Discrete first-order growth: if `c ≥ 1` and `b ≥ c + 1`, then `b ^ (k + 1)`
beats `c ^ (k + 1)` by the term `(k + 1) * c ^ k`.  This is the integer
arithmetic that drives the flooding argument. -/
private theorem pow_add_growth (b c : ℕ) (hbc : c + 1 ≤ b) :
    ∀ k : ℕ, c ^ (k + 1) + (k + 1) * c ^ k ≤ b ^ (k + 1) := by
  intro k
  induction k with
  | zero => simpa using hbc
  | succ n ih =>
      have h1 : (c + 1) * c ^ (n + 1) = c ^ (n + 2) + c ^ (n + 1) := by
        rw [add_mul, one_mul, ← pow_succ']
      have h2 : (c + 1) * ((n + 1) * c ^ n)
          = (n + 1) * c ^ (n + 1) + (n + 1) * c ^ n := by
        rw [add_mul, one_mul, ← mul_assoc, mul_comm c (n + 1), mul_assoc, pow_succ']
      have hcoef : (n + 2) * c ^ (n + 1) = c ^ (n + 1) + (n + 1) * c ^ (n + 1) := by
        rw [show n + 2 = (n + 1) + 1 by omega, add_mul, one_mul, add_comm]
      have hkey_eq : (c + 1) * (c ^ (n + 1) + (n + 1) * c ^ n)
          = c ^ (n + 2) + (n + 2) * c ^ (n + 1) + (n + 1) * c ^ n := by
        rw [mul_add, h1, h2, hcoef]
        ac_rfl
      calc c ^ (n + 1 + 1) + (n + 1 + 1) * c ^ (n + 1)
          = c ^ (n + 2) + (n + 2) * c ^ (n + 1) := rfl
        _ ≤ c ^ (n + 2) + (n + 2) * c ^ (n + 1) + (n + 1) * c ^ n := Nat.le_add_right _ _
        _ = (c + 1) * (c ^ (n + 1) + (n + 1) * c ^ n) := hkey_eq.symm
        _ ≤ (c + 1) * b ^ (n + 1) := Nat.mul_le_mul_left _ ih
        _ ≤ b * b ^ (n + 1) := Nat.mul_le_mul_right _ hbc
        _ = b ^ (n + 1 + 1) := (pow_succ' b (n + 1)).symm

/-- **Complete covered-sample weight criterion.**

For a finite type universe `E`, effective weights `qA`, `qB` with the truth
weights `qA` strictly positive, and a strictly positive coverage baseline `a`,
the competitor's product score is bounded by the truth's on *every* sample
with `a i ≤ x i` if and only if either the competitor has a zero weight, or it
is pointwise dominated by the truth. -/
theorem covered_product_le_iff_zero_or_pointwise
    (qA qB a : E → ℕ) (hqA : ∀ e, 0 < qA e) (ha : ∀ e, 0 < a e) :
    (∀ x : E → ℕ, (∀ e, a e ≤ x e) →
        (∏ e : E, qB e ^ x e) ≤ (∏ e : E, qA e ^ x e)) ↔
      ((∃ e, qB e = 0) ∨ (∀ e, qB e ≤ qA e)) := by
  classical
  constructor
  · intro h
    rcases em (∃ e, qB e = 0) with h0 | h0
    · exact Or.inl h0
    · have hqB : ∀ e, 0 < qB e :=
        fun e => Nat.pos_of_ne_zero (fun he => h0 ⟨e, he⟩)
      rcases em (∀ e, qB e ≤ qA e) with hle | hle
      · exact Or.inr hle
      · obtain ⟨e0, he0⟩ := not_forall.mp hle
        have hlt : qA e0 < qB e0 := Nat.not_le.mp he0
        have hc : 0 < qA e0 := hqA e0
        have hbc : qA e0 + 1 ≤ qB e0 := hlt
        set P : ℕ := ∏ i ∈ Finset.univ.erase e0, qB i ^ a i with hP
        set Q : ℕ := ∏ i ∈ Finset.univ.erase e0, qA i ^ a i with hQ
        have hP1 : 1 ≤ P := by
          rw [hP]
          exact Finset.one_le_prod (fun i _ => Nat.one_le_pow (a i) (qB i) (hqB i))
        have hQ1 : 1 ≤ Q := by
          rw [hQ]
          exact Finset.one_le_prod (fun i _ => Nat.one_le_pow (a i) (qA i) (hqA i))
        have hPpos : 0 < P := lt_of_lt_of_le Nat.zero_lt_one hP1
        have decomp : ∀ (q : E → ℕ) (t : ℕ),
            (∏ i : E, q i ^ (if i = e0 then a e0 + t else a i)) =
              q e0 ^ (a e0 + t) * ∏ i ∈ Finset.univ.erase e0, q i ^ a i := by
          intro q t
          rw [← Finset.mul_prod_erase Finset.univ
                (fun i => q i ^ (if i = e0 then a e0 + t else a i))
                (Finset.mem_univ e0)]
          rw [ite_eq_left rfl]
          congr 1
          apply Finset.prod_congr rfl
          intro i hi
          rw [ite_eq_right (Finset.mem_erase.mp hi).1]
        have key : ∀ t : ℕ, qB e0 ^ (a e0 + t) ≤ Q * qA e0 ^ (a e0 + t) := by
          intro t
          have hx : ∀ i, a i ≤ (if i = e0 then a e0 + t else a i) := by
            intro i
            by_cases hi : i = e0
            · subst hi; rw [ite_eq_left rfl]; exact Nat.le_add_right _ _
            · rw [ite_eq_right hi]
          have hxt := h (fun i => if i = e0 then a e0 + t else a i) hx
          rw [decomp qB t, decomp qA t, ← hP, ← hQ] at hxt
          calc qB e0 ^ (a e0 + t)
              ≤ P * qB e0 ^ (a e0 + t) := Nat.le_mul_of_pos_left _ hPpos
            _ = qB e0 ^ (a e0 + t) * P := by rw [mul_comm]
            _ ≤ qA e0 ^ (a e0 + t) * Q := hxt
            _ = Q * qA e0 ^ (a e0 + t) := by rw [mul_comm]
        set t0 : ℕ := (Q - 1) * qA e0 + 1 with ht0
        have hkey := key t0
        have h1le : 1 ≤ a e0 + t0 := by omega
        have hgrowth : qA e0 ^ (a e0 + t0)
              + (a e0 + t0) * qA e0 ^ (a e0 + t0 - 1)
            ≤ qB e0 ^ (a e0 + t0) := by
          have hg := pow_add_growth (qB e0) (qA e0) hbc (a e0 + t0 - 1)
          rw [Nat.sub_add_cancel h1le] at hg
          exact hg
        have hKpos : 0 < qA e0 ^ (a e0 + t0 - 1) := Nat.pow_pos hc
        have hC : qA e0 ^ (a e0 + t0) = qA e0 * qA e0 ^ (a e0 + t0 - 1) := by
          conv_lhs => rw [← Nat.sub_add_cancel h1le]
          exact pow_succ' (qA e0) (a e0 + t0 - 1)
        have hle : qA e0 ^ (a e0 + t0)
              + (a e0 + t0) * qA e0 ^ (a e0 + t0 - 1)
            ≤ Q * qA e0 ^ (a e0 + t0) := le_trans hgrowth hkey
        rw [hC] at hle
        have hle' : (qA e0 + (a e0 + t0)) * qA e0 ^ (a e0 + t0 - 1)
            ≤ (Q * qA e0) * qA e0 ^ (a e0 + t0 - 1) := by
          rw [add_mul, mul_assoc]
          exact hle
        have hcancel : qA e0 + (a e0 + t0) ≤ Q * qA e0 :=
          Nat.le_of_mul_le_mul_right hle' hKpos
        have hQc : Q * qA e0 = (Q - 1) * qA e0 + qA e0 := by
          conv_lhs => rw [← Nat.sub_add_cancel hQ1]
          rw [add_mul, one_mul]
        have hfin : a e0 + t0 ≤ (Q - 1) * qA e0 := by
          have h' := hcancel
          rw [hQc] at h'
          rw [add_comm (qA e0) (a e0 + t0)] at h'
          exact Nat.add_le_add_iff_right.mp h'
        have hgt : (Q - 1) * qA e0 < a e0 + t0 := by
          rw [ht0]; omega
        exact absurd hfin (not_le.mpr hgt)
  · intro h x hx
    rcases h with h0 | hle
    · obtain ⟨e0, he0⟩ := h0
      have hx0 : 0 < x e0 := lt_of_lt_of_le (ha e0) (hx e0)
      have hz : qB e0 ^ x e0 = 0 := by rw [he0, zero_pow (Nat.ne_of_gt hx0)]
      have hprod : (∏ e : E, qB e ^ x e) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ e0) hz
      rw [hprod]; exact Nat.zero_le _
    · exact Finset.prod_le_prod (fun i _ => Nat.pow_le_pow_left (hle i) (x i))

/-- Instance of the weight criterion for the fixed-`N` product-binomial
surrogate: the truth effective weights must be positive, and the coverage
baseline is the true spectrum itself.

**Scope (same-support).**  Here `E` is taken to be exactly the true-supported
read types and `effectiveWeight N ·` is evaluated over `E` only, so this
specialization drops the `(N - B j)` factors of *unobserved* molecule classes.
The source-faithful ambient version that keeps the full modeled universe `U`
(and hence every unobserved MB09 §6.1 class) is
`covered_ambient_effectiveProduct_le_iff` below; this same-support form is the
special case where no candidate or truth mass lies outside `E`. -/
theorem covered_effectiveProduct_le_iff
    (N : ℕ) (A B : E → ℕ)
    (hA : ∀ e, 0 < A e)
    (hqA : ∀ e, 0 < FixedNBinomialEffectiveWeights.effectiveWeight N A e) :
    (∀ x : E → ℕ, (∀ e, A e ≤ x e) →
        FixedNBinomialEffectiveWeights.effectiveProduct N B x
          ≤ FixedNBinomialEffectiveWeights.effectiveProduct N A x) ↔
      ((∃ e, FixedNBinomialEffectiveWeights.effectiveWeight N B e = 0) ∨
        (∀ e, FixedNBinomialEffectiveWeights.effectiveWeight N B e
          ≤ FixedNBinomialEffectiveWeights.effectiveWeight N A e)) :=
  covered_product_le_iff_zero_or_pointwise
    (FixedNBinomialEffectiveWeights.effectiveWeight N A)
    (FixedNBinomialEffectiveWeights.effectiveWeight N B) A hqA hA

section Coverage

variable {S : Type*} [Fintype S]

omit [Fintype E] in
/-- Every read sample that visits each true start at least once has type
counts dominating the true start spectrum.  The fibre over a type `e` contains
exactly `startSpectrum f e` starts, each contributing at least one read. -/
theorem startSpectrum_le_of_sampleStartCoverage
    (f : S → E) {x : E → ℕ}
    (hx : FiniteStartCoverage.SampleStartCoverage f x) :
    ∀ e, FiniteStartCoverage.startSpectrum f e ≤ x e := by
  obtain ⟨m, hm, hsum⟩ := hx
  intro e
  have hcard : (Finset.univ.filter (fun s => f s = e)).card
      = FiniteStartCoverage.startSpectrum f e := rfl
  have hle : (Finset.univ.filter (fun s => f s = e)).card
      ≤ ∑ s ∈ Finset.univ.filter (fun s => f s = e), m s := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum (fun s _ => hm s)
  rw [← hsum e, ← hcard]
  exact hle

/-- **Covered-start-sample classification.**  For a surjective start-to-type
map `f`, the truth spectrum's product-binomial score dominates a competitor
`B` on every read sample that covers each true genome start at least once if
and only if the competitor has a zero effective weight on the modeled types or
its effective weights are pointwise dominated by the truth's. -/
theorem covered_start_samples_effectiveProduct_le_iff
    (f : S → E) (hf : Function.Surjective f) (N : ℕ) (B : E → ℕ)
    (hA : ∀ e, 0 < FiniteStartCoverage.startSpectrum f e)
    (hqA : ∀ e, 0 < FixedNBinomialEffectiveWeights.effectiveWeight N
      (FiniteStartCoverage.startSpectrum f) e) :
    (∀ x : E → ℕ, FiniteStartCoverage.SampleStartCoverage f x →
        FixedNBinomialEffectiveWeights.effectiveProduct N B x
          ≤ FixedNBinomialEffectiveWeights.effectiveProduct N
              (FiniteStartCoverage.startSpectrum f) x) ↔
      ((∃ e, FixedNBinomialEffectiveWeights.effectiveWeight N B e = 0) ∨
        (∀ e, FixedNBinomialEffectiveWeights.effectiveWeight N B e
          ≤ FixedNBinomialEffectiveWeights.effectiveWeight N
              (FiniteStartCoverage.startSpectrum f) e)) := by
  have key := covered_effectiveProduct_le_iff N
    (FiniteStartCoverage.startSpectrum f) B hA hqA
  constructor
  · intro h
    refine key.mp ?_
    intro x hx
    exact h x (FiniteStartCoverage.coverage_of_type_budget f hf x hx)
  · intro h x hx
    exact key.mpr h x (startSpectrum_le_of_sampleStartCoverage f hx)

end Coverage

/-! ## Ambient full-universe support

The same-support specialization above fixes `E` to be exactly the true support
and evaluates `effectiveWeight N ·` over `E` only.  MB09 §6.1 instead scores
over the *whole* modeled molecule universe `U` (all `4 ^ k` classes for read
length `k`), so a candidate's effective weight `q_i(B) = B i * ∏_{j : U, j ≠ i}
(N - B j)` keeps the `(N - B j)` factors of classes with `x j = 0`, and a
candidate may put mass on a class outside the truth's support.  The adapter
below keeps the full universe: the generic criterion is run on the subtype
`{j : U // 0 < A j}` of true-supported classes while `q_i(A)` and `q_i(B)` are
computed over all of `U`.  The whole-universe product reduces to the product
over the true support because off-support counts are `0` and `q ^ 0 = 1`. -/

section Ambient

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- For an ambient sample supported on `A`'s true support, the whole-universe
product-binomial numerator equals the product over the true-supported
coordinates.  This keeps every unobserved `(N - B j)` factor of `#259`'s MB09
§6.1 model while running the generic criterion on the true support. -/
theorem effectiveProduct_eq_trueSupportProduct
    (N : ℕ) (A B x : U → ℕ) (hx : ∀ j, A j = 0 → x j = 0) :
    FixedNBinomialEffectiveWeights.effectiveProduct N B x
      = ∏ i : {j : U // 0 < A j},
          FixedNBinomialEffectiveWeights.effectiveWeight N B i.1 ^ x i.1 := by
  unfold FixedNBinomialEffectiveWeights.effectiveProduct
  rw [← Finset.prod_filter_of_ne (s := Finset.univ) (p := fun i => 0 < A i)
        (f := fun i => FixedNBinomialEffectiveWeights.effectiveWeight N B i ^ x i)
        (fun i _ hne => by
          by_contra hA
          have hA0 : A i = 0 := Nat.eq_zero_of_not_pos hA
          rw [hx i hA0, pow_zero] at hne
          exact hne rfl)]
  exact Finset.prod_subtype (Finset.univ.filter (fun i => 0 < A i)) (fun i => by simp)
    (fun i => FixedNBinomialEffectiveWeights.effectiveWeight N B i ^ x i)

/-- **Ambient-support covered-sample criterion.**  Over the full modeled
molecule universe `U` — so every MB09 §6.1 class, including unobserved ones,
enters `effectiveWeight N B` — a candidate `B` is dominated by the truth `A` on
every supported covered sample if and only if it has a zero effective weight on
a true-supported class or its effective weights are pointwise dominated on the
true support. -/
theorem covered_ambient_effectiveProduct_le_iff
    (N : ℕ) (A B : U → ℕ)
    (hqA : ∀ i, 0 < A i → 0 < FixedNBinomialEffectiveWeights.effectiveWeight N A i) :
    (∀ x : U → ℕ, (∀ i, A i ≤ x i) → (∀ j, A j = 0 → x j = 0) →
        FixedNBinomialEffectiveWeights.effectiveProduct N B x
          ≤ FixedNBinomialEffectiveWeights.effectiveProduct N A x) ↔
      ((∃ i, 0 < A i ∧ FixedNBinomialEffectiveWeights.effectiveWeight N B i = 0) ∨
        (∀ i, 0 < A i → FixedNBinomialEffectiveWeights.effectiveWeight N B i
          ≤ FixedNBinomialEffectiveWeights.effectiveWeight N A i)) := by
  have key := covered_product_le_iff_zero_or_pointwise
    (fun i : {j : U // 0 < A j} =>
      FixedNBinomialEffectiveWeights.effectiveWeight N A i.1)
    (fun i : {j : U // 0 < A j} =>
      FixedNBinomialEffectiveWeights.effectiveWeight N B i.1)
    (fun i : {j : U // 0 < A j} => A i.1)
    (fun i => hqA i.1 i.2) (fun i => i.2)
  have hLHS : (∀ x : U → ℕ, (∀ i, A i ≤ x i) → (∀ j, A j = 0 → x j = 0) →
        FixedNBinomialEffectiveWeights.effectiveProduct N B x
          ≤ FixedNBinomialEffectiveWeights.effectiveProduct N A x) ↔
      (∀ y : {j : U // 0 < A j} → ℕ, (∀ i, A i.1 ≤ y i) →
        (∏ i : {j : U // 0 < A j},
            FixedNBinomialEffectiveWeights.effectiveWeight N B i.1 ^ y i)
          ≤ (∏ i : {j : U // 0 < A j},
              FixedNBinomialEffectiveWeights.effectiveWeight N A i.1 ^ y i)) := by
    constructor
    · intro h y hy
      have hdom : ∀ i, A i ≤ (fun j => if h : 0 < A j then y ⟨j, h⟩ else 0) i := by
        intro i
        change A i ≤ (if h : 0 < A i then y ⟨i, h⟩ else 0)
        by_cases hi : 0 < A i
        · rw [dite_eq_left hi]; exact hy ⟨i, hi⟩
        · rw [dite_eq_right hi]; exact Nat.le_of_eq (Nat.eq_zero_of_not_pos hi)
      have hsupp : ∀ j, A j = 0 →
          (fun j => if h : 0 < A j then y ⟨j, h⟩ else 0) j = 0 := by
        intro j hj
        change (if h : 0 < A j then y ⟨j, h⟩ else 0) = 0
        rw [dite_eq_right (by omega : ¬ 0 < A j)]
      have hpr := h _ hdom hsupp
      rw [effectiveProduct_eq_trueSupportProduct N A B _ hsupp,
          effectiveProduct_eq_trueSupportProduct N A A _ hsupp] at hpr
      have hamb : ∀ i : {j : U // 0 < A j},
          (fun j => if h : 0 < A j then y ⟨j, h⟩ else 0) i.1 = y i := by
        intro i
        change (if h : 0 < A i.1 then y ⟨i.1, h⟩ else 0) = y i
        rw [dite_eq_left i.2]
      simpa only [hamb] using hpr
    · intro h x hxdom hxsupp
      have hpr := h (fun i : {j : U // 0 < A j} => x i.1) (fun i => hxdom i.1)
      rw [effectiveProduct_eq_trueSupportProduct N A B x hxsupp,
          effectiveProduct_eq_trueSupportProduct N A A x hxsupp]
      exact hpr
  have hRHS : ((∃ i : {j : U // 0 < A j},
          FixedNBinomialEffectiveWeights.effectiveWeight N B i.1 = 0) ∨
        (∀ i : {j : U // 0 < A j},
          FixedNBinomialEffectiveWeights.effectiveWeight N B i.1
            ≤ FixedNBinomialEffectiveWeights.effectiveWeight N A i.1)) ↔
      ((∃ i, 0 < A i ∧ FixedNBinomialEffectiveWeights.effectiveWeight N B i = 0) ∨
        (∀ i, 0 < A i → FixedNBinomialEffectiveWeights.effectiveWeight N B i
          ≤ FixedNBinomialEffectiveWeights.effectiveWeight N A i)) := by
    constructor
    · rintro (⟨i, hi⟩ | h)
      · exact Or.inl ⟨i.1, i.2, hi⟩
      · exact Or.inr (fun i hi => h ⟨i, hi⟩)
    · rintro (⟨i, hi, h0⟩ | h)
      · exact Or.inl ⟨⟨i, hi⟩, h0⟩
      · exact Or.inr (fun i => h i.1 i.2)
  exact hLHS.trans (key.trans hRHS)

variable {S : Type*} [Fintype S]

omit [Fintype U] in
/-- A start-coverage sample never observes a read type that no true genome
start produces: if `startSpectrum f j = 0`, the fibre over `j` is empty, so its
sample count is `0`.  This is the support condition the ambient criterion
needs, obtained from actual start coverage rather than assumed. -/
theorem sampleStartCoverage_eq_zero_of_startSpectrum_eq_zero
    (f : S → U) {x : U → ℕ}
    (hx : FiniteStartCoverage.SampleStartCoverage f x) (j : U)
    (hj : FiniteStartCoverage.startSpectrum f j = 0) : x j = 0 := by
  obtain ⟨m, _hm, hsum⟩ := hx
  rw [← hsum j]
  have hempty : Finset.univ.filter (fun s => f s = j) = ∅ := by
    apply Finset.card_eq_zero.mp
    have hc : (Finset.univ.filter (fun s => f s = j)).card
        = FiniteStartCoverage.startSpectrum f j := rfl
    rw [hc, hj]
  rw [hempty, Finset.sum_empty]

omit [Fintype U] in
/-- A type-wise budget that dominates the true start spectrum and is supported
on the true support is realizable by positive multiplicities of every true
genome start, even when the ambient modeled universe `U` is strictly larger
than the true support.  This is the ambient analogue of
`FiniteStartCoverage.coverage_of_type_budget`, which required surjectivity onto
the *whole* universe; here only surjectivity onto the supported subtype
`{i : U // 0 < startSpectrum f i}` is needed, and it holds automatically. -/
theorem sampleStartCoverage_of_budget
    (f : S → U) {x : U → ℕ}
    (hdom : ∀ i, FiniteStartCoverage.startSpectrum f i ≤ x i)
    (hsupp : ∀ j, FiniteStartCoverage.startSpectrum f j = 0 → x j = 0) :
    FiniteStartCoverage.SampleStartCoverage f x := by
  classical
  let f0 : S → {i : U // 0 < FiniteStartCoverage.startSpectrum f i} := fun s =>
    ⟨f s, by
      unfold FiniteStartCoverage.startSpectrum
      exact Finset.card_pos.mpr
        ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ s, rfl⟩⟩⟩
  have hf0 : Function.Surjective f0 := by
    intro i
    have hpos : 0 < FiniteStartCoverage.startSpectrum f i.1 := i.2
    unfold FiniteStartCoverage.startSpectrum at hpos
    obtain ⟨s, hs⟩ := Finset.card_pos.mp hpos
    exact ⟨s, Subtype.ext (Finset.mem_filter.mp hs).2⟩
  have hspec : ∀ i : {j : U // 0 < FiniteStartCoverage.startSpectrum f j},
      FiniteStartCoverage.startSpectrum f0 i
        = FiniteStartCoverage.startSpectrum f i.1 := by
    intro i
    unfold FiniteStartCoverage.startSpectrum
    congr 1
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, f0]
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  obtain ⟨m, hmpos, hcounts⟩ := FiniteStartCoverage.coverage_of_type_budget f0 hf0
    (fun i => x i.1) (fun i => by rw [hspec i]; exact hdom i.1)
  refine ⟨m, hmpos, fun e => ?_⟩
  by_cases he : 0 < FiniteStartCoverage.startSpectrum f e
  · have hc := hcounts ⟨e, he⟩
    have hfilter : Finset.univ.filter (fun s => f s = e)
        = Finset.univ.filter (fun s => f0 s = ⟨e, he⟩) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, f0]
      constructor
      · intro h; exact Subtype.ext h
      · intro h; exact congrArg Subtype.val h
    rw [hfilter]
    exact hc
  · have hA0 : FiniteStartCoverage.startSpectrum f e = 0 :=
      Nat.eq_zero_of_not_pos he
    rw [hsupp e hA0]
    have hempty : Finset.univ.filter (fun s => f s = e) = ∅ := by
      apply Finset.card_eq_zero.mp
      have hc : (Finset.univ.filter (fun s => f s = e)).card
          = FiniteStartCoverage.startSpectrum f e := rfl
      rw [hc, hA0]
    rw [hempty, Finset.sum_empty]

/-- **Ambient covered-start-sample classification.**  Over the full modeled
molecule universe `U` — so every MB09 §6.1 class, including unobserved ones,
enters `effectiveWeight N B` — a candidate `B` is dominated by the true start
spectrum `A = startSpectrum f` on every read sample that visits each true
genome start at least once if and only if it has a zero effective weight on a
true-supported class or its effective weights are pointwise dominated by the
truth's on the true support.  Unlike
`covered_start_samples_effectiveProduct_le_iff`, this does **not** require `f`
to be surjective onto `U`; a candidate may put mass on classes outside the
truth's support, and those unobserved `(N - B j)` factors are retained. -/
theorem covered_ambient_start_samples_effectiveProduct_le_iff
    (f : S → U) (N : ℕ) (B : U → ℕ)
    (hqA : ∀ i, 0 < FiniteStartCoverage.startSpectrum f i →
      0 < FixedNBinomialEffectiveWeights.effectiveWeight N
        (FiniteStartCoverage.startSpectrum f) i) :
    (∀ x : U → ℕ, FiniteStartCoverage.SampleStartCoverage f x →
        FixedNBinomialEffectiveWeights.effectiveProduct N B x
          ≤ FixedNBinomialEffectiveWeights.effectiveProduct N
              (FiniteStartCoverage.startSpectrum f) x) ↔
      ((∃ i, 0 < FiniteStartCoverage.startSpectrum f i ∧
          FixedNBinomialEffectiveWeights.effectiveWeight N B i = 0) ∨
        (∀ i, 0 < FiniteStartCoverage.startSpectrum f i →
          FixedNBinomialEffectiveWeights.effectiveWeight N B i
            ≤ FixedNBinomialEffectiveWeights.effectiveWeight N
                (FiniteStartCoverage.startSpectrum f) i)) := by
  have key := covered_ambient_effectiveProduct_le_iff N
    (FiniteStartCoverage.startSpectrum f) B hqA
  constructor
  · intro h
    refine key.mp ?_
    intro x hdom hsupp
    exact h x (sampleStartCoverage_of_budget f hdom hsupp)
  · intro h x hx
    exact key.mpr h x
      (startSpectrum_le_of_sampleStartCoverage f hx)
      (sampleStartCoverage_eq_zero_of_startSpectrum_eq_zero f hx)

end Ambient

/-- A candidate supported on a **new** molecule class (outside the truth's
support) can still be dominated: with `A = (2, 0)`, `B = (1, 1)`, `N = 4` the
unobserved class-`1` factor gives `effectiveWeight 4 B 0 = 1 * (4 - 1) = 3 ≤ 8
= effectiveWeight 4 A 0`, so the dominance branch holds and the truth is a
uniform covered-sample maximizer. -/
theorem newsupport_dominated :
    ((∃ i, 0 < (fun i : Fin 2 => if i = 0 then 2 else 0) i ∧
        FixedNBinomialEffectiveWeights.effectiveWeight 4
          (fun i : Fin 2 => if i = 0 then 1 else 1) i = 0) ∨
      (∀ i, 0 < (fun i : Fin 2 => if i = 0 then 2 else 0) i →
        FixedNBinomialEffectiveWeights.effectiveWeight 4
            (fun i : Fin 2 => if i = 0 then 1 else 1) i
          ≤ FixedNBinomialEffectiveWeights.effectiveWeight 4
              (fun i : Fin 2 => if i = 0 then 2 else 0) i)) := by
  decide

/-- A candidate with new support can also **defeat** the truth: with
`A = (2, 0)`, `B = (3, 1)`, `N = 4` we get `effectiveWeight 4 B 0 = 3 * (4 - 1)
= 9 > 8 = effectiveWeight 4 A 0` and the zero branch fails, so the truth is not
a uniform covered-sample maximizer.  This attains the ambient criterion's
failure branch with genuinely new support. -/
theorem newsupport_defeats :
    ¬ ((∃ i, 0 < (fun i : Fin 2 => if i = 0 then 2 else 0) i ∧
        FixedNBinomialEffectiveWeights.effectiveWeight 4
          (fun i : Fin 2 => if i = 0 then 3 else 1) i = 0) ∨
      (∀ i, 0 < (fun i : Fin 2 => if i = 0 then 2 else 0) i →
        FixedNBinomialEffectiveWeights.effectiveWeight 4
            (fun i : Fin 2 => if i = 0 then 3 else 1) i
          ≤ FixedNBinomialEffectiveWeights.effectiveWeight 4
              (fun i : Fin 2 => if i = 0 then 2 else 0) i)) := by
  decide

/-! ## Non-vacuity witnesses

The classification is not vacuous: on the one-element universe both sides are
genuinely satisfiable, the zero-weight branch is exercised, and the left-hand
dominance condition can genuinely fail (so it is not an empty hypothesis). -/

/-- Both sides hold with equal positive weights. -/
theorem nonvacuity_holds :
    (∀ x : Fin 1 → ℕ, (∀ e, 1 ≤ x e) →
        (∏ e : Fin 1, (1 : ℕ) ^ x e) ≤ (∏ e : Fin 1, (1 : ℕ) ^ x e)) ∧
      ((∃ _e : Fin 1, (1 : ℕ) = 0) ∨ (∀ _e : Fin 1, (1 : ℕ) ≤ (1 : ℕ))) :=
  ⟨fun _ _ => le_refl _, Or.inr (fun _ => le_refl 1)⟩

/-- Both sides hold through the zero-weight branch: the competitor score is
`0` on every covered sample while the truth score is positive. -/
theorem nonvacuity_zero :
    (∀ x : Fin 1 → ℕ, (∀ e, 1 ≤ x e) →
        (∏ e : Fin 1, (0 : ℕ) ^ x e) ≤ (∏ e : Fin 1, (1 : ℕ) ^ x e)) ∧
      ((∃ _e : Fin 1, (0 : ℕ) = 0) ∨ (∀ _e : Fin 1, (0 : ℕ) ≤ (1 : ℕ))) :=
  ⟨fun x _ => Finset.prod_le_prod
      (fun e _ => Nat.pow_le_pow_left (Nat.zero_le 1) (x e)),
    Or.inl ⟨0, rfl⟩⟩

/-- The dominance condition genuinely fails: the competing weight `2` beats
the truth weight `1` on the covered sample `x = 1`, so the left-hand side of
the classification is not a triviality. -/
theorem nonvacuity_left_fails :
    ¬ (∀ x : Fin 1 → ℕ, (∀ e, 1 ≤ x e) →
        (∏ e : Fin 1, (2 : ℕ) ^ x e) ≤ (∏ e : Fin 1, (1 : ℕ) ^ x e)) := by
  intro h
  have hbad := h (fun _ => 1) (fun _ => le_refl 1)
  exact absurd hbad (by decide)

end AssemblyP1.CoveredBinomialWeightsIff
