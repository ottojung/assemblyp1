import AssemblyP1.Section62BinomialCriterion

/-!
# Fixed-n extreme-sample reduction (#261)

This is the finite-sample counterpart of the existing all-sample
`Section62BinomialCriterion.binomial_uniform_criterion`.
Given n at least the number of distinct observed types I, write
n = |I| + t. Every full-coverage sample has one copy of each observed
type and distributes t surplus copies. Because a product of nonnegative
weights with a fixed exponent sum is maximized by concentrating the
surplus on a single maximally weighted type, the whole infinite-looking
family of allocations reduces to |I| explicit extreme allocations.

The first theorem is a model-independent finite product statement in Q.
The direct §6.1 count-vector specialization is derived below; this
module makes no assertion about flow realizability or candidate genomes.
-/

set_option linter.unusedSectionVars false

namespace AssemblyP1.Section62FiniteNExtremeSamples

open Finset
open AssemblyP1.Section62BinomialCriterion
open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

/-- For any nonnegative rational weights, concentrating all t units of
exponent on a maximum-weight coordinate dominates every allocation of t
units over a finite nonempty set. -/
theorem product_le_extreme
    (I : Finset ι) (hI : I.Nonempty) (r : ι → ℚ) (x : ι → ℕ)
    (t : ℕ) (hr : ∀ i ∈ I, 0 ≤ r i)
    (hsum : ∑ i ∈ I, x i = t) :
    ∃ k ∈ I, (∏ i ∈ I, r i ^ x i) ≤ r k ^ t := by
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image I r hI
  refine ⟨k, hk, ?_⟩
  calc
    (∏ i ∈ I, r i ^ x i) ≤ ∏ i ∈ I, r k ^ x i := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact pow_nonneg (hr i hi) (x i)
      · intro i hi
        exact pow_le_pow_left₀ (hr i hi) (hmax i hi) (x i)
    _ = r k ^ t := by rw [Finset.prod_pow_eq_pow_sum, hsum]

/-- The precise fixed-surplus iff: a nonnegative baseline ratio times
every weighted product with exponent sum t is <= 1 iff the same
inequality holds at the |I| concentrated extreme points. -/
theorem rational_extreme_iff
    (I : Finset ι) (hI : I.Nonempty) (r : ι → ℚ)
    (R : ℚ) (t : ℕ)
    (hr : ∀ i ∈ I, 0 ≤ r i) (hR : 0 ≤ R) :
    (∀ x : ι → ℕ, (∑ i ∈ I, x i) = t →
      R * (∏ i ∈ I, r i ^ x i) ≤ 1) ↔
      (∀ k ∈ I, R * r k ^ t ≤ 1) := by
  constructor
  · intro hall k hk
    let x : ι → ℕ := fun i => if i = k then t else 0
    have hsum : ∑ i ∈ I, x i = t := by
      simp [x, hk]
    have hscore := hall x hsum
    simpa [x, hk] using hscore
  · intro hext x hx
    obtain ⟨k, hk, hprod⟩ := product_le_extreme I hI r x t hr hx
    exact (mul_le_mul_of_nonneg_left hprod hR).trans (hext k hk)


/-- Cross-multiplied fixed-surplus iff over rational score weights.  The
denominator weights `a` must be strictly positive; candidate weights `b`
may vanish. This avoids informal division by a zero likelihood. -/
theorem weighted_extreme_iff
    (I : Finset ι) (hI : I.Nonempty)
    (a b : ι → ℚ) (PA PB : ℚ) (t : ℕ)
    (ha : ∀ i ∈ I, 0 < a i) (hb : ∀ i ∈ I, 0 ≤ b i)
    (hPA : 0 < PA) (hPB : 0 ≤ PB) :
    (∀ e : ι → ℕ, (∑ i ∈ I, e i) = t →
       PB * (∏ i ∈ I, b i ^ e i) ≤
         PA * (∏ i ∈ I, a i ^ e i)) ↔
      (∀ k ∈ I, PB * (b k) ^ t ≤ PA * (a k) ^ t) := by
  let r : ι → ℚ := fun i => b i / a i
  let R : ℚ := PB / PA
  have hr : ∀ i ∈ I, 0 ≤ r i := by
    intro i hi
    exact div_nonneg (hb i hi) (le_of_lt (ha i hi))
  have hR : 0 ≤ R := div_nonneg hPB (le_of_lt hPA)
  have hscore (e : ι → ℕ) :
      (R * (∏ i ∈ I, r i ^ e i) ≤ 1) ↔
        (PB * (∏ i ∈ I, b i ^ e i) ≤
          PA * (∏ i ∈ I, a i ^ e i)) := by
    have hden : 0 < PA * (∏ i ∈ I, a i ^ e i) := by
      apply mul_pos hPA
      apply Finset.prod_pos
      intro i hi
      exact pow_pos (ha i hi) _
    have hratio :
        R * (∏ i ∈ I, r i ^ e i) =
          (PB * (∏ i ∈ I, b i ^ e i)) /
            (PA * (∏ i ∈ I, a i ^ e i)) := by
      dsimp [R,r]
      simp_rw [div_pow]
      rw [Finset.prod_div_distrib]
      exact div_mul_div_comm PB PA _ _
    rw [hratio, div_le_one hden]
  have hcorner (k : ι) (hk : k ∈ I) :
      (R * r k ^ t ≤ 1) ↔ PB * b k ^ t ≤ PA * a k ^ t := by
    have hden : 0 < PA * a k ^ t :=
      mul_pos hPA (pow_pos (ha k hk) _)
    dsimp [R,r]
    rw [div_pow, div_mul_div_comm, div_le_one hden]
  constructor
  · intro hall k hk
    have hratio : ∀ e : ι → ℕ, (∑ i ∈ I, e i) = t →
        R * (∏ i ∈ I, r i ^ e i) ≤ 1 :=
      fun e he => (hscore e).mpr (hall e he)
    have hbound := (rational_extreme_iff I hI r R t hr hR).mp hratio k hk
    exact (hcorner k hk).mp hbound
  · intro hcornerBound e he
    have hext : ∀ k ∈ I, R * r k ^ t ≤ 1 := by
      intro k hk
      exact (hcorner k hk).mpr (hcornerBound k hk)
    have hbound := (rational_extreme_iff I hI r R t hr hR).mpr hext e he
    exact (hscore e).mp hbound

#print axioms weighted_extreme_iff


/-! ## Direct fixed-n §6.1 count-vector criterion -/

variable [Fintype ι]

/-- For an exactly covered observed support, removing the mandatory one
occurrence per observed class leaves exactly n-|I| surplus occurrences. -/
theorem surplus_sum_of_fullcoverage
    (I : Finset ι) (x : ι → ℕ) (t : ℕ)
    (hx : IsSupportedOn I x)
    (hTotal : (∑ i, x i) = I.card + t) :
    ∑ i ∈ I, (x i - 1) = t := by
  have hPos : ∀ i ∈ I, 0 < x i :=
    fun i hi => (hx i).mpr hi
  have hsumI : (∑ i ∈ I, x i) = ∑ i, x i := by
    apply Finset.sum_subset (Finset.subset_univ I)
    intro i _ hi
    have hn : ¬ 0 < x i := fun hp => hi ((hx i).mp hp)
    omega
  have hdecomp : (∑ i ∈ I, x i) =
      I.card + (∑ i ∈ I, (x i - 1)) := by
    calc
      (∑ i ∈ I, x i) =
          ∑ i ∈ I, ((1 : ℕ) + (x i - 1)) := by
            apply Finset.sum_congr rfl
            intro i hi
            have := hPos i hi
            omega
      _ = (∑ _i ∈ I, (1 : ℕ)) + ∑ i ∈ I, (x i - 1) := by
            rw [Finset.sum_add_distrib]
      _ = I.card + (∑ i ∈ I, (x i - 1)) := by simp
  omega

/-- The §6.1 q-factorization for an exactly covered sample with its
mandatory one read per type extracted. -/
theorem binomCoreNat_factor_surplus
    (C x : ι → ℕ) (N : ℕ) (I : Finset ι)
    (hx : IsSupportedOn I x) :
    binomCoreNat C x N =
      (∏ i ∈ I, qFac C i N) *
        ∏ i ∈ I, qFac C i N ^ (x i - 1) := by
  rw [binomCoreNat_eq_prod_qFac, prod_qFac_subset C x N I hx]
  calc
    (∏ i ∈ I, qFac C i N ^ x i) =
        ∏ i ∈ I, (qFac C i N * qFac C i N ^ (x i - 1)) := by
          apply Finset.prod_congr rfl
          intro i hi
          have hPos : 0 < x i := (hx i).mpr hi
          have heq : x i = 1 + (x i - 1) := by omega
          calc
            qFac C i N ^ x i = qFac C i N ^ (1 + (x i - 1)) :=
              congrArg (fun j : ℕ => qFac C i N ^ j) heq
            _ = qFac C i N * qFac C i N ^ (x i - 1) := by simp [pow_add]
    _ = (∏ i ∈ I, qFac C i N) *
        ∏ i ∈ I, qFac C i N ^ (x i - 1) :=
          Finset.prod_mul_distrib

/-- **Exact fixed-n full-coverage extreme-sample iff.**
For any observed nonempty support I, fixed read total |I|+t, positive
truth effective weights q_A(i), and *full-universe* §6.1 product-binomial
scores, no precisely-supported sample can make candidate B beat A iff
none of |I| explicit concentration samples can. The finite-n criterion
is PA*q_A(k)^t >= PB*q_B(k)^t for all k∈I, where
PA=∏_{i∈I}q_A(i), PB=∏_{i∈I}q_B(i).
This is only for the count-vector universe; candidate flow/genome
realizability is not assumed. -/
theorem binomial_fixed_n_extreme_iff
    (A B : ι → ℕ) (N : ℕ)
    (I : Finset ι) (hI : I.Nonempty) (t : ℕ)
    (hA : ∀ i ∈ I, 0 < qFac A i N) :
    (∀ x : ι → ℕ, IsSupportedOn I x →
      (∑ i, x i) = I.card + t →
      binomCoreNat B x N ≤ binomCoreNat A x N) ↔
        (∀ k ∈ I,
          (∏ i ∈ I, qFac B i N) * qFac B k N ^ t ≤
            (∏ i ∈ I, qFac A i N) * qFac A k N ^ t) := by
  let PA : ℕ := ∏ i ∈ I, qFac A i N
  let PB : ℕ := ∏ i ∈ I, qFac B i N
  have hPA : 0 < PA := Finset.prod_pos (fun i hi => hA i hi)
  have hWeight : (∀ e : ι → ℕ, (∑ i ∈ I, e i) = t →
        PB * (∏ i ∈ I, qFac B i N ^ e i) ≤
          PA * (∏ i ∈ I, qFac A i N ^ e i)) ↔
        (∀ k ∈ I, PB * qFac B k N ^ t ≤ PA * qFac A k N ^ t) := by
    have hAq : ∀ i ∈ I, 0 < (qFac A i N : ℚ) := by
      intro i hi
      exact_mod_cast hA i hi
    have hBq : ∀ i ∈ I, 0 ≤ (qFac B i N : ℚ) := by
      intro i hi
      positivity
    have hPAq : 0 < (PA : ℚ) := by exact_mod_cast hPA
    have hPBq : 0 ≤ (PB : ℚ) := by positivity
    have hq := weighted_extreme_iff I hI
      (fun i => (qFac A i N : ℚ))
      (fun i => (qFac B i N : ℚ))
      (PA : ℚ) (PB : ℚ) t hAq hBq hPAq hPBq
    constructor
    · intro hall k hk
      have hqall : ∀ e : ι → ℕ, (∑ i ∈ I, e i) = t →
          (PB : ℚ) * (∏ i ∈ I, (qFac B i N : ℚ) ^ e i) ≤
            (PA : ℚ) * (∏ i ∈ I, (qFac A i N : ℚ) ^ e i) := by
        intro e he
        exact_mod_cast hall e he
      have hres := hq.mp hqall k hk
      exact_mod_cast hres
    · intro hext e he
      have hqext : ∀ k ∈ I,
          (PB : ℚ) * (qFac B k N : ℚ) ^ t ≤
            (PA : ℚ) * (qFac A k N : ℚ) ^ t := by
        intro k hk
        exact_mod_cast hext k hk
      have hres := hq.mpr hqext e he
      exact_mod_cast hres
  constructor
  · intro hall k hk
    let x : ι → ℕ := fun i => (if i ∈ I then 1 else 0) +
      (if i = k then t else 0)
    have hx : IsSupportedOn I x := isSupportedOn_concentrated I k hk t
    have htotal : (∑ i, x i) = I.card + t := by
      simp [x, Finset.sum_add_distrib]
    have hres := hall x hx htotal
    rw [show binomCoreNat B x N = PB * qFac B k N ^ t from
      binomCoreNat_concentrated B N I k hk t,
      show binomCoreNat A x N = PA * qFac A k N ^ t from
      binomCoreNat_concentrated A N I k hk t] at hres
    exact hres
  · intro hext x hx htotal
    have hsum := surplus_sum_of_fullcoverage I x t hx htotal
    have hres := hWeight.mpr hext (fun i => x i - 1) hsum
    rw [binomCoreNat_factor_surplus B x N I hx,
      binomCoreNat_factor_surplus A x N I hx]
    exact hres

#print axioms surplus_sum_of_fullcoverage
#print axioms binomCoreNat_factor_surplus
#print axioms binomial_fixed_n_extreme_iff


namespace Regression

/-- At n=2 and I={0,1}, every covered sample has exactly one copy of
each observed type. Truth A=(1,2) and candidate B=(1,1) therefore tie,
even though B's first q-weight (2) exceeds A's first q-weight (1). -/
theorem fixed_two_reads_never_beat :
    ∀ x : Fin 2 → ℕ,
      IsSupportedOn Finset.univ x →
      (∑ i, x i) = 2 →
      binomCoreNat ![1,1] x 3 ≤ binomCoreNat ![1,2] x 3 := by
  have hI : (Finset.univ : Finset (Fin 2)).Nonempty := by simp
  have hA : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      0 < qFac ![1,2] i 3 := by decide
  have h := (binomial_fixed_n_extreme_iff
    ![1,2] ![1,1] 3 (Finset.univ : Finset (Fin 2))
    hI 0 hA).mpr (by decide)
  simpa using h

/-- As soon as n=3 (one surplus observation), concentrating that extra
read on type zero strictly lets B beat A. -/
theorem fixed_three_reads_can_beat :
    ¬ (∀ x : Fin 2 → ℕ,
      IsSupportedOn Finset.univ x →
      (∑ i, x i) = 3 →
      binomCoreNat ![1,1] x 3 ≤ binomCoreNat ![1,2] x 3) := by
  have hI : (Finset.univ : Finset (Fin 2)).Nonempty := by simp
  have hA : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      0 < qFac ![1,2] i 3 := by decide
  intro hall
  have h := (binomial_fixed_n_extreme_iff
    ![1,2] ![1,1] 3 (Finset.univ : Finset (Fin 2))
    hI 1 hA).mp hall
  have hfalse : ¬ (∀ k ∈ (Finset.univ : Finset (Fin 2)),
      (∏ i : Fin 2, qFac ![1,1] i 3) * qFac ![1,1] k 3 ^ 1 ≤
        (∏ i : Fin 2, qFac ![1,2] i 3) * qFac ![1,2] k 3 ^ 1) := by decide
  exact hfalse h

/-- Candidate with a zero q-weight on an observed type is never better
on a full-coverage sample, for any surplus count, even with other
candidate weights positive. This checks the zero boundary. -/
theorem zero_candidate_weight_never_beats (t : ℕ) :
    ∀ x : Fin 2 → ℕ,
      IsSupportedOn Finset.univ x →
      (∑ i, x i) = 2 + t →
      binomCoreNat ![0,1] x 3 ≤ binomCoreNat ![1,2] x 3 := by
  have hI : (Finset.univ : Finset (Fin 2)).Nonempty := by simp
  have hA : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      0 < qFac ![1,2] i 3 := by decide
  have h := (binomial_fixed_n_extreme_iff
    ![1,2] ![0,1] 3 (Finset.univ : Finset (Fin 2))
    hI t hA).mpr (by
      intro k hk
      have hPB : (∏ i : Fin 2, qFac ![0,1] i 3) = 0 := by decide
      simp [hPB])
  simpa using h

#print axioms fixed_two_reads_never_beat
#print axioms fixed_three_reads_can_beat
#print axioms zero_candidate_weight_never_beats

end Regression

#print axioms product_le_extreme
#print axioms rational_extreme_iff

end AssemblyP1.Section62FiniteNExtremeSamples
