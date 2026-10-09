import AssemblyP1.SameLengthSection62Counterexample

/-!
# Parametric strengthening of the same-length §6.2 counterexample

This file is an *independent optional strengthening* of the already
kernel-checked same-length Section 6.2 counterexample in
`AssemblyP1.SameLengthSection62Counterexample`.  It does **not** replace the
`k = 0` theorem there; it packages the whole family.

Fix the genuine MB09 molecule-flow witness of that module:

* truth `S = AAATAT`, competitor `D = AAAAAT`, both length `G = 6`;
* read length `L = 3`, external genome size `N = 6`;
* molecule classes `AAA, AAT, ATA, TAA` (`Fin 8` codes `0, 1, 2, 4`);
* the four realized placements `{0, 1, 3, 5}` (start `0` sampled twice).

For an arbitrary `k : ℕ` we add `k` extra *actual* `AAA` reads at start `0`.
The realized sampling then has `n = 5 + k` reads and observed molecule counts

* `x AAA = 2 + k`, `x AAT = 1`, `x ATA = 1`, `x TAA = 1`, all others `0`.

The set of realized *placements* is unchanged (`{0, 1, 3, 5}`), so the observed
read support, the historical `I_s` coverage/bridging hypothesis and the full
§6.2 spelled-flow feasibility of both `S` and `D` are *literally unchanged* from
the `k = 0` module.  What changes is only the multiplicity entering the two
likelihood objectives.

The main results are the candidate-intrinsic exact multinomial ratio

* `exactLik_ratio : exactLik dD (obsK k) / exactLik dS (obsK k) = 3 ^ (k + 1)`

and the fixed-`N` §6.1 product-of-binomial-marginals ratio (with *all* eight
class factors, including the zero-count ones)

* `likN_ratio : likN (5 + k) (obsK k) dD / likN (5 + k) (obsK k) dS = 5 ^ (k + 1)`,

both strictly `> 1` for every `k`.  The exact algebra is the one described in
MB09 §6.1: the increment `x AAA + 1` multiplies the exact ratio by `3` (because
`d_D AAA / d_S AAA = 3`), while the binomial ratio increment additionally shifts
`n` in every complement exponent, giving `3 * (5 / 3) = 5` per step.

Scope.  As with the `k = 0` module, this is a statement about this one finite
instance family, not a settlement of which Medvedev–Brudno object the
Shomorony et al. (2016) sentence intends.
-/

set_option maxHeartbeats 2000000

namespace AssemblyP1.SameLengthSection62Parametric

open AssemblyP1.SameLengthSection62Counterexample
open AssemblyP1.Section62Flow
open SourceFaithfulIs

/-! ## The parameterized read realization -/

/-- The original five realized starts with `k` extra `AAA` reads at start `0`.

For `k = 0` this is exactly `[0, 0, 1, 3, 5]`, the sampling realization of the
`k = 0` module. -/
def readStartsK (k : Nat) : List (Fin 6) :=
  List.replicate (2 + k) (0 : Fin 6) ++ [1, 3, 5]

/-- Observed read-molecule counts for the parameterized realization:
`x AAA = 2 + k` and the other three observed classes have count `1`. -/
def obsK (k : Nat) (c : Fin 8) : Nat :=
  if c = 0 then 2 + k
  else if c = 1 then 1
  else if c = 2 then 1
  else if c = 4 then 1
  else 0

/-! ## The counts are the genuine observed counts of `readStartsK` -/

/-- The molecule class of the window starting at `0` of the truth is `AAA`. -/
lemma cls_start0 : cls (window6 truth (0 : Fin 6)) = (0 : Fin 8) := by
  unfold cls window6 cyc6 code rc bitA comp truth
  decide

/-- The molecule class of the window starting at `1` of the truth is `AAT`. -/
lemma cls_start1 : cls (window6 truth (1 : Fin 6)) = (1 : Fin 8) := by
  unfold cls window6 cyc6 code rc bitA comp truth
  decide

/-- The molecule class of the window starting at `3` of the truth is `ATA`. -/
lemma cls_start3 : cls (window6 truth (3 : Fin 6)) = (2 : Fin 8) := by
  unfold cls window6 cyc6 code rc bitA comp truth
  decide

/-- The molecule class of the window starting at `5` of the truth is `TAA`. -/
lemma cls_start5 : cls (window6 truth (5 : Fin 6)) = (4 : Fin 8) := by
  unfold cls window6 cyc6 code rc bitA comp truth
  decide

/-- The contribution of the three non-`AAA` placements to the observed counts. -/
lemma tail_count (c : Fin 8) :
    ([1, 3, 5] : List (Fin 6)).countP (fun r => cls (window6 truth r) = c) =
      (if c = 1 then 1 else 0) + (if c = 2 then 1 else 0) +
        (if c = 4 then 1 else 0) := by
  fin_cases c <;> decide

/-- `obsK` is literally the observed class count of the parameterized read list,
so it is a genuine observed-read statistic and not a hand-picked function. -/
theorem obsK_eq_countP (k : Nat) (c : Fin 8) :
    obsK k c = (readStartsK k).countP (fun r => cls (window6 truth r) = c) := by
  rw [readStartsK, List.countP_append, List.countP_replicate, tail_count]
  fin_cases c <;> simp [obsK, cls_start0]

/-- The parameterized counts have exactly the same support as the `k = 0`
observed counts: adding `AAA` reads only scales an already-observed class. -/
theorem obsK_support (k : Nat) (c : Fin 8) : 0 < obsK k c ↔ 0 < obs c := by
  by_cases hc : c ∈ relevant
  · fin_cases c <;>
      simp_all [obsK, relevant, obs_0, obs_1, obs_2, obs_4]
  · have h0 := (truth_zero_off c hc).1
    have hk : obsK k c = 0 := by
      fin_cases c <;> simp_all [obsK, relevant]
    rw [h0, hk]

/-! ## The placement set is unchanged, so `I_s` and the §6.2 flow are unchanged -/

/-- The set of distinct placements of the parameterized realization is still
`{0, 1, 3, 5}`: the extra reads are duplicates at start `0`. -/
theorem readStartsK_toFinset (k : Nat) :
    (readStartsK k).toFinset = realizedStarts := by
  ext r
  simp only [readStartsK, List.mem_toFinset, List.mem_append, List.mem_replicate,
    List.mem_cons, List.not_mem_nil, or_false, realizedStarts,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨-, hr⟩ | hr | hr | hr)
    · exact Or.inl hr
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr (Or.inl hr))
    · exact Or.inr (Or.inr (Or.inr hr))
  · rintro (hr | hr | hr | hr)
    · subst hr; exact Or.inl ⟨by omega, rfl⟩
    · subst hr; exact Or.inr (Or.inl rfl)
    · subst hr; exact Or.inr (Or.inr (Or.inl rfl))
    · subst hr; exact Or.inr (Or.inr (Or.inr rfl))

/-- The historical source-faithful `I_s` hypothesis holds unchanged for the
parameterized placement set. -/
theorem truth_information_feasible_k (k : Nat) :
    SourceFaithfulIs.InformationFeasible truthGenome 3 (readStartsK k).toFinset := by
  rw [readStartsK_toFinset]
  exact truth_information_feasible

/-! ## A generalized §6.1 objective with `n` reads -/

/-- One §6.1 binomial marginal for molecule class `c`, with fixed external
`N = 6`, total reads `n`, observed count `x c`, and candidate count `d c`. -/
def marginalN (n : Nat) (x d : Fin 8 → Nat) (c : Fin 8) : ℚ :=
  (Nat.choose n (x c) : ℚ) * ((d c : ℚ) / 6) ^ (x c) *
    (1 - (d c : ℚ) / 6) ^ (n - x c)

/-- The literal §6.1 product of binomial marginals over all eight molecule
classes, with zero-count factors retained. -/
def likN (n : Nat) (x d : Fin 8 → Nat) : ℚ :=
  ∏ c : Fin 8, marginalN n x d c

/-- At `n = 5` this is the `k = 0` objective of the original module. -/
theorem marginalN_five (x d : Fin 8 → Nat) (c : Fin 8) :
    marginalN 5 x d c = marginal x d c := rfl

/-- A class with zero observed count and zero candidate multiplicity contributes
the factor `1` to the literal product. -/
lemma marginalN_eq_one_of_zero (n : Nat) (x d : Fin 8 → Nat) (c : Fin 8)
    (hx : x c = 0) (hd : d c = 0) : marginalN n x d c = 1 := by
  simp [marginalN, hx, hd]

/-- Only the four classes with positive counts matter; the other four factors
are `1`. -/
lemma likN_eq_relevant_prod (n : Nat) (x d : Fin 8 → Nat)
    (h : ∀ c : Fin 8, c ∉ relevant → x c = 0 ∧ d c = 0) :
    likN n x d = ∏ c ∈ relevant, marginalN n x d c := by
  unfold likN
  exact (Finset.prod_subset (s₁ := relevant) (s₂ := Finset.univ)
    (by intro c _; exact Finset.mem_univ c)
    (by intro c _ hc; exact marginalN_eq_one_of_zero n x d c (h c hc).1 (h c hc).2)).symm

/-- A binomial coefficient, cast to `ℚ`, is positive when the lower index is
within range. -/
lemma choose_cast_pos (n m : Nat) (h : m ≤ n) : (0 : ℚ) < (Nat.choose n m : ℚ) := by
  exact_mod_cast Nat.choose_pos h

/-- A single §6.1 marginal is strictly positive whenever the candidate count is
in `(0, 6)` and the observed count is at most the total. -/
lemma marginalN_pos_of (n : Nat) (x d : Fin 8 → Nat) (c : Fin 8)
    (hd0 : 0 < d c) (hd6 : d c < 6) (hx : x c ≤ n) : 0 < marginalN n x d c := by
  unfold marginalN
  have h1 : (0 : ℚ) < (Nat.choose n (x c) : ℚ) := choose_cast_pos n (x c) hx
  have h2 : (0 : ℚ) < (d c : ℚ) / 6 := by positivity
  have h3 : (0 : ℚ) < 1 - (d c : ℚ) / 6 := by
    have hlt : (d c : ℚ) < 6 := by exact_mod_cast hd6
    linarith
  exact mul_pos (mul_pos h1 (pow_pos h2 _)) (pow_pos h3 _)

/-- Cancel a common nonzero factor that occurs as the leading factor of both the
numerator and the denominator. -/
lemma cancel_common (C A B A' B' : ℚ) (hC : C ≠ 0) :
    C * A * B / (C * A' * B') = A * B / (A' * B') := by
  rw [show C * A * B = C * (A * B) by ring,
      show C * A' * B' = C * (A' * B') by ring]
  exact mul_div_mul_left _ _ hC

/-! ## Closed values of the parameterized observed counts -/

theorem obsK_0 (k : Nat) : obsK k 0 = 2 + k := by simp [obsK]

theorem obsK_1 (k : Nat) : obsK k 1 = 1 := by simp [obsK]

theorem obsK_2 (k : Nat) : obsK k 2 = 1 := by simp [obsK]

theorem obsK_4 (k : Nat) : obsK k 4 = 1 := by simp [obsK]

theorem obsK_zero_off (k : Nat) :
    ∀ c : Fin 8, c ∉ relevant → obsK k c = 0 := by
  intro c hc
  fin_cases c <;> simp_all [obsK, relevant]

/-! ## Candidate-intrinsic exact multinomial ratio -/

/-- The candidate-intrinsic exact multinomial of the truth is `3`, independent
of `k`, because the extra reads land on the `AAA` class where `d_S AAA = 1`. -/
theorem exactLik_truth_k (k : Nat) : exactLik dS (obsK k) = 3 := by
  rw [exactLik_eq_relevant dS (obsK k) (fun c hc => (obsK_zero_off k c hc)),
    relevant_prod_eq]
  norm_num [exactFactor, dS_0, dS_1, dS_2, dS_4, obsK_0, obsK_1, obsK_2, obsK_4]

/-- The competitor's exact multinomial is `3 ^ (2 + k)`. -/
theorem exactLik_competitor_k (k : Nat) : exactLik dD (obsK k) = 3 ^ (2 + k) := by
  rw [exactLik_eq_relevant dD (obsK k) (fun c hc => (obsK_zero_off k c hc)),
    relevant_prod_eq]
  norm_num [exactFactor, dD_0, dD_1, dD_2, dD_4, obsK_0, obsK_1, obsK_2, obsK_4]

/-- **Candidate-intrinsic exact multinomial ratio**: `D / S = 3 ^ (k + 1)`. -/
theorem exactLik_ratio (k : Nat) :
    exactLik dD (obsK k) / exactLik dS (obsK k) = 3 ^ (k + 1) := by
  rw [exactLik_truth_k, exactLik_competitor_k]
  rw [show 2 + k = k + 1 + 1 by omega, pow_succ]
  rw [mul_div_cancel_right₀ _ (by norm_num : (3:ℚ) ≠ 0)]

/-- The exact multinomial strictly improves: `D` beats `S` for every `k`. -/
theorem exactLik_competitor_strictly_better (k : Nat) :
    exactLik dS (obsK k) < exactLik dD (obsK k) := by
  have h := exactLik_ratio k
  rw [exactLik_truth_k] at h ⊢
  have hpos : (0:ℚ) < 3 := by norm_num
  rw [div_eq_iff (ne_of_gt hpos)] at h
  rw [h]
  have hpow : (1:ℚ) < 3 ^ (k + 1) := by
    rw [pow_succ']
    have := one_le_pow₀ (show (1:ℚ) ≤ 3 by norm_num) (n := k)
    nlinarith
  nlinarith

/-! ## The §6.1 binomial ratios of the four relevant classes -/

/-- `d_S 0 = 1`, `d_D 0 = 3`: the `AAA` marginal ratio, the source of the `3`
in the exact objective and of the leading `3` in the binomial objective. -/
theorem marginalN_ratio_0 (k : Nat) :
    marginalN (5 + k) (obsK k) dD 0 / marginalN (5 + k) (obsK k) dS 0 =
      3 ^ (2 + k) * (3 / 5) ^ 3 := by
  rw [marginalN, marginalN, obsK_0, dD_0, dS_0]
  have hk : 5 + k - (2 + k) = 3 := by omega
  rw [hk]
  have hc : ((Nat.choose (5 + k) (2 + k) : ℕ) : ℚ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact (Nat.choose_pos (by omega)).ne'
  rw [cancel_common _ _ _ _ _ hc]
  rw [← div_mul_div_comm, ← div_pow, ← div_pow]
  norm_num

/-- `d_S 1 = d_D 1 = 1`: the `AAT` marginal ratio is `1`. -/
theorem marginalN_ratio_1 (k : Nat) :
    marginalN (5 + k) (obsK k) dD 1 / marginalN (5 + k) (obsK k) dS 1 = 1 := by
  rw [marginalN, marginalN, obsK_1, dD_1, dS_1]
  have hc : ((Nat.choose (5 + k) 1 : ℕ) : ℚ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact (Nat.choose_pos (by omega)).ne'
  rw [cancel_common _ _ _ _ _ hc]
  rw [div_self (ne_of_gt (by positivity))]

/-- `d_S 2 = 3`, `d_D 2 = 1`: the `ATA` marginal ratio is `(1/3) * (5/3)^(4+k)`,
the source of the `5/3` per-step factor in the binomial objective. -/
theorem marginalN_ratio_2 (k : Nat) :
    marginalN (5 + k) (obsK k) dD 2 / marginalN (5 + k) (obsK k) dS 2 =
      (1 / 3) * (5 / 3) ^ (4 + k) := by
  rw [marginalN, marginalN, obsK_2, dD_2, dS_2]
  have hk : 5 + k - 1 = 4 + k := by omega
  rw [hk]
  have hc : ((Nat.choose (5 + k) 1 : ℕ) : ℚ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact (Nat.choose_pos (by omega)).ne'
  rw [cancel_common _ _ _ _ _ hc]
  rw [← div_mul_div_comm, ← div_pow, ← div_pow]
  rw [pow_one]
  norm_num

/-- `d_S 4 = d_D 4 = 1`: the `TAA` marginal ratio is `1`. -/
theorem marginalN_ratio_4 (k : Nat) :
    marginalN (5 + k) (obsK k) dD 4 / marginalN (5 + k) (obsK k) dS 4 = 1 := by
  rw [marginalN, marginalN, obsK_4, dD_4, dS_4]
  have hc : ((Nat.choose (5 + k) 1 : ℕ) : ℚ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact (Nat.choose_pos (by omega)).ne'
  rw [cancel_common _ _ _ _ _ hc]
  rw [div_self (ne_of_gt (by positivity))]

/-! ## The exact algebra of the binomial ratio -/

/-- The per-class ratios multiply to `5 ^ (k + 1)`: the leading `3 ^ (2 + k)`
from `AAA`, the constant `(3 / 5) ^ 3`, and the `(1 / 3) * (5 / 3) ^ (4 + k)`
from `ATA` combine with `3 ^ k * (5 / 3) ^ k = 5 ^ k`. -/
lemma arith_binom (k : Nat) :
    (3 : ℚ) ^ (2 + k) * (3 / 5) ^ 3 * (1 / 3) * (5 / 3) ^ (4 + k) =
      5 ^ (k + 1) := by
  have h3 : (3 : ℚ) ^ (2 + k) = 3 ^ 2 * 3 ^ k := by rw [pow_add]
  have h5 : ((5 : ℚ) / 3) ^ (4 + k) = (5 / 3) ^ 4 * (5 / 3) ^ k := by rw [pow_add]
  have hcomb : (3 : ℚ) ^ k * (5 / 3) ^ k = 5 ^ k := by
    rw [← mul_pow]
    norm_num
  rw [h3, h5]
  rw [show (3 : ℚ) ^ 2 * 3 ^ k * (3 / 5) ^ 3 * (1 / 3) *
        ((5 / 3) ^ 4 * (5 / 3) ^ k) =
      ((3 : ℚ) ^ 2 * (3 / 5) ^ 3 * (1 / 3) * (5 / 3) ^ 4) *
        (3 ^ k * (5 / 3) ^ k) by ring]
  rw [hcomb]
  rw [show (3 : ℚ) ^ 2 * (3 / 5) ^ 3 * (1 / 3) * (5 / 3) ^ 4 = 5 by norm_num]
  rw [show (5 : ℚ) * 5 ^ k = 5 ^ (k + 1) by rw [pow_succ']]

/-! ## The main binomial ratio and strict improvement -/

/-- **Fixed-`N` §6.1 product-of-binomial-marginals ratio**: `D / S = 5 ^ (k + 1)`,
with all eight class factors, including the zero-count ones. -/
theorem likN_ratio (k : Nat) :
    likN (5 + k) (obsK k) dD / likN (5 + k) (obsK k) dS = 5 ^ (k + 1) := by
  rw [likN_eq_relevant_prod (5 + k) (obsK k) dD
        (fun c hc => ⟨obsK_zero_off k c hc, (competitor_zero_off c hc).2⟩),
      likN_eq_relevant_prod (5 + k) (obsK k) dS
        (fun c hc => ⟨obsK_zero_off k c hc, (truth_zero_off c hc).2⟩)]
  rw [← Finset.prod_div_distrib]
  rw [relevant_prod_eq]
  rw [marginalN_ratio_0, marginalN_ratio_1, marginalN_ratio_2, marginalN_ratio_4]
  rw [show (3 : ℚ) ^ (2 + k) * (3 / 5) ^ 3 *
        (1 * ((1 / 3) * (5 / 3) ^ (4 + k) * 1)) =
      (3 : ℚ) ^ (2 + k) * (3 / 5) ^ 3 * (1 / 3) * (5 / 3) ^ (4 + k) by ring]
  exact arith_binom k

/-- The truth's §6.1 likelihood is strictly positive, so the ratio can be
converted into a strict inequality. -/
theorem likN_truth_pos (k : Nat) : 0 < likN (5 + k) (obsK k) dS := by
  rw [likN_eq_relevant_prod (5 + k) (obsK k) dS
        (fun c hc => ⟨obsK_zero_off k c hc, (truth_zero_off c hc).2⟩),
      relevant_prod_eq]
  exact mul_pos
    (marginalN_pos_of (5 + k) (obsK k) dS 0
      (by rw [dS_0]; norm_num) (by rw [dS_0]; norm_num) (by rw [obsK_0]; omega))
    (mul_pos
      (marginalN_pos_of (5 + k) (obsK k) dS 1
        (by rw [dS_1]; norm_num) (by rw [dS_1]; norm_num) (by rw [obsK_1]; omega))
      (mul_pos
        (marginalN_pos_of (5 + k) (obsK k) dS 2
          (by rw [dS_2]; norm_num) (by rw [dS_2]; norm_num) (by rw [obsK_2]; omega))
        (marginalN_pos_of (5 + k) (obsK k) dS 4
          (by rw [dS_4]; norm_num) (by rw [dS_4]; norm_num) (by rw [obsK_4]; omega))))

/-- The §6.1 binomial objective strictly improves: `D` beats `S` for every `k`. -/
theorem likN_competitor_strictly_better (k : Nat) :
    likN (5 + k) (obsK k) dS < likN (5 + k) (obsK k) dD := by
  have h := likN_ratio k
  have hpos := likN_truth_pos k
  rw [div_eq_iff (ne_of_gt hpos)] at h
  rw [h]
  have hpow : (1 : ℚ) < 5 ^ (k + 1) := by
    rw [pow_succ']
    have := one_le_pow₀ (show (1 : ℚ) ≤ 5 by norm_num) (n := k)
    nlinarith
  nlinarith

/-! ## The parametric endpoint theorem -/

/-- **Parametric strengthening.**  For every `k : ℕ`, adding `k` extra genuine
`AAA` reads at start `0` leaves the observed read support, the historical
source-faithful `I_s` hypothesis and the full MB09 §6.2 spelled-flow feasibility
of both candidates unchanged, while the competitor beats the truth under both
same-length objectives with ratios `5 ^ (k + 1)` and `3 ^ (k + 1)`. -/
theorem parametric_se62_counterexample (k : Nat) :
    SourceFaithfulIs.InformationFeasible truthGenome 3 (readStartsK k).toFinset ∧
      (genomeLength truth = genomeLength competitor) ∧
      (SpelledFeasible62 Base Strand3 toList3 rep3 rc3 readLen oMin readVerts
          spellTruth truthCircuitFlow noTerm dS' ∧
        (SpelledFeasible62 Base Strand3 toList3 rep3 rc3 readLen oMin readVerts
            spellCompetitor competitorCircuitFlow noTerm dD' ∧
          (likN (5 + k) (obsK k) dS < likN (5 + k) (obsK k) dD ∧
            (likN (5 + k) (obsK k) dD / likN (5 + k) (obsK k) dS = 5 ^ (k + 1) ∧
              (exactLik dD (obsK k) / exactLik dS (obsK k) = 3 ^ (k + 1) ∧
                exactLik dS (obsK k) < exactLik dD (obsK k)))))) :=
  ⟨truth_information_feasible_k k, ⟨same_candidate_length,
    ⟨truth_spelled_feasible62, ⟨competitor_spelled_feasible62,
      ⟨likN_competitor_strictly_better k, ⟨likN_ratio k,
        ⟨exactLik_ratio k, exactLik_competitor_strictly_better k⟩⟩⟩⟩⟩⟩⟩

end AssemblyP1.SameLengthSection62Parametric
