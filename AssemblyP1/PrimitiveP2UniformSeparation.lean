import AssemblyP1.PrimitiveP2FiniteClass

/-!
# Uniform separation and an explicit exponential exact-ML error bound for
  primitive-P2 genomes (issue #281)

`AssemblyP1.PrimitiveP2FiniteClass.all_primitiveP2_ML_confidence` proves that,
over the *complete* primitive-P2 admissible class, the exact iid
maximum-likelihood error probability tends to zero. It is an *existence*
statement: it produces an `N` for every tolerance `δ` but says nothing about
how `N` depends on the read length `L` or the alphabet size `q`.

This module upgrades the statement to an **explicit uniform exponential
rate**. The mechanism is a self-contained quantitative separation, not the
population uniqueness theorem: the read law of a primitive-P2 genome of
length `G` is a count vector divided by `G`, so two distinct read laws differ
by a rational with denominator dividing `G_S * G_D`. Combined with the
coordinate inequality `|√p - √q| ≥ |p - q|/2` and the Hellinger identity
`1 - ρ = (1/2) ∑ (√p_w - √q_w)²`, this yields a *uniform* affinity gap
`ρ(p_S, p_D) ≤ 1 - 1/(8 B^4)` for every non-rotational admissible competitor,
where `B = 2 q^(L-1)` is the primitive-P2 length bound of
`AssemblyP1.PrimitiveP2FiniteClass.primitive_P2_len_le`.

Feeding this into the merged finite-iid Hellinger union bound
(`AssemblyP1.FiniteReadRecoveryGenome.circular_wrong_le_card`) gives the main
guarantee

    P_S[∃ D non-rotational admissible, L_D ≥ L_S] ≤ N_C · exp(-n/(8 B^4)),

with `N_C ≤ ∑_{g=1}^{B} q^g`, hence a sufficient read count
`n ≥ 8 B^4 · log(N_C / δ)`. The constants are deliberately loose: `B` is
exponential in `L` and `N_C` is enormous. The point is *kernel-checked
finiteness and positivity of the rate*, not tractability.

## Scope and boundaries

* Competitor class: primitive-P2 admissible, oriented, exact iid reads.
* The bound is **not** universal ML over all genomes, and **not** the MB09
  product-binomial surrogate.
* This is distinct from the Bayes-optimality rationale: it is a frequentist
  uniform-separation guarantee for exact multinomial likelihood.
* Nothing here claims the rate is efficient or that enumeration is feasible.

No `axiom`, `sorry` or `admit` is introduced, and no existing definition is
changed. The only kernel axioms are `propext`, `Classical.choice` and
`Quot.sound`.
-/

namespace AssemblyP1.PrimitiveP2UniformSeparation

open AssemblyP1.SourceFaithfulIs
open AssemblyP1.FiniteReadRecovery
open AssemblyP1.FiniteReadRecoveryGenome
open AssemblyP1.FiniteReadRecoveryP2Complete
open AssemblyP1.PopulationUniqueness
open AssemblyP1.PopulationReduction
open AssemblyP1.PrimitiveP2FiniteClass
open Finset
open scoped Classical BigOperators

variable {α : Type} [DecidableEq α] [Fintype α]

/-! ## 1. The cross-multiplied integer denominator separation -/

/-- Two distinct natural numbers differ by at least one, as reals. This is the
"cross-multiplied Nat denominator" fact: a nonzero integer numerator has
absolute value at least one. -/
theorem one_le_abs_cast_sub {a b : ℕ} (h : a ≠ b) :
    (1 : ℝ) ≤ |(a : ℝ) - (b : ℝ)| := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have h1 : (a : ℝ) + 1 ≤ (b : ℝ) := by
      have : a + 1 ≤ b := hlt
      exact_mod_cast this
    have hpos : 0 ≤ (b : ℝ) - (a : ℝ) := by linarith
    rw [abs_sub_comm, abs_of_nonneg hpos]
    linarith
  · have h1 : (b : ℝ) + 1 ≤ (a : ℝ) := by
      have : b + 1 ≤ a := hgt
      exact_mod_cast this
    have hpos : 0 ≤ (a : ℝ) - (b : ℝ) := by linarith
    rw [abs_of_nonneg hpos]
    linarith

omit [Fintype α] in
/-- **Pointwise read-law separation.** Two distinct uniform-start oriented
circular read laws differ by at least `1/(G_S * G_D)` at some length-`L` word.
The witness is the cross-multiplied integer numerator: read probabilities are
counts divided by genome lengths, so the difference is
`(c_w G_D - c'_w G_S)/(G_S G_D)` and a nonzero integer numerator has absolute
value at least one. -/
theorem readLaw_separation (S D : Genome α) (L : ℕ)
    (hne : circularReadPMF S L ≠ circularReadPMF D L) :
    ∃ w : Fin L → α,
      1 / ((S.len : ℝ) * (D.len : ℝ))
        ≤ |circularReadPMF S L w - circularReadPMF D L w| := by
  classical
  have hne' : ¬ ∀ w, circularReadPMF S L w = circularReadPMF D L w := by
    intro h; exact hne (funext h)
  rw [not_forall] at hne'
  obtain ⟨w, hw⟩ := hne'
  refine ⟨w, ?_⟩
  set cS : ℕ := (Finset.univ.filter (fun t : Fin S.len => S.window L t = w)).card
  set cD : ℕ := (Finset.univ.filter (fun t : Fin D.len => D.window L t = w)).card
  have hpS : circularReadPMF S L w = (cS : ℝ) / (S.len : ℝ) := by
    rw [circularReadPMF_eq_count]
  have hpD : circularReadPMF D L w = (cD : ℝ) / (D.len : ℝ) := by
    rw [circularReadPMF_eq_count]
  have hGS : (0 : ℝ) < S.len := by exact_mod_cast S.len_pos
  have hGD : (0 : ℝ) < D.len := by exact_mod_cast D.len_pos
  have hne_num : cS * D.len ≠ cD * S.len := by
    intro h
    apply hw
    rw [hpS, hpD]
    have hcast : (cS : ℝ) * (D.len : ℝ) = (cD : ℝ) * (S.len : ℝ) := by
      rw [← Nat.cast_mul, ← Nat.cast_mul, h]
    field_simp
    linarith
  have hnum : (1 : ℝ) ≤ |(cS : ℝ) * (D.len : ℝ) - (cD : ℝ) * (S.len : ℝ)| := by
    have h := one_le_abs_cast_sub hne_num
    rwa [Nat.cast_mul, Nat.cast_mul] at h
  have hden : 0 < (S.len : ℝ) * (D.len : ℝ) := mul_pos hGS hGD
  rw [hpS, hpD]
  rw [div_sub_div (cS : ℝ) (cD : ℝ) (ne_of_gt hGS) (ne_of_gt hGD)]
  rw [abs_div, abs_of_pos hden]
  rw [mul_comm (S.len : ℝ) (cD : ℝ)]
  rw [div_le_div_iff_of_pos_right hden]
  exact hnum

/-! ## 2. The coordinate square-root inequality and the Hellinger gap -/

/-- Coordinate inequality for the Hellinger identity: for `p, q ∈ [0,1]`,
`|p - q| ≤ 2 |√p - √q|`. Stated multiplicatively so that `p = q = 0` needs
no division. -/
theorem abs_sub_le_two_abs_sqrt_sub (p q : ℝ) (hp0 : 0 ≤ p) (hq0 : 0 ≤ q)
    (hp1 : p ≤ 1) (hq1 : q ≤ 1) :
    |p - q| ≤ 2 * |Real.sqrt p - Real.sqrt q| := by
  have ha : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0
  have hb : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0
  have hsum_nonneg : 0 ≤ Real.sqrt p + Real.sqrt q := by positivity
  have hfactor : p - q = (Real.sqrt p - Real.sqrt q) * (Real.sqrt p + Real.sqrt q) := by
    have h := sq_sub_sq (Real.sqrt p) (Real.sqrt q)
    rw [ha, hb] at h
    rw [h]; ring
  have hab : |p - q| = |Real.sqrt p - Real.sqrt q| * (Real.sqrt p + Real.sqrt q) := by
    rw [hfactor, abs_mul, abs_of_nonneg hsum_nonneg]
  have hsum : Real.sqrt p + Real.sqrt q ≤ 2 := by
    have hp : Real.sqrt p ≤ 1 := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hp1
    have hq : Real.sqrt q ≤ 1 := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hq1
    linarith
  rw [hab]
  calc |Real.sqrt p - Real.sqrt q| * (Real.sqrt p + Real.sqrt q)
      ≤ |Real.sqrt p - Real.sqrt q| * 2 :=
        mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = 2 * |Real.sqrt p - Real.sqrt q| := by ring

/-- For a pmf, every value is at most one. -/
theorem pmf_le_one {W : Type*} [Fintype W] {p : W → ℝ} (hp : IsPmf p) (w : W) :
    p w ≤ 1 := by
  have h := Finset.single_le_sum (f := p) (fun i _ => hp.1 i) (Finset.mem_univ w)
  rw [hp.2] at h
  exact h

/-- **Quantitative Hellinger separation from a pointwise gap.** If two pmfs
`p, q` differ by at least `1/(G*H)` at some word, then
`1 - ρ(p,q) ≥ 1/(8*(G*H)^2)`. -/
theorem one_sub_hellinger_ge_of_gap {W : Type*} [Fintype W]
    (p q : W → ℝ) (hp : IsPmf p) (hq : IsPmf q)
    (G H : ℝ) (hG : 0 < G) (hH : 0 < H)
    (w0 : W) (hgap : 1 / (G * H) ≤ |p w0 - q w0|) :
    1 / (8 * (G * H) ^ 2) ≤ 1 - hellinger p q := by
  have hp0 : ∀ w, 0 ≤ p w := hp.1
  have hq0 : ∀ w, 0 ≤ q w := hq.1
  have hident := hellinger_sq_identity p q hp0 hq0 hp.2 hq.2
  have hrho : 1 - hellinger p q =
      (1 / 2) * ∑ w : W, (Real.sqrt (p w) - Real.sqrt (q w)) ^ 2 := by
    rw [hident]; ring
  have hcoord : |p w0 - q w0| ≤ 2 * |Real.sqrt (p w0) - Real.sqrt (q w0)| :=
    abs_sub_le_two_abs_sqrt_sub (p w0) (q w0) (hp0 w0) (hq0 w0)
      (pmf_le_one hp w0) (pmf_le_one hq w0)
  have hhalf : 1 / (2 * (G * H)) ≤ |Real.sqrt (p w0) - Real.sqrt (q w0)| := by
    have h2 : 1 / (G * H) ≤ 2 * |Real.sqrt (p w0) - Real.sqrt (q w0)| :=
      hgap.trans hcoord
    have h3 : 1 ≤ 2 * |Real.sqrt (p w0) - Real.sqrt (q w0)| * (G * H) :=
      (div_le_iff₀ (mul_pos hG hH)).mp h2
    have h4 : 1 ≤ |Real.sqrt (p w0) - Real.sqrt (q w0)| * (2 * (G * H)) := by
      nlinarith [h3]
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (G * H))).mpr h4
  have hsingle : (Real.sqrt (p w0) - Real.sqrt (q w0)) ^ 2
      ≤ ∑ w : W, (Real.sqrt (p w) - Real.sqrt (q w)) ^ 2 :=
    Finset.single_le_sum (f := fun w => (Real.sqrt (p w) - Real.sqrt (q w)) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ w0)
  have hsq : (1 / (2 * (G * H))) ^ 2
      ≤ (Real.sqrt (p w0) - Real.sqrt (q w0)) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1 / (2 * (G * H))) hhalf 2
    rwa [sq_abs] at this
  rw [hrho]
  calc 1 / (8 * (G * H) ^ 2) = (1 / 2) * (1 / (2 * (G * H))) ^ 2 := by ring_nf
    _ ≤ (1 / 2) * ∑ w : W, (Real.sqrt (p w) - Real.sqrt (q w)) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact hsq.trans hsingle

/-! ## 3. The uniform affinity gap at the genome level -/

/-- **Quantitative uniform Hellinger separation.** For any two genomes whose
lengths are bounded by `B` and whose oriented read laws are distinct, the
Hellinger affinity is at most `1 - 1/(8 B^4)`. -/
theorem hellinger_le_of_length_bound (L : ℕ) (S D : Genome α) (B : ℕ)
    (hSB : S.len ≤ B) (hDB : D.len ≤ B)
    (hne : circularReadPMF S L ≠ circularReadPMF D L) :
    hellinger (circularReadPMF S L) (circularReadPMF D L)
      ≤ 1 - 1 / (8 * (B : ℝ) ^ 4) := by
  obtain ⟨w0, hgap⟩ := readLaw_separation S D L hne
  have hGS : 0 < (S.len : ℝ) := by exact_mod_cast S.len_pos
  have hGD : 0 < (D.len : ℝ) := by exact_mod_cast D.len_pos
  have hsep := one_sub_hellinger_ge_of_gap (circularReadPMF S L) (circularReadPMF D L)
    (circularReadPMF_isPmf S L) (circularReadPMF_isPmf D L)
    (S.len : ℝ) (D.len : ℝ) hGS hGD w0 hgap
  have hBpos : 0 < (B : ℝ) := by
    have : 0 < B := lt_of_lt_of_le S.len_pos hSB
    exact_mod_cast this
  have hGSle : (S.len : ℝ) ≤ (B : ℝ) := by exact_mod_cast hSB
  have hGDle : (D.len : ℝ) ≤ (B : ℝ) := by exact_mod_cast hDB
  have hGHle : (S.len : ℝ) * (D.len : ℝ) ≤ (B : ℝ) ^ 2 := by
    have := mul_le_mul hGSle hGDle (le_of_lt hGD) (le_of_lt hBpos)
    simpa [pow_two] using this
  have hGHsq : ((S.len : ℝ) * (D.len : ℝ)) ^ 2 ≤ (B : ℝ) ^ 4 := by
    have h := pow_le_pow_left₀ (mul_nonneg (le_of_lt hGS) (le_of_lt hGD)) hGHle 2
    rwa [show ((B : ℝ) ^ 2) ^ 2 = (B : ℝ) ^ 4 by ring] at h
  have hmono : 1 / (8 * (B : ℝ) ^ 4)
      ≤ 1 / (8 * ((S.len : ℝ) * (D.len : ℝ)) ^ 2) := by
    apply one_div_le_one_div_of_le
    · positivity
    · nlinarith [hGHsq]
  have := hmono.trans hsep
  linarith

/-! ## 4. The explicit exponential exact-ML error bound -/

/-- **Exponential exact-ML error bound from a length bound.** If every
competitor in a finite family `C` has length at most `B`, the true genome `S`
also has length at most `B`, and every competitor's read law differs from the
truth's, then the probability that some competitor ties or beats the truth
after `n` iid oriented reads is at most `|C| · exp(-n/(8 B^4))`. -/
theorem exp_error_bound_of_length_bound (L n : ℕ) (S : Genome α)
    (C : Finset (Genome α)) (B : ℕ)
    (hSB : S.len ≤ B) (hDB : ∀ D ∈ C, D.len ≤ B)
    (hne : ∀ D ∈ C, circularReadPMF S L ≠ circularReadPMF D L) :
    eventProb (circularReadPMF S L) n
      (wrongEvent (circularReadPMF S L) (readLawFamily C L) n)
    ≤ ((readLawFamily C L).card : ℝ)
        * Real.exp (-(n : ℝ) / (8 * (B : ℝ) ^ 4)) := by
  set t : ℝ := 1 / (8 * (B : ℝ) ^ 4) with ht
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by
    have : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le S.len_pos hSB))
    exact_mod_cast this
  have hB4 : (1 : ℝ) ≤ (B : ℝ) ^ 4 := one_le_pow₀ hB1
  have ht_lt_one : t < 1 := by
    rw [ht, div_lt_one (by positivity : (0 : ℝ) < 8 * (B : ℝ) ^ 4)]
    nlinarith
  have hρ : ∀ D ∈ C, hellinger (circularReadPMF S L) (circularReadPMF D L) ≤ 1 - t := by
    intro D hD
    have := hellinger_le_of_length_bound L S D B hSB (hDB D hD) (hne D hD)
    simpa [ht] using this
  have hcard := circular_wrong_le_card S C L n (1 - t) hρ
  have hpow : (1 - t) ^ n ≤ Real.exp (-(n : ℝ) * t) := by
    have hbase : 1 - t ≤ Real.exp (-t) := Real.one_sub_le_exp_neg t
    have hnn : 0 ≤ 1 - t := by linarith
    have h := pow_le_pow_left₀ hnn hbase n
    have hexp : Real.exp (-t) ^ n = Real.exp (-(n : ℝ) * t) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rwa [hexp] at h
  calc eventProb (circularReadPMF S L) n
        (wrongEvent (circularReadPMF S L) (readLawFamily C L) n)
      ≤ ((readLawFamily C L).card : ℝ) * (1 - t) ^ n := hcard
    _ ≤ ((readLawFamily C L).card : ℝ) * Real.exp (-(n : ℝ) * t) :=
        mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)
    _ = ((readLawFamily C L).card : ℝ)
          * Real.exp (-(n : ℝ) / (8 * (B : ℝ) ^ 4)) := by
        rw [ht]; congr 1; ring_nf

/-- If `K * log(N/δ) ≤ n` with `K, δ > 0`, then `N * exp(-n/K) ≤ δ`. This is
the standard geometric-confidence threshold. -/
theorem card_mul_exp_neg_div_le {N : ℕ} {δ K : ℝ} (hδ : 0 < δ) (hK : 0 < K)
    (n : ℕ) (hn : K * Real.log ((N : ℝ) / δ) ≤ (n : ℝ)) :
    (N : ℝ) * Real.exp (-(n : ℝ) / K) ≤ δ := by
  by_cases hN : N = 0
  · subst hN
    simp only [Nat.cast_zero, zero_mul]
    exact le_of_lt hδ
  · have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    have hratio : 0 < (N : ℝ) / δ := div_pos hNpos hδ
    have hlog : Real.log ((N : ℝ) / δ) ≤ (n : ℝ) / K := by
      rw [le_div_iff₀ hK, mul_comm]
      exact hn
    have hexp : Real.exp (-(n : ℝ) / K) ≤ δ / (N : ℝ) := by
      have h1 : Real.exp (-(n : ℝ) / K) ≤ Real.exp (-(Real.log ((N : ℝ) / δ))) := by
        apply Real.exp_le_exp.mpr
        rw [neg_div]
        exact neg_le_neg hlog
      have h2 : Real.exp (-(Real.log ((N : ℝ) / δ))) = δ / (N : ℝ) := by
        rw [Real.exp_neg, Real.exp_log hratio]
        field_simp
      rw [h2] at h1
      exact h1
    calc (N : ℝ) * Real.exp (-(n : ℝ) / K)
        ≤ (N : ℝ) * (δ / (N : ℝ)) := mul_le_mul_of_nonneg_left hexp (le_of_lt hNpos)
      _ = δ := by field_simp

/-- **The main mathematical guarantee.** Over the complete primitive-P2
admissible non-rotational competitor class, the exact iid maximum-likelihood
error probability after `n` oriented reads decays at least as fast as
`N_C · exp(-n/(8 B^4))`, where `B = 2 q^(L-1)` and `N_C` is the number of
distinct competitor read laws. This is a uniform-separation statement, distinct
from the Bayes-optimality rationale. -/
theorem primitiveP2_exponential_error_bound (L : ℕ) (hL : 2 ≤ L) (S : Genome α)
    (hPrimS : PopulationReduction.IsPrimitive S.sym) (hP2S : P2 S.len_pos L S.sym)
    (n : ℕ) :
    eventProb (circularReadPMF S L) n
      (wrongEvent (circularReadPMF S L)
        (readLawFamily (nonRotationalCandidates L S) L) n)
    ≤ ((readLawFamily (nonRotationalCandidates L S) L).card : ℝ)
        * Real.exp (-(n : ℝ) / (8 * (maxLen (α := α) L : ℝ) ^ 4)) := by
  refine exp_error_bound_of_length_bound L n S (nonRotationalCandidates L S)
    (maxLen (α := α) L) ?_ ?_ ?_
  · exact primitive_P2_len_le S.len_pos S.sym hL hPrimS hP2S
  · intro D hD
    exact primitive_P2_len_le D.len_pos D.sym hL
      (mem_nonRotationalCandidates_adm L hL S D hD).1
      (mem_nonRotationalCandidates_adm L hL S D hD).2
  · intro D hD hLaw
    exact mem_nonRotationalCandidates_notRot L hL S D hD
      (equal_laws_imply_rotation_of_primitiveP2 S D L (by omega) hPrimS hP2S
        (mem_nonRotationalCandidates_adm L hL S D hD) hLaw)

/-- **Explicit finite-read confidence.** If the read count exceeds
`8 B^4 · log(N_C/δ)`, the exact iid ML error probability over the complete
primitive-P2 non-rotational class is at most `δ`. -/
theorem primitiveP2_ML_confidence_explicit (L : ℕ) (hL : 2 ≤ L) (S : Genome α)
    (hPrimS : PopulationReduction.IsPrimitive S.sym) (hP2S : P2 S.len_pos L S.sym)
    (δ : ℝ) (hδ : 0 < δ) (n : ℕ)
    (hn : 8 * (maxLen (α := α) L : ℝ) ^ 4
        * Real.log (((readLawFamily (nonRotationalCandidates L S) L).card : ℝ) / δ)
        ≤ (n : ℝ)) :
    eventProb (circularReadPMF S L) n
      (wrongEvent (circularReadPMF S L)
        (readLawFamily (nonRotationalCandidates L S) L) n) ≤ δ := by
  have hSle := primitive_P2_len_le S.len_pos S.sym hL hPrimS hP2S
  have hB1 : (1 : ℝ) ≤ (maxLen (α := α) L : ℝ) := by
    have : 1 ≤ maxLen (α := α) L := le_trans S.len_pos hSle
    exact_mod_cast this
  have hK : 0 < 8 * (maxLen (α := α) L : ℝ) ^ 4 := by
    have : (0 : ℝ) < (maxLen (α := α) L : ℝ) := lt_of_lt_of_le one_pos hB1
    positivity
  have hbound := primitiveP2_exponential_error_bound L hL S hPrimS hP2S n
  have hthr := card_mul_exp_neg_div_le (N := (readLawFamily
      (nonRotationalCandidates L S) L).card) (δ := δ)
    (K := 8 * (maxLen (α := α) L : ℝ) ^ 4) hδ hK n hn
  exact hbound.trans hthr

/-! ## 5. An explicit bound on the number of competitor read laws -/

omit [DecidableEq α] in
/-- The number of genomes of length at most `m` is at most `∑_{g=1}^{m} q^g`.
`shortGenomes m` is the image of the finite σ-type of words of known length, so
its cardinality is bounded by that σ-type's cardinality, which is the sum of
the per-length word counts. -/
theorem card_shortGenomes_le (m : ℕ) :
    (shortGenomes (α := α) m).card
      ≤ ∑ g ∈ Finset.Icc 1 m, Fintype.card α ^ g := by
  have h1 : (shortGenomes (α := α) m).card
      ≤ Fintype.card (Σ n : Fin m, Fin (n.val + 1) → α) := by
    rw [shortGenomes]
    exact (Finset.card_image_le).trans (by simp)
  refine h1.trans ?_
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => Fintype.card α ^ (i + 1)) m]
  have hIcc : (Finset.Icc 1 m) = (Finset.range m).image (fun i => i + 1) := by
    ext g
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨g - 1, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  rw [hIcc, Finset.sum_image (fun x _ y _ h => by omega)]

/-- The number of distinct competitor read laws is at most `∑_{g=1}^{B} q^g`
with `B = 2 q^(L-1)`. -/
theorem readLawFamily_card_le (L : ℕ) (hL : 2 ≤ L) (S : Genome α) :
    (readLawFamily (nonRotationalCandidates L S) L).card
      ≤ ∑ g ∈ Finset.Icc 1 (maxLen (α := α) L), Fintype.card α ^ g := by
  have h2 : (nonRotationalCandidates L S).card
      ≤ (shortGenomes (α := α) (maxLen (α := α) L)).card := by
    apply Finset.card_le_card
    intro D hD
    have hAdm := mem_nonRotationalCandidates_adm L hL S D hD
    exact (mem_shortGenomes (α := α) (maxLen (α := α) L) D).mpr
      (primitive_P2_len_le D.len_pos D.sym hL hAdm.1 hAdm.2)
  calc (readLawFamily (nonRotationalCandidates L S) L).card
      ≤ (nonRotationalCandidates L S).card := Finset.card_image_le
    _ ≤ (shortGenomes (α := α) (maxLen (α := α) L)).card := h2
    _ ≤ ∑ g ∈ Finset.Icc 1 (maxLen (α := α) L), Fintype.card α ^ g :=
        card_shortGenomes_le _

/-! ## 6. Non-vacuity: the affinity bound is a genuine strict gap -/

/-- At the smallest read length `L = 2` over a two-letter alphabet the length
bound is `B = 4`, so the uniform affinity gap `1 - 1/(8 B^4)` is strictly less
than one. This records that the separation constant is not the trivial bound
`ρ ≤ 1`. -/
theorem separation_gap_strict_at_L2 : (1 : ℝ) - 1 / (8 * (4 : ℝ) ^ 4) < 1 := by
  norm_num

end AssemblyP1.PrimitiveP2UniformSeparation
