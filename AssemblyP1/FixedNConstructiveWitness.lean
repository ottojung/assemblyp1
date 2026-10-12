import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A verified integer witness for fixed-N product-binomial ML (#259)

This module proves an explicit *strict adversarial observation certificate*
for two distinct positive oriented count spectra A and B on one fixed finite
read-type universe. Both have the same total G and each coordinate is strictly
between 0 and G. The binomial external denominator N satisfies G <= N.

Define T = sum_i B_i*(N-B_i), n = N*T,
x_i = B_i*(T + (N-G)*(N-B_i)).
Lean checks sum x=n, 0<x_i<n, and the strict logarithmic score comparison
logScore(A;x)-logScore(B;x)<0 using the strict log-tangent inequality. It also
proves that G*x_i >= A_i for all i, and that positive scaling preserves strict
log-ratio ordering. No KKT necessity on a discrete lattice is asserted.

IMPORTANT MODEL BOUNDARIES:
* The objective is the separable product of binomial marginals used as a
  fixed-external-N optimization approximation in Medvedev-Brudno 2009
  Section 6.1, not the genuine multinomial joint sampling likelihood.
* The candidate universe is positive count spectra on an identical finite,
  oriented, positive read-type support, NOT the arbitrary bidirected flow
  or reverse-complement molecule universe of MB09 Section 6.2.
* G*x_i >= A_i is a type-count coverage *budget*, not itself a Lean
  proof constructing a placement list covering each actual genome start.
  That realization bridge and the resulting full sample-uniform iff
  theorem remain separate research tasks.

This is an independently checked replacement for the unmerged, failing
723-line experimental witness. All theorems here are kernel checked without
sorry/admit, and accompanied by an axiom audit and exact integer regression.
-/

open Finset BigOperators

namespace AssemblyP1.FixedNConstructiveWitness

variable {E : Type*} [Fintype E]

/-- Positive integer normalizer for an auxiliary candidate copy spectrum. -/
def auxiliaryT (N : ℕ) (B : E → ℕ) : ℕ :=
  ∑ e, B e * (N - B e)

/-- Exact finite integer witness sample-count vector. -/
def auxiliaryX (G N : ℕ) (B : E → ℕ) (e : E) : ℕ :=
  B e * (auxiliaryT N B + (N - G) * (N - B e))

/-- Sum of the integer witness counts is precisely its stated sample size. -/
theorem auxiliaryX_sum (G N : ℕ) (B : E → ℕ)
    (hG : ∑ e, B e = G) (hNG : G ≤ N) :
    (∑ e, auxiliaryX G N B e) = N * auxiliaryT N B := by
  have hterm (e : E) :
      auxiliaryX G N B e =
        B e * auxiliaryT N B +
          (N - G) * (B e * (N - B e)) := by
    unfold auxiliaryX
    ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [hG]
  change G * auxiliaryT N B + (N - G) * auxiliaryT N B =
    N * auxiliaryT N B
  calc
    _ = (G + (N-G)) * auxiliaryT N B := by ring
    _ = N * auxiliaryT N B := by congr 1; omega

/-- Algebraic tangent identity, prior to taking a logarithmic supporting line. -/
theorem tangent_identity (N G T A B : ℝ)
    (hN : N ≠ 0) (hT : T ≠ 0) (hB : B ≠ 0) (hNB : N - B ≠ 0) :
    (B * (T + (N - G) * (N - B)) / (N * T)) * (A / B - 1) +
      (1 - B * (T + (N - G) * (N - B)) / (N * T)) *
        ((N - A) / (N - B) - 1) = (N - G) / T * (A - B) := by
  field_simp
  ring


/-- Positivity of the normalizer when at least one read type has strictly
positive frequency smaller than the external genome-size parameter. -/
theorem auxiliaryT_pos (N : ℕ) (B : E → ℕ)
    (hex : ∃ e, 0 < B e ∧ B e < N) : 0 < auxiliaryT N B := by
  obtain ⟨e, he, hlt⟩ := hex
  have hp : 0 < B e * (N - B e) :=
    Nat.mul_pos he (Nat.sub_pos_of_lt hlt)
  have hle : B e * (N - B e) ≤ auxiliaryT N B := by
    unfold auxiliaryT
    exact Finset.single_le_sum (f := fun j => B j * (N - B j))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
  exact lt_of_lt_of_le hp hle

/-- The explicit integer witness is positive on the candidate support. -/
theorem auxiliaryX_pos (G N : ℕ) (B : E → ℕ)
    (hT : 0 < auxiliaryT N B) (hB : ∀ e, 0 < B e) (e : E) :
    0 < auxiliaryX G N B e := by
  unfold auxiliaryX
  exact Nat.mul_pos (hB e) (by omega)

/-- The internal quadratic normalizer exceeds the correction required
for a proper (< n) binomial observation, on every category with B_e < G. -/
theorem auxiliaryT_gap (G N : ℕ) (B : E → ℕ)
    (hNG : G ≤ N) (hB : ∀ e, 0 < B e)
    (hBG : ∀ e, B e < G) (e : E) :
    (N - G) * B e < auxiliaryT N B := by
  have hBN : B e ≤ N := le_trans (Nat.le_of_lt (hBG e)) hNG
  have hNsplit : N - G + G = N := Nat.sub_add_cancel hNG
  have hBsplit : N - B e + B e = N := Nat.sub_add_cancel hBN
  have hBg : B e < G := hBG e
  have hlt : N - G < N - B e := by omega
  have hprod : (N - G) * B e < (N - B e) * B e :=
    Nat.mul_lt_mul_of_pos_right hlt (hB e)
  have hle : (N - B e) * B e ≤ auxiliaryT N B := by
    unfold auxiliaryT
    have h := Finset.single_le_sum (f := fun j => B j * (N - B j))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
    nlinarith
  omega

/-- A useful difference factorization avoiding subtraction in exponents. -/
theorem auxiliaryX_plus_complement (G N : ℕ) (B : E → ℕ)
    (_hNG : G ≤ N) (e : E)
    (hBN : B e ≤ N)
    (hT : (N - G) * B e ≤ auxiliaryT N B) :
    auxiliaryX G N B e +
      (N - B e) * (auxiliaryT N B - (N - G) * B e) =
      N * auxiliaryT N B := by
  have hsum :
      (N - B e) * ((N-G)*B e) +
      (N - B e) * (auxiliaryT N B - (N-G)*B e) =
      (N-B e) * auxiliaryT N B := by
    calc
      _ = (N-B e) * ((N-G)*B e + (auxiliaryT N B - (N-G)*B e)) := by ring
      _ = (N-B e) * auxiliaryT N B := by rw [Nat.add_sub_of_le hT]
  calc
    auxiliaryX G N B e +
        (N - B e) * (auxiliaryT N B - (N-G)*B e) =
        B e * auxiliaryT N B +
          ((N-B e) * ((N-G)*B e) +
            (N-B e) * (auxiliaryT N B - (N-G)*B e)) := by
      unfold auxiliaryX
      ring
    _ = B e * auxiliaryT N B + (N-B e)*auxiliaryT N B := by rw [hsum]
    _ = (B e + (N-B e)) * auxiliaryT N B := by ring
    _ = N * auxiliaryT N B := by rw [Nat.add_sub_of_le hBN]

/-- Strict upper-bound needed so *both* factors of each binomial likelihood
are positive. -/
theorem auxiliaryX_lt_sample (G N : ℕ) (B : E → ℕ)
    (hNG : G ≤ N) (hB : ∀ e, 0 < B e)
    (hBG : ∀ e, B e < G) (e : E) :
    auxiliaryX G N B e < N * auxiliaryT N B := by
  have hgap := auxiliaryT_gap G N B hNG hB hBG e
  have hBN : B e ≤ N := le_trans (Nat.le_of_lt (hBG e)) hNG
  have hNB : 0 < N - B e := Nat.sub_pos_of_lt (lt_of_lt_of_le (hBG e) hNG)
  have hpos : 0 < (N-B e) * (auxiliaryT N B - (N-G)*B e) :=
    Nat.mul_pos hNB (by omega)
  have hid := auxiliaryX_plus_complement G N B hNG e hBN (le_of_lt hgap)
  omega


/-- Log-likelihood difference in fixed-N product-binomial coordinates;
positive counts and interior masses are required for its statistical meaning. -/
noncomputable def logRatioTerm (N n : ℝ) (A B x : E → ℝ) (e : E) : ℝ :=
  x e * Real.log (A e / B e) +
    (n - x e) * Real.log ((N - A e) / (N - B e))

private noncomputable def tangentTerm (N n : ℝ) (A B x : E → ℝ) (e : E) : ℝ :=
  x e * (A e / B e - 1) +
    (n - x e) * ((N - A e) / (N - B e) - 1)

/-- Strict supporting-line theorem for the explicit real witness. Unlike
a continuous KKT argument on an integer lattice, this directly establishes
a *particular* observation where every distinct same-total vector loses. -/
theorem strict_witness_log_ratio
    (N G T n : ℝ) (A B x : E → ℝ)
    (hBpos : ∀ e, 0 < B e) (hNBpos : ∀ e, 0 < N - B e)
    (hApos : ∀ e, 0 < A e) (hNApos : ∀ e, 0 < N - A e)
    (hxpos : ∀ e, 0 < x e) (hnx : ∀ e, 0 ≤ n - x e)
    (hx : ∀ e, x e = B e * (T + (N - G) * (N - B e)))
    (hn : n = N * T) (hmass : (∑ e, A e) = ∑ e, B e)
    (hne : A ≠ B) :
    (∑ e, logRatioTerm N n A B x e) < 0 := by
  have htangent (e : E) :
      tangentTerm N n A B x e = N * (N - G) * (A e - B e) := by
    unfold tangentTerm
    rw [hx e, hn]
    have hbne : B e ≠ 0 := ne_of_gt (hBpos e)
    have hnbne : N - B e ≠ 0 := ne_of_gt (hNBpos e)
    field_simp
    ring
  have hle (e : E) :
      logRatioTerm N n A B x e ≤ tangentTerm N n A B x e := by
    have hu : 0 < A e / B e := div_pos (hApos e) (hBpos e)
    have hv : 0 < (N - A e) / (N - B e) :=
      div_pos (hNApos e) (hNBpos e)
    have hu' := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos hu) (le_of_lt (hxpos e))
    have hv' := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos hv) (hnx e)
    unfold logRatioTerm tangentTerm
    linarith
  obtain ⟨e₀, he₀⟩ : ∃ e, A e ≠ B e := by
    by_contra h
    apply hne
    funext e
    by_contra he
    exact h ⟨e, he⟩
  have hlt (e : E) (hAB : A e ≠ B e) :
      logRatioTerm N n A B x e < tangentTerm N n A B x e := by
    have hu : 0 < A e / B e := div_pos (hApos e) (hBpos e)
    have hv : 0 < (N - A e) / (N - B e) :=
      div_pos (hNApos e) (hNBpos e)
    have hune : A e / B e ≠ 1 := by
      intro heq
      have hmul := congrArg (fun z : ℝ => z * B e) heq
      have hbne : B e ≠ 0 := ne_of_gt (hBpos e)
      field_simp at hmul
      exact hAB (by linarith)
    have hu' := mul_lt_mul_of_pos_left
      (Real.log_lt_sub_one_of_pos hu hune) (hxpos e)
    have hv' := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos hv) (hnx e)
    unfold logRatioTerm tangentTerm
    linarith
  have hsum : (∑ e, tangentTerm N n A B x e) = 0 := by
    calc
      _ = (∑ e, N * (N - G) * (A e - B e)) :=
        Finset.sum_congr rfl (fun e _ => htangent e)
      _ = N * (N - G) * (∑ e, (A e - B e)) := by
        rw [← Finset.mul_sum]
      _ = 0 := by rw [Finset.sum_sub_distrib, hmass]; ring
  have hsumlt : (∑ e, logRatioTerm N n A B x e) <
      (∑ e, tangentTerm N n A B x e) :=
    Finset.sum_lt_sum (fun e _ => hle e) ⟨e₀, Finset.mem_univ e₀, hlt e₀ he₀⟩
  rw [hsum] at hsumlt
  exact hsumlt


/-- Positive same-length integral spectra with at least two types: integer
witness provides lower log ratio for truth A than competitor B.
This does not yet assert latent start-placement coverage. -/
theorem integer_witness_strict_log_ratio
    (G N : ℕ) (A B : E → ℕ)
    (hGN : G ≤ N)
    (hApos : ∀ e, 0 < A e) (hBpos : ∀ e, 0 < B e)
    (hAltG : ∀ e, A e < G) (hBltG : ∀ e, B e < G)
    (hmass : (∑ e, A e) = (∑ e, B e))
    (hneq : A ≠ B) :
    (∑ e, logRatioTerm (N : ℝ) ((N * auxiliaryT N B : ℕ) : ℝ)
      (fun e => (A e : ℝ)) (fun e => (B e : ℝ))
      (fun e => (auxiliaryX G N B e : ℝ)) e) < 0 := by
  obtain ⟨e₀, he₀⟩ : ∃ e, A e ≠ B e := by
    by_contra h
    apply hneq
    funext e
    by_contra he
    exact h ⟨e, he⟩
  have hTpos : 0 < auxiliaryT N B :=
    auxiliaryT_pos N B ⟨e₀, hBpos e₀, lt_of_lt_of_le (hBltG e₀) hGN⟩
  have hAposR : ∀ e, (0 : ℝ) < (A e : ℝ) := by
    intro e
    exact_mod_cast hApos e
  have hBposR : ∀ e, (0 : ℝ) < (B e : ℝ) := by
    intro e
    exact_mod_cast hBpos e
  have hNAposR : ∀ e, (0 : ℝ) < (N : ℝ) - (A e : ℝ) := by
    intro e
    have hh : A e < N := lt_of_lt_of_le (hAltG e) hGN
    exact sub_pos.mpr (by exact_mod_cast hh)
  have hNBposR : ∀ e, (0 : ℝ) < (N : ℝ) - (B e : ℝ) := by
    intro e
    have hh : B e < N := lt_of_lt_of_le (hBltG e) hGN
    exact sub_pos.mpr (by exact_mod_cast hh)
  have hxposR : ∀ e, (0 : ℝ) < (auxiliaryX G N B e : ℝ) := by
    intro e
    exact_mod_cast auxiliaryX_pos G N B hTpos hBpos e
  have hnxR : ∀ e,
      (0 : ℝ) ≤ ((N * auxiliaryT N B : ℕ) : ℝ) -
        (auxiliaryX G N B e : ℝ) := by
    intro e
    have hlt := auxiliaryX_lt_sample G N B hGN hBpos hBltG e
    have hltR : ((auxiliaryX G N B e : ℕ) : ℝ) <
        ((N * auxiliaryT N B : ℕ) : ℝ) := by exact_mod_cast hlt
    linarith
  have hxR : ∀ e,
      (auxiliaryX G N B e : ℝ) =
      (B e : ℝ) * ((auxiliaryT N B : ℝ) +
        ((N : ℝ) - (G : ℝ)) * ((N : ℝ) - (B e : ℝ))) := by
    intro e
    have hBN : B e ≤ N := le_trans (Nat.le_of_lt (hBltG e)) hGN
    simp only [auxiliaryX, Nat.cast_mul, Nat.cast_add,
      Nat.cast_sub hGN, Nat.cast_sub hBN]
  have hnR : ((N * auxiliaryT N B : ℕ) : ℝ) =
      (N : ℝ) * (auxiliaryT N B : ℝ) := by norm_cast
  have hmassR : (∑ e, (A e : ℝ)) = (∑ e, (B e : ℝ)) := by
    exact_mod_cast hmass
  have hneqR : (fun e => (A e : ℝ)) ≠ (fun e => (B e : ℝ)) := by
    intro h
    apply hneq
    funext e
    have hh := congrFun h e
    exact_mod_cast hh
  exact strict_witness_log_ratio (N : ℝ) (G : ℝ)
    (auxiliaryT N B : ℝ) ((N * auxiliaryT N B : ℕ) : ℝ)
    (fun e => (A e : ℝ)) (fun e => (B e : ℝ))
    (fun e => (auxiliaryX G N B e : ℝ))
    hBposR hNBposR hAposR hNAposR hxposR hnxR hxR hnR
    hmassR hneqR


/-- Scaling an observation and its sample size by a positive integer
preserves strict negativity of the product-binomial log likelihood ratio. -/
theorem strict_log_ratio_scale (N n : ℝ) (A B x : E → ℝ)
    (hscore : (∑ e, logRatioTerm N n A B x e) < 0)
    (k : ℕ) (hk : 0 < k) :
    (∑ e, logRatioTerm N ((k : ℝ) * n) A B
      (fun e => (k : ℝ) * x e) e) < 0 := by
  have hterm (e : E) :
      logRatioTerm N ((k : ℝ) * n) A B (fun e => (k : ℝ) * x e) e =
        (k : ℝ) * logRatioTerm N n A B x e := by
    unfold logRatioTerm
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  exact mul_neg_of_pos_of_neg (by exact_mod_cast hk) hscore

/-- For a fixed type spectrum A of total genome-start mass G, G copies of
any strictly positive count vector can accommodate at least one sampled
read per true start of each type. This is an algebraic count inequality:
the actual sampling-placement map is a separate model-specific bridge. -/
theorem positive_witness_scaled_covers_type_multiplicity
    (G N : ℕ) (A B : E → ℕ)
    (hAsum : (∑ e, A e) = G)
    (hBpos : ∀ e, 0 < B e)
    (hTpos : 0 < auxiliaryT N B) :
    ∀ e, A e ≤ G * auxiliaryX G N B e := by
  intro e
  have hA_le : A e ≤ G := by
    calc
      A e ≤ (∑ i, A i) :=
        Finset.single_le_sum (f := A) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ e)
      _ = G := hAsum
  have hXpos := auxiliaryX_pos G N B hTpos hBpos e
  have hG_le : G ≤ G * auxiliaryX G N B e := by
    calc
      G = G * 1 := by omega
      _ ≤ G * auxiliaryX G N B e :=
        Nat.mul_le_mul_left G (by omega)
  exact le_trans hA_le hG_le


/-- Consolidated **finite counterexample certificate** for positive, interior,
same-mass oriented count spectra. The witness is a legitimate nonnegative
integer count vector summing to its declared sample size, with each type
occurring strictly between zero and n. The competitor B strictly wins
under the product-binomial LOG SCORE. Scaling by the total mass G produces
at least as many observations of each type as there are truth starts of
that type.

This certificate does not claim that every possible bidirected flow spells
a single circular genome. Nor does it itself construct the list of sampled
start positions; that model-specific realization is a separate obligation. -/
theorem integral_witness_certificate
    (G N : ℕ) (A B : E → ℕ)
    (hGN : G ≤ N)
    (hApos : ∀ e, 0 < A e) (hBpos : ∀ e, 0 < B e)
    (hAltG : ∀ e, A e < G) (hBltG : ∀ e, B e < G)
    (hBtotal : (∑ e, B e) = G)
    (hmass : (∑ e, A e) = (∑ e, B e))
    (hneq : A ≠ B) :
    (∑ e, auxiliaryX G N B e) = N * auxiliaryT N B ∧
    (∀ e, 0 < auxiliaryX G N B e ∧
      auxiliaryX G N B e < N * auxiliaryT N B) ∧
    (∀ e, A e ≤ G * auxiliaryX G N B e) ∧
    (∑ e, logRatioTerm (N : ℝ) ((N * auxiliaryT N B : ℕ) : ℝ)
      (fun e => (A e : ℝ)) (fun e => (B e : ℝ))
      (fun e => (auxiliaryX G N B e : ℝ)) e) < 0 := by
  obtain ⟨e₀, he₀⟩ : ∃ e, A e ≠ B e := by
    by_contra h
    apply hneq
    funext e
    by_contra he
    exact h ⟨e, he⟩
  have hT : 0 < auxiliaryT N B :=
    auxiliaryT_pos N B ⟨e₀, hBpos e₀, lt_of_lt_of_le (hBltG e₀) hGN⟩
  have hAsum : (∑ e, A e) = G := by rw [hmass, hBtotal]
  refine ⟨auxiliaryX_sum G N B hBtotal hGN, ?_, ?_, ?_⟩
  · intro e
    exact ⟨auxiliaryX_pos G N B hT hBpos e,
      auxiliaryX_lt_sample G N B hGN hBpos hBltG e⟩
  · exact positive_witness_scaled_covers_type_multiplicity
      G N A B hAsum hBpos hT
  · exact integer_witness_strict_log_ratio G N A B hGN
      hApos hBpos hAltG hBltG hmass hneq

end AssemblyP1.FixedNConstructiveWitness
