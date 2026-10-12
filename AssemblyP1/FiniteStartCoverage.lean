import AssemblyP1.FixedNConstructiveWitness
import Mathlib

open Finset BigOperators

namespace AssemblyP1.FiniteStartCoverage

variable {S E : Type*} [Fintype S] [DecidableEq E]

/-- Number of genome starts producing each observed read type. -/
def startSpectrum (f : S → E) (e : E) : ℕ :=
  (Finset.univ.filter (fun s => f s = e)).card

/-- An explicit finite multiplicity function is a sampling plan. If a read
from every true start must appear, positivity of the multiplicity is the
coverage condition. -/
def SampleStartCoverage (f : S → E) (x : E → ℕ) : Prop :=
  ∃ m : S → ℕ, (∀ s, 0 < m s) ∧
    ∀ e, (∑ s ∈ Finset.univ.filter (fun s => f s = e), m s) = x e

/-- A type-wise budget exceeding the true start multiplicities is sufficient
to realize a read sample that covers every start, as long as every modeled
read type is realized by at least one start. The proof is constructive:
sample each start once, then assign all excess reads of type e to any
representative start of that type. -/
theorem coverage_of_type_budget
    (f : S → E) (hf : Function.Surjective f) (x : E → ℕ)
    (hdom : ∀ e, startSpectrum f e ≤ x e) :
    SampleStartCoverage f x := by
  classical
  obtain ⟨rep, hrep⟩ := hf.hasRightInverse
  let m : S → ℕ := fun s =>
    1 + if s = rep (f s) then x (f s) - startSpectrum f (f s) else 0
  refine ⟨m, ?_, ?_⟩
  · intro s
    simp only [m]
    omega
  · intro e
    let fibre : Finset S := Finset.univ.filter (fun s => f s = e)
    have hmem : rep e ∈ fibre := by simp [fibre, hrep e]
    have hformula : ∀ s ∈ fibre,
        m s = 1 + (if s = rep e then x e - startSpectrum f e else 0) := by
      intro s hs
      have hsfe : f s = e := (Finset.mem_filter.mp hs).2
      simp [m, hsfe]
    calc
      (∑ s ∈ fibre, m s) =
          ∑ s ∈ fibre, (1 + (if s = rep e then x e - startSpectrum f e else 0)) :=
        Finset.sum_congr rfl hformula
      _ = fibre.card + (x e - startSpectrum f e) := by
        rw [Finset.sum_add_distrib]
        simp [Finset.sum_ite_eq', hmem]
      _ = x e := by
        have hfibre : fibre.card = startSpectrum f e := rfl
        rw [hfibre]
        exact Nat.add_sub_of_le (hdom e)


/-- If every modeled read type appears among the true genome starts,
then the start-to-read-type map is surjective. -/
theorem surjective_of_positive_start_spectrum
    (f : S → E) (hpos : ∀ e, 0 < startSpectrum f e) :
    Function.Surjective f := by
  intro e
  have hh : (Finset.univ.filter (fun s => f s = e)).Nonempty :=
    Finset.card_pos.mp (hpos e)
  obtain ⟨s, hs⟩ := hh
  exact ⟨s, (Finset.mem_filter.mp hs).2⟩

/-! ## Concrete genome-start bridge from the fixed-N witness -/

variable [Fintype E]

open AssemblyP1.FixedNConstructiveWitness

/-- The scaled integer binomial witness can be realized by actual positive
multiplicities of *every* genome start, rather than just by a type-count budget.
The read type of start s is f(s), and A is its true start spectrum.

The log score below is the natural log of the positive product-binomial
likelihood ratio of truth A to competitor B. This theorem uses the fixed
external N, equal mass, and a common positive oriented type support; it is
not a result about arbitrary MB09 bidirected flows. -/
theorem strict_covered_witness_for_positive_spectra
    (f : S → E)
    (G N : ℕ) (B : E → ℕ)
    (hGpos : 0 < G) (hGN : G ≤ N)
    (hApos : ∀ e, 0 < startSpectrum f e)
    (hBpos : ∀ e, 0 < B e)
    (hAltG : ∀ e, startSpectrum f e < G)
    (hBltG : ∀ e, B e < G)
    (hBtotal : (∑ e, B e) = G)
    (hmass : (∑ e, startSpectrum f e) = (∑ e, B e))
    (hneq : startSpectrum f ≠ B) :
    ∃ m : S → ℕ,
      (∀ s, 0 < m s) ∧
      (∀ e, (∑ s ∈ Finset.univ.filter (fun s => f s = e), m s) =
        G * auxiliaryX G N B e) ∧
      (∑ e,
        logRatioTerm (N : ℝ) ((G : ℝ) * ((N * auxiliaryT N B : ℕ) : ℝ))
          (fun e => (startSpectrum f e : ℝ)) (fun e => (B e : ℝ))
          (fun e => (G : ℝ) * (auxiliaryX G N B e : ℝ)) e) < 0 := by
  have hAsum : (∑ e, startSpectrum f e) = G := by rw [hmass, hBtotal]
  have hneqAux : startSpectrum f ≠ B := hneq
  obtain ⟨_, _, hbudget, hscore⟩ :=
    integral_witness_certificate G N (startSpectrum f) B hGN
      hApos hBpos hAltG hBltG hBtotal hmass hneqAux
  obtain ⟨m, hpos, hcounts⟩ :=
    coverage_of_type_budget f (surjective_of_positive_start_spectrum f hApos)
      (fun e => G * auxiliaryX G N B e) hbudget
  refine ⟨m, hpos, hcounts, ?_⟩
  exact strict_log_ratio_scale (N : ℝ) ((N * auxiliaryT N B : ℕ) : ℝ)
    (fun e => (startSpectrum f e : ℝ)) (fun e => (B e : ℝ))
    (fun e => (auxiliaryX G N B e : ℝ))
    hscore G hGpos

end AssemblyP1.FiniteStartCoverage

namespace AssemblyP1.FiniteStartCoverage

variable {S E : Type*} [Fintype S] [Fintype E] [DecidableEq E]

/-- Read count of each observed type from a multiplicity-valued start sample. -/
def typeCounts (f : S → E) (m : S → ℕ) (e : E) : ℕ :=
  ∑ s ∈ Finset.univ.filter (fun s => f s = e), m s

/-- Sum of type counts is the total number of sampled starts with multiplicity. -/
theorem total_typeCounts (f : S → E) (m : S → ℕ) :
    (∑ e, typeCounts f m e) = (∑ s, m s) := by
  classical
  unfold typeCounts
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp

end AssemblyP1.FiniteStartCoverage


namespace AssemblyP1.FiniteStartCoverage

variable {S E : Type*} [Fintype S] [Fintype E] [DecidableEq E]

open AssemblyP1.FixedNConstructiveWitness

/-- Log score of the truth-relative-to-B ratio from a multiset of positive
start multiplicities, represented by its type-count vector. -/
noncomputable def truthLogRatio (f : S → E) (m : S → ℕ)
    (N : ℕ) (B : E → ℕ) : ℝ :=
  ∑ e, logRatioTerm (N : ℝ) (((∑ i, typeCounts f m i) : ℕ) : ℝ)
    (fun i => (startSpectrum f i : ℝ))
    (fun i => (B i : ℝ))
    (fun i => (typeCounts f m i : ℝ)) e

/-- Truth is a log-score maximizer for every covered finite start sample,
among the specified modeled candidate spectra. -/
def UniformCoveredMaximizer (f : S → E)
    (C : Finset (E → ℕ)) (N : ℕ) : Prop :=
  ∀ m : S → ℕ, (∀ s, 0 < m s) →
    ∀ B ∈ C, 0 ≤ truthLogRatio f m N B

/-- Every candidate within the chosen class has the same read-type spectrum
as truth. This is spectrum rigidity, not genome uniqueness up to rotation. -/
def SpectrumRigid (f : S → E) (C : Finset (E → ℕ)) : Prop :=
  ∀ B ∈ C, B = startSpectrum f

/-- Necessary-and-sufficient finite fixed-N spectrum criterion.
Under positive same-supported interior read-type spectra with total G,
the truth maximizes the product-binomial log score for every sampled-start
coverage observation iff the candidate class has no distinct spectrum.

This is a scoped theorem about oriented positive spectrum candidates, NOT the
arbitrary molecule-type/bidirected flow domain of MB09 Section 6.2. -/
theorem uniform_covered_maximizer_iff_spectrum_rigid
    (f : S → E) (C : Finset (E → ℕ)) (G N : ℕ)
    (hGpos : 0 < G) (hGN : G ≤ N)
    (hApos : ∀ e, 0 < startSpectrum f e)
    (hAltG : ∀ e, startSpectrum f e < G)
    (hAtotal : (∑ e, startSpectrum f e) = G)
    (hC : ∀ B ∈ C,
      (∀ e, 0 < B e ∧ B e < G) ∧ (∑ e, B e) = G) :
    UniformCoveredMaximizer f C N ↔ SpectrumRigid f C := by
  classical
  constructor
  · intro hmax B hBC
    by_contra hne
    obtain ⟨hBounds, hBtotal⟩ := hC B hBC
    have hmass : (∑ e, startSpectrum f e) = (∑ e, B e) := by
      rw [hAtotal, hBtotal]
    obtain ⟨m, hmpos, hmcounts, hscore⟩ :=
      strict_covered_witness_for_positive_spectra f G N B
        hGpos hGN hApos (fun e => (hBounds e).1)
        hAltG (fun e => (hBounds e).2)
        hBtotal hmass (Ne.symm hne)
    have hn : (∑ e, typeCounts f m e) =
        G * (N * auxiliaryT N B) := by
      calc
        (∑ e, typeCounts f m e) =
            (∑ e, G * auxiliaryX G N B e) :=
          Finset.sum_congr rfl (fun e _ => hmcounts e)
        _ = G * (∑ e, auxiliaryX G N B e) := by
          rw [Finset.mul_sum]
        _ = G * (N * auxiliaryT N B) := by
          rw [auxiliaryX_sum G N B hBtotal hGN]
    have hscore_eq :
        truthLogRatio f m N B =
          ∑ e, logRatioTerm (N : ℝ)
            ((G : ℝ) * ((N * auxiliaryT N B : ℕ) : ℝ))
            (fun e => (startSpectrum f e : ℝ))
            (fun e => (B e : ℝ))
            (fun e => (G : ℝ) * (auxiliaryX G N B e : ℝ)) e := by
      unfold truthLogRatio
      have hnR : (((∑ e, typeCounts f m e) : ℕ) : ℝ) =
          (G : ℝ) * ((N * auxiliaryT N B : ℕ) : ℝ) := by
        rw [hn]; norm_cast
      rw [hnR]
      apply Finset.sum_congr rfl
      intro e _
      have hxe : typeCounts f m e = G * auxiliaryX G N B e := hmcounts e
      simp only [logRatioTerm, hxe, Nat.cast_mul]
    have hnonneg := hmax m hmpos B hBC
    rw [hscore_eq] at hnonneg
    exact (not_lt_of_ge hnonneg) hscore
  · intro hrig m hmpos B hBC
    have hB : B = startSpectrum f := hrig B hBC
    subst B
    unfold truthLogRatio
    have hz : ∀ e,
        logRatioTerm (N : ℝ) (((∑ i, typeCounts f m i) : ℕ) : ℝ)
          (fun i => (startSpectrum f i : ℝ))
          (fun i => (startSpectrum f i : ℝ))
          (fun i => (typeCounts f m i : ℝ)) e = 0 := by
      intro e
      have hAne : (startSpectrum f e : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (hApos e))
      have hNAne : (N : ℝ) - (startSpectrum f e : ℝ) ≠ 0 := by
        have he : startSpectrum f e < N := lt_of_lt_of_le (hAltG e) hGN
        have hh : (startSpectrum f e : ℝ) < (N : ℝ) := by exact_mod_cast he
        linarith
      unfold logRatioTerm
      simp [div_self hAne, div_self hNAne]
    simp_rw [hz]
    simp

end AssemblyP1.FiniteStartCoverage
