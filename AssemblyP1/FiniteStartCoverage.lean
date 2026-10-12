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
