import Mathlib

/-!
# Population normalized-to-ordinary spectrum reduction (primitive P2)

Mathematical source: `paper/sections/05-population.tex` and
`docs/maximum-likelihood-models-for-genome-assembly.md` §6.

This file kernel-checks the reusable arithmetic core of the population
reduction and a regression showing primitivity alone is insufficient.
The two external mathematical inputs used by the paper proof are kept
as **explicit hypotheses**, never as axioms:

* **Gibbs/KL tie characterization** (Cover–Thomas): a population tie
  `ℓpop_S(D) = ℓpop_S(S)` holds iff the normalized spectra agree.
  Stated here as an explicit hypothesis `hGibbsTie`.
* **Division–Eulerian gcd-one mechanism + BBT/Ukkonen uniqueness**
  (Bresler–Bresler–Tse 2013, Theorem 3): for primitive P2 genomes the
  ordinary `L`-spectrum has gcd one over its positive entries, and equal
  ordinary spectra imply rotation equivalence. Both appear below as
  explicit hypotheses `hGcdS`, `hGcdD`, `hBBT`.

What is fully proved here (`normalized_to_ordinary`):
proportional gcd-one integer spectrum vectors are equal (hence the two
lengths agree). The regression (`primitivity_insufficient`) shows the
gcd-one hypothesis cannot be dropped: primitive `S = AAB` (`|S| = 3`)
and `D = AAABAB` (`|D| = 6`) share normalized 2-spectra but not
ordinary 2-spectra.
-/

namespace AssemblyP1.PopulationReduction

variable {W : Type*} [Fintype W]

/-- Gcd-one over all entries (zeros contribute nothing: every `g`
divides `0`, so this is the gcd of the positive entries). -/
def IsGcdOne (c : W → ℕ) : Prop :=
  ∀ g : ℕ, (∀ w : W, g ∣ c w) → g = 1

/-- Normalized-spectrum equality, stated multiplicatively to avoid
division: `c(w)/n = d(w)/m` for every word `w`. -/
def NormalizedEqual (c d : W → ℕ) (n m : ℕ) : Prop :=
  ∀ w : W, c w * m = d w * n

theorem normalized_to_ordinary {c d : W → ℕ} {n m : ℕ}
    (hn : 0 < n) (_hm : 0 < m)
    (_hS : ∑ w : W, c w = n) (_hD : ∑ w : W, d w = m)
    (hNorm : NormalizedEqual c d n m)
    (hGcdC : IsGcdOne c) (hGcdD : IsGcdOne d) :
    n = m ∧ c = d := by
  -- Let `g = gcd n m`, `n₁ = n / g`, `m₁ = m / g` coprime.
  set g := Nat.gcd n m with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left m hn
  have hcop : Nat.Coprime (n / g) (m / g) :=
    Nat.coprime_div_gcd_div_gcd hgpos
  have hn_eq : g * (n / g) = n := Nat.mul_div_cancel' (Nat.gcd_dvd_left n m)
  have hm_eq : g * (m / g) = m := Nat.mul_div_cancel' (Nat.gcd_dvd_right n m)
  -- From `c w * m = d w * n` cancel `g`.
  have hcancel : ∀ w : W, c w * (m / g) = d w * (n / g) := by
    intro w
    have h := hNorm w
    rw [← hm_eq, ← hn_eq] at h
    have h2 : (c w * (m / g)) * g = (d w * (n / g)) * g := by
      linear_combination h
    exact Nat.mul_right_cancel hgpos h2
  -- `n/g ∣ c w` for every `w`, since `n/g ∣ d w * (n/g) = c w * (m/g)` and coprime.
  have hn₁_dvd : ∀ w : W, (n / g) ∣ c w := by
    intro w
    have h1 : (n / g) ∣ c w * (m / g) := by
      rw [hcancel w]
      exact dvd_mul_left _ _
    exact (Nat.Coprime.dvd_of_dvd_mul_right hcop h1)
  have hm₁_dvd : ∀ w : W, (m / g) ∣ d w := by
    intro w
    have h1 : (m / g) ∣ d w * (n / g) := by
      rw [← hcancel w]
      exact dvd_mul_left _ _
    exact (Nat.Coprime.dvd_of_dvd_mul_right hcop.symm h1)
  have hn₁ : n / g = 1 := hGcdC (n / g) hn₁_dvd
  have hm₁ : m / g = 1 := hGcdD (m / g) hm₁_dvd
  have hnm : n = m := by
    calc n = g * (n / g) := hn_eq.symm
    _ = g * (m / g) := by rw [hn₁, hm₁]
    _ = m := hm_eq
  refine ⟨hnm, ?_⟩
  funext w
  have h := hcancel w
  rw [hn₁, hm₁, mul_one, mul_one] at h
  exact h

/--
Explicit-hypothesis wrapper recording the paper's proof chain.
`hGibbsTie` is the Gibbs/KL input (Cover–Thomas: tie iff normalized
equality); `hGcdS`/`hGcdD` are discharged in notes by the
division–Eulerian argument; `hBBT` is Bresler–Bresler–Tse (2013)
Theorem 3 at `K = L - 1`. No external fact is hidden: each is a
universally quantified hypothesis.
-/
theorem population_tie_reduction {cS cD : W → ℕ} {nS nD : ℕ}
    (hnS : 0 < nS) (hnD : 0 < nD)
    (hSumS : ∑ w : W, cS w = nS) (hSumD : ∑ w : W, cD w = nD)
    (hGibbsTie : NormalizedEqual cS cD nS nD)
    (hGcdS : IsGcdOne cS) (hGcdD : IsGcdOne cD) :
    nS = nD ∧ cS = cD :=
  normalized_to_ordinary hnS hnD hSumS hSumD hGibbsTie hGcdS hGcdD

/-- BBT uniqueness step with the external theorem explicit. -/
theorem population_uniqueness_of_ordinary {Genome V : Type*}
    (cS cD : V → ℕ)
    (hOrd : cS = cD)
    (rotEquiv : Genome → Genome → Prop)
    (S D : Genome)
    (hBBT : cS = cD → rotEquiv D S) :
    rotEquiv D S :=
  hBBT hOrd

-- ---------------------------------------------------------------------------
-- Regression: primitivity alone does not imply the reduction.
-- ---------------------------------------------------------------------------

/-- Two-letter alphabet keeps the regression enumerations tiny. -/
inductive Bin where
  | A | B
  deriving DecidableEq, Repr, Inhabited, BEq

instance : Fintype Bin :=
  ⟨{.A, .B}, by intro x; cases x <;> simp⟩

abbrev Word3 := Fin 3 → Bin
abbrev Word6 := Fin 6 → Bin
abbrev DiBin := Fin 2 → Bin

def regS : Word3 := ![Bin.A, Bin.A, Bin.B]
def regD : Word6 := ![Bin.A, Bin.A, Bin.A, Bin.B, Bin.A, Bin.B]

def regSCyc (i : Nat) : Bin := regS ⟨i % 3, Nat.mod_lt _ (by norm_num)⟩
def regDCyc (i : Nat) : Bin := regD ⟨i % 6, Nat.mod_lt _ (by norm_num)⟩

def regSWin (r : Fin 3) : DiBin := fun d => regSCyc (r.val + d.val)
def regDWin (r : Fin 6) : DiBin := fun d => regDCyc (r.val + d.val)

def regSOcc (w : DiBin) : ℕ :=
  (Finset.univ.filter (fun r : Fin 3 => regSWin r = w)).card

def regDOcc (w : DiBin) : ℕ :=
  (Finset.univ.filter (fun r : Fin 6 => regDWin r = w)).card

def RegSPrimitive : Prop :=
  ∀ k : Fin 3, k ≠ 0 → ∃ i : Fin 3, regSCyc (i.val + k.val) ≠ regS i

def RegDPrimitive : Prop :=
  ∀ k : Fin 6, k ≠ 0 → ∃ i : Fin 6, regDCyc (i.val + k.val) ≠ regD i

theorem reg_S_primitive : RegSPrimitive := by unfold RegSPrimitive; decide

theorem reg_D_primitive : RegDPrimitive := by unfold RegDPrimitive; decide

/-- The two ordinary 2-spectra are proportional with factor two. -/
theorem reg_normalized_equal : NormalizedEqual regSOcc regDOcc 3 6 := by
  intro w
  fin_cases w <;> decide

theorem reg_sum_S : ∑ w : DiBin, regSOcc w = 3 := by decide

theorem reg_sum_D : ∑ w : DiBin, regDOcc w = 6 := by decide

private def diAA : DiBin := ![Bin.A, Bin.A]

theorem reg_ordinary_differ : regSOcc ≠ regDOcc := by
  intro h
  have h1 : regSOcc diAA = 1 := by decide
  have h2 : regDOcc diAA = 2 := by decide
  rw [h] at h1
  omega

/-- The competitor spectrum `(AA:2, AB:2, BA:2)` is divisible by two,
so the gcd-one hypothesis genuinely fails there. -/
theorem reg_competitor_not_gcd_one : ¬ IsGcdOne regDOcc := by
  intro h
  have h2 := h 2 (by intro w; fin_cases w <;> decide)
  norm_num at h2

/-- Regression: both words are primitive and share normalized spectra,
yet ordinary spectra differ — primitivity alone is insufficient and the
gcd-one hypothesis in `normalized_to_ordinary` cannot be dropped. -/
theorem primitivity_insufficient :
    RegSPrimitive ∧ RegDPrimitive ∧
      NormalizedEqual regSOcc regDOcc 3 6 ∧ regSOcc ≠ regDOcc ∧
      ¬ IsGcdOne regDOcc :=
  ⟨reg_S_primitive, reg_D_primitive, reg_normalized_equal,
    reg_ordinary_differ, reg_competitor_not_gcd_one⟩

end AssemblyP1.PopulationReduction
