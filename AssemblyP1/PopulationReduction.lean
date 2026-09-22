import Mathlib

/-!
# Population normalized-to-ordinary spectrum reduction (primitive P2)

Mathematical source: `paper/sections/05-population.tex` and
`docs/maximum-likelihood-models-for-genome-assembly.md` §6.

This file kernel-checks the reusable arithmetic core of the population
reduction, the AssemblyP1-original primitive-P2 division–Eulerian
derivation of gcd-one (conditional on explicit spelling/uniqueness
premises), and a regression showing primitivity alone is insufficient.
External mathematical inputs are kept as **explicit hypotheses**,
never as axioms:

* **Gibbs/KL tie characterization** (Cover–Thomas): a population tie
  `ℓpop_S(D) = ℓpop_S(S)` holds iff the normalized spectra agree.
  Gibbs itself stays outside this file; theorems below take the
  resulting normalized equality (`NormalizedEqual`) as a premise.
* **Eulerian spelling of a divided balanced connected spectrum**
  (standard Eulerian-circuit existence applied to the paper's divided
  circulation `c/g`): stated as an explicit premise `hSpell`.
* **Bresler–Bresler–Tse (2013), Theorem 3** complete-spectrum
  uniqueness at `K = L - 1`: an explicit premise `hBBT`.

What is fully proved here:
* `normalized_to_ordinary`: proportional gcd-one integer spectrum
  vectors are equal (hence the two lengths agree).
* Circulation division (`divided_balanced`, `divided_sum`,
  `divided_support`): dividing a balanced integer circulation by a
  common divisor preserves balance, scales the total, and preserves
  support — the project-side division half of `lem:scaling`.
* Power lifting (`pow_spec_of_spell`): a spelling `W` of the quotient
  lifts to `spec (power W g) = spec S` via the explicit power-scale
  interface — the project-side repeated-spectrum identity.
* `gcd_one_of_primitive_P2`: from those project-side steps plus BBT
  uniqueness, primitivity, its rotation-invariance, and
  non-primitivity of nontrivial powers, derive `IsGcdOne`.
* `population_uniqueness_primitive_P2`: the end-to-end project-level
  reduction (normalized equality → ordinary equality → rotation
  equivalence) under the same premises.
The regression (`primitivity_insufficient`) shows the
gcd-one conclusion cannot be obtained from primitivity alone:
primitive `S = AAB` (`|S| = 3`) and `D = AAABAB` (`|D| = 6`) share
normalized 2-spectra but not ordinary 2-spectra.
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
`hNormEq` is normalized-spectrum equality, the conclusion of the
external Gibbs/KL input (Cover–Thomas: tie iff normalized equality),
which itself stays outside this file; `hGcdS`/`hGcdD` are the
gcd-one facts discharged by `gcd_one_of_primitive_P2` via the
division–Eulerian argument under explicit Eulerian-spelling and BBT
premises (see below); `hBBT` in the uniqueness theorem is
Bresler–Bresler–Tse (2013) Theorem 3 at `K = L - 1`. No external fact
is hidden: each is a universally quantified hypothesis.
-/
theorem population_tie_reduction {cS cD : W → ℕ} {nS nD : ℕ}
    (hnS : 0 < nS) (hnD : 0 < nD)
    (hSumS : ∑ w : W, cS w = nS) (hSumD : ∑ w : W, cD w = nD)
    (hNormEq : NormalizedEqual cS cD nS nD)
    (hGcdS : IsGcdOne cS) (hGcdD : IsGcdOne cD) :
    nS = nD ∧ cS = cD :=
  normalized_to_ordinary hnS hnD hSumS hSumD hNormEq hGcdS hGcdD

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
-- AssemblyP1-original primitive-P2 division–Eulerian gcd-one mechanism.
-- Paper source: `paper/sections/05-population.tex`, proof of
-- `lem:scaling`, via `thm:BBT` (Bresler–Bresler–Tse 2013, Theorem 3).
-- Balance is stated against abstract out/in edge families so this file
-- does not rebuild de Bruijn infrastructure or duplicate the
-- circular-spectrum word layer of issue #69: instantiations plug in
-- `(L-1)`-mer vertices and `L`-mer edges. The standard existence of an
-- Eulerian closed trail spelling the divided circulation `c/g` is an
-- explicit premise `hSpell`; complete-spectrum uniqueness is an
-- explicit premise `hBBT`. What Lean checks is the project-side
-- division of the circulation, the power-lifting identity
-- `spec (W^g) = spec S`, and the derivation from those premises (plus
-- primitivity and its rotation-invariance and non-primitivity of
-- nontrivial powers) to `IsGcdOne`. In particular gcd-one itself is
-- never assumed.
-- ---------------------------------------------------------------------------

section CirculationDivision

variable {V E : Type*}

/-- Balance of an integer circulation against abstract out/in edge
families (instantiated with de Bruijn prefix/suffix edges). -/
def Balanced (Out In : V → Finset E) (c : E → ℕ) : Prop :=
  ∀ v : V, ∑ e ∈ Out v, c e = ∑ e ∈ In v, c e

/-- The divided circulation `c/g` of the manuscript proof. -/
def divided (c : E → ℕ) (g : ℕ) : E → ℕ :=
  fun e => c e / g

theorem divided_balanced {Out In : V → Finset E} {c : E → ℕ} {g : ℕ}
    (hg : 0 < g) (hdiv : ∀ e : E, g ∣ c e)
    (hbal : Balanced Out In c) :
    Balanced Out In (divided c g) := by
  intro v
  have hout : g * ∑ e ∈ Out v, divided c g e = ∑ e ∈ Out v, c e := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    exact Nat.mul_div_cancel' (hdiv e)
  have hin : g * ∑ e ∈ In v, divided c g e = ∑ e ∈ In v, c e := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    exact Nat.mul_div_cancel' (hdiv e)
  have h := hbal v
  rw [← hout, ← hin] at h
  exact Nat.mul_left_cancel (by omega : 0 < g) h

theorem divided_sum {c : E → ℕ} {g : ℕ}
    (hg : 0 < g) (hdiv : ∀ e : E, g ∣ c e) (s : Finset E) :
    ∑ e ∈ s, divided c g e = (∑ e ∈ s, c e) / g := by
  have h : g * ∑ e ∈ s, divided c g e = ∑ e ∈ s, c e := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    exact Nat.mul_div_cancel' (hdiv e)
  rw [← h]
  exact (Nat.mul_div_cancel_left _ hg).symm

theorem divided_support {c : E → ℕ} {g : ℕ}
    (_hg : 0 < g) (hdiv : ∀ e : E, g ∣ c e) (e : E) :
    divided c g e = 0 ↔ c e = 0 := by
  constructor
  · intro h
    have h2 : g * divided c g e = c e := Nat.mul_div_cancel' (hdiv e)
    rw [h, mul_zero] at h2
    exact h2.symm
  · intro h
    simp [divided, h, Nat.zero_div]

end CirculationDivision

/-- Power lifting: a spelling `W` of the quotient `spec S / g` repeats
to the original spectrum, via the explicit power-scale interface
`hPowScale` (what `power W g`, i.e. `W^g`, means for spectra: each
cyclic window count scales by `g`, cf. `lem:scaling` "each cyclic
length-`L` window of `W` lifts to exactly `g` windows of `W^g`").
Lean checks the arithmetic lift `g * (c/g) = c`; only the Eulerian
existence of `W` (`hSpell`) and BBT below stay premises. -/
theorem pow_spec_of_spell {Genome V : Type*} [Fintype V]
    {spec : Genome → (V → ℕ)} {power : Genome → ℕ → Genome}
    {S W : Genome} {g : ℕ}
    (hdiv : ∀ v : V, g ∣ spec S v)
    (hSpell : spec W = fun v => spec S v / g)
    (hPowScale : spec (power W g) = fun v => g * spec W v) :
    spec (power W g) = spec S := by
  funext v
  rw [hPowScale]
  simp only
  rw [hSpell]
  simp only
  exact Nat.mul_div_cancel' (hdiv v)

/-- Primitive-P2 spectra have gcd one, conditional on the explicit
Eulerian-spelling and BBT premises of the paper proof. -/
theorem gcd_one_of_primitive_P2 {Genome V : Type*} [Fintype V]
    {spec : Genome → (V → ℕ)} {len : Genome → ℕ}
    {Primitive AdmP2 : Genome → Prop}
    {rotEquiv : Genome → Genome → Prop}
    {power : Genome → ℕ → Genome}
    (S : Genome)
    (hSum : ∑ v : V, spec S v = len S)
    (hlen : 0 < len S)
    (hPrim : Primitive S)
    (hP2S : AdmP2 S)
    (hSpell : ∀ g : ℕ, 1 < g → (∀ v : V, g ∣ spec S v) →
      ∃ W : Genome, spec W = fun v => spec S v / g)
    (hPowScale : ∀ W : Genome, ∀ g : ℕ,
      spec (power W g) = fun v => g * spec W v)
    (hPowerNonPrim : ∀ W : Genome, ∀ g : ℕ, 1 < g → ¬ Primitive (power W g))
    (hBBT : ∀ D : Genome, AdmP2 S → spec D = spec S → rotEquiv D S)
    (hRotPrim : ∀ D : Genome, rotEquiv D S → Primitive S → Primitive D) :
    IsGcdOne (spec S) := by
  intro g hg
  by_cases h1 : g = 1
  · exact h1
  · have hpos : 0 < g := by
      rcases Nat.eq_zero_or_pos g with rfl | hp
      · exfalso
        have hall : ∀ v : V, spec S v = 0 :=
          fun v => Nat.eq_zero_of_zero_dvd (hg v)
        have hzero : ∑ v : V, spec S v = 0 :=
          Finset.sum_eq_zero (fun v _ => hall v)
        omega
      · exact hp
    have hlt : 1 < g := by omega
    obtain ⟨W, hSpecW⟩ := hSpell g hlt hg
    have hLift : spec (power W g) = spec S :=
      pow_spec_of_spell hg hSpecW (hPowScale W g)
    have hRot := hBBT (power W g) hP2S hLift
    have hPrimW := hRotPrim (power W g) hRot hPrim
    exact absurd hPrimW (hPowerNonPrim W g hlt)

/-- End-to-end project-level reduction for primitive P2 genomes:
normalized equality forces ordinary equality and rotation
equivalence, under the same explicit Eulerian-spelling/BBT premises
for each genome plus one final BBT uniqueness application. -/
theorem population_uniqueness_primitive_P2 {Genome V : Type*} [Fintype V]
    {spec : Genome → (V → ℕ)} {len : Genome → ℕ}
    {Primitive AdmP2 : Genome → Prop}
    {rotEquiv : Genome → Genome → Prop}
    {power : Genome → ℕ → Genome}
    (S D : Genome)
    (hSumS : ∑ v : V, spec S v = len S)
    (hSumD : ∑ v : V, spec D v = len D)
    (hlenS : 0 < len S) (hlenD : 0 < len D)
    (hPrimS : Primitive S) (hPrimD : Primitive D)
    (hP2S : AdmP2 S) (hP2D : AdmP2 D)
    (hNormEq : NormalizedEqual (spec S) (spec D) (len S) (len D))
    (hSpellS : ∀ g : ℕ, 1 < g → (∀ v : V, g ∣ spec S v) →
      ∃ W : Genome, spec W = fun v => spec S v / g)
    (hSpellD : ∀ g : ℕ, 1 < g → (∀ v : V, g ∣ spec D v) →
      ∃ W : Genome, spec W = fun v => spec D v / g)
    (hPowScale : ∀ W : Genome, ∀ g : ℕ,
      spec (power W g) = fun v => g * spec W v)
    (hPowerNonPrim : ∀ W : Genome, ∀ g : ℕ, 1 < g → ¬ Primitive (power W g))
    (hBBTS : ∀ E : Genome, AdmP2 S → spec E = spec S → rotEquiv E S)
    (hBBTD : ∀ E : Genome, AdmP2 D → spec E = spec D → rotEquiv E D)
    (hRotPrimS : ∀ E : Genome, rotEquiv E S → Primitive S → Primitive E)
    (hRotPrimD : ∀ E : Genome, rotEquiv E D → Primitive D → Primitive E)
    (hBBTuniq : spec S = spec D → rotEquiv D S) :
    len S = len D ∧ spec S = spec D ∧ rotEquiv D S := by
  have hGcdS : IsGcdOne (spec S) :=
    gcd_one_of_primitive_P2 S hSumS hlenS hPrimS hP2S hSpellS
      hPowScale hPowerNonPrim hBBTS hRotPrimS
  have hGcdD : IsGcdOne (spec D) :=
    gcd_one_of_primitive_P2 D hSumD hlenD hPrimD hP2D hSpellD
      hPowScale hPowerNonPrim hBBTD hRotPrimD
  have hOrd := normalized_to_ordinary hlenS hlenD hSumS hSumD hNormEq hGcdS hGcdD
  exact ⟨hOrd.1, hOrd.2, hBBTuniq hOrd.2⟩

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
