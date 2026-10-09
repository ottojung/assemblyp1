import Mathlib

/-!
# Fibre-count arithmetic for the exact same-length spectrum fibre (board #219)

This module formalizes the **number-theoretic core** of the exact
same-length complete-spectrum fibre count of
`docs/exact-fibre-count-theorem-219.md`: the divisor-Möbius inversion that
converts the stabilizer-weighted BEST quantity `B_h` into the primitive orbit
count `P_h`, the classical Möbius/totient divisor identity, and the positive
totient/Burnside rearrangement giving the total orbit count `N(c)` without
Möbius inversion.

The graph/BEST content (the weighted Matrix-Tree quantity `B_h`, the
double-counting identity `B_h = Σ 1/s(W)`, and the singleton criterion's
branching argument) is **external**: the BEST theorem is classical
(van Aardenne-Ehrenfest–de Bruijn 1951; Tutte 1975) and the branching
primitive-spelling construction is already kernel-checked in
`AssemblyP1/ScalarPrimitiveSpellings.lean`.  What is formalised here is the
elementary divisor-sum manipulation that is the board's own contribution and
that could otherwise carry a convention error.

All functions are `ℕ → ℚ` (the `B_h` are rational in general).  The
identities are stated for arbitrary such functions, so they apply to the
fibre-count `B` and `P` of the note.
-/

namespace AssemblyP1.FibreCount

open Finset Nat
open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-! ## Divisor-sum helpers -/

/-- Convert an antidiagonal divisor sum to a divisor sum. -/
theorem sum_antidiagonal_eq_sum_divisors {R : Type*} [CommSemiring R] {n : ℕ}
    (f : ℕ → ℕ → R) (_hn : n ≠ 0) :
    ∑ x ∈ n.divisorsAntidiagonal, f x.1 x.2
      = ∑ d ∈ n.divisors, f (n / d) d := by
  rw [← map_div_left_divisors]
  rw [Finset.sum_map]
  rfl

/-- Reindex a divisor sum by the involution `d ↦ n/d`. -/
theorem sum_divisors_inv_mul_eq {R : Type*} [CommSemiring R] {n : ℕ}
    (f : ℕ → ℕ → R) (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, f (n / d) d = ∑ d ∈ n.divisors, f d (n / d) := by
  refine Finset.sum_bij (fun d _ => n / d) ?_ ?_ ?_ ?_
  · intro d hd
    exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (dvd_of_mem_divisors hd), hn⟩
  · intro d₁ hd₁ d₂ hd₂ heq
    have e1 : n / (n / d₁) = d₁ := Nat.div_div_self (dvd_of_mem_divisors hd₁) hn
    have e2 : n / (n / d₂) = d₂ := Nat.div_div_self (dvd_of_mem_divisors hd₂) hn
    rw [← e1, ← e2, heq]
  · intro b hb
    exact ⟨n / b, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (dvd_of_mem_divisors hb), hn⟩,
      by rw [Nat.div_div_self (dvd_of_mem_divisors hb) hn]⟩
  · intro d hd
    rw [Nat.div_div_self (dvd_of_mem_divisors hd) hn]

/-- **Divisor-sum reindex.**  For any `n` and `f B : ℕ → R`,

    Σ_{h | n} Σ_{d | h} f d · B (h / d) = Σ_{k | n} B k · Σ_{d | n/k} f d.

This is the change of variables `h = k · d` (`k = h/d`) that turns the
primitive-orbit Möbius sum into the Burnside/totient form.  It is the only
nontrivial combinatorial step in Theorem 2 of
`docs/exact-fibre-count-theorem-219.md`. -/
theorem sum_divisors_divisors {R : Type*} [CommSemiring R] (n : ℕ) (f B : ℕ → R) :
    ∑ h ∈ n.divisors, ∑ d ∈ h.divisors, f d * B (h / d)
      = ∑ k ∈ n.divisors, B k * ∑ d ∈ (n / k).divisors, f d := by
  rw [Finset.sum_sigma' (f := fun h d => f d * B (h / d))]
  have hR : ∑ k ∈ n.divisors, B k * ∑ d ∈ (n / k).divisors, f d
      = ∑ k ∈ n.divisors, ∑ d ∈ (n / k).divisors, B k * f d :=
    Finset.sum_congr rfl (fun k _ => Finset.mul_sum ..)
  rw [hR, Finset.sum_sigma' (f := fun k d => B k * f d)]
  refine Finset.sum_bij
    (fun x _ => (⟨x.fst / x.snd, x.snd⟩ : Sigma (fun _ => ℕ))) ?_ ?_ ?_ ?_
  · rintro ⟨h, d⟩ hx
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hx ⊢
    obtain ⟨⟨hdvdn, hn0⟩, ⟨ddvdh, _⟩⟩ := hx
    refine ⟨⟨?_, hn0⟩, ?_, ?_⟩
    · exact dvd_trans (Nat.div_dvd_of_dvd ddvdh) hdvdn
    · rw [Nat.dvd_div_iff_mul_dvd (dvd_trans (Nat.div_dvd_of_dvd ddvdh) hdvdn)]
      rw [Nat.div_mul_cancel ddvdh]
      exact hdvdn
    · intro hzero
      have hdiv : h / d ∣ n := dvd_trans (Nat.div_dvd_of_dvd ddvdh) hdvdn
      have hmn := Nat.div_mul_cancel hdiv
      rw [hzero, zero_mul] at hmn
      exact hn0 hmn.symm
  · rintro ⟨h₁, d₁⟩ hx₁ ⟨h₂, d₂⟩ hx₂ heq
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hx₁ hx₂
    obtain ⟨_, ⟨ddvdh₁, _⟩⟩ := hx₁
    obtain ⟨_, ⟨ddvdh₂, _⟩⟩ := hx₂
    simp only at heq
    injection heq with hquot hd
    subst hd
    have e1 : h₁ / d₁ * d₁ = h₁ := Nat.div_mul_cancel ddvdh₁
    have e2 : h₂ / d₁ * d₁ = h₂ := Nat.div_mul_cancel ddvdh₂
    rw [← e1, ← e2, hquot]
  · rintro ⟨k, d⟩ hy
    rw [Finset.mem_sigma] at hy
    obtain ⟨hk, hd⟩ := hy
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    rw [Nat.mem_divisors] at hk hd
    refine ⟨⟨k * d, d⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma]
      refine ⟨?_, ?_⟩
      · rw [Nat.mem_divisors]
        exact ⟨Nat.mul_dvd_of_dvd_div hk.1 hd.1, hk.2⟩
      · rw [Nat.mem_divisors]
        refine ⟨dvd_mul_left d k, ?_⟩
        have hkne : k ≠ 0 := by
          intro hkz
          exact hk.2 (Nat.zero_dvd.mp (hkz ▸ hk.1))
        exact Nat.mul_ne_zero hkne (ne_of_gt hdpos)
    · simp only
      rw [Nat.mul_div_cancel k hdpos]
  · rintro ⟨h, d⟩ _
    simp only
    exact mul_comm _ _

/-! ## The Möbius/totient divisor identity -/

/-- The classical identity `Σ_{d|n} μ(d)/d = φ(n)/n`, derived from
`sum_totient : Σ_{d|n} φ(d) = n` by Möbius inversion. -/
theorem sum_moebius_div_eq_totient (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, ((moebius d : ℤ) : ℚ) / d = ((Nat.totient n : ℕ) : ℚ) / n := by
  have h1 : ∀ m : ℕ, m > 0 → ∑ d ∈ m.divisors, ((Nat.totient d : ℕ) : ℚ) = (m : ℚ) := by
    intro m hm
    exact_mod_cast (sum_totient m)
  have h2 := (sum_eq_iff_sum_mul_moebius_eq (R := ℚ) (f := fun k => (Nat.totient k : ℚ))
    (g := fun k => (k : ℚ))).mp h1
  have hh := h2 n hn
  rw [sum_antidiagonal_eq_sum_divisors (f := fun a b => ((moebius a : ℤ) : ℚ) * (b : ℚ))
    (Nat.ne_zero_of_lt hn)] at hh
  rw [sum_divisors_inv_mul_eq (f := fun a b => ((moebius a : ℤ) : ℚ) * (b : ℚ))
    (Nat.ne_zero_of_lt hn)] at hh
  have h4 : (n : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hn
  have h5 : ∀ d ∈ n.divisors, ((moebius d : ℤ) : ℚ) * ((n / d : ℕ) : ℚ)
      = (n : ℚ) * (((moebius d : ℤ) : ℚ) / d) := by
    intro d hd
    have hdn : (d : ℚ) ≠ 0 := by
      have : (d : ℕ) ≠ 0 := Nat.ne_zero_of_lt (pos_of_mem_divisors hd)
      exact_mod_cast this
    have hdvd : d ∣ n := dvd_of_mem_divisors hd
    rw [Nat.cast_div hdvd hdn]
    field_simp
  rw [sum_congr rfl h5] at hh
  rw [← mul_sum] at hh
  rw [eq_div_iff h4, mul_comm]
  exact hh

/-! ## Möbius inversion for the fibre count -/

/-- **Möbius inversion (fibre form).**  If `B h = (1/h) · Σ_{j|h} j · P j` for
every `h > 0`, then `P h = Σ_{d|h} (μ(d)/d) · B (h/d)`.

This is the step that converts the stabilizer-weighted BEST quantity `B_h`
into the primitive orbit count `P_h` in Theorem 1 of
`docs/exact-fibre-count-theorem-219.md`. -/
theorem fibre_mobius_inversion {B P : ℕ → ℚ}
    (hB : ∀ h > 0, B h = (1 / h) * ∑ j ∈ h.divisors, (j : ℚ) * P j) :
    ∀ h > 0, P h = ∑ d ∈ h.divisors, ((moebius d : ℤ) : ℚ) / d * B (h / d) := by
  have key : ∀ m : ℕ, m > 0 → ∑ j ∈ m.divisors, (j : ℚ) * P j = (m : ℚ) * B m := by
    intro m hm
    have hmn : (m : ℚ) ≠ 0 := by
      have hm0 : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm
      exact_mod_cast hm0
    have := hB m hm
    rw [this]
    field_simp
  have h2 := (sum_eq_iff_sum_mul_moebius_eq (R := ℚ) (f := fun k => (k : ℚ) * P k)
    (g := fun k => (k : ℚ) * B k)).mp key
  intro h hh
  have hh2 := h2 h hh
  rw [sum_antidiagonal_eq_sum_divisors
    (f := fun a b => ((moebius a : ℤ) : ℚ) * ((b : ℚ) * B b))
    (Nat.ne_zero_of_lt hh)] at hh2
  rw [sum_divisors_inv_mul_eq
    (f := fun a b => ((moebius a : ℤ) : ℚ) * ((b : ℚ) * B b))
    (Nat.ne_zero_of_lt hh)] at hh2
  have h4 : (h : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hh
  have h5 : ∀ d ∈ h.divisors, ((moebius d : ℤ) : ℚ) * (((h / d : ℕ) : ℚ) * B (h / d))
      = (h : ℚ) * (((moebius d : ℤ) : ℚ) / d * B (h / d)) := by
    intro d hd
    have hdn : (d : ℚ) ≠ 0 := by
      have : (d : ℕ) ≠ 0 := Nat.ne_zero_of_lt (pos_of_mem_divisors hd)
      exact_mod_cast this
    have hdvd : d ∣ h := dvd_of_mem_divisors hd
    rw [Nat.cast_div hdvd hdn]
    field_simp
  rw [sum_congr rfl h5] at hh2
  rw [← mul_sum] at hh2
  exact (mul_left_cancel₀ h4 hh2).symm

/-! ## The totient/Burnside rearrangement -/

/-- **Totient rearrangement (fibre form).**  Under the same hypothesis as
`fibre_mobius_inversion`, the total orbit count satisfies

    Σ_{h|g} P h = Σ_{k|g} φ(g/k)/(g/k) · B k.

This is Theorem 2 of `docs/exact-fibre-count-theorem-219.md`: a positive
Burnside-style form with no Möbius inversion. -/
theorem fibre_totient {B P : ℕ → ℚ}
    (hB : ∀ h > 0, B h = (1 / h) * ∑ j ∈ h.divisors, (j : ℚ) * P j)
    (g : ℕ) (hg : 0 < g) :
    ∑ h ∈ g.divisors, P h
      = ∑ k ∈ g.divisors, ((Nat.totient (g / k) : ℕ) : ℚ) / ((g / k : ℕ) : ℚ) * B k := by
  have hP := fibre_mobius_inversion hB
  have hL : ∑ h ∈ g.divisors, P h
      = ∑ h ∈ g.divisors, ∑ d ∈ h.divisors, ((moebius d : ℤ) : ℚ) / d * B (h / d) := by
    apply sum_congr rfl
    intro h hh
    exact hP h (pos_of_mem_divisors hh)
  rw [hL]
  rw [sum_divisors_divisors g (fun d => ((moebius d : ℤ) : ℚ) / d) B]
  apply sum_congr rfl
  intro k hk
  have hgk : 0 < g / k :=
    Nat.div_pos (Nat.le_of_dvd hg (dvd_of_mem_divisors hk)) (pos_of_mem_divisors hk)
  rw [sum_moebius_div_eq_totient (g / k) hgk, mul_comm]

end AssemblyP1.FibreCount
