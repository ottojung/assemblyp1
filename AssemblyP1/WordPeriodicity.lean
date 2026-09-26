import Mathlib.Data.List.Basic
import Mathlib.Data.List.PeriodicityLemma

/-!
# Periods of finite words: a self-contained Fine–Wilf (gcd-period) theorem

This module fixes the vocabulary that the later `A^m B^m` work needs:

* a period of a *finite* word (a `List α`), in the index formulation;
* the bridge between that formulation and Mathlib's overlap formulation
  `List.HasPeriod`;
* the **Fine–Wilf theorem**: a word of length `≥ p + q - gcd p q` with
  periods `p` and `q` has period `gcd p q`.

The Fine–Wilf implication itself is taken from Mathlib's
`List.HasPeriod.gcd`, whose statement is exactly the classical theorem;
everything specific to this repository's modelling choices is proved here.

## Relationship to the textbook statement

The textbook form is: if `w` has periods `p, q` and `|w| ≥ p + q - gcd p q`
then `gcd p q` is a period of `w`, usually stated with `p, q > 0`. Two
Lean-friendly adjustments, both *equivalent* to the textbook statement
rather than weaker:

1. Periods are formulated by indices (`Period` below) instead of by prefix
   overlap. `Period.period_iff_hasPeriod` proves the two notions
   equivalent, and Mathlib proves the same equivalence for its own
   definition (`List.hasPeriod_iff_getElem?`), so this is a change of
   presentation, not of content.
2. No `p, q > 0` hypothesis is required in the main theorem. This is
   harmless, because `gcd 0 q = q` and the hypothesis then degenerates to
   what is already assumed; `Period.fineWilf_pos` records the textbook
   positive-period form, and `Period.fineWilf_length_lower` records the
   length consequence `p ≤ |w| ∧ q ≤ |w|` that the main theorem's proof
   and later `A^m B^m` work will need (note that this length consequence
   genuinely does need `p, q > 0`: for `q = 0` the hypothesis reduces to
   `0 ≤ |w|` and says nothing about `p`).
-/

namespace AssemblyP1

open List

variable {α : Type _}

/-- `Period w p`: the letter at index `i` equals the letter at index `i + p`
whenever both lie inside the word; i.e. `w` overlaps itself at offset `p`. -/
def Period (w : List α) (p : ℕ) : Prop :=
  ∀ (i : ℕ), i + p < w.length → w[i]? = w[i + p]?

@[simp] theorem period_zero (w : List α) : Period w 0 := by
  intro i _; rw [Nat.add_zero]

@[simp] theorem period_of_length_le (w : List α) (p : ℕ) (h : w.length ≤ p) : Period w p := by
  intro i hi; omega

/-- Every index of a word with period `p` is determined by its residue
modulo `p`: `w[i]? = w[i % p]?`. This elementary half of Fine–Wilf is the
form used later for `A^m B^m`-type words. -/
theorem Period.of_mod {w : List α} {p : ℕ} (per : Period w p) (hp : 0 < p) :
    ∀ i, i < w.length → w[i]? = w[i % p]? := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases hlt : i < p
    · rw [Nat.mod_eq_of_lt hlt]
    · have hle : p ≤ i := Nat.le_of_not_gt hlt
      have hsub : i - p + p = i := Nat.sub_add_cancel hle
      have hlen : i - p + p < w.length := hsub.symm ▸ hi
      have hstep : w[i]? = w[i - p]? := by
        have h := per (i - p) hlen
        rw [hsub] at h
        exact h.symm
      have hlt'' : i - p < i := Nat.sub_lt (by omega) hp
      have hlt' : i - p < w.length := hlt''.trans hi
      calc w[i]? = w[i - p]? := hstep
        _ = w[(i - p) % p]? := ih (i - p) hlt'' hlt'
        _ = w[i % p]? := by
          have hmod : (i - p) % p = i % p := by
            calc (i - p) % p = (i - p + p) % p := by rw [Nat.add_mod_right]
              _ = i % p := by rw [hsub]
          rw [hmod]

/-- The index formulation `Period` and Mathlib's overlap formulation
`List.HasPeriod` are equivalent, so results transfer verbatim in both
directions. -/
theorem Period.period_iff_hasPeriod {w : List α} {p : ℕ} :
    Period w p ↔ List.HasPeriod w p := by
  rw [List.hasPeriod_iff_getElem?]
  constructor
  · intro h i hi
    have hlen : i + p < w.length := by omega
    have h1 := h i hlen
    simpa only [List.getElem?_eq_getElem (by omega : i < w.length),
      List.getElem?_eq_getElem hlen] using h1
  · intro h i hi
    have h1 := h i (by omega : i < w.length - p)
    simpa only [List.getElem?_eq_getElem (by omega : i < w.length),
      List.getElem?_eq_getElem hi] using h1

/-- The index formulation implies Mathlib's overlap formulation. -/
theorem Period.to_hasPeriod {w : List α} {p : ℕ} (per : Period w p) : List.HasPeriod w p :=
  (Period.period_iff_hasPeriod (w := w) (p := p)).mp per

/-- Mathlib's overlap formulation implies the index formulation. -/
theorem Period.of_hasPeriod {w : List α} {p : ℕ} (per : List.HasPeriod w p) : Period w p :=
  (Period.period_iff_hasPeriod (w := w) (p := p)).mpr per

/-- A period of a word is a period of each of its factors. -/
theorem Period.infix {w : List α} {p : ℕ} (per : Period w p) {u : List α} (h : u <:+: w) :
    Period u p :=
  Period.of_hasPeriod (per.to_hasPeriod.infix h)

/-- **Fine–Wilf theorem**, in Mathlib's overlap formulation. -/
theorem hasPeriod_fineWilf {w : List α} {p q : ℕ}
    (per_p : List.HasPeriod w p) (per_q : List.HasPeriod w q)
    (len : p + q - p.gcd q ≤ w.length) : List.HasPeriod w (p.gcd q) :=
  per_p.gcd per_q len

/-- **Fine–Wilf theorem** in the local index formulation. -/
theorem Period.fineWilf {w : List α} {p q : ℕ} (per_p : Period w p) (per_q : Period w q)
    (len : p + q - p.gcd q ≤ w.length) : Period w (p.gcd q) :=
  Period.of_hasPeriod (hasPeriod_fineWilf per_p.to_hasPeriod per_q.to_hasPeriod len)

/-- The textbook positive-period form of Fine–Wilf. -/
theorem Period.fineWilf_pos {w : List α} {p q : ℕ} (_hp : 0 < p) (_hq : 0 < q)
    (per_p : Period w p) (per_q : Period w q)
    (len : p + q - p.gcd q ≤ w.length) : Period w (p.gcd q) :=
  per_p.fineWilf per_q len

/-- Under the Fine–Wilf length hypothesis and for positive periods, both
periods fit inside the word (used to discharge index side conditions later). -/
theorem Period.fineWilf_length_lower {w : List α} {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (len : p + q - p.gcd q ≤ w.length) : p ≤ w.length ∧ q ≤ w.length := by
  have hgq : p.gcd q ≤ q := Nat.gcd_le_right p hq
  have hsubq : 0 ≤ q - p.gcd q := by omega
  have h2 : p + (q - p.gcd q) ≤ w.length := by omega
  have hpw : p ≤ w.length := Nat.le_trans (Nat.le_add_right p _) h2
  have hgp : p.gcd q ≤ p := Nat.gcd_le_left q hp
  have hsubp : 0 ≤ p - p.gcd q := by omega
  have h4 : q + (p - p.gcd q) ≤ w.length := by omega
  exact ⟨hpw, by omega⟩

/-- Consequence of Fine–Wilf used later: under the length hypothesis, the
common period `gcd p q` divides each of `p` and `q`. -/
theorem Period.fineWilf_dvd {w : List α} {p q : ℕ} (_per_p : Period w p) (_per_q : Period w q)
    (_len : p + q - p.gcd q ≤ w.length) : Nat.gcd p q ∣ p ∧ Nat.gcd p q ∣ q :=
  ⟨Nat.gcd_dvd_left p q, Nat.gcd_dvd_right p q⟩

/-- Sanity check that the statements above are not vacuous: the word
`[1,2,1,2,1]` really does have periods `2` and `4`, the length hypothesis
`2 + 4 - gcd 2 4 = 4 ≤ 5` holds, and the resulting period is `gcd 2 4 = 2`. -/
theorem period_example : List.HasPeriod ([1, 2, 1, 2, 1] : List Nat) 2 := by
  show [1, 2, 1, 2, 1] <+: [1, 2] ++ [1, 2, 1, 2, 1]
  exact ⟨[2, 1], rfl⟩

theorem period_example_4 : List.HasPeriod ([1, 2, 1, 2, 1] : List Nat) 4 := by
  show [1, 2, 1, 2, 1] <+: [1, 2, 1, 2] ++ [1, 2, 1, 2, 1]
  exact ⟨[2, 1, 2, 1], rfl⟩

theorem period_example_gcd : List.HasPeriod ([1, 2, 1, 2, 1] : List Nat) (Nat.gcd 2 4) :=
  hasPeriod_fineWilf period_example period_example_4 (by decide)

theorem period_example_length :
    2 ≤ ([1, 2, 1, 2, 1] : List Nat).length ∧ 4 ≤ ([1, 2, 1, 2, 1] : List Nat).length :=
  Period.fineWilf_length_lower (by decide) (by decide) (by decide)

end AssemblyP1
