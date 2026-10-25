import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-!
# Fixed-`x` exact-ML: same-length maximality does not transfer to variable length (#255)

Frozen axis: **same vs variable genome length**, exact multinomial objective,
fixed observation `x` (regime (A)).

At a fixed `x` the multinomial coefficient cancels, so the exact-ML comparison
of a candidate count vector `c` with total `G` against the truth depends only on
the normalized spectrum `c i / G` via `∏ i, (c i / G) ^ (x i)`.  In particular
nothing in the comparison formula forces the totals to agree.

## Falsifiable lemma (proved here)

The conjecture *"if the truth uniquely maximizes among same-total spectra at a
fixed `x`, then it maximizes among all totals at that `x`"* is **false**.
Witness on two read types with `x = (2, 1)`:

* truth `A = (3, 1)`, total `G = 4`, is the unique maximizer of the
  spectrum factor among all count vectors of total `4`;
* the different-total candidate `B = (2, 1)`, total `G' = 3`, strictly beats it
  at the same `x`: `4/27 > 9/64`.

Epistemic class: kernel-checked refutation of the transfer conjecture on the
exact-multinomial fixed-`x` slice.  It does not classify regime (B), does not
touch the §6.1 surrogate or §6.2 flows, and closes no child issue.
-/

set_option autoImplicit false

namespace AssemblyP1.FixedXVariableLengthSeparation

/-- Exact-multinomial fixed-`x` spectrum factor on two read types.

For a candidate count vector `c` with total `G > 0` and fixed observation
`x`, this is `∏ i, (c i / G) ^ (x i)` over `ℚ`: the candidate-dependent part
of the exact multinomial likelihood once the `x`-dependent multinomial
coefficient (common to all candidates) is dropped. -/
noncomputable def specFactor255 (c : Fin 2 → ℕ) (G : ℕ) (x : Fin 2 → ℕ) : ℚ :=
  ((c 0 : ℚ) / (G : ℚ)) ^ (x 0) * (((c 1 : ℚ) / (G : ℚ)) ^ (x 1))

/-- Truth spectrum: `A = (3, 1)` of total `4`. -/
def truthA255 : Fin 2 → ℕ := ![3, 1]

/-- Variable-length competitor: `B = (2, 1)` of total `3`. -/
def compB255 : Fin 2 → ℕ := ![2, 1]

/-- Fixed observation: `x = (2, 1)`. -/
def obsX255 : Fin 2 → ℕ := ![2, 1]

theorem truthA255_total : truthA255 0 + truthA255 1 = 4 := by decide

theorem compB255_total : compB255 0 + compB255 1 = 3 := by decide

/-- The variable-length candidate strictly beats the truth at the fixed `x`:
`specFactor B 3 x = 4 / 27 > 9 / 64 = specFactor A 4 x`. -/
theorem varlen_beats_samelen255 :
    specFactor255 truthA255 4 obsX255 < specFactor255 compB255 3 obsX255 := by
  unfold specFactor255 truthA255 compB255 obsX255
  norm_num

/-- The truth is the unique maximizer among same-total (`= 4`) spectra at `x`. -/
theorem samelen_unique_max255 (C : Fin 2 → ℕ) (hC : C 0 + C 1 = 4) :
    specFactor255 C 4 obsX255 ≤ specFactor255 truthA255 4 obsX255 ∧
    (specFactor255 C 4 obsX255 = specFactor255 truthA255 4 obsX255 →
      C 0 = 3 ∧ C 1 = 1) := by
  have h0 : C 0 ≤ 4 := by omega
  interval_cases h : C 0
  · have h1 : C 1 = 4 := by omega
    unfold specFactor255 truthA255 obsX255
    simp only [h, h1, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;> norm_num
  · have h1 : C 1 = 3 := by omega
    unfold specFactor255 truthA255 obsX255
    simp only [h, h1, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;> norm_num
  · have h1 : C 1 = 2 := by omega
    unfold specFactor255 truthA255 obsX255
    simp only [h, h1, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;> norm_num
  · have h1 : C 1 = 1 := by omega
    unfold specFactor255 truthA255 obsX255
    simp only [h, h1, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;> norm_num
  · have h1 : C 1 = 0 := by omega
    unfold specFactor255 truthA255 obsX255
    simp only [h, h1, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;> norm_num

/-- Main separation: same-total unique maximality at fixed `x` coexists with a
strict variable-length beater.  Same-length rigidity does not transfer. -/
theorem samelen_does_not_imply_varlen255 :
    (∀ C : Fin 2 → ℕ, C 0 + C 1 = 4 →
      specFactor255 C 4 obsX255 ≤ specFactor255 truthA255 4 obsX255) ∧
    specFactor255 truthA255 4 obsX255 < specFactor255 compB255 3 obsX255 := by
  exact ⟨fun C hC => (samelen_unique_max255 C hC).1, varlen_beats_samelen255⟩

end AssemblyP1.FixedXVariableLengthSeparation
