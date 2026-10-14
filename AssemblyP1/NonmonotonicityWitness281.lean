import AssemblyP1.SourceFaithfulIs
import AssemblyP1.FiniteReadRecovery

/-!
# Non-monotonicity of finite-sample exact-ML success (Antonina #281)

This module kernel-checks the small circular-genome witness requested by
Antonina #281: the probability that the *exact* maximum-likelihood rule over
a fixed two-genome candidate class returns the truth is **not monotone** in
the number of reads.

## Model (the project's actual genome / read / likelihood definitions)

* Alphabet `DNA = Fin 2` with `0 = A`, `1 = C`.
* Truth `S = AAC` (circular, length `3`) and competitor `D = AAAC`
  (circular, length `4`), both `SourceFaithfulIs.Genome`s.
* `readLaw G L` is the uniform-start oriented circular read law: a length-`L`
  read starts at a uniformly random genomic position and returns the cyclic
  window `G.window L t`.  This is the same law as
  `AssemblyP1.FiniteReadRecoveryGenome.circularReadPMF` (defined there), here
  restated locally to keep this module independent of that development.
* `tupleLikelihood` and `eventProb` are the exact iid product likelihood and
  its probability, from `AssemblyP1.FiniteReadRecovery`.

For `L = 2` the two read laws are
```
  p_S : AA ↦ 1/3,  AC ↦ 1/3,  CA ↦ 1/3,  CC ↦ 0
  p_D : AA ↦ 1/2,  AC ↦ 1/4,  CA ↦ 1/4,  CC ↦ 0
```
so they are distinct and `ρ(p_S, p_D) = (1 + √2)/√6 < 1`; the exponential
finite-read recovery bound of `AssemblyP1.FiniteReadRecovery` applies.

## Result

Writing `succ(n) = P_S(L_S(R_1..R_n) > L_D(R_1..R_n))` for the probability
that the truth *strictly* beats the competitor under the exact ML rule,
```
  succ(1) = 2/3,   succ(2) = 4/9,   succ(1) > succ(2),
```
so `succ` is not monotone in `n`, even though it tends to `1`.  There are no
ties for any `n` (the strict and non-strict events coincide), because
`L_D/L_S = 3^n / 2^(2n-a)` with `a = #AA` and the threshold
`n·log₂(4/3)` is never an integer.  This is the "success probability need not
increase monotonically in sample count" caveat of #281, made exact.
-/

namespace AssemblyP1.NonmonotonicityWitness281

open AssemblyP1.SourceFaithfulIs
open AssemblyP1.FiniteReadRecovery
open Finset BigOperators
open scoped Classical

set_option maxHeartbeats 4000000

/-- DNA alphabet, `0 = A`, `1 = C`. -/
abbrev DNA := Fin 2

/-- Oriented length-2 read words, as functions `Fin 2 → DNA`. -/
abbrev Word := Fin 2 → DNA

/-- The four length-2 words, coded as `Fin 4`:
`0 = AA`, `1 = AC`, `2 = CA`, `3 = CC`. -/
def enc4 : Fin 4 → Word
  | 0 => ![0, 0]
  | 1 => ![0, 1]
  | 2 => ![1, 0]
  | 3 => ![1, 1]

/-- The true circular genome `AAC`. -/
abbrev truth : Genome DNA where
  len := 3
  len_pos := by norm_num
  sym := ![0, 0, 1]

/-- The competitor circular genome `AAAC`. -/
abbrev competitor : Genome DNA where
  len := 4
  len_pos := by norm_num
  sym := ![0, 0, 0, 1]

/-- The uniform-start oriented circular read law of `G` at read length `L`:
every genomic start position is equally likely and the read returns the
cyclic window `G.window L t`. -/
noncomputable def readLaw (G : Genome DNA) (L : ℕ) : (Fin L → DNA) → ℝ :=
  fun w => ∑ t : Fin G.len, if G.window L t = w then 1 / (G.len : ℝ) else 0

/-- The event that the competitor `D = AAAC` ties or beats the truth
`S = AAC` in the exact iid product likelihood on `n` reads. -/
def errorEvent (n : ℕ) (t : Fin n → Word) : Prop :=
  tupleLikelihood (readLaw truth 2) n t ≤ tupleLikelihood (readLaw competitor 2) n t

/-- The event that the truth `S` *strictly* beats the competitor `D`. -/
def successEvent (n : ℕ) (t : Fin n → Word) : Prop :=
  tupleLikelihood (readLaw competitor 2) n t < tupleLikelihood (readLaw truth 2) n t

/-! ## Read-law values on the four words -/

theorem readLaw_truth_enc4 (k : Fin 4) :
    readLaw truth 2 (enc4 k) = ![1/3, 1/3, 1/3, 0] k := by
  have h3 : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  fin_cases k <;> · unfold readLaw truth enc4; rw [h3]; simp +decide; try norm_num

theorem readLaw_competitor_enc4 (k : Fin 4) :
    readLaw competitor 2 (enc4 k) = ![1/2, 1/4, 1/4, 0] k := by
  have h4 : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  fin_cases k <;> · unfold readLaw competitor enc4; rw [h4]; simp +decide; try norm_num

/-! ## Enumeration of the read-tuple spaces -/

/-- The 16 two-read tuples, encoded by a pair of word codes. -/
def enc2 : Fin 4 × Fin 4 → (Fin 2 → Word) := fun p => ![enc4 p.1, enc4 p.2]

/-- The single-read tuple space is the four constant tuples. -/
theorem univ_one : (Finset.univ : Finset (Fin 1 → Word)) =
    {fun _ => enc4 0, fun _ => enc4 1, fun _ => enc4 2, fun _ => enc4 3} := by
  decide

/-- The two-read tuple space is the image of the 16 word-code pairs. -/
theorem univ_two : (Finset.univ : Finset (Fin 2 → Word)) =
    (Finset.univ : Finset (Fin 4 × Fin 4)).image enc2 := by
  decide

theorem enc2_injective : Function.Injective enc2 := by
  decide

/-! ## Exact success / error probabilities -/

/-- One read: the truth strictly beats the competitor with probability
`2/3` (the observed word is `AC` or `CA`). -/
theorem succ_one :
    eventProb (readLaw truth 2) 1 (successEvent 1) = 2/3 := by
  unfold eventProb successEvent tupleLikelihood
  rw [univ_one]
  simp +decide [readLaw_truth_enc4, readLaw_competitor_enc4]
  norm_num

/-- Two reads: the truth strictly beats the competitor with probability
`4/9`. -/
theorem succ_two :
    eventProb (readLaw truth 2) 2 (successEvent 2) = 4/9 := by
  have h4 : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  unfold eventProb successEvent tupleLikelihood
  rw [univ_two, Finset.sum_image (by intro x _ y _ h; exact enc2_injective h)]
  rw [Fintype.sum_prod_type, h4]
  simp +decide [readLaw_truth_enc4, readLaw_competitor_enc4, enc2]
  norm_num

/-- One read: the competitor ties or beats the truth with probability
`1/3`. -/
theorem err_one :
    eventProb (readLaw truth 2) 1 (errorEvent 1) = 1/3 := by
  unfold eventProb errorEvent tupleLikelihood
  rw [univ_one]
  simp +decide [readLaw_truth_enc4, readLaw_competitor_enc4]
  norm_num

/-- Two reads: the competitor ties or beats the truth with probability
`5/9`. -/
theorem err_two :
    eventProb (readLaw truth 2) 2 (errorEvent 2) = 5/9 := by
  have h4 : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  unfold eventProb errorEvent tupleLikelihood
  rw [univ_two, Finset.sum_image (by intro x _ y _ h; exact enc2_injective h)]
  rw [Fintype.sum_prod_type, h4]
  simp +decide [readLaw_truth_enc4, readLaw_competitor_enc4, enc2]
  norm_num

/-- **Non-monotonicity.** The exact finite-sample ML success probability for
the two-genome class `{AAC, AAAC}` under oriented length-2 reads is strictly
smaller at `n = 2` than at `n = 1`. -/
theorem success_not_monotone :
    eventProb (readLaw truth 2) 1 (successEvent 1)
      > eventProb (readLaw truth 2) 2 (successEvent 2) := by
  rw [succ_one, succ_two]
  norm_num

end AssemblyP1.NonmonotonicityWitness281
