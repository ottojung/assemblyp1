import AssemblyP1.Issue48FreeLengthCounterexample

/-!
# Issue #48: kernel check of the headline witness `AABBC -> AABC`

This file kernel-checks the issue-#48 headline free-length counterexample
(`S = AABBC`, `D = AABC`, read length `L = 3`, observed reads `{AAB, BCA}` at
realized starts `0, 3`), the member `L = 3` of the length-shrinkage family of
`docs/issue48-length-shrinkage-family.md`.

Conventions are exactly those of `AssemblyP1/Issue48FreeLengthCounterexample.lean`:
single-strand oriented reads, free candidate length `N(D) = D.length`, exact
Medvedev–Brudno read-count multinomial.

The kernel-checked facts are:

* `Covers5 truth5 3`: the realized reads at starts `0, 3` cover `AABBC`;
* `NoTripleRepeat truth5`: the truth has no Bresler triple repeat, so the
  triple-repeat clause of `I_s` is vacuous (there is no interleaved pair
  either; that finite check is left to the verification script, as in the
  companion module);
* `Strong truth5 3` and `Strong competitor4 3`: no `(L-1) = 2`-mer occurs twice
  in either word (the `STRONG` / `P1` intrinsic condition);
* `IsPrimitive truth5` and `IsPrimitive competitor4`;
* `likelihood5 truth5 < likelihood5 competitor4`, with exact rationals
  `1/25 < 1/16`, i.e. free-length ratio `25/16`.
-/

namespace AssemblyP1.Issue48

open Base

/-- The true circular genome `S = AABBC` (length `5`). -/
def truth5 : List Base := [A, A, B, B, C]

/-- The shorter competitor `D = AABC` (length `4`). -/
def competitor4 : List Base := [A, A, B, C]

/-- Exact Medvedev–Brudno read-count likelihood for the observed multiset
`{AAB, BCA}`, with candidate-intrinsic length `N(D) = D.length`. -/
def likelihood5 (D : List Base) : ℚ :=
  (occ D [A, A, B] : ℚ) / D.length * ((occ D [B, C, A] : ℚ) / D.length)

/-- Realized read start positions on `truth5`. -/
def readStarts5 : List Nat := [0, 3]

/-- The realized reads cover `S`. -/
def Covers5 (S : List Base) (L : Nat) : Prop :=
  ∀ p : Fin S.length, ∃ i : Fin readStarts5.length, ∃ d : Fin L,
    p.val = (readStarts5[i.val] + d.val) % S.length

theorem occ_truth5_AAB : occ truth5 [A, A, B] = 1 := by decide

theorem occ_truth5_BCA : occ truth5 [B, C, A] = 1 := by decide

theorem occ_competitor4_AAB : occ competitor4 [A, A, B] = 1 := by decide

theorem occ_competitor4_BCA : occ competitor4 [B, C, A] = 1 := by decide

/-- Exact likelihood of the observed reads under the truth. -/
theorem likelihood5_truth : likelihood5 truth5 = 1 / 25 := by
  unfold likelihood5
  rw [occ_truth5_AAB, occ_truth5_BCA]
  norm_num [truth5]

/-- Exact likelihood of the observed reads under the shorter competitor. -/
theorem likelihood5_competitor : likelihood5 competitor4 = 1 / 16 := by
  unfold likelihood5
  rw [occ_competitor4_AAB, occ_competitor4_BCA]
  norm_num [competitor4]

/-- The free-length exact likelihood strictly prefers the shorter candidate. -/
theorem competitor4_strictly_more_likely :
    likelihood5 truth5 < likelihood5 competitor4 := by
  rw [likelihood5_truth, likelihood5_competitor]
  norm_num

theorem truth5_primitive : IsPrimitive truth5 := by
  unfold IsPrimitive IsPower
  decide

theorem competitor4_primitive : IsPrimitive competitor4 := by
  unfold IsPrimitive IsPower
  decide

theorem truth5_strong : Strong truth5 3 := by unfold Strong; decide

theorem competitor4_strong : Strong competitor4 3 := by unfold Strong; decide

theorem truth5_covers : Covers5 truth5 3 := by unfold Covers5 readStarts5; decide

theorem truth5_no_triple : NoTripleRepeat truth5 := by
  unfold NoTripleRepeat IsTripleRepeat prev follow win
  decide

/--
Kernel-checked finite refutation of the issue-#48 free-length repaired theorem on
the issue's headline witness: the truth is primitive and `STRONG`, the
competitor is primitive and `STRONG`, and the competitor is strictly more likely
under the exact free-length Medvedev–Brudno multinomial (ratio `25/16`).
-/
theorem issue48_aabbc_aabc_counterexample :
    Covers5 truth5 3 ∧ NoTripleRepeat truth5 ∧
      Strong truth5 3 ∧ IsPrimitive truth5 ∧
      Strong competitor4 3 ∧ IsPrimitive competitor4 ∧
      likelihood5 truth5 < likelihood5 competitor4 :=
  ⟨truth5_covers, truth5_no_triple, truth5_strong, truth5_primitive,
    competitor4_strong, competitor4_primitive, competitor4_strictly_more_likely⟩

end AssemblyP1.Issue48
