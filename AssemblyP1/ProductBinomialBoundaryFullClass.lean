import AssemblyP1.ProductBinomialRigidityNecessity
import AssemblyP1.CoveredBinomialWeightsIff
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Full-class sample-uniform maximality of the MB09 §6.1 product-binomial
surrogate, boundary coordinates included (board issue #259, axis B)

Medvedev–Brudno 2009 §6.1 score a candidate read-type spectrum `B : E → ℕ` by a
**product of marginal binomials** with a fixed external genome length `N`.  For a
fixed finite read-type universe `E` and an observed count vector `x` with
`n = ∑ x`, the candidate-dependent integer numerator is

```
effectiveProduct N B x = ∏_e (effectiveWeight N B e) ^ (x e),
effectiveWeight N B e = B e * ∏_{j ≠ e} (N - B j).
```

This is **not** the exact joint multinomial read likelihood of `#256`: the
`(N - B j) ^ (n - x j)` factors of the unobserved coordinates (including
zero-count coordinates, and the boundary values `d(w) = 0` and `d(w) = N`) are
exactly what separates the surrogate from the exact objective.  It is also not
the §6.2 bidirected-flow objective (`#260`/`#261`).

## What this file classifies

Earlier `#259` work classified **one competitor at a time**:

* `AssemblyP1.CoveredBinomialWeightsIff.covered_ambient_effectiveProduct_le_iff`
  says the truth `A` dominates a fixed competitor `B` on **every** covered sample
  supported on `supp A` iff either `B` has a zero effective weight on `supp A`
  or `B`'s effective weights are pointwise dominated by `A`'s;
* `AssemblyP1.ProductBinomialRigidityNecessity.robust_iff_unique` turns this
  into the **necessity of rigidity** over any class `F` of *positive* count
  vectors of total `N` containing `A`: `A` is a sample-uniform maximizer over `F`
  iff `F = {A}`;
* `AssemblyP1.FixedXProductBinomialMaximality` handles axis A (a single fixed
  `x`).

The genuinely open axis-B question is the classification of the truth `A` itself
over the **full same-total candidate class** — *all* `B` with `∑ B = N`,
including boundary coordinates `B e = 0` and `B e = N` and new support.  This
file proves that classification.

> **`fullClass_sampleUniformMax_iff`.**  Let `A : E → ℕ` with `∑ A = N`.  Then
> `A` is a sample-uniform maximizer over the full class `{B | ∑ B = N}` on every
> covered sample supported on `supp A` **iff** `A` puts all mass on a single
> class (`∃ e, A e = N`) **or** `A` is `{0,1}` valued (`∀ e, A e ≤ 1`, which with
> `∑ A = N` means `A` is the indicator of an `N`-element support).

So over the *full* candidate class the only maximal truths are the degenerate
ones: a mass-on-one-class spectrum, or a `{0,1}`-valued spectrum.  The proof
isolates two mechanisms:

* **Boundary candidates never beat the truth.**  A candidate with `B e = 0` on
  `supp A`, or with `B e = N` somewhere, has zero effective weight on `supp A`
  and is therefore dominated.  This is the precise sense in which the boundary
  probabilities `0`/`1` and the zero-count coordinates are harmless.
* **A one-unit transfer beats the truth.**  If `A` has two supported coordinates
  `i ≠ j` and `A j ≥ 2`, the candidate `B = A - e_j + e_i` stays positive on
  `supp A` and strictly raises the effective weight at `i`
  (`transfer_effectiveWeight_lt`), so the covered-sample criterion produces a
  beating sample.

## Scope

* Objective: MB09 §6.1 fixed-external-`N` product-binomial **surrogate**.
* Candidate length: same-length, fixed finite read-type universe `E`.
* Normalization `N`: fixed external; omitted candidate-constant factors
  (`∏_e choose(n, x_e)` and `N ^ (-n · card E)`) cancel in every comparison.
* Support: full same-total candidate class, boundary and new-support included.
* Sample size `n = ∑ x`: free, bounded below coordinatewise by the truth
  spectrum `A ≤ x` (covered samples).
* Still open: the same classification restricted to *realizable* (balanced)
  spectra rather than all count vectors; variable genome length; §6.2
  bidirected flows (`#260`/`#261`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset BigOperators

namespace AssemblyP1.ProductBinomialBoundaryFullClass

open AssemblyP1.FixedNBinomialEffectiveWeights

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The **full same-total candidate class** over the ambient read-type universe:
every count vector `B` whose coordinates sum to the external length `N`
(boundary coordinates and new support included). -/
def FullCandidateClass (N : ℕ) : Set (E → ℕ) := {B | ∑ e, B e = N}

/-- **Sample-uniform maximality** of `A` over a candidate class `F`: on every
covered sample `x` (dominating the truth spectrum `A` coordinatewise and
supported on `supp A`), every candidate `B ∈ F` scores at most as high as `A`. -/
def SampleUniformMax (N : ℕ) (A : E → ℕ) (F : Set (E → ℕ)) : Prop :=
  ∀ x : E → ℕ, (∀ e, A e ≤ x e) → (∀ e, A e = 0 → x e = 0) →
    ∀ B ∈ F, effectiveProduct N B x ≤ effectiveProduct N A x

/-! ## Elementary arithmetic helpers -/

/-- Product strict monotonicity for `ℕ` (Nat lacks the `MulLeftStrictMono`
instance that `Finset.prod_lt_prod` needs): if `f ≤ g` pointwise on `s`, `f` is
positive on `s`, and `f j < g j` at some `j ∈ s`, then `∏ f < ∏ g`. -/
theorem prod_lt_prod_nat {ι : Type*} [DecidableEq ι] {s : Finset ι} {f g : ι → ℕ}
    (hfpos : ∀ i ∈ s, 0 < f i) (hle : ∀ i ∈ s, f i ≤ g i)
    {j : ι} (hj : j ∈ s) (hlt : f j < g j) : ∏ i ∈ s, f i < ∏ i ∈ s, g i := by
  have hPf1 : 1 ≤ ∏ i ∈ s.erase j, f i :=
    Finset.one_le_prod (fun i hi => hfpos i (Finset.mem_of_mem_erase hi))
  have hPfpos : 0 < ∏ i ∈ s.erase j, f i := lt_of_lt_of_le Nat.zero_lt_one hPf1
  have hPle : ∏ i ∈ s.erase j, f i ≤ ∏ i ∈ s.erase j, g i :=
    Finset.prod_le_prod (fun i hi => hle i (Finset.mem_of_mem_erase hi))
  rw [← Finset.mul_prod_erase s f hj, ← Finset.mul_prod_erase s g hj]
  exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hlt hPfpos) (Nat.mul_le_mul_left _ hPle)

/-- A product of factors each `≥ 1` over a finite set of `ℕ` is positive. -/
theorem prod_pos_of_one_le {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → ℕ}
    (h : ∀ i ∈ s, 1 ≤ f i) : 0 < ∏ i ∈ s, f i :=
  lt_of_lt_of_le Nat.zero_lt_one (Finset.one_le_prod h)

/-- The effective weight of `v` at a positive coordinate is positive, provided
every coordinate of `v` is strictly below `N`. -/
theorem effectiveWeight_pos_of (N : ℕ) (v : E → ℕ) (i : E)
    (hi : 0 < v i) (hN : ∀ l, v l < N) : 0 < effectiveWeight N v i := by
  rw [AssemblyP1.ProductBinomialRigidityNecessity.effectiveWeight_eq_erase]
  exact Nat.mul_pos hi (prod_pos_of_one_le (fun l _ => Nat.sub_pos_of_lt (hN l)))

/-! ## The one-unit transfer strictly raises the effective weight at the target -/

/-- **Transfer lemma.**  If `A` has positive mass at `i`, at least two units at a
distinct class `j`, and every coordinate strictly below `N`, then replacing one
unit of mass at `j` by one unit at `i` strictly increases the effective weight at
`i`.  This is the engine that turns a "non-degenerate" truth into a beaten one. -/
theorem transfer_effectiveWeight_lt (N : ℕ) (A : E → ℕ) (i j : E) (hij : i ≠ j)
    (hAi : 0 < A i) (hAj : 2 ≤ A j) (hN : ∀ l, A l < N) :
    effectiveWeight N A i
      < effectiveWeight N (Function.update (Function.update A j (A j - 1)) i (A i + 1)) i := by
  set B : E → ℕ := Function.update (Function.update A j (A j - 1)) i (A i + 1) with hB
  have hBi : B i = A i + 1 := by rw [hB, Function.update_self]
  have hBj : B j = A j - 1 := by
    rw [hB, Function.update_of_ne (Ne.symm hij), Function.update_self]
  have hBl : ∀ l, l ≠ i → l ≠ j → B l = A l := by
    intro l hli hlj
    rw [hB, Function.update_of_ne hli, Function.update_of_ne hlj]
  have hBl_le : ∀ l, l ≠ i → B l ≤ A l := by
    intro l hli
    by_cases hlj : l = j
    · rw [hlj, hBj]; exact Nat.sub_le _ _
    · rw [hBl l hli hlj]
  rw [AssemblyP1.ProductBinomialRigidityNecessity.effectiveWeight_eq_erase,
    AssemblyP1.ProductBinomialRigidityNecessity.effectiveWeight_eq_erase, hBi]
  have hPle : ∀ l ∈ Finset.univ.erase i, (N - A l) ≤ (N - B l) := by
    intro l hl
    exact Nat.sub_le_sub_left (hBl_le l (Finset.mem_erase.mp hl).1) N
  have hjmem : j ∈ Finset.univ.erase i :=
    Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
  have hPjlt : (N - A j) < (N - B j) := by
    have h1 := hN j
    rw [hBj]
    omega
  have hPlt : (∏ l ∈ Finset.univ.erase i, (N - A l))
      < (∏ l ∈ Finset.univ.erase i, (N - B l)) :=
    prod_lt_prod_nat (fun l _ => Nat.sub_pos_of_lt (hN l)) hPle hjmem hPjlt
  have hPApos : 0 < ∏ l ∈ Finset.univ.erase i, (N - A l) :=
    prod_pos_of_one_le (fun l _ => Nat.sub_pos_of_lt (hN l))
  calc A i * (∏ l ∈ Finset.univ.erase i, (N - A l))
      < (A i + 1) * (∏ l ∈ Finset.univ.erase i, (N - A l)) :=
        Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) hPApos
    _ ≤ (A i + 1) * (∏ l ∈ Finset.univ.erase i, (N - B l)) :=
        Nat.mul_le_mul_left _ (le_of_lt hPlt)

/-- **Singleton transfer lemma.**  If `A` is supported on the single class `j`
with `2 ≤ A j < N`, then moving all mass to `j` (the candidate `N · δ_j`) strictly
increases the effective weight at `j`. -/
theorem singleton_transfer_effectiveWeight_lt (N : ℕ) (A : E → ℕ) (j : E)
    (hAj2 : 2 ≤ A j) (hAjN : A j < N) (hsupp : ∀ l, l ≠ j → A l = 0) :
    effectiveWeight N A j < effectiveWeight N (fun l => if l = j then N else 0) j := by
  set B : E → ℕ := fun l => if l = j then N else 0 with hB
  have hBj : B j = N := by rw [hB]; simp
  have hP : (∏ l ∈ Finset.univ.erase j, (N - A l))
      = (∏ l ∈ Finset.univ.erase j, (N - B l)) := by
    apply Finset.prod_congr rfl
    intro l hl
    have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
    have hBl : B l = 0 := by rw [hB]; simp [hlj]
    rw [hsupp l hlj, hBl]
  have hPBpos : 0 < ∏ l ∈ Finset.univ.erase j, (N - B l) :=
    prod_pos_of_one_le (fun l hl => by
      have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
      have hBl : B l = 0 := by rw [hB]; simp [hlj]
      rw [hBl, Nat.sub_zero]
      omega)
  rw [AssemblyP1.ProductBinomialRigidityNecessity.effectiveWeight_eq_erase,
    AssemblyP1.ProductBinomialRigidityNecessity.effectiveWeight_eq_erase, hBj, hP]
  exact Nat.mul_lt_mul_of_pos_right hAjN hPBpos

/-! ## Boundary candidates and the `{0,1}` case -/

/-- If `A` is `{0,1}`-valued with `∑ A = N` and `B` is any same-total vector whose
effective weights are positive on `supp A`, then `B = A`.  This is the engine of
the sufficiency direction in the `{0,1}` case. -/
theorem eq_of_effectiveWeight_pos_of_zero_one (N : ℕ) (A B : E → ℕ)
    (hAtot : ∑ e, A e = N) (hA01 : ∀ e, A e ≤ 1) (hBtot : ∑ e, B e = N)
    (hpos : ∀ k, 0 < A k → 0 < effectiveWeight N B k) : B = A := by
  classical
  set S : Finset E := Finset.univ.filter (fun l => 0 < A l) with hS
  have hA_S : ∀ l ∈ S, A l = 1 := by
    intro l hl
    have h1 : 0 < A l := (Finset.mem_filter.mp hl).2
    have h2 : A l ≤ 1 := hA01 l
    omega
  have hA_notS : ∀ l, l ∉ S → A l = 0 := by
    intro l hl
    have h1 : ¬ 0 < A l := fun h => hl (by rw [hS]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, h⟩)
    omega
  have hcardS : S.card = N := by
    have hcardA : S.card = ∑ l ∈ S, A l := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_congr rfl (fun l hl => (hA_S l hl).symm)
    have hsumA : (∑ l, A l) = ∑ l ∈ S, A l := by
      have h1 : (∑ l, A l) = ∑ l, (if l ∈ S then A l else 0) := by
        apply Finset.sum_congr rfl
        intro l _
        by_cases hl : l ∈ S
        · rw [ite_eq_left hl]
        · rw [ite_eq_right hl, hA_notS l hl]
      have h2 : (∑ l, (if l ∈ S then A l else 0)) = ∑ l ∈ S, A l := by
        rw [← Finset.sum_filter]
        have hfil : Finset.univ.filter (fun l => l ∈ S) = S := by ext l; simp
        rw [hfil]
      rw [h1, h2]
    rw [hcardA, ← hsumA]; exact hAtot
  have hBpos : ∀ l ∈ S, 1 ≤ B l := by
    intro l hl
    have hAl : 0 < A l := (Finset.mem_filter.mp hl).2
    have hq := hpos l hAl
    rw [AssemblyP1.ProductBinomialRigidityNecessity.effectiveWeight_eq_erase] at hq
    rcases Nat.eq_zero_or_pos (B l) with h0 | h0
    · rw [h0, zero_mul] at hq; exact absurd hq (Nat.lt_irrefl 0)
    · exact h0
  have hsumS : ∑ l ∈ S, B l = N := by
    apply le_antisymm
    · calc ∑ l ∈ S, B l ≤ ∑ l, B l :=
            Finset.sum_le_sum_of_subset_of_nonneg (fun l _ => Finset.mem_univ l)
              (fun l _ _ => Nat.zero_le _)
        _ = N := hBtot
    · calc N = S.card := hcardS.symm
        _ = ∑ _l ∈ S, (1 : ℕ) := Finset.card_eq_sum_ones S
        _ ≤ ∑ l ∈ S, B l := Finset.sum_le_sum hBpos
  have hB_S : ∀ l ∈ S, B l = 1 := by
    have hsum1 : (∑ l ∈ S, (1 : ℕ)) = ∑ l ∈ S, B l := by
      rw [← Finset.card_eq_sum_ones]
      exact hcardS.trans hsumS.symm
    intro l hl
    exact ((Finset.sum_eq_sum_iff_of_le (s := S) (f := fun _ => (1 : ℕ)) (g := B)
      (fun l hl => hBpos l hl)).mp hsum1 l hl).symm
  have hB_notS : ∀ l, l ∉ S → B l = 0 := by
    have hle : ∀ l ∈ (Finset.univ : Finset E), (if l ∈ S then B l else 0) ≤ B l := by
      intro l _
      by_cases hl : l ∈ S
      · rw [ite_eq_left hl]
      · rw [ite_eq_right hl]; exact Nat.zero_le _
    have hsum : (∑ l, (if l ∈ S then B l else 0)) = ∑ l, B l := by
      have h1 : (∑ l, (if l ∈ S then B l else 0)) = ∑ l ∈ S, B l := by
        rw [← Finset.sum_filter]
        have hfil : Finset.univ.filter (fun l => l ∈ S) = S := by ext l; simp
        rw [hfil]
      rw [h1, hsumS, hBtot]
    have hpoint := (Finset.sum_eq_sum_iff_of_le (s := (Finset.univ : Finset E))
      (f := fun l => if l ∈ S then B l else 0) (g := B) hle).mp hsum
    intro l hl
    have hh := hpoint l (Finset.mem_univ l)
    rw [ite_eq_right hl] at hh
    exact hh.symm
  funext l
  by_cases hl : l ∈ S
  · rw [hB_S l hl, hA_S l hl]
  · rw [hB_notS l hl, hA_notS l hl]

/-! ## The classification -/

/-- **Full-class sample-uniform maximality (axis B, boundary included).**  For a
truth `A` with `∑ A = N`, `A` is a sample-uniform maximizer over the full
same-total candidate class on every covered sample supported on `supp A` iff
`A` is concentrated on a single class (`∃ e, A e = N`) or is `{0,1}`-valued
(`∀ e, A e ≤ 1`). -/
theorem fullClass_sampleUniformMax_iff (N : ℕ) (A : E → ℕ) (hAtot : ∑ e, A e = N) :
    SampleUniformMax N A (FullCandidateClass N) ↔
      (∃ e, A e = N) ∨ (∀ e, A e ≤ 1) := by
  constructor
  · -- necessity: a non-degenerate truth is beaten
    intro hmax
    by_contra h
    have hne : ∀ e, A e ≠ N := by
      intro e he; exact h (Or.inl ⟨e, he⟩)
    have hj2 : ∃ e, 2 ≤ A e := by
      by_contra hc
      exact h (Or.inr (fun e => by have := Nat.lt_of_not_le (fun hge => hc ⟨e, hge⟩); omega))
    obtain ⟨j, hj⟩ := hj2
    have hN : ∀ l, A l < N := by
      intro l
      have hle : A l ≤ N := by
        calc A l ≤ ∑ e, A e :=
              Finset.single_le_sum (fun e _ => Nat.zero_le _) (Finset.mem_univ l)
          _ = N := hAtot
      exact lt_of_le_of_ne hle (hne l)
    have hqA : ∀ i, 0 < A i → 0 < effectiveWeight N A i :=
      fun i hi => effectiveWeight_pos_of N A i hi hN
    by_cases hcase : ∃ i, i ≠ j ∧ 0 < A i
    · -- transfer one unit from j to a distinct supported i
      obtain ⟨i, hij, hAi⟩ := hcase
      set B : E → ℕ := Function.update (Function.update A j (A j - 1)) i (A i + 1) with hB
      have hBi : B i = A i + 1 := by rw [hB, Function.update_self]
      have hBj : B j = A j - 1 := by
        rw [hB, Function.update_of_ne (Ne.symm hij), Function.update_self]
      have hBrest : ∀ l, l ≠ i → l ≠ j → B l = A l := by
        intro l hli hlj; rw [hB, Function.update_of_ne hli, Function.update_of_ne hlj]
      have hjmem : j ∈ Finset.univ.erase i :=
        Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
      have hBtot : ∑ e, B e = N := by
        have hsplitB : ∑ e, B e
            = (∑ e ∈ (Finset.univ.erase i).erase j, B e) + B j + B i := by
          rw [← Finset.sum_erase_add Finset.univ B (Finset.mem_univ i),
            ← Finset.sum_erase_add (Finset.univ.erase i) B hjmem]
        have hsplitA : ∑ e, A e
            = (∑ e ∈ (Finset.univ.erase i).erase j, A e) + A j + A i := by
          rw [← Finset.sum_erase_add Finset.univ A (Finset.mem_univ i),
            ← Finset.sum_erase_add (Finset.univ.erase i) A hjmem]
        rw [hsplitA] at hAtot
        rw [hsplitB]
        have hrest : (∑ e ∈ (Finset.univ.erase i).erase j, B e)
            = (∑ e ∈ (Finset.univ.erase i).erase j, A e) :=
          Finset.sum_congr rfl (fun e he =>
            hBrest e (Finset.mem_erase.mp (Finset.mem_of_mem_erase he)).1
              (Finset.mem_erase.mp he).1)
        rw [hrest, hBj, hBi]
        omega
      have hBmem : B ∈ FullCandidateClass N := hBtot
      have hlt_i : effectiveWeight N A i < effectiveWeight N B i :=
        transfer_effectiveWeight_lt N A i j hij hAi hj hN
      have hpair : A i + A j ≤ N := by
        calc A i + A j = ∑ e ∈ ({i, j} : Finset E), A e := by
              rw [Finset.sum_pair hij]
          _ ≤ ∑ e, A e := Finset.sum_le_sum_of_subset_of_nonneg
              (fun e _ => Finset.mem_univ e) (fun e _ _ => Nat.zero_le _)
          _ = N := hAtot
      have hBlt : ∀ l, B l < N := by
        intro l
        by_cases hli : l = i
        · rw [hli, hBi]; omega
        · by_cases hlj : l = j
          · rw [hlj, hBj]; omega
          · rw [hBrest l hli hlj]; exact hN l
      have hBpos : ∀ l, 0 < A l → 0 < B l := by
        intro l hl
        by_cases hli : l = i
        · rw [hli, hBi]; omega
        · by_cases hlj : l = j
          · rw [hlj, hBj]; omega
          · rw [hBrest l hli hlj]; exact hl
      have hnozero : ¬ (∃ k, 0 < A k ∧ effectiveWeight N B k = 0) := by
        rintro ⟨k, hk, hk0⟩
        exact absurd hk0 (ne_of_gt (effectiveWeight_pos_of N B k (hBpos k hk) hBlt))
      have hnotpoint : ¬ (∀ k, 0 < A k → effectiveWeight N B k ≤ effectiveWeight N A k) :=
        fun hp => absurd (hp i hAi) (not_le.mpr hlt_i)
      have hiff := AssemblyP1.CoveredBinomialWeightsIff.covered_ambient_effectiveProduct_le_iff
        N A B hqA
      have hLHS : ∀ x, (∀ e, A e ≤ x e) → (∀ e, A e = 0 → x e = 0) →
          effectiveProduct N B x ≤ effectiveProduct N A x :=
        fun x hx hx0 => hmax x hx hx0 B hBmem
      exact absurd (hiff.mp hLHS) (not_or.mpr ⟨hnozero, hnotpoint⟩)
    · -- singleton support: move all mass to j
      have hsupp : ∀ l, l ≠ j → A l = 0 := by
        intro l hl
        by_contra hne
        exact hcase ⟨l, hl, Nat.pos_of_ne_zero hne⟩
      set B : E → ℕ := fun l => if l = j then N else 0 with hB
      have hBtot : ∑ e, B e = N := by
        rw [hB, Finset.sum_eq_single j]
        · simp
        · intro b _ hb; rw [ite_eq_right hb]
        · intro hj'; exact absurd (Finset.mem_univ j) hj'
      have hBmem : B ∈ FullCandidateClass N := hBtot
      have hlt_j : effectiveWeight N A j < effectiveWeight N B j :=
        singleton_transfer_effectiveWeight_lt N A j hj (hN j) hsupp
      have hnozero : ¬ (∃ k, 0 < A k ∧ effectiveWeight N B k = 0) := by
        rintro ⟨k, hk, hk0⟩
        have hkj : k = j := by
          by_contra hne
          have := hsupp k hne
          omega
        have hq : 0 < effectiveWeight N B j := by
          have hBj : B j = N := by rw [hB]; simp
          rw [AssemblyP1.ProductBinomialRigidityNecessity.effectiveWeight_eq_erase, hBj]
          refine Nat.mul_pos (by have := hN j; omega) ?_
          exact prod_pos_of_one_le (fun l hl => by
            have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
            have hBl : B l = 0 := by rw [hB]; simp [hlj]
            rw [hBl, Nat.sub_zero]
            have := hN j
            omega)
        rw [hkj] at hk0
        exact absurd hk0 (ne_of_gt hq)
      have hnotpoint : ¬ (∀ k, 0 < A k → effectiveWeight N B k ≤ effectiveWeight N A k) :=
        fun hp => absurd (hp j (by omega)) (not_le.mpr hlt_j)
      have hiff := AssemblyP1.CoveredBinomialWeightsIff.covered_ambient_effectiveProduct_le_iff
        N A B hqA
      have hLHS : ∀ x, (∀ e, A e ≤ x e) → (∀ e, A e = 0 → x e = 0) →
          effectiveProduct N B x ≤ effectiveProduct N A x :=
        fun x hx hx0 => hmax x hx hx0 B hBmem
      exact absurd (hiff.mp hLHS) (not_or.mpr ⟨hnozero, hnotpoint⟩)
  · -- sufficiency
    intro h x hx hx0 B hB
    have hBtot : ∑ e, B e = N := hB
    have hqA : ∀ i, 0 < A i → 0 < effectiveWeight N A i := by
      rcases h with ⟨e, he⟩ | h1
      · intro i hi
        have hsupp : ∀ l, l ≠ e → A l = 0 := by
          intro l hl
          have hsum := Finset.sum_erase_add Finset.univ A (Finset.mem_univ e)
          have hz : (∑ g ∈ Finset.univ.erase e, A g) = 0 := by omega
          have hle : A l ≤ ∑ g ∈ Finset.univ.erase e, A g :=
            Finset.single_le_sum (fun g _ => Nat.zero_le _)
              (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩)
          omega
        have hie : i = e := by
          by_contra hne
          have := hsupp i hne
          omega
        subst hie
        rw [AssemblyP1.ProductBinomialRigidityNecessity.effectiveWeight_eq_erase]
        refine Nat.mul_pos hi ?_
        exact prod_pos_of_one_le (fun l hl => by
          have h0 := hsupp l (Finset.mem_erase.mp hl).1
          omega)
      · intro i hi
        rw [AssemblyP1.ProductBinomialRigidityNecessity.effectiveWeight_eq_erase]
        have hAi : A i = 1 := by have := h1 i; omega
        rw [hAi]
        refine Nat.mul_pos (by norm_num) ?_
        refine prod_pos_of_one_le (fun l hl => ?_)
        have hli : l ≠ i := (Finset.mem_erase.mp hl).1
        have hAl : A l ≤ 1 := h1 l
        have hpair : A i + A l ≤ N := by
          calc A i + A l = ∑ g ∈ ({i, l} : Finset E), A g := by
                rw [Finset.sum_pair (Ne.symm hli)]
            _ ≤ ∑ g, A g := Finset.sum_le_sum_of_subset_of_nonneg
                (fun g _ => Finset.mem_univ g) (fun g _ _ => Nat.zero_le _)
            _ = N := hAtot
        omega
    have hiff := AssemblyP1.CoveredBinomialWeightsIff.covered_ambient_effectiveProduct_le_iff
      N A B hqA
    refine hiff.mpr ?_ x hx hx0
    rcases h with ⟨e, he⟩ | h1
    · -- concentrated truth A = N · δ_e
      have hsupp : ∀ l, l ≠ e → A l = 0 := by
        intro l hl
        have hsum := Finset.sum_erase_add Finset.univ A (Finset.mem_univ e)
        have hz : (∑ g ∈ Finset.univ.erase e, A g) = 0 := by omega
        have hle : A l ≤ ∑ g ∈ Finset.univ.erase e, A g :=
          Finset.single_le_sum (fun g _ => Nat.zero_le _)
            (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩)
        omega
      by_cases hN0 : N = 0
      · -- A = 0 and B = 0
        refine Or.inr ?_
        intro k hk
        exfalso
        have hAk : A k = 0 := by
          by_cases hke : k = e
          · rw [hke, he, hN0]
          · exact hsupp k hke
        omega
      · have hAe : 0 < A e := by rw [he]; omega
        by_cases hz : effectiveWeight N B e = 0
        · exact Or.inl ⟨e, hAe, hz⟩
        · refine Or.inr ?_
          intro k hk
          have hke : k = e := by
            by_contra hne
            have := hsupp k hne
            omega
          rw [hke]
          rw [AssemblyP1.ProductBinomialRigidityNecessity.effectiveWeight_eq_erase,
            AssemblyP1.ProductBinomialRigidityNecessity.effectiveWeight_eq_erase]
          have hBle : B e ≤ N := by
            calc B e ≤ ∑ g, B g :=
                  Finset.single_le_sum (fun g _ => Nat.zero_le _) (Finset.mem_univ e)
              _ = N := hBtot
          have hprodA : (∏ l ∈ Finset.univ.erase e, (N - A l))
              = ∏ _l ∈ Finset.univ.erase e, N :=
            Finset.prod_congr rfl (fun l hl => by
              rw [hsupp l (Finset.mem_erase.mp hl).1, Nat.sub_zero])
          have hprodB_le : (∏ l ∈ Finset.univ.erase e, (N - B l))
              ≤ ∏ _l ∈ Finset.univ.erase e, N :=
            Finset.prod_le_prod (fun l _ => Nat.sub_le _ _)
          rw [hprodA, he]
          exact Nat.mul_le_mul hBle hprodB_le
    · -- {0,1} case
      by_cases hz : ∃ k, 0 < A k ∧ effectiveWeight N B k = 0
      · exact Or.inl hz
      · refine Or.inr ?_
        have hBeqA : B = A :=
          eq_of_effectiveWeight_pos_of_zero_one N A B hAtot h1 hBtot
            (fun k hk => Nat.pos_of_ne_zero (fun h0 => hz ⟨k, hk, h0⟩))
        intro k _
        rw [hBeqA]

/-! ## Corollaries and non-vacuity witnesses -/

/-- Support form of the classification: over the full candidate class the only
maximal truths are the mass-on-one-class spectra and the `{0,1}`-valued spectra
(indicators of an `N`-element support). -/
theorem fullClass_max_iff_support (N : ℕ) (A : E → ℕ) (hAtot : ∑ e, A e = N) :
    SampleUniformMax N A (FullCandidateClass N) ↔
      (∃ e, A e = N ∧ ∀ l ≠ e, A l = 0) ∨ (∀ e, A e = 0 ∨ A e = 1) := by
  rw [fullClass_sampleUniformMax_iff N A hAtot]
  constructor
  · rintro (⟨e, he⟩ | h1)
    · left
      refine ⟨e, he, fun l hl => ?_⟩
      have hsum := Finset.sum_erase_add Finset.univ A (Finset.mem_univ e)
      have hz : (∑ g ∈ Finset.univ.erase e, A g) = 0 := by omega
      have hle : A l ≤ ∑ g ∈ Finset.univ.erase e, A g :=
        Finset.single_le_sum (fun g _ => Nat.zero_le _)
          (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩)
      omega
    · right
      intro e
      rcases Nat.eq_zero_or_pos (A e) with h0 | hpos
      · exact Or.inl h0
      · exact Or.inr (by have := h1 e; omega)
  · rintro (⟨e, he, _⟩ | h1)
    · exact Or.inl ⟨e, he⟩
    · exact Or.inr (fun e => by have := h1 e; omega)

/-- A **boundary candidate never beats the truth** (the criterion's zero branch):
if the candidate vanishes on a true-supported class, the truth is maximal
against it. -/
theorem boundary_candidate_dominated (N : ℕ) (A B : E → ℕ)
    (hqA : ∀ i, 0 < A i → 0 < effectiveWeight N A i)
    (hzero : ∃ i, 0 < A i ∧ effectiveWeight N B i = 0) :
    ∀ x : E → ℕ, (∀ e, A e ≤ x e) → (∀ e, A e = 0 → x e = 0) →
      effectiveProduct N B x ≤ effectiveProduct N A x :=
  (AssemblyP1.CoveredBinomialWeightsIff.covered_ambient_effectiveProduct_le_iff
    N A B hqA).mpr (Or.inl hzero)

/-- **Non-vacuity: a maximal truth exists.**  The `{0,1}` truth `(1,1,1,1)` over
`Fin 4` with `N = 4` is a sample-uniform maximizer over the full class. -/
theorem maximal_example :
    SampleUniformMax 4 ![1, 1, 1, 1] (FullCandidateClass 4 : Set (Fin 4 → ℕ)) :=
  (fullClass_sampleUniformMax_iff 4 ![1, 1, 1, 1] (by decide)).mpr
    (Or.inr (by decide))

/-- **Non-vacuity: the classification genuinely fails for a non-degenerate
truth.**  The rigid length-`4` spectrum `(2,1,1,0)` of `0001` is *not* a
sample-uniform maximizer over the full class (it is beaten by `(1,1,1,1)`), so
rigidity is not sufficient and the full-class condition is strictly stronger. -/
theorem nonmaximal_example :
    ¬ SampleUniformMax 4 ![2, 1, 1, 0] (FullCandidateClass 4 : Set (Fin 4 → ℕ)) := by
  rw [fullClass_sampleUniformMax_iff 4 ![2, 1, 1, 0] (by decide)]
  decide

/-- **The smallest `{0,1}` maximal truth with two supported classes.**  `(0,1,1)`
over `Fin 3` with `N = 2` is maximal over the full class although it is not the
unique positive same-total vector (e.g. `(1,1,0)` is also positive and
same-total), so global uniqueness is *not* necessary for full-class
maximality. -/
theorem maximal_two_support :
    SampleUniformMax 2 ![0, 1, 1] (FullCandidateClass 2 : Set (Fin 3 → ℕ)) :=
  (fullClass_sampleUniformMax_iff 2 ![0, 1, 1] (by decide)).mpr
    (Or.inr (by decide))

end AssemblyP1.ProductBinomialBoundaryFullClass
