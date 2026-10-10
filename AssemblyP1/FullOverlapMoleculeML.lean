import Mathlib

/-!
# Full-overlap reverse-complement molecule ML maximality

This module is the lane **#260** deliverable of the AssemblyP1 research program
#255: the restricted **full-overlap** (`o_min = L − 1`), **fixed genome length**
(`|D| = |S| = G`), reverse-complement **molecule** domain.

It kernel-checks the abstract exact-multinomial criterion that the program
conjectured around *uniqueness of the normalized count vector*, in the precise
form dictated by the Medvedev–Brudno (2009) §6.2 candidate universe read
faithfully (vertices are the observed read molecules, each with lower bound `1`,
so an admissible spelled candidate has the same molecule-class support as the
observed reads).

## The objective

All admissible candidates have the same length `G = N`, so the exact
Medvedev–Brudno §6.1 multinomial likelihood of a candidate with molecule-class
count vector `d` at an observed class count vector `x` is

```text
L(d; x) = (n! / ∏ᵢ xᵢ!) · ∏ᵢ (dᵢ / G)^{xᵢ}.
```

Between two candidates `A` and `B` of the same length the observation-only
factor `n! / ∏ xᵢ!` and the common `G^{-n}` cancel, so the comparison
`L(B;x) ≤ L(A;x)` is exactly

```text
∏ᵢ (Bᵢ)^{xᵢ} ≤ ∏ᵢ (Aᵢ)^{xᵢ}.
```

`exactLik` below is the right-hand natural-number product, i.e. the exact
likelihood up to the positive candidate-independent constant.  Comparing
`exactLik` is therefore faithful to comparing the exact multinomial likelihood.

## What is proved here

* `exactLik_le_of_forall_le`: **coordinatewise dominance** on the observed
  support implies the truth never loses on any realizable sample.
* `robust_maximality_iff_unique`: for a candidate set of equal total and equal
  support, the truth is a maximizer against every competitor for **every**
  observed count vector supported inside the truth's support **iff** the
  normalized count vector is unique (`F = {A}`).  This is the source-faithful
  iff; the equal-support hypothesis is exactly the §6.2 vertex lower bound `1`
  on the observed reads.
* `w1_not_robust`, `w1_amplified_beats`: the concrete `AAATAT → AAAAAT` finite
  witness (`W1` of `AssemblyP1.HistoricalCoverageSameLengthWitnesses`)
  instantiated at the abstract level, exhibiting the non-uniqueness and the
  amplified sample `x = e_AAA` on which the competitor strictly beats the truth.
* `broad_reading_counterexample`: the equal-support hypothesis is **essential**.
  If the candidate universe is relaxed to spelled count vectors of arbitrary
  support (the broad "all spelled genomes" reading), non-uniqueness can coexist
  with sample-uniform maximality, so the literal "uniqueness of the normalized
  count vector" is then *not* necessary.

## Scope

Finite instances only.  This module is about the count-vector layer of the
full-overlap molecule model.  It does not formalize the spelled bidirected graph
itself (that is `AssemblyP1.Section62Flow`), and it does not settle which
Medvedev–Brudno layer the Shomorony et al. (2016) sentence intends.  Arbitrary
overlap and variable length are out of scope and remain open for #261.
-/

set_option autoImplicit false

open Finset

namespace AssemblyP1.FullOverlapMoleculeML

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact multinomial factor for read class `i`, up to the candidate-independent
multinomial coefficient `n! / ∏ xᵢ!` and the common length factor `N^{-n}`:
`(d i) ^ (x i)`. -/
def exactFactor (d x : ι → ℕ) (i : ι) : ℕ := (d i) ^ (x i)

/-- The exact multinomial likelihood of a same-length candidate with class
counts `d` at an observed class count vector `x`, up to the positive factor
`n! / ∏ xᵢ! · N^{-n}` common to every candidate of the same length `N`. -/
def exactLik (d x : ι → ℕ) : ℕ := ∏ i, exactFactor d x i

omit [DecidableEq ι] in
/-- **Coordinatewise dominance implies sample-uniform maximality.**
If every observed coordinate (`0 < x i`) satisfies `B i ≤ A i`, then the
candidate with counts `B` never beats the truth with counts `A`, for every
observed vector supported inside `supp A`. -/
theorem exactLik_le_of_forall_le (A B x : ι → ℕ)
    (h : ∀ i, 0 < x i → B i ≤ A i) :
    exactLik B x ≤ exactLik A x := by
  unfold exactLik exactFactor
  apply Finset.prod_le_prod
  intro i _
  by_cases hx : 0 < x i
  · exact pow_le_pow_left' (h i hx) (x i)
  · have hz : x i = 0 := Nat.eq_zero_of_not_pos hx
    simp [hz]

/-- **The exact-multinomial robust-maximality iff (source-faithful reading).**
Fix the truth class-count vector `A` (length `G = ∑ A`).  Let `F` be a finite set
of admissible competitor count vectors, each of the same total `G` and the same
molecule-class support as `A` (the §6.2 vertex lower bound `1` on the observed
reads, together with "vertices are the observed reads").  Then the truth is an
exact-ML maximizer against every competitor for **every** observed count vector
`x` supported inside `supp A` **iff** the normalized count vector is unique,
i.e. every admissible `B` equals `A`.

The `⟸` direction is immediate; the `⟹` direction is the W1 amplification
mechanism: if `B ≠ A`, equal totals force some class `w ∈ supp A` with
`B w > A w`, and the concentrated sample `x = e_w` (realizable because
`w ∈ supp A`) makes `B` strictly better. -/
theorem robust_maximality_iff_unique (A : ι → ℕ) (F : Finset (ι → ℕ))
    (hsum : ∀ B ∈ F, ∑ i, B i = ∑ i, A i)
    (hsupp : ∀ B ∈ F, ∀ i, 0 < B i ↔ 0 < A i) :
    (∀ x : ι → ℕ, (∀ i, 0 < x i → 0 < A i) →
        ∀ B ∈ F, exactLik B x ≤ exactLik A x) ↔
      ∀ B ∈ F, B = A := by
  constructor
  · intro h B hB
    by_contra hne
    -- Equal totals and `B ≠ A` force a coordinate where `B` strictly exceeds `A`.
    have hex : ∃ i, A i < B i := by
      by_contra hno
      push Not at hno
      have hlt : ∃ i, B i < A i := by
        by_contra hno2
        push Not at hno2
        exact hne (funext (fun i => le_antisymm (hno i) (hno2 i)))
      obtain ⟨i, hi⟩ := hlt
      have hstrict :
          ∑ j, B j < ∑ j, A j :=
        Finset.sum_lt_sum (s := Finset.univ) (fun j _ => hno j)
          ⟨i, Finset.mem_univ i, hi⟩
      rw [hsum B hB] at hstrict
      exact lt_irrefl _ hstrict
    obtain ⟨i, hi⟩ := hex
    have hBi : 0 < B i := lt_of_le_of_lt (Nat.zero_le _) hi
    have hAi : 0 < A i := (hsupp B hB i).mp hBi
    let x : ι → ℕ := Pi.single i 1
    have hxsupp : ∀ j, 0 < x j → 0 < A j := by
      intro j hj
      have hji : j = i := by
        by_contra hne'
        have hz : x j = 0 := by simp [x, Pi.single_eq_of_ne hne']
        rw [hz] at hj
        exact Nat.lt_irrefl 0 hj
      subst hji
      exact hAi
    have hineq := h x hxsupp B hB
    have hBx : exactLik B x = B i := by
      unfold exactLik exactFactor
      rw [Fintype.prod_eq_single i (fun j hj => by simp [x, Pi.single_eq_of_ne hj])]
      simp [x]
    have hAx : exactLik A x = A i := by
      unfold exactLik exactFactor
      rw [Fintype.prod_eq_single i (fun j hj => by simp [x, Pi.single_eq_of_ne hj])]
      simp [x]
    rw [hBx, hAx] at hineq
    exact absurd hineq (Nat.not_le.mpr hi)
  · intro h x _ B hB
    rw [h B hB]

omit [DecidableEq ι] in
/-- **Sufficiency of uniqueness.**  If every admissible competitor has the
truth's count vector, the truth ties them all and is a maximizer on every
realizable sample. -/
theorem robust_maximality_of_unique (A : ι → ℕ) (F : Finset (ι → ℕ))
    (h : ∀ B ∈ F, B = A) :
    ∀ x : ι → ℕ, (∀ i, 0 < x i → 0 < A i) →
      ∀ B ∈ F, exactLik B x ≤ exactLik A x := by
  intro x _ B hB
  rw [h B hB]

/-! ## The concrete `W1` witness at the abstract level

Codes: `0 = AAA`, `1 = AAT`, `2 = ATA`, `4 = TAA` in the `Fin 8` class space of
`AssemblyP1.SameLengthSection62Counterexample`.  The truth `AAATAT` has
`d_S = (1,1,3,0,1,0,0,0)` and the competitor `AAAAAT` has
`d_D = (3,1,1,0,1,0,0,0)`: equal total `6`, equal support `{0,1,2,4}`, distinct
count vectors.  So the truth is **not** robustly maximal, and the amplified
sample `x = e_AAA` is the one on which the competitor strictly wins. -/

/-- Truth class-count vector of `W1` (`AAATAT`, length `6`). -/
def w1A : Fin 8 → ℕ := ![1, 1, 3, 0, 1, 0, 0, 0]

/-- Competitor class-count vector of `W1` (`AAAAAT`, length `6`). -/
def w1B : Fin 8 → ℕ := ![3, 1, 1, 0, 1, 0, 0, 0]

theorem w1A_sum : ∑ i, w1A i = 6 := by decide

theorem w1B_sum : ∑ i, w1B i = 6 := by decide

theorem w1_support : ∀ i, 0 < w1B i ↔ 0 < w1A i := by decide

theorem w1_ne : w1B ≠ w1A := by decide

/-- The explicit amplified sample `x = e_AAA` on which `W1`'s competitor strictly
beats the truth: `exactLik w1B x = 3 > 1 = exactLik w1A x`. -/
theorem w1_amplified_beats :
    exactLik w1B (Pi.single 0 1) > exactLik w1A (Pi.single 0 1) := by
  unfold exactLik exactFactor
  rw [Fintype.prod_eq_single 0 (fun j hj => by rw [Pi.single_eq_of_ne hj]; simp),
    Fintype.prod_eq_single 0 (fun j hj => by rw [Pi.single_eq_of_ne hj]; simp)]
  simp [Pi.single_eq_same, w1A, w1B]

/-- The abstract iff applied to `W1`: because the count vector is not unique,
the truth is not a maximizer for every realizable sample. -/
theorem w1_not_robust :
    ¬ (∀ x : Fin 8 → ℕ, (∀ i, 0 < x i → 0 < w1A i) →
        exactLik w1B x ≤ exactLik w1A x) := by
  intro h
  have h' : ∀ x : Fin 8 → ℕ, (∀ i, 0 < x i → 0 < w1A i) →
      ∀ B ∈ ({w1B} : Finset (Fin 8 → ℕ)), exactLik B x ≤ exactLik w1A x := by
    intro x hx B hB
    rw [Finset.mem_singleton] at hB
    subst hB
    exact h x hx
  have hiff :=
    (robust_maximality_iff_unique (A := w1A) (F := {w1B}) (by
        intro B hB
        rw [Finset.mem_singleton] at hB
        subst hB
        exact w1B_sum.trans w1A_sum.symm)
      (by
        intro B hB
        rw [Finset.mem_singleton] at hB
        subst hB
        exact w1_support)).mp h'
  exact w1_ne (hiff w1B (Finset.mem_singleton_self w1B))

/-! ## The equal-support hypothesis is essential

Under the broad reading — admissible candidates are *all* spelled length-`G`
genomes, with no §6.2 vertex lower bound tying their support to the observed
reads — the literal "uniqueness of the normalized count vector" is **not**
necessary.  The witness is the full-overlap molecule pair `AATT → AAAT` over the
class space `(AAT, TAA, AAA, ATA)`: the truth `AATT` has counts `(2,2,0,0)`, the
competitor `AAAT` has counts `(1,1,1,1)`.  The competitor is coordinatewise
`≤` the truth on the truth's support, so the truth dominates on every realizable
sample, yet the count vectors differ. -/

/-- Broad-reading witness: truth `AATT` over classes `(AAT,TAA,AAA,ATA)`. -/
def broadA : Fin 4 → ℕ := ![2, 2, 0, 0]

/-- Broad-reading witness: competitor `AAAT` over classes `(AAT,TAA,AAA,ATA)`. -/
def broadB : Fin 4 → ℕ := ![1, 1, 1, 1]

theorem broad_sum : ∑ i, broadB i = ∑ i, broadA i := by decide

theorem broad_ne : broadB ≠ broadA := by decide

/-- Non-uniqueness does not prevent sample-uniform maximality once the
equal-support hypothesis is dropped: the truth still dominates every realizable
sample. -/
theorem broad_reading_counterexample :
    ∃ A B : Fin 4 → ℕ,
      (∑ i, B i = ∑ i, A i) ∧ B ≠ A ∧
        (∀ x : Fin 4 → ℕ, (∀ i, 0 < x i → 0 < A i) →
          exactLik B x ≤ exactLik A x) := by
  refine ⟨broadA, broadB, broad_sum, broad_ne, ?_⟩
  intro x hx
  apply exactLik_le_of_forall_le
  intro i hi
  fin_cases i
  · simp [broadA, broadB]
  · simp [broadA, broadB]
  · exact absurd (hx _ hi) (by simp [broadA])
  · exact absurd (hx _ hi) (by simp [broadA])

end AssemblyP1.FullOverlapMoleculeML
