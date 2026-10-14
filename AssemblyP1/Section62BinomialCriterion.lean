import Mathlib

/-!
# The genuine §6.1 separable-binomial count-vector criterion (issue #261)

This module formalizes, at the **count-vector layer**, the exact
necessary-and-sufficient maximality criterion for the Medvedev–Brudno (2009)
§6.1 *separable product-binomial approximation* with a fixed **external** genome
size `N`.

## What is here

* `qFac d i N = d i * ∏_{j ≠ i} (N - d j)` — the per-class *effective weight*.
* `binomCoreNat d x N` — the §6.1 binomial comparison core
  `∏ᵢ dᵢ^{xᵢ} · (N - dᵢ)^{n - xᵢ}` (`n = ∑ x`), obtained from the literal product
  `∏ᵢ C(n, xᵢ) (dᵢ/N)^{xᵢ} (1 - dᵢ/N)^{n - xᵢ}` after dropping the
  candidate-independent `C(n, xᵢ)` and the common `N^{-n}`.
* `binomCoreNat_eq_prod_qFac` — the exact **q-factorization**
  `K(d; x) = ∏ᵢ qᵢ(d)^{xᵢ}`, an identity over `ℕ` (no probability needed).
* `binomCoreNat_concentrated` — the score of the "one copy of every observed
  class, `t` extra copies of class `k`" sample, in closed form
  `(∏_{i∈I} qᵢ) · qₖ^t`.
* `binomial_uniform_criterion` — the count-vector criterion.  For a fixed
  candidate `B`, a fixed observed support `I`, and a truth `A` with strictly
  positive effective weights on `I`, the candidate never strictly beats the
  truth on **any** sample whose support is exactly `I` (any total read count)
  **iff** `∏_{i∈I} qᵢ(B) = 0`, or `qᵢ(B) ≤ qᵢ(A)` for every `i ∈ I`.
* `witness_qFac_A`, `witness_qFac_B`, `witness_beats` — the concrete
  `A = (1,2)`, `B = (1,1)`, `N = 3` witness: the criterion fails and `B`
  strictly beats `A`, reproducing the kernel-checked
  `binomial_not_coordinatewise` fact through the new factorization.

## Scope and what is *not* claimed

The theorem is a statement about **count vectors** with a **fixed external `N`**.
It is *not* a claim about the §6.2 bidirected feasible-flow set, the transitive
reduction, the terminal-penalized solver objective, or the exact iid
multinomial.  In particular:

* the §6.1 **exact multinomial** (candidate's own length `N(D)`) is a different
  objective (`GeneralBidirectedFlowML.varLengthCriterion`);
* the **exact iid multinomial** and the **fixed-external-`N` product**
  (`GeneralBidirectedFlowML.flow_dominance_criterion`) are different again;
* the adapter from a source-faithful §6.2 integer/half-integral bidirected flow
  to such a count vector is **OPEN** (see
  `docs/issue261-general-bidirected-flow-ml.md`).

The probability domain `0 ≤ dᵢ ≤ N` is *not* required by the algebra: the
identity and criterion hold for arbitrary natural count vectors with truncated
subtraction, which is the honest domain of the finite count-vector layer.
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace AssemblyP1.Section62BinomialCriterion

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The per-class §6.1 effective weight `qᵢ(d) = dᵢ · ∏_{j ≠ i} (N - dⱼ)`.
This is the class-`i` factor that survives the q-factorization of the separable
product-binomial core. -/
def qFac (d : ι → ℕ) (i : ι) (N : ℕ) : ℕ :=
  d i * ∏ j ∈ univ.erase i, (N - d j)

/-- The §6.1 separable-binomial comparison core over `ℕ`:
`∏ᵢ dᵢ^{xᵢ} · (N - dᵢ)^{n - xᵢ}` with `n = ∑ x`.  This is the literal §6.1
product-binomial `∏ᵢ C(n,xᵢ)(dᵢ/N)^{xᵢ}(1 - dᵢ/N)^{n-xᵢ}` with the
candidate-independent `C(n,xᵢ)` and the common `N^{-n}` removed. -/
def binomCoreNat (d x : ι → ℕ) (N : ℕ) : ℕ :=
  ∏ i, d i ^ x i * (N - d i) ^ (∑ j, x j - x i)

/-- `qFac` as an unrestricted product with the diagonal entry `dᵢ`. -/
theorem qFac_eq_prod (d : ι → ℕ) (i : ι) (N : ℕ) :
    qFac d i N = ∏ j, if j = i then d i else N - d j := by
  unfold qFac
  conv_rhs => rw [← Finset.prod_erase_mul univ
    (fun j => if j = i then d i else N - d j) (Finset.mem_univ i), ite_eq_left rfl]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [ite_eq_right (Finset.mem_erase.mp hj).1]

/-- **The q-factorization.**  `K(d; x) = ∏ᵢ qᵢ(d)^{xᵢ}` exactly, over `ℕ`.
This is the algebraic heart of the fixed-`N` binomial comparison. -/
theorem binomCoreNat_eq_prod_qFac (d x : ι → ℕ) (N : ℕ) :
    binomCoreNat d x N = ∏ i, qFac d i N ^ x i := by
  have h1 : ∏ i, qFac d i N ^ x i
      = ∏ i, (∏ j, (if j = i then d i else N - d j)) ^ x i := by
    apply Finset.prod_congr rfl
    intro i _
    rw [qFac_eq_prod]
  rw [h1]
  have h2 : ∀ i, (∏ j, (if j = i then d i else N - d j)) ^ x i
      = ∏ j, (if j = i then d i else N - d j) ^ x i := by
    intro i
    rw [← Finset.prod_pow]
  simp_rw [h2]
  rw [Finset.prod_comm]
  have h4 : ∀ j, (∏ i, (if j = i then d i else N - d j) ^ x i)
      = d j ^ x j * (N - d j) ^ (∑ i ∈ univ.erase j, x i) := by
    intro j
    have herase : (∏ i ∈ univ.erase j, (if j = i then d i else N - d j) ^ x i)
        = (N - d j) ^ (∑ i ∈ univ.erase j, x i) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_congr rfl
      intro i hi
      rw [ite_eq_right (Ne.symm (Finset.mem_erase.mp hi).1)]
    rw [← Finset.prod_erase_mul univ
      (fun i => (if j = i then d i else N - d j) ^ x i) (Finset.mem_univ j)]
    rw [ite_eq_left rfl, herase]
    rw [mul_comm]
  simp_rw [h4]
  apply Finset.prod_congr rfl
  intro j _
  have hexp : (∑ i, x i - x j) = ∑ i ∈ univ.erase j, x i := by
    have hsum := Finset.sum_erase_add univ x (Finset.mem_univ j)
    omega
  rw [hexp]

/-- A sample is **supported exactly on `I`** when it is positive precisely on the
classes of `I`. -/
def IsSupportedOn (I : Finset ι) (x : ι → ℕ) : Prop :=
  ∀ i, 0 < x i ↔ i ∈ I

/-- Restrict a full q-product to the support `I`. -/
theorem prod_qFac_subset (C x : ι → ℕ) (N : ℕ) (I : Finset ι)
    (hx : IsSupportedOn I x) :
    ∏ i, qFac C i N ^ x i = ∏ i ∈ I, qFac C i N ^ x i :=
  (Finset.prod_subset (Finset.subset_univ I) fun i _ hiI => by
    have hzero : x i = 0 := by
      by_contra hne
      exact hiI ((hx i).mp (Nat.pos_of_ne_zero hne))
    rw [hzero, pow_zero]).symm

-- The concentrated sample is supported exactly on `I`.
omit [Fintype ι] in
theorem isSupportedOn_concentrated (I : Finset ι) (k : ι) (hk : k ∈ I) (t : ℕ) :
    IsSupportedOn I
      (fun i => (if i ∈ I then 1 else 0) + (if i = k then t else 0)) := by
  intro i
  change 0 < ((if i ∈ I then 1 else 0) + (if i = k then t else 0) : ℕ) ↔ i ∈ I
  by_cases hiI : i ∈ I
  · have h1 : (if i ∈ I then (1 : ℕ) else 0) = 1 := ite_eq_left hiI
    rw [h1]
    exact ⟨fun _ => hiI, fun _ => by omega⟩
  · have hik : i ≠ k := fun hh => hiI (hh ▸ hk)
    have h0 : ((if i ∈ I then 1 else 0) + (if i = k then t else 0) : ℕ) = 0 := by
      rw [ite_eq_right hiI, ite_eq_right hik, add_zero]
    rw [h0]
    exact ⟨fun h => absurd h (Nat.lt_irrefl 0), fun h => absurd h hiI⟩

/-- **Concentrated sample score.**  For the sample that puts one copy on every
class of `I` and `t` extra copies on `k ∈ I`, the §6.1 core equals
`(∏_{i∈I} qᵢ) · qₖ^t`. -/
theorem binomCoreNat_concentrated (C : ι → ℕ) (N : ℕ) (I : Finset ι)
    (k : ι) (hk : k ∈ I) (t : ℕ) :
    binomCoreNat C
        (fun i => (if i ∈ I then 1 else 0) + (if i = k then t else 0)) N
      = (∏ i ∈ I, qFac C i N) * qFac C k N ^ t := by
  rw [binomCoreNat_eq_prod_qFac]
  rw [← Finset.prod_subset (Finset.subset_univ I) (fun i _ hiI => by
        have hik : i ≠ k := fun h => hiI (h ▸ hk)
        have hzero : ((if i ∈ I then 1 else 0) + (if i = k then t else 0) : ℕ) = 0 := by
          rw [ite_eq_right hiI, ite_eq_right hik, add_zero]
        rw [hzero, pow_zero])]
  rw [← Finset.prod_erase_mul I
    (fun i => qFac C i N ^ ((if i ∈ I then 1 else 0) + (if i = k then t else 0))) hk]
  have herase : ∏ i ∈ I.erase k,
        qFac C i N ^ ((if i ∈ I then 1 else 0) + (if i = k then t else 0))
      = ∏ i ∈ I.erase k, qFac C i N := by
    apply Finset.prod_congr rfl
    intro i hi
    have hik : i ≠ k := (Finset.mem_erase.mp hi).1
    have hiI : i ∈ I := (Finset.mem_erase.mp hi).2
    rw [ite_eq_left hiI, ite_eq_right hik, add_zero, pow_one]
  have hk1 : ((if k ∈ I then 1 else 0) + (if k = k then t else 0) : ℕ) = t + 1 := by
    rw [ite_eq_left hk, ite_eq_left rfl, add_comm]
  rw [herase, hk1, pow_add, pow_one]
  have hAI : (∏ i ∈ I.erase k, qFac C i N) * qFac C k N = ∏ i ∈ I, qFac C i N :=
    Finset.prod_erase_mul I (fun i => qFac C i N) hk
  rw [← hAI]
  ring

/-- Power growth for natural numbers: if `0 < a < b` and `PA, PB > 0`, then some
positive number of extra copies makes `PA · aᵗ` strictly smaller than `PB · bᵗ`. -/
theorem exists_pow_mul_lt {a b PA PB : ℕ} (ha : 0 < a) (hab : a < b)
    (_hPA : 0 < PA) (hPB : 0 < PB) :
    ∃ t : ℕ, PA * a ^ t < PB * b ^ t := by
  have haq : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha
  have hPBq : (0 : ℚ) < (PB : ℚ) := by exact_mod_cast hPB
  have hb1 : (1 : ℚ) < (b : ℚ) / (a : ℚ) := by
    rw [lt_div_iff₀ haq, one_mul]
    exact_mod_cast hab
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt ((PA : ℚ) / (PB : ℚ)) hb1
  refine ⟨t, ?_⟩
  have h1 : (PA : ℚ) / (PB : ℚ) < ((b : ℚ) / (a : ℚ)) ^ t := ht
  rw [div_pow, div_lt_div_iff₀ hPBq (pow_pos haq t)] at h1
  have h2 : (PA : ℚ) * (a : ℚ) ^ t < (PB : ℚ) * (b : ℚ) ^ t := by
    calc (PA : ℚ) * (a : ℚ) ^ t < (b : ℚ) ^ t * (PB : ℚ) := h1
      _ = (PB : ℚ) * (b : ℚ) ^ t := by ring
  exact_mod_cast h2

/-- **The genuine §6.1 separable-binomial count-vector criterion.**

Fix a truth count vector `A`, a candidate count vector `B`, an external genome
size `N`, and an observed support `I`.  Assume the truth has strictly positive
effective weight on every class of `I` (an interior truth).  Then the candidate
never strictly beats the truth on any sample supported exactly on `I` (for every
possible total read count) **iff** either the candidate has zero effective
product on `I`, or its effective weight is coordinatewise dominated by the
truth's on `I`.

This is the exact count-vector necessary-and-sufficient condition derived in
`docs/issue261-general-bidirected-flow-ml.md` (Class 2′, "uniformly over every
`n ≥ m`").  It is *not* the flow-level classification; the flow-to-count-vector
adapter is a separate obligation. -/
theorem binomial_uniform_criterion (A B : ι → ℕ) (N : ℕ) (I : Finset ι)
    (hA : ∀ i ∈ I, 0 < qFac A i N) :
    (∀ x : ι → ℕ, IsSupportedOn I x →
        binomCoreNat B x N ≤ binomCoreNat A x N) ↔
      (∏ i ∈ I, qFac B i N = 0 ∨
        ∀ i ∈ I, qFac B i N ≤ qFac A i N) := by
  constructor
  · intro h
    by_cases hPB : ∏ i ∈ I, qFac B i N = 0
    · exact Or.inl hPB
    · right
      intro k hk
      by_contra hle
      have hlt : qFac A k N < qFac B k N := not_le.mp hle
      have hPA : 0 < ∏ i ∈ I, qFac A i N := Finset.prod_pos fun i hi => hA i hi
      have hPBpos : 0 < ∏ i ∈ I, qFac B i N := Nat.pos_of_ne_zero hPB
      obtain ⟨t, ht⟩ := exists_pow_mul_lt (hA k hk) hlt hPA hPBpos
      have hsup := isSupportedOn_concentrated I k hk t
      have hbeats := h _ hsup
      rw [binomCoreNat_concentrated B N I k hk t,
          binomCoreNat_concentrated A N I k hk t] at hbeats
      omega
  · rintro (hPB | hdom) x hx
    · rw [binomCoreNat_eq_prod_qFac, binomCoreNat_eq_prod_qFac,
          prod_qFac_subset B x N I hx, prod_qFac_subset A x N I hx]
      have hzero : ∏ i ∈ I, qFac B i N ^ x i = 0 := by
        obtain ⟨k, hk, hzk⟩ := Finset.prod_eq_zero_iff.mp hPB
        exact Finset.prod_eq_zero hk (by
          have hxpos : 0 < x k := (hx k).mpr hk
          rw [hzk, zero_pow (Nat.pos_iff_ne_zero.mp hxpos)])
      rw [hzero]
      exact Nat.zero_le _
    · rw [binomCoreNat_eq_prod_qFac, binomCoreNat_eq_prod_qFac,
          prod_qFac_subset B x N I hx, prod_qFac_subset A x N I hx]
      apply Finset.prod_le_prod
      intro i hi
      exact pow_le_pow_left' (hdom i hi) (x i)

/-! ## Concrete witness `A = (1,2)`, `B = (1,1)`, `N = 3`

The effective weights are `q(A) = (1, 4)` and `q(B) = (2, 2)`, so the criterion
fails (the candidate is not dominated at class `0`), and `B` strictly beats `A`
on the sample `x = (2, 1)`, matching `GeneralBidirectedFlowML.binomial_not_coordinatewise`. -/

theorem qFac_fin2_zero (d : Fin 2 → ℕ) (N : ℕ) : qFac d 0 N = d 0 * (N - d 1) := by
  rw [qFac_eq_prod, Fin.prod_univ_two]
  simp

theorem qFac_fin2_one (d : Fin 2 → ℕ) (N : ℕ) : qFac d 1 N = d 1 * (N - d 0) := by
  rw [qFac_eq_prod, Fin.prod_univ_two]
  simp [mul_comm]

theorem witness_qFac_A : qFac ![1, 2] 0 3 = 1 ∧ qFac ![1, 2] 1 3 = 4 := by
  constructor
  · rw [qFac_fin2_zero]; norm_num
  · rw [qFac_fin2_one]; norm_num

theorem witness_qFac_B : qFac ![1, 1] 0 3 = 2 ∧ qFac ![1, 1] 1 3 = 2 := by
  constructor
  · rw [qFac_fin2_zero]; norm_num
  · rw [qFac_fin2_one]; norm_num

/-- The criterion fails for this instance: the candidate product is nonzero and
is not dominated at class `0`. -/
theorem witness_criterion_fails :
    ¬ (∏ i : Fin 2, qFac ![1, 1] i 3 = 0 ∨
        ∀ i, qFac ![1, 1] i 3 ≤ qFac ![1, 2] i 3) := by
  rintro (h | h)
  · rw [Fin.prod_univ_two, witness_qFac_B.1, witness_qFac_B.2] at h
    norm_num at h
  · have h0 := h 0
    rw [witness_qFac_B.1, witness_qFac_A.1] at h0
    norm_num at h0

/-- `B = (1,1)` strictly beats `A = (1,2)` at `x = (2,1)`, `N = 3`. -/
theorem witness_beats :
    binomCoreNat ![1, 1] ![2, 1] 3 > binomCoreNat ![1, 2] ![2, 1] 3 := by
  rw [binomCoreNat, binomCoreNat, Fin.prod_univ_two, Fin.prod_univ_two]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

#print axioms qFac_eq_prod
#print axioms binomCoreNat_eq_prod_qFac
#print axioms prod_qFac_subset
#print axioms isSupportedOn_concentrated
#print axioms binomCoreNat_concentrated
#print axioms exists_pow_mul_lt
#print axioms binomial_uniform_criterion
#print axioms qFac_fin2_zero
#print axioms qFac_fin2_one
#print axioms witness_qFac_A
#print axioms witness_qFac_B
#print axioms witness_criterion_fails
#print axioms witness_beats

end AssemblyP1.Section62BinomialCriterion
