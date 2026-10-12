import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Fixed-N product-binomial effective weights (#259(A))

Medvedev and Brudno 2009 Section 6.1 distinguish the genuine multinomial
joint read-count likelihood from the separable product of binomial marginals
used as an optimization approximation with a fixed external N.

For a fixed finite read-type universe E and observations x with sum x = n,
define q_i(B) = B_i * product_{j != i} (N - B_j). Then the candidate-dependent
integer numerator of the product-binomial objective is EXACTLY
product_i q_i(B)^(x_i).

This identity is over Nat, so it includes zero counts and their 0^0=1
convention; interpreting it probabilistically needs N>0, 0<=B_i<=N and
candidate-invariant E,N,x,n. All modeled zero-observed read types must
remain included. The normalized product-binomial score has candidate-constant
factors product_i choose(n,x_i) and N^(-n * card E).

This is a first scoped theorem, not the sample-uniform rigidity iff (#259(B))
nor the source's general bidirected flow model (#261).
-/

namespace AssemblyP1.FixedNBinomialEffectiveWeights

open Finset
open BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E]

private theorem inner_product_factor (C x : E → ℕ) (j : E) :
    (∏ i : E, (if i = j then (1 : ℕ) else C j) ^ x i) =
      (C j) ^ (∑ i ∈ (Finset.univ.erase j), x i) := by
  simp_rw [ite_pow, one_pow]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Finset.filter_ne']

theorem product_factor (A C x : E → ℕ) :
    (∏ i : E, (A i * ∏ j : E, if i = j then (1 : ℕ) else C j) ^ x i) =
      ∏ i : E, A i ^ x i * C i ^ (∑ j ∈ Finset.univ.erase i, x j) := by
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib]
  simp_rw [← Finset.prod_pow]
  rw [Finset.prod_comm]
  simp_rw [inner_product_factor]
  rw [← Finset.prod_mul_distrib]


/-- Product-binomial surrogate read-type weight. The second product ranges
over ALL modeled types, including zero-observed ones. -/
def effectiveWeight (N : ℕ) (B : E → ℕ) (i : E) : ℕ :=
  B i * ∏ j : E, if i = j then (1 : ℕ) else (N - B j)

def effectiveProduct (N : ℕ) (B x : E → ℕ) : ℕ :=
  ∏ i : E, (effectiveWeight N B i) ^ x i

/-- Candidate-dependent integer numerator of the product of binomial
marginal scores. The binomial coefficients and the factor N^(-n*|E|)
are omitted, because they are constant in B when E,N,n,x are fixed. -/
def binomialNumerator (N n : ℕ) (B x : E → ℕ) : ℕ :=
  ∏ i : E, (B i) ^ x i * (N - B i) ^ (n - x i)

private theorem erase_count_eq (x : E → ℕ) (n : ℕ)
    (hn : (∑ i : E, x i) = n) (j : E) :
    (∑ i ∈ Finset.univ.erase j, x i) = n - x j := by
  calc
    (∑ i ∈ Finset.univ.erase j, x i) =
      ((∑ i ∈ Finset.univ.erase j, x i) + x j) - x j := by simp
    _ = (∑ i : E, x i) - x j := by
      rw [Finset.sum_erase_add Finset.univ x (Finset.mem_univ j)]
    _ = n - x j := by rw [hn]

/-- Exact finite product identity for the fixed-N product-binomial surrogate,
including zero sample counts. This is not the exact multinomial likelihood,
and it does not formalize the general bidirected flow candidate universe. -/
theorem effectiveProduct_eq_binomialNumerator
    (N n : ℕ) (B x : E → ℕ) (hn : (∑ i : E, x i) = n) :
    effectiveProduct N B x = binomialNumerator N n B x := by
  unfold effectiveProduct effectiveWeight binomialNumerator
  rw [product_factor]
  apply Finset.prod_congr rfl
  intro i _
  rw [erase_count_eq x n hn i]

theorem binomialNumerator_le_iff_effectiveProduct_le
    (N n : ℕ) (A B x : E → ℕ) (hn : (∑ i : E, x i) = n) :
    binomialNumerator N n A x ≤ binomialNumerator N n B x ↔
      effectiveProduct N A x ≤ effectiveProduct N B x := by
  rw [← effectiveProduct_eq_binomialNumerator N n A x hn,
      ← effectiveProduct_eq_binomialNumerator N n B x hn]

end AssemblyP1.FixedNBinomialEffectiveWeights
