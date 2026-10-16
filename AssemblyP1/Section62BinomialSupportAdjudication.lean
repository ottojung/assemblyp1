import AssemblyP1.Section62BinomialCriterion

/-!
# Source-fidelity adjudication: unobserved molecule types in the §6.1 criterion
(issue #261)

This module adjudicates the open review objection recorded on issue #261:

> MB09 §6.1's fixed-`N` separable product-binomial pseudo-likelihood is a
> product over **all** `4^k` molecule types (including types with observed count
> `x_i = 0`), whereas the §6.2 overlap graph carries only *observed* read
> vertices.  A candidate that leaves an unobserved type at count `0` might
> therefore silently avoid the `(1 - d_i/N)^n < 1` penalty that a spelled genome
> with a positive count on that type must pay.

## Verdict (kernel-checked below)

1. **Which `c_i(d_i)` terms the criterion includes.**  At the count-vector layer
   the criterion is *already* full-support.  The literal §6.1 product
   `K(d;x) = ∏_j d_j^{x_j}(N-d_j)^{n-x_j}` runs over the whole class universe
   `T`; `binomCoreNat_support_split` makes the bookkeeping literal: for `x`
   supported on the observed set `I` and `n = ∑ x`,
   `K(d;x) = (∏_{j∉I}(N-d_j))^n · ∏_{i∈I} d_i^{x_i}(N-d_i)^{n-x_i}`.
   Each **unobserved** class `j ∉ I` therefore contributes the full factor
   `(N-d_j)^n` — it is *not* dropped.  Equivalently, by
   `binomCoreNat_eq_prod_qFac` / `criterion_is_full_support`, the score is
   `∏_{i∈I} q_i(d)^{x_i}` with `q_i(d) = d_i ∏_{j≠i}(N-d_j)`, and
   `qFac_split` exhibits the unobserved factors `(N-d_j)` inside every `q_i`.

2. **Unobserved coordinates are neither forced to zero nor immaterial.**  The
   count-vector theorem places no restriction on the unobserved coordinates;
   `unobserved_coord_matters` exhibits two count vectors agreeing on `I` but
   scoring differently, and `observedOnly_insufficient` shows that the naive
   *observed-only* shortcut `q^I_i(d) = d_i ∏_{j∈I,j≠i}(N-d_j)` is a **wrong**
   criterion: it predicts "candidate never beats truth" while the candidate
   strictly beats the truth under the full product.  Thus the full-support
   terms are indispensable, and the criterion is *not* a function of the
   observed coordinates alone.

3. **The flow-level §6.2 obligation is genuinely different and stays OPEN.**
   A §6.2 feasible flow's throughput is supported on the observed read
   vertices, so it does not by itself specify the unobserved coordinates.
   `flow_genome_gap` quantifies the resulting discrepancy exactly: if a flow
   `d` agrees with a genome `d'` on `I` and is `0` off `I`, then for any sample
   supported on `I` the full scores are related by
   `K(d;x)·(∏_{j∉I}(N-d'_j))^n = K(d';x)·(∏_{j∉I} N)^n`, i.e. the flow is
   larger by `∏_{j∉I}(N/(N-d'_j))^n ≥ 1`.  A flow does **not** pay for the
   genome's unobserved mass.  Constructing the source-faithful flow→count
   adapter (and deciding the unobserved-coordinate convention) remains OPEN.

## Candidate / truth / likelihood / length universe (the well-defined class)

* **Candidates**: count vectors `d : T → ℕ` over the *full* molecule-type
  universe, with the observed support `I` and the unobserved coordinates
  *explicitly specified*.  Not §6.2 flows, not spelled circuits, not circular
  genomes.
* **Truth**: admitted (any full count vector `A` with `q_i(A) > 0` on `I`).
* **Likelihood**: MB09 §6.1 fixed-external-`N` separable product-binomial
  (equivalently its core `binomCoreNat`).
* **Length universe**: fixed external `N`.

The theorem therefore covers exactly the count-vector class with a fully
specified support; it does not close the §6.2 flow-level classification.
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace AssemblyP1.Section62BinomialSupportAdjudication

open AssemblyP1.Section62BinomialCriterion

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Exact support splitting of the §6.1 core.**  If the sample `x` is
supported on `I` and `n = ∑ x`, the literal product over *all* classes splits
into the observed factors `d_i^{x_i}(N-d_i)^{n-x_i}` and one full `(N-d_j)^n`
factor per **unobserved** class `j ∉ I`.  This is the exact `c_i(d_i)`
bookkeeping the §6.1 display performs: no unobserved term is dropped. -/
theorem binomCoreNat_support_split (d x : ι → ℕ) (N : ℕ) (I : Finset ι)
    (hx : IsSupportedOn I x) :
    binomCoreNat d x N =
      (∏ j ∈ Iᶜ, (N - d j)) ^ (∑ i, x i) *
        ∏ i ∈ I, (d i ^ x i * (N - d i) ^ (∑ k, x k - x i)) := by
  have hx0 : ∀ j, j ∉ I → x j = 0 := by
    intro j hj
    by_contra hne
    exact hj ((hx j).mp (Nat.pos_of_ne_zero hne))
  have hcompl : (∏ j ∈ Iᶜ, (d j ^ x j * (N - d j) ^ (∑ k, x k - x j)))
      = (∏ j ∈ Iᶜ, (N - d j)) ^ (∑ k, x k) := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro j hj
    have hxj : x j = 0 := hx0 j (by simpa [Finset.mem_compl] using hj)
    rw [hxj, pow_zero, one_mul, Nat.sub_zero]
  have hsplit : (∏ i, d i ^ x i * (N - d i) ^ (∑ k, x k - x i))
      = (∏ i ∈ I, d i ^ x i * (N - d i) ^ (∑ k, x k - x i)) *
        ∏ j ∈ Iᶜ, (d j ^ x j * (N - d j) ^ (∑ k, x k - x j)) :=
    (Finset.prod_mul_prod_compl I
      (fun i => d i ^ x i * (N - d i) ^ (∑ k, x k - x i))).symm
  rw [binomCoreNat, hsplit, hcompl]
  exact mul_comm _ _

/-- **The unobserved factors inside each effective weight.**  For an observed
class `i ∈ I`, the §6.1 effective weight `q_i(d) = d_i ∏_{j≠i}(N-d_j)`
splits into the observed factors over `I.erase i` and the unobserved factors
over `Iᶜ`.  This shows the criterion's per-class term is *not* observed-only. -/
theorem qFac_split (d : ι → ℕ) (N : ℕ) (I : Finset ι) (i : ι) (hi : i ∈ I) :
    qFac d i N = d i * (∏ j ∈ Iᶜ, (N - d j)) * ∏ j ∈ I.erase i, (N - d j) := by
  unfold qFac
  have hset : (Finset.univ.erase i : Finset ι) = I.erase i ∪ Iᶜ := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_compl, Finset.mem_univ,
      and_true]
    constructor
    · intro hji
      by_cases hjI : j ∈ I
      · exact Or.inl ⟨hji, hjI⟩
      · exact Or.inr hjI
    · rintro (⟨hji, -⟩ | hjI)
      · exact hji
      · intro h
        exact hjI (h ▸ hi)
  have hdisj : Disjoint (I.erase i) Iᶜ := by
    rw [Finset.disjoint_left]
    intro j hj hjI
    exact (Finset.mem_compl.mp hjI) (Finset.mem_of_mem_erase hj)
  rw [hset, Finset.prod_union hdisj]
  ring

/-- **Count-vector verdict.**  The §6.1 core over the full class universe equals
the observed-qFac product, whose factors `q_i(d)` carry the unobserved
coordinates.  Hence `binomial_uniform_criterion` is a full-support criterion:
it is *not* a function of the observed coordinates alone. -/
theorem criterion_is_full_support (d x : ι → ℕ) (N : ℕ) (I : Finset ι)
    (hx : IsSupportedOn I x) :
    binomCoreNat d x N = ∏ i ∈ I, qFac d i N ^ x i := by
  rw [binomCoreNat_eq_prod_qFac, prod_qFac_subset d x N I hx]

/-- **Rigorous unobserved-factor bound.**  If two count vectors `d` and `d'`
agree on the observed support `I`, then on any sample supported on `I` their
full §6.1 scores differ by exactly the ratio of the unobserved factors to the
`n`-th power (cross-multiplied).  This is the exact magnitude of the
source-fidelity obstruction. -/
theorem binomCoreNat_unobserved_ratio (d d' x : ι → ℕ) (N : ℕ) (I : Finset ι)
    (hx : IsSupportedOn I x) (hagree : ∀ i ∈ I, d i = d' i) :
    binomCoreNat d x N * (∏ j ∈ Iᶜ, (N - d' j)) ^ (∑ i, x i) =
      binomCoreNat d' x N * (∏ j ∈ Iᶜ, (N - d j)) ^ (∑ i, x i) := by
  have hobs : (∏ i ∈ I, (d i ^ x i * (N - d i) ^ (∑ k, x k - x i)))
      = ∏ i ∈ I, (d' i ^ x i * (N - d' i) ^ (∑ k, x k - x i)) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [hagree i hi]
  rw [binomCoreNat_support_split d x N I hx,
    binomCoreNat_support_split d' x N I hx, hobs]
  ac_rfl

/-- **Flow-vs-genome bookkeeping.**  If a candidate count vector `d` agrees with
a genome vector `d'` on the observed support `I` and is `0` on every unobserved
class (the §6.2 flow default), then the full §6.1 scores differ by exactly the
unobserved factors: `K(d;x)·(∏_{j∉I}(N-d'_j))^n = K(d';x)·(∏_{j∉I} N)^n`.  Since
`N - d'_j ≤ N`, the flow's score is at least the genome's by
`∏_{j∉I}(N/(N-d'_j))^n ≥ 1`: the flow does **not** pay for the genome's
unobserved mass. -/
theorem flow_genome_gap (d d' x : ι → ℕ) (N : ℕ) (I : Finset ι)
    (hx : IsSupportedOn I x) (hagree : ∀ i ∈ I, d i = d' i)
    (hzero : ∀ j ∈ Iᶜ, d j = 0) :
    binomCoreNat d x N * (∏ j ∈ Iᶜ, (N - d' j)) ^ (∑ i, x i) =
      binomCoreNat d' x N * (∏ _ ∈ Iᶜ, N) ^ (∑ i, x i) := by
  have hprod : (∏ j ∈ Iᶜ, (N - d j)) = ∏ _ ∈ Iᶜ, N := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [hzero j hj, Nat.sub_zero]
  rw [← hprod]
  exact binomCoreNat_unobserved_ratio d d' x N I hx hagree

/-! ## Concrete witnesses -/

namespace Witness

/-- Observed support `{0, 1}` in a three-class universe. -/
def wI : Finset (Fin 3) := {0, 1}

/-- One read of each observed class, nothing on the unobserved class `2`. -/
def wx : Fin 3 → ℕ := ![1, 1, 0]

/-- Count vector with the unobserved class `2` at `0`. -/
def wd : Fin 3 → ℕ := ![2, 1, 0]

/-- Same observed counts, unobserved class `2` at `1`. -/
def wd' : Fin 3 → ℕ := ![2, 1, 1]

theorem wI_supported : IsSupportedOn wI wx := by unfold IsSupportedOn; decide

theorem wd_agree : ∀ i ∈ wI, wd i = wd' i := by decide

theorem wd_score : binomCoreNat wd wx 5 = 600 := by decide

theorem wd'_score : binomCoreNat wd' wx 5 = 384 := by decide

/-- **Unobserved coordinates are not forced to zero and matter.**  `wd` and
`wd'` agree on the observed support `wI` but the full §6.1 score changes. -/
theorem unobserved_coord_matters :
    binomCoreNat wd wx 5 ≠ binomCoreNat wd' wx 5 := by decide

/-- The score ratio is exactly the unobserved factor `(N - d'_2)^n/(N - d_2)^n`
with `N = 5`, `n = 2`. -/
theorem unobserved_coord_ratio :
    binomCoreNat wd wx 5 * ((5 : ℕ) - wd' 2) ^ 2 =
      binomCoreNat wd' wx 5 * ((5 : ℕ) - wd 2) ^ 2 := by decide

end Witness

namespace ObservedOnly

/-- The **observed-only** effective weight `q^I_i(d) = d_i ∏_{j∈I, j≠i}(N-d_j)`,
the naive shortcut that ignores the unobserved coordinates. -/
def qObs (d : ι → ℕ) (i : ι) (N : ℕ) (I : Finset ι) : ℕ :=
  d i * ∏ j ∈ I.erase i, (N - d j)

/-- Observed support `{0, 1}` in a three-class universe. -/
def oI : Finset (Fin 3) := {0, 1}

/-- One read of each observed class, nothing on the unobserved class `2`. -/
def ox : Fin 3 → ℕ := ![1, 1, 0]

/-- Truth carrying mass `4` on the unobserved class `2`. -/
def oA : Fin 3 → ℕ := ![2, 1, 4]

/-- Candidate leaving the unobserved class `2` at `0`. -/
def oB : Fin 3 → ℕ := ![2, 1, 0]

theorem oI_supported : IsSupportedOn oI ox := by unfold IsSupportedOn; decide

theorem observedOnly_dominance_holds :
    ∀ i ∈ oI, qObs oB i 5 oI ≤ qObs oA i 5 oI := by decide

theorem observedOnly_candidate_beats :
    binomCoreNat oA ox 5 < binomCoreNat oB ox 5 := by decide

/-- **The observed-only shortcut is not a valid criterion.**  Here the
observed-only effective weights dominate, yet the candidate strictly beats the
truth under the full §6.1 product.  The unobserved `c_i(d_i)` terms are
indispensable. -/
theorem observedOnly_insufficient :
    (∀ i ∈ oI, qObs oB i 5 oI ≤ qObs oA i 5 oI) ∧
      binomCoreNat oA ox 5 < binomCoreNat oB ox 5 :=
  ⟨observedOnly_dominance_holds, observedOnly_candidate_beats⟩

/-- The full-support criterion correctly detects the defeat: `oA` is interior
on `oI`, the candidate's full effective product is nonzero, and domination
fails. -/
theorem full_criterion_detects :
    (∀ i ∈ oI, 0 < qFac oA i 5) ∧
      (∏ i ∈ oI, qFac oB i 5) ≠ 0 ∧
      ¬ (∀ i ∈ oI, qFac oB i 5 ≤ qFac oA i 5) := by decide

/-- Consequently (by the kernel-checked `binomial_uniform_criterion`) there is
an observation supported exactly on `oI` on which `oB` strictly beats `oA`; the
explicit `ox` is one such sample. -/
theorem exists_defeating_sample :
    ∃ x : Fin 3 → ℕ, IsSupportedOn oI x ∧
      binomCoreNat oA x 5 < binomCoreNat oB x 5 := by
  have hA : ∀ i ∈ oI, 0 < qFac oA i 5 := full_criterion_detects.1
  have hRHS : ¬ ((∏ i ∈ oI, qFac oB i 5) = 0 ∨
      ∀ i ∈ oI, qFac oB i 5 ≤ qFac oA i 5) := by
    rintro (h | h)
    · exact full_criterion_detects.2.1 h
    · exact full_criterion_detects.2.2 h
  have hLHS : ¬ (∀ x : Fin 3 → ℕ, IsSupportedOn oI x →
      binomCoreNat oB x 5 ≤ binomCoreNat oA x 5) :=
    fun h => hRHS ((binomial_uniform_criterion oA oB 5 oI hA).mp h)
  push Not at hLHS
  obtain ⟨x, hx, hlt⟩ := hLHS
  exact ⟨x, hx, hlt⟩

end ObservedOnly

#print axioms binomCoreNat_support_split
#print axioms qFac_split
#print axioms criterion_is_full_support
#print axioms binomCoreNat_unobserved_ratio
#print axioms flow_genome_gap
#print axioms Witness.wI_supported
#print axioms Witness.wd_agree
#print axioms Witness.wd_score
#print axioms Witness.wd'_score
#print axioms Witness.unobserved_coord_matters
#print axioms Witness.unobserved_coord_ratio
#print axioms ObservedOnly.oI_supported
#print axioms ObservedOnly.observedOnly_dominance_holds
#print axioms ObservedOnly.observedOnly_candidate_beats
#print axioms ObservedOnly.observedOnly_insufficient
#print axioms ObservedOnly.full_criterion_detects
#print axioms ObservedOnly.exists_defeating_sample

end AssemblyP1.Section62BinomialSupportAdjudication
