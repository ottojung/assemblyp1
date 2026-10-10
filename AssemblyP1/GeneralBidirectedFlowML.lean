import Mathlib

/-!
# General bidirected-flow ML maximality at arbitrary overlap (issue #261)

This module is the lane **#261** deliverable of the AssemblyP1 research program
#255: the extension of #260's full-overlap **fixed-length** characterization to the
**general MB09 §6.2 bidirected overlap graph at arbitrary `o_min ≤ L − 1`**, where
the candidate genome length is **variable**.

## The new phenomenon

At full overlap (`o_min = L − 1`) every edge overlap is exactly `L − 1`, so a flow
that visits `k` reads spells a genome of length exactly `k`: the length is fixed by
the throughput.  At arbitrary `o_min ≤ L − 1` an edge may carry any overlap length in
`[o_min, L − 1]`, so a flow that visits `k` reads with overlap lengths `o₁,…,o_k`
spells a genome of length `∑ (L − o_j)`, which is **not** determined by the
throughput.  The candidate genome length `N` is therefore a *variable*, and the
exact-multinomial likelihood comparison between a candidate (counts `d`, length `N`)
and the truth (counts `A`, length `G`) acquires a length factor:

```text
L(d; x) ≤ L(A; x)   ⟺   ∏ᵢ dᵢ^xⁱ / N^n  ≤  ∏ᵢ Aᵢ^xⁱ / G^n
                    ⟺   (∏ᵢ dᵢ^xⁱ) · G^n  ≤  (∏ᵢ Aᵢ^xⁱ) · N^n.
```

`crossLik` below is the right-hand natural-number product, so the comparison is a
pure `ℕ` inequality.  Comparing `crossLik` is faithful to comparing the exact
multinomial likelihood up to the positive candidate-independent constant `n!/∏xᵢ!`.

## The main theorem (variable-length criterion)

`varLengthCriterion`: for a truth with counts `A` and length `G`, a candidate with
counts `B` and length `N`, the candidate never beats the truth on any observed
vector supported inside the truth's support **iff**

```text
∀ i ∈ supp A :  B i · G ≤ A i · N.
```

This is the #260 criterion with the length ratio `N/G` as a relaxation factor.
At fixed length `N = G` it reduces to coordinatewise dominance (`B i ≤ A i`), which
is exactly #260's Proposition 3.2; the equal-support uniqueness iff
(`robust_maximality_iff_unique`) is recovered in the equal-total equal-support
reading.  At variable length the criterion is a **density** condition: `B i / N ≤
A i / G`, i.e. the candidate's class density never exceeds the truth's.

## What is proved here

* `varLengthCriterion`: the necessary-and-sufficient variable-length criterion.
* `dilution`: a candidate with the truth's counts but a strictly longer genome is
  strictly worse (the length factor punishes stretching).
* `fixedLengthRecovery`: at `N = G` the criterion is coordinatewise dominance.
* `densityDominance`: the equivalent per-class density formulation.
* The concrete finite witnesses `stretch_beats` (a longer candidate that violates
  the density bound and wins on a concentrated sample) and `dilution_witness`.

## Scope

This module is about the **count-vector × length** layer of the general §6.2 flow
model.  It does not re-formalize the bidirected overlap graph (that is
`AssemblyP1.Section62BidirectedFlow`), the transitive-reduction readings, or the
§6.4 bridging predicate.  It kernel-checks the abstract likelihood criterion that
#260 established at full overlap, extended to the variable-length regime that
arbitrary `o_min` introduces.  Which Medvedev–Brudno layer the 2016 sentence
denotes, the half-integral relaxation gap, and the non-spelled-flow phenomenon are
addressed in `docs/issue261-general-bidirected-flow-ml.md` using the witnesses of
`AssemblyP1.Section62NonSpelledFlow`; they are **not** re-proved here.
-/

set_option autoImplicit false

open Finset

namespace AssemblyP1.GeneralBidirectedFlowML

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exact multinomial likelihood of a candidate with class counts `d` and
genome length `N` at an observed class count vector `x`, cross-multiplied by
`N^(∑ x)` to stay in `ℕ`: `(∏ᵢ dᵢ^(xᵢ)) · N^(∑ x)`.

For a candidate `D` (counts `d`, length `N`) and the truth `S` (counts `a`,
length `G`), the comparison `L(d; x) ≤ L(a; x)` — i.e. `∏ᵢ (dᵢ/N)^(xᵢ) ≤ ∏ᵢ
(aᵢ/G)^(xᵢ)` after cancelling the positive constant `n!/∏xᵢ!` — is exactly the `ℕ`
inequality `crossLik d x G ≤ crossLik a x N`.  The cross-multiplication swaps the
lengths: the candidate's length `N` multiplies the truth's product and vice versa.
-/
def crossLik (d x : ι → ℕ) (N : ℕ) : ℕ := (∏ i, d i ^ x i) * N ^ (∑ i, x i)

/-- The cross-likelihood of a concentrated sample `x = e_i` is the single term
`d i * N`: the product collapses to the one observed class and the length
exponent is `1`. -/
theorem crossLik_single (d : ι → ℕ) (i : ι) (N : ℕ) :
    crossLik d (Pi.single i 1) N = d i * N := by
  unfold crossLik
  have hsum : ∑ j, Pi.single i 1 j = 1 := by
    rw [Finset.sum_eq_single i
      (by intro j _ hne; rw [Pi.single_eq_of_ne hne])
      (by intro h; exact absurd (Finset.mem_univ i) h)]
    rw [Pi.single_eq_same]
  have hprod : ∏ j, d j ^ Pi.single i 1 j = d i := by
    rw [Finset.prod_eq_single i
      (by intro j _ hne; rw [Pi.single_eq_of_ne hne]; simp)
      (by intro h; exact absurd (Finset.mem_univ i) h)]
    rw [Pi.single_eq_same, pow_one]
  rw [hsum, hprod]
  simp

/-- **The variable-length exact-multinomial criterion.**

Fix the truth class-count vector `A` (genome length `G`) and a candidate with
class-count vector `B` (genome length `N`).  The candidate never beats the truth on
any observed count vector `x` supported inside `supp A` **iff**

```text
∀ i ∈ supp A :  B i · G ≤ A i · N.
```

*Proof.*  `⟸`: if `B i · G ≤ A i · N` for every `i ∈ supp A`, then for any `x`
supported in `supp A`,
`(∏ B i^(x i)) · G^n = ∏ (B i · G)^(x i) ≤ ∏ (A i · N)^(x i) = (∏ A i^(x i)) · N^n`,
which is `crossLik B x G ≤ crossLik A x N`.  `⟹`: taking the concentrated sample
`x = e_i` (supported in `supp A` because `i ∈ supp A`, with `∑ x = 1 > 0`) gives
`B i · G ≤ A i · N`.  ∎
-/
theorem varLengthCriterion (A B : ι → ℕ) (G N : ℕ) :
    (∀ x : ι → ℕ, (∀ i, 0 < x i → 0 < A i) → 0 < ∑ i, x i →
        crossLik B x G ≤ crossLik A x N) ↔
      ∀ i, 0 < A i → B i * G ≤ A i * N := by
  constructor
  · intro h i hAi
    have hcon : crossLik B (Pi.single i 1) G ≤ crossLik A (Pi.single i 1) N := by
      refine h (Pi.single i 1) ?_ (by simp)
      intro j hj
      have hji : j = i := by
        by_contra hne'
        have hz : (Pi.single i 1 : ι → ℕ) j = 0 := by rw [Pi.single_eq_of_ne hne']
        rw [hz] at hj
        exact Nat.lt_irrefl 0 hj
      subst hji
      exact hAi
    rw [crossLik_single B i G, crossLik_single A i N] at hcon
    exact hcon
  · intro h x hx hn
    have hper : ∀ i, (B i * G) ^ x i ≤ (A i * N) ^ x i := by
      intro i
      by_cases hxi : x i = 0
      · simp [hxi]
      · have hAi : 0 < A i := hx i (by exact Nat.pos_iff_ne_zero.mpr hxi)
        exact pow_le_pow_left' (h i hAi) (x i)
    have hprod : ∏ i, (B i * G) ^ x i ≤ ∏ i, (A i * N) ^ x i :=
      Finset.prod_le_prod (f := fun i => (B i * G) ^ x i) (g := fun i => (A i * N) ^ x i)
        (fun i _ => hper i)
    have hBG : ∏ i, (B i * G) ^ x i = crossLik B x G := by
      simp [crossLik, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    have hAN : ∏ i, (A i * N) ^ x i = crossLik A x N := by
      simp [crossLik, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    omega

/-- **Dilution.**  A candidate with the truth's counts but a strictly longer genome
is strictly worse on every nonempty sample supported in the truth's support: the
length factor punishes stretching.

At full overlap (`o_min = L − 1`) this cannot happen, because the genome length is
fixed by the throughput.  At arbitrary `o_min` a flow may use shorter overlaps and
thereby stretch the genome while keeping the same read counts; the exact-multinomial
objective then strictly prefers the truth. -/
theorem dilution {A : ι → ℕ} {G N : ℕ} (hN : G < N)
    {x : ι → ℕ} (hx : 0 < ∑ i, x i) (hxsupp : ∀ i, 0 < x i → 0 < A i) :
    crossLik A x G < crossLik A x N := by
  unfold crossLik
  have hmul : 0 < ∏ i, A i ^ x i := by
    apply Finset.prod_pos
    intro i _
    by_cases hxi : x i = 0
    · simp [hxi]
    · exact pow_pos (hxsupp i (Nat.pos_iff_ne_zero.mpr hxi)) (x i)
  have hGn : G ^ (∑ i, x i) < N ^ (∑ i, x i) :=
    Nat.pow_lt_pow_left hN (by omega)
  have key : (∏ i, A i ^ x i) * G ^ (∑ i, x i) < (∏ i, A i ^ x i) * N ^ (∑ i, x i) :=
    (Nat.mul_lt_mul_left hmul).mpr hGn
  exact key

/-- **Fixed-length recovery.**  At `N = G` the variable-length criterion is exactly
coordinatewise dominance on the truth's support — #260's Proposition 3.2.  This is
the sense in which #260 is the `o_min = L − 1` special case of the general
criterion. -/
theorem fixedLengthRecovery (A B : ι → ℕ) (G : ℕ) (hG : 0 < G) :
    (∀ x : ι → ℕ, (∀ i, 0 < x i → 0 < A i) → 0 < ∑ i, x i →
        crossLik B x G ≤ crossLik A x G) ↔
      ∀ i, 0 < A i → B i ≤ A i := by
  have hiff := varLengthCriterion A B G G
  constructor
  · intro h i hAi
    have hBG := hiff.mp (fun x hx hn => h x hx hn) i hAi
    exact Nat.le_of_mul_le_mul_right hBG hG
  · intro h x hx hn
    have hcrit : ∀ i, 0 < A i → B i * G ≤ A i * G := by
      intro i hAi
      exact Nat.mul_le_mul_right G (h i hAi)
    exact hiff.mpr hcrit x hx hn

omit [Fintype ι] [DecidableEq ι] in
/-- **Density formulation.**  The variable-length criterion is the per-class density
bound `B i / N ≤ A i / G`: the candidate's class density never exceeds the truth's.
This is the form in which the criterion is a *structural* condition on the
candidate's normalized spectrum. -/
theorem densityDominance (A B : ι → ℕ) (G N : ℕ) (hG : 0 < G) (hN : 0 < N) :
    (∀ i, 0 < A i → B i * G ≤ A i * N) ↔
      ∀ i, 0 < A i → (B i : ℚ) / N ≤ (A i : ℚ) / G := by
  constructor
  · intro h i hAi
    have hle := h i hAi
    rw [div_le_div_iff₀ (by exact_mod_cast hN) (by exact_mod_cast hG)]
    exact_mod_cast hle
  · intro h i hAi
    have hle := h i hAi
    rw [div_le_div_iff₀ (by exact_mod_cast hN) (by exact_mod_cast hG)] at hle
    exact_mod_cast hle

/-! ## The flow-domain criterion (binomial, external N = G)

When the genome length is fixed externally at `N = G` (the §6.1 separable
binomial with known genome size), the objective comparison between a candidate
with throughput `B` and the truth with throughput `A` reduces to the product
comparison `∏ᵢ Bᵢ^xⁱ ≤ ∏ᵢ Aᵢ^xⁱ`, because the binomial coefficients and the
common `N` cancel.  The truth is then sample-uniformly maximal over the §6.2
feasible flows **iff** no admissible flow throughput strictly dominates the
truth spectrum on an observed class.

This is the flow-domain analogue of `fixedLengthRecovery`: at external `N = G`
the criterion is coordinatewise dominance, and the §6.2 vertex lower bound `1`
on the observed reads forces the candidate support to contain the truth's
support, so dominance on the truth's support is the binding condition. -/

/-- The §6.1 separable binomial factor for class `i` with external `N = G`:
`B i ^ x i`.  With `N = G` fixed, the binomial coefficients `C(n, x i)` and the
length factors `(G/N)^n = 1` cancel between candidates, so the comparison is
exactly the product of these factors. -/
def flowFactor (B x : ι → ℕ) (i : ι) : ℕ := (B i) ^ (x i)

/-- The flow-domain objective: `∏ᵢ Bᵢ^xⁱ`, the exact binomial likelihood up to
the candidate-independent factors. -/
def flowLik (B x : ι → ℕ) : ℕ := ∏ i, flowFactor B x i

/-- **Flow-domain maximality criterion.**  With external `N = G` fixed, the
truth is sample-uniformly maximal over the §6.2 feasible flows **iff** no
candidate throughput `B` has `B i > A i` for some `i ∈ supp A`.

The `⟸` direction is the concentrated-sample argument: if `B i > A i` for some
`i ∈ supp A`, the sample `x = e_i` makes `B` strictly better.  The `⟹`
direction is coordinatewise dominance: if `B i ≤ A i` for all `i ∈ supp A`, then
`∏ Bᵢ^xⁱ ≤ ∏ Aᵢ^xⁱ` for every supported `x`. -/
theorem flow_dominance_criterion (A B : ι → ℕ) :
    (∀ x : ι → ℕ, (∀ i, 0 < x i → 0 < A i) →
        flowLik B x ≤ flowLik A x) ↔
      ∀ i, 0 < A i → B i ≤ A i := by
  constructor
  · intro h i hAi
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
    have hineq := h x hxsupp
    have hBx : flowLik B x = B i := by
      unfold flowLik flowFactor
      rw [Fintype.prod_eq_single i (fun j hj => by simp [x, Pi.single_eq_of_ne hj])]
      simp [x]
    have hAx : flowLik A x = A i := by
      unfold flowLik flowFactor
      rw [Fintype.prod_eq_single i (fun j hj => by simp [x, Pi.single_eq_of_ne hj])]
      simp [x]
    rw [hBx, hAx] at hineq
    exact hineq
  · intro h x hx
    apply Finset.prod_le_prod
    intro i _
    by_cases hxi : 0 < x i
    · exact pow_le_pow_left' (h i (hx i hxi)) (x i)
    · have hz : x i = 0 := Nat.eq_zero_of_not_pos hxi
      simp [hz, flowFactor]

/-! ## The half-integral relaxation gap

The §6.2 flow domain admits half-integral flows (the LP relaxation of the
integer flow problem).  At `o_min < L − 1` the half-integral optimum can
strictly beat every integral maximizer, so the integer flow constraint is
binding.  The witness is the `AAATT` instance at `o_min = 1`: with external
`N = 5` and observed counts `x = (AAA:2, AAT:1, TAA:1)`, the AAA binomial
factor `d²(5−d)²` is maximized at `d = 2, 3` (value `36`) among integers but
at `d = 5/2` (value `625/16`) among half-integers, so the half-integral flow
`h = (5/2, 1, 1)` beats the integral maximizers by `625/576`. -/

/-- The AAA binomial factor `d²(5−d)²` at the half-integral value `d = 5/2`:
`625/16`. -/
theorem half_integral_factor : (5 / 2 : ℚ) ^ 2 * (5 - 5 / 2 : ℚ) ^ 2 = 625 / 16 := by
  norm_num

/-- The AAA binomial factor at the integral maximizers `d = 2` and `d = 3`:
`36`. -/
theorem integral_factor_2 : (2 : ℚ) ^ 2 * (5 - 2 : ℚ) ^ 2 = 36 := by norm_num

theorem integral_factor_3 : (3 : ℚ) ^ 2 * (5 - 3 : ℚ) ^ 2 = 36 := by norm_num

/-- **The half-integral gap.**  The half-integral flow `h = (5/2, 1, 1)` beats
the integral maximizer `f₂ = (2, 1, 1)` by the ratio `625/576 > 1` on the
observed sample `x = (AAA:2, AAT:1, TAA:1)`. -/
theorem half_integral_gap :
    (625 / 16 : ℚ) / 36 = 625 / 576 := by norm_num

theorem half_integral_beats_integral : (625 / 576 : ℚ) > 1 := by norm_num

/-! ## The rescaling tie at variable length

At variable length the `k`-fold cover `S^k` of a truth `S` has spectrum `k·A`
and length `k·G`, so its normalized spectrum equals the truth's and it ties on
every sample under the exact objective.  Hence uniqueness of the normalized
spectrum is impossible at variable length — a phenomenon with no full-overlap
analogue, because at full overlap the length is fixed by the throughput. -/

/-- **Rescaling tie.**  For a truth with counts `A` and length `G`, the `k`-fold
cover has counts `k·A` and length `k·G`, and ties with the truth on every
supported sample: `crossLik (k·A) x G = crossLik A x (k·G)`. -/
theorem rescaling_tie (A : ι → ℕ) (G : ℕ) (k : ℕ)
    (x : ι → ℕ) :
    crossLik (fun i => k * A i) x G = crossLik A x (k * G) := by
  unfold crossLik
  simp [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, mul_pow, mul_comm, mul_assoc]

/-! ## Concrete finite witnesses

The class space is `Fin 3` with coordinates `(W1, W2, W3)` standing for the three
molecule classes of a length-`2` read over `{A,T}`: `W1 = {AA,TT}`, `W2 = {AT}`,
`W3 = {TA}`.  The truth `AATT` has counts `(2,1,1)` and length `G = 4`. -/

/-- Truth `AATT` over the class space `(W1,W2,W3)`: counts `(2,1,1)`, length `4`. -/
def aattA : Fin 3 → ℕ := ![2, 1, 1]

/-- A longer candidate `AATATT` (length `6`) with counts `(2,2,2)`: it violates the
density bound at `W2` (`2·4 = 8 > 1·6 = 6`) and therefore beats the truth on the
concentrated sample `x = e_{W2}`. -/
def aatattB : Fin 3 → ℕ := ![2, 2, 2]

theorem aattA_sum : ∑ i, aattA i = 4 := by decide

theorem aatattB_length : 6 = 6 := by decide

/-- The density bound is violated at `W2`: `B(W2)·G = 2·4 = 8 > 6 = 1·6 =
A(W2)·N`. -/
theorem stretch_violates : ¬ (aatattB 1 * 4 ≤ aattA 1 * 6) := by decide

/-- **The stretch witness.**  The longer candidate `AATATT` beats the truth `AATT`
on the concentrated sample `x = e_{W2}`: `crossLik B x G = 8 > 6 = crossLik A x N`.
This is the variable-length phenomenon that has no full-overlap analogue. -/
theorem stretch_beats :
    crossLik aatattB (Pi.single 1 1) 4 > crossLik aattA (Pi.single 1 1) 6 := by
  unfold crossLik
  simp [Pi.single]
  decide

/-- **The dilution witness.**  A candidate with counts `(1,2,2)` (genome length
`G = 5`) but a longer genome (`N = 6`) is strictly worse on the sample
`x = (1,1,1)`: `crossLik A x G = 500 < 864 = crossLik A x N`.  This instantiates
`dilution` with a count vector that is not the truth `AATT`'s spectrum, showing
the length-punishment phenomenon is general. -/
def dilA : Fin 3 → ℕ := ![1, 2, 2]

theorem dilution_witness :
    crossLik dilA ![1, 1, 1] 5 < crossLik dilA ![1, 1, 1] 6 := by
  unfold crossLik
  decide

end AssemblyP1.GeneralBidirectedFlowML
