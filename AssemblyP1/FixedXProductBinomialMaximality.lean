import AssemblyP1.ProductBinomialRigidityNecessity

/-!
# Fixed-`x` maximality for the MB09 §6.1 product-binomial surrogate (#259 axis A)

Medvedev–Brudno 2009 §6.1 score a candidate spectrum `B : E → ℕ` over a fixed
finite read-type universe `E` by a **product of marginal binomials** with a
fixed external genome length `N`.  Dropping the candidate-constant binomial
coefficients `∏_e choose(n, x_e)` and the normalization `N ^ (-n · card E)`, the
candidate-dependent integer numerator is

```
effectiveProduct N B x = ∏_e (effectiveWeight N B e) ^ (x e),
effectiveWeight N B e = B e * ∏_{j ≠ e} (N - B j).
```

The extra `(N - B j) ^ (n - x j)` factors of the *unobserved* coordinates are
exactly what separates this surrogate from the exact joint multinomial read
likelihood of `#256`.

## Axis A: a fixed observed count vector `x`

Board `#259` distinguishes two regimes.  Axis **B** (`robust_iff_unique`, the
merged `AssemblyP1/ProductBinomialRigidityNecessity`) asks for maximality over
*every* covered sample at once and classifies it by rigidity.  Axis **A**, this
module, fixes a single observed count vector `x` with `n = ∑ x` and asks when the
truth `A` is an ML maximizer **at that `x`**.

The key structural fact is that at a fixed `x` the surrogate is **separable**:
the candidate-dependent numerator factors over read types as a product of
independent per-type binomial likelihoods

```
effectiveProduct N B x = ∏_e B e ^ (x e) * (N - B e) ^ (n - x e)   (n = ∑ x).
```

Consequently the fixed-`x` comparison `A`-versus-`B` is exactly the product
inequality `∏_e B e ^ (x e) (N - B e) ^ (n - x e) ≤ ∏_e A e ^ (x e)
(N - A e) ^ (n - x e)`.  This is a genuine necessary-and-sufficient criterion
(`fixedX_le_iff`), and its natural sufficient strengthening is the
**coordinatewise** inequality (`fixedX_le_of_coordwise`).  Pointwise
effective-weight domination is a special sufficient condition
(`fixedX_le_of_effectiveWeight_le`) that is *strictly stronger* than fixed-`x`
maximality at a single sample: the counterexample `fixedX_weaker_than_pointwise`
exhibits a positive equal-total pair with `q_B 0 > q_A 0` on which `A`
nevertheless wins at the covered sample `x = (2,2)`.  Quantifying the fixed-`x`
criterion over *all* covered samples collapses it to the pointwise inequality
(`sampleUniform_iff_pointwise`), which is the axis-A-to-axis-B bridge and the
fixed-`x` content of `robust_iff_unique`.

## Scope

* Objective: MB09 §6.1 fixed-external-`N` product-binomial **surrogate**.
* Candidate length: same-length, fixed finite universe `E`.
* Normalization `N`: fixed external; omitted candidate-constant factors cancel.
* Support: arbitrary (the criterion and counterexample use full-support
  candidates; `sampleUniform_iff_pointwise` is over a positive universe).
* Sample size `n = ∑ x`: free (fixed by `x`); `n` need not equal `N`.
* Still open: variable genome length, §6.2 bidirected flows (`#260`/`#261`),
  and a full-class fixed-`x` maximizer classification for non-integral
  empirical frequencies.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset BigOperators

namespace AssemblyP1.FixedXProductBinomialMaximality

open AssemblyP1.FixedNBinomialEffectiveWeights

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- **Fixed-`x` maximality.**  At the single observed count vector `x`, the
truth `A` scores at least as high as every candidate in the class `F`.  This is
axis A of `#259`: the sample-uniform (axis B) predicate is
`∀ x, (∀ e, A e ≤ x e) → FixedXMax N A F x`. -/
def FixedXMax (N : ℕ) (A : E → ℕ) (F : Set (E → ℕ)) (x : E → ℕ) : Prop :=
  ∀ B ∈ F, effectiveProduct N B x ≤ effectiveProduct N A x

/-- **Separable form of the fixed-`x` objective.**  At a fixed observed count
vector `x` with `n = ∑ x`, the candidate-dependent numerator is the product over
read types of independent per-type binomial likelihoods
`B e ^ (x e) * (N - B e) ^ (n - x e)`.  The exponent `n - x e` on `N - B e` is
the retained `(1 - B e / N) ^ (n - x e)` factor of the MB09 §6.1 surrogate,
absent from the exact multinomial `#256`. -/
theorem fixedX_eq_separable (N n : ℕ) (B x : E → ℕ) (hx : ∑ e, x e = n) :
    effectiveProduct N B x
      = ∏ e, B e ^ (x e) * (N - B e) ^ (n - x e) :=
  effectiveProduct_eq_binomialNumerator N n B x hx

/-- **Exact fixed-`x` criterion (necessary and sufficient).**  At the fixed
observed count vector `x` (`n = ∑ x`), the truth `A` scores at least as high as
the competitor `B` if and only if the product of per-type binomial factors for
`A` dominates that for `B`.  This is the fixed-`x` classification: the
inequality is the whole criterion. -/
theorem fixedX_le_iff (N n : ℕ) (A B x : E → ℕ) (hx : ∑ e, x e = n) :
    effectiveProduct N B x ≤ effectiveProduct N A x ↔
      ∏ e, B e ^ (x e) * (N - B e) ^ (n - x e)
        ≤ ∏ e, A e ^ (x e) * (N - A e) ^ (n - x e) := by
  rw [fixedX_eq_separable N n B x hx, fixedX_eq_separable N n A x hx]

/-- **Fixed-`x` sufficient inequality (coordinatewise).**  If every per-type
binomial factor of `B` is dominated by the corresponding factor of `A`, then
`A` beats `B` at the fixed sample `x`.  This is the sharp sufficient condition
specialized to the separable fixed-`x` objective. -/
theorem fixedX_le_of_coordwise (N n : ℕ) (A B x : E → ℕ) (hx : ∑ e, x e = n)
    (h : ∀ e, B e ^ (x e) * (N - B e) ^ (n - x e)
        ≤ A e ^ (x e) * (N - A e) ^ (n - x e)) :
    effectiveProduct N B x ≤ effectiveProduct N A x := by
  rw [fixedX_le_iff N n A B x hx]
  exact Finset.prod_le_prod (fun e _ => h e)

/-- **Pointwise effective-weight domination implies fixed-`x` maximality.**  If
`q_B ≤ q_A` on every read type then `A` beats `B` at every fixed sample.  This
is the sufficient condition that the sample-uniform criterion makes necessary
(`sampleUniform_iff_pointwise`); at a *single* fixed `x` it is not necessary
(`fixedX_weaker_than_pointwise`). -/
theorem fixedX_le_of_effectiveWeight_le (N : ℕ) (A B x : E → ℕ)
    (h : ∀ e, effectiveWeight N B e ≤ effectiveWeight N A e) :
    effectiveProduct N B x ≤ effectiveProduct N A x :=
  Finset.prod_le_prod (fun e _ => Nat.pow_le_pow_left (h e) (x e))

/-- **The fixed-`x` criterion is strictly weaker than pointwise domination.**
The positive total-`4` vectors `A = (2,2)` and `B = (3,1)` over `Fin 2` have
`q_B 0 = 9 > 4 = q_A 0`, so `B` is *not* pointwise dominated.  Yet at the
covered sample `x = (2,2)` the truth `A` scores `256` against `B`'s `81`.  Hence
pointwise effective-weight domination is sufficient but not necessary for
fixed-`x` maximality: a truth can win at one fixed covered sample while failing
to be a sample-uniform maximizer. -/
theorem fixedX_weaker_than_pointwise :
    ∃ (N : ℕ) (A B x : Fin 2 → ℕ),
      (∀ e, 0 < A e) ∧ (∀ e, 0 < B e) ∧
      (∑ e, A e = N) ∧ (∑ e, B e = N) ∧
      (∀ e, A e ≤ x e) ∧
      effectiveProduct N B x ≤ effectiveProduct N A x ∧
      ¬ (∀ e, effectiveWeight N B e ≤ effectiveWeight N A e) := by
  refine ⟨4, ![2, 2], ![3, 1], ![2, 2], by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

/-- **Reduction of sample-uniform maximality to the fixed-`x` criterion.**  For
a positive truth `A` and positive competitor `B` of the same total `N` with
every coordinate below `N`, maximality over *every* covered sample collapses to
a single pointwise inequality `q_B ≤ q_A` on every read type.  Equivalently, `A`
is a fixed-`x` maximizer at every covered sample iff it is pointwise dominant;
this is the axis-A-to-axis-B bridge and the fixed-`x` engine of
`ProductBinomialRigidityNecessity.robust_iff_unique`. -/
theorem sampleUniform_iff_pointwise (N : ℕ) (A B : E → ℕ)
    (hA : ∀ e, 0 < A e) (hB : ∀ e, 0 < B e)
    (hAN : ∀ e, A e < N) (hBN : ∀ e, B e < N)
    (hAtot : ∑ e, A e = N) (hBtot : ∑ e, B e = N) :
    (∀ x : E → ℕ, (∀ e, A e ≤ x e) →
        effectiveProduct N B x ≤ effectiveProduct N A x) ↔
      (∀ e, effectiveWeight N B e ≤ effectiveWeight N A e) := by
  have hqA : ∀ e, 0 < effectiveWeight N A e :=
    AssemblyP1.ProductBinomialRigidityNecessity.effectiveWeight_pos hA hAN
  have hiff := AssemblyP1.CoveredBinomialWeightsIff.covered_effectiveProduct_le_iff
    N A B hA hqA
  constructor
  · intro h
    rcases hiff.mp h with h0 | hle
    · obtain ⟨e, he⟩ := h0
      exact absurd
        (AssemblyP1.ProductBinomialRigidityNecessity.effectiveWeight_pos hB hBN e)
        (by rw [he]; exact Nat.lt_irrefl 0)
    · exact hle
  · intro h x _
    exact fixedX_le_of_effectiveWeight_le N A B x h

/-- **Concentrated-sample classification.**  When the fixed sample observes only
one read type `e` (`x = c · δ_e` with `c > 0`), the exact fixed-`x` criterion
collapses to a *single* effective-weight comparison: `A` beats `B` at `x` iff
`q_B e ≤ q_A e`.  So a truth that fails pointwise domination at other coordinates
can still be a fixed-`x` maximizer at a concentrated sample. -/
theorem fixedX_concentrated_iff (N c : ℕ) (hc : 0 < c) (A B : E → ℕ) (e : E) :
    effectiveProduct N B (fun j => if j = e then c else 0)
        ≤ effectiveProduct N A (fun j => if j = e then c else 0) ↔
      effectiveWeight N B e ≤ effectiveWeight N A e := by
  have hB : effectiveProduct N B (fun j => if j = e then c else 0)
      = effectiveWeight N B e ^ c := by
    rw [effectiveProduct,
      Finset.prod_eq_single_of_mem e (Finset.mem_univ e)
        (fun b _ hb => by simp [hb])]
    simp
  have hA : effectiveProduct N A (fun j => if j = e then c else 0)
      = effectiveWeight N A e ^ c := by
    rw [effectiveProduct,
      Finset.prod_eq_single_of_mem e (Finset.mem_univ e)
        (fun b _ hb => by simp [hb])]
    simp
  rw [hB, hA, Nat.pow_le_pow_iff_left (show c ≠ 0 by omega)]

/-! ## A finite full-class fixed-`x` classification

The exact criterion is usable for concrete instances.  On `Fin 2` with `N = 4`
and the complete-support sample `x = (2,2)`, the positive total-`4` candidates
are exactly `(1,3)`, `(2,2)`, `(3,1)`; the truth `(2,2)` beats all of them,
while every other truth is beaten by `(2,2)`.  This is a full-class fixed-`x`
maximality classification for the smallest nontrivial instance. -/

/-- The positive total-`4` count vectors over `Fin 2` are exactly `(1,3)`,
`(2,2)`, `(3,1)`. -/
theorem fin2_total4_enum (B : Fin 2 → ℕ) (hpos : ∀ e, 0 < B e)
    (htot : ∑ e, B e = 4) :
    B = ![1, 3] ∨ B = ![2, 2] ∨ B = ![3, 1] := by
  have hsum : B 0 + B 1 = 4 := by simpa [Fin.sum_univ_two] using htot
  have h0 := hpos 0
  have h1 := hpos 1
  have key : (B 0 = 1 ∧ B 1 = 3) ∨ (B 0 = 2 ∧ B 1 = 2)
      ∨ (B 0 = 3 ∧ B 1 = 1) := by omega
  rcases key with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · left; funext i; fin_cases i <;> simp_all
  · right; left; funext i; fin_cases i <;> simp_all
  · right; right; funext i; fin_cases i <;> simp_all

/-- **Full-class fixed-`x` classification on the smallest instance.**  At the
complete-support sample `x = (2,2)` over `Fin 2` with `N = 4`, the truth
`(2,2)` is a fixed-`x` maximizer over the entire positive total-`4` class, and
every other positive total-`4` truth is strictly beaten at `x` by `(2,2)`. -/
theorem fixedX_fin2_full_class :
    (∀ B : Fin 2 → ℕ, (∀ e, 0 < B e) → (∑ e, B e = 4) →
        effectiveProduct 4 B ![2, 2] ≤ effectiveProduct 4 ![2, 2] ![2, 2]) ∧
      (∀ A : Fin 2 → ℕ, (∀ e, 0 < A e) → (∑ e, A e = 4) → A ≠ ![2, 2] →
        ∃ B : Fin 2 → ℕ, (∀ e, 0 < B e) ∧ (∑ e, B e = 4) ∧
          effectiveProduct 4 A ![2, 2] < effectiveProduct 4 B ![2, 2]) := by
  constructor
  · intro B hpos htot
    rcases fin2_total4_enum B hpos htot with h | h | h
    · subst h; decide
    · subst h; decide
    · subst h; decide
  · intro A hpos htot hne
    rcases fin2_total4_enum A hpos htot with h | h | h
    · subst h; exact ⟨![2, 2], by decide, by decide, by decide⟩
    · exact absurd h hne
    · subst h; exact ⟨![2, 2], by decide, by decide, by decide⟩

end AssemblyP1.FixedXProductBinomialMaximality
