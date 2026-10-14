# Covered-sample maximality for the MB09 §6.1 product-binomial surrogate (board issue #259)

_Status: kernel-checked Lean theorem (`AssemblyP1/CoveredBinomialWeightsIff.lean`),
imported by `AssemblyP1.lean`, with `#print axioms` audit
(`CoveredBinomialWeightsIffAudit.lean`) reporting only `propext`,
`Classical.choice`, `Quot.sound`.  Independent exact-rational Python
verification in `scripts/verify_covered_binomial_weights_259.py`.  This note
records a scoped finite-weight classification; it does not close the full
board issue #259, which still asks for the general source-faithful
bidirected-flow statement of #260/#261._

## 1. Model, and what is *not* claimed

Medvedev and Brudno 2009, J Comput Biol, §6.1 model the read-count objective as
a **product of binomial marginals** with a fixed external genome length `N`
(<https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/>).  This is a separable
optimization *surrogate*, and it is deliberately distinct from two other
objects:

* the **exact joint multinomial** read-count likelihood of the observed count
  vector (the subject of #256), and
* the **§6.2 bidirected-flow** candidate universe over molecule types
  (#260/#261).

For a fixed finite read-type universe `U` (the full modeled molecule class set;
`4 ^ k` classes for read length `k`) and a candidate spectrum `B : U → ℕ`, the
candidate-dependent integer numerator of the §6.1 surrogate is exactly

```
effectiveProduct N B x = ∏_{i : U} (effectiveWeight N B i) ^ (x i),
effectiveWeight N B i = B i * ∏_{j : U, j ≠ i} (N - B j).
```

The second product runs over **all** modeled classes, including classes with
`x j = 0`; this is the extra `(1 - d(w)/N) ^ (n - x(w))` factor that separates
the binomial surrogate from the exact multinomial likelihood.  The omitted
factors (`∏_i choose(n, x_i)` and `N ^ (- n * card U)`) are candidate-independent
and cancel in every comparison.

The theorems below are statements about this integer surrogate.  They are
**not** statements about the true joint multinomial likelihood and **not**
statements about §6.2 flows.

## 2. The classification

Fix a coverage baseline `a : E → ℕ` with `a e > 0` for every `e`, and consider
the set of sample count vectors with `a e ≤ x e` for every modeled type (the
sample size `n = ∑ x` is otherwise free).

> **Theorem (`covered_product_le_iff_zero_or_pointwise`).**
> For a finite `E`, weights `qA qB : E → ℕ` with `qA e > 0` for all `e`, and a
> strictly positive baseline `a`,
> `(∀ x, (∀ e, a e ≤ x e) → ∏ qB e ^ x e ≤ ∏ qA e ^ x e)`
> **iff** `(∃ e, qB e = 0) ∨ (∀ e, qB e ≤ qA e)`.

The two directions:

* **(⇐)** If `qB e ≤ qA e` everywhere, pointwise power monotonicity gives the
  product bound.  If `qB e0 = 0`, then `a e0 > 0` forces `x e0 ≥ 1` on every
  covered sample, so the competitor's product has a factor `0 ^ (x e0) = 0` and
  is `≤` the truth's product.
* **(⇒)** Suppose no `qB e` is zero and some `qA e0 < qB e0`.  Flooding
  coordinate `e0` with `t` mandatory reads (`x e0 = a e0 + t`, other
  coordinates at the baseline) turns the score ratio into a positive constant
  times `(qB e0 / qA e0) ^ t`; the integer growth lemma `pow_add_growth`
  (`b ^ (k+1) ≥ c ^ (k+1) + (k+1) * c ^ k` for `b ≥ c + 1`) makes this exceed
  `1` for a finite `t`.  Hence the competitor beats the truth on some covered
  sample, contradicting the hypothesis.

This is the finite weight-level statement behind "truth is a maximizer for
every realizable complete-support sample".  The baseline `a` is *mandatory
coverage*: every modeled type in the support is observed at least once.

## 3. Ambient full-universe support (the `#259` scope fix)

The same-support specialization `covered_effectiveProduct_le_iff` fixes `E` to
be exactly the true support and evaluates `effectiveWeight N ·` over `E` only;
it therefore drops the `(N - B j)` factors of **unobserved** classes and cannot
represent a candidate that puts mass on a class outside the truth's support.
The ambient version keeps the full universe:

> **Theorem (`covered_ambient_effectiveProduct_le_iff`).**
> For `A B : U → ℕ` with truth effective weights positive on `A`'s support,
> `(∀ x, (∀ i, A i ≤ x i) → (∀ j, A j = 0 → x j = 0) →
> effectiveProduct N B x ≤ effectiveProduct N A x)`
> **iff**
> `(∃ i, 0 < A i ∧ effectiveWeight N B i = 0) ∨
> (∀ i, 0 < A i → effectiveWeight N B i ≤ effectiveWeight N A i)`.

Here `q_i(A)` and `q_i(B)` are computed **over the whole universe `U`**, so
every unobserved `(N - B j)` factor is retained, and the candidate may put mass
on classes outside the truth's support.  The reduction uses the support
adapter `effectiveProduct_eq_trueSupportProduct`: for a sample supported on the
truth support, the whole-universe product collapses to the product over the
true-supported coordinates (off-support counts are `0` and `q ^ 0 = 1`).  The
generic criterion is then run on the subtype `{i : U // 0 < A i}`.

`covered_start_samples_effectiveProduct_le_iff` instantiates the same-support
form with `FiniteStartCoverage.coverage_of_type_budget`, so a "covered sample"
is one that visits every true genome start at least once.

## 4. New-support examples

`newsupport_dominated` and `newsupport_defeats` (both checked by `decide`)
exhibit candidates whose support lies **outside** the truth's support on
`U = Fin 2`:

| truth `A` | candidate `B` | `N` | `q_0(A)` | `q_0(B)` | outcome |
|-----------|---------------|-----|----------|----------|---------|
| `(2, 0)`  | `(1, 1)`      | 4   | `2 * 4 = 8` | `1 * (4 - 1) = 3` | truth dominates (dominance branch) |
| `(2, 0)`  | `(3, 1)`      | 4   | `8`      | `3 * (4 - 1) = 9` | truth fails (no zero, `q_0(B) > q_0(A)`) |

The unobserved class-`1` factor `(N - B 1)` is exactly what makes the first
comparison `3` (dominated) rather than `1`, and the second comparison `9`
(defeating) rather than `3`.  Both outcomes are attained with genuinely new
support, so the ambient classification is non-vacuous in the scope the reviewer
flagged.

Non-vacuity of the generic criterion is also recorded directly:
`nonvacuity_holds` (equal positive weights), `nonvacuity_zero` (zero-weight
branch), and `nonvacuity_left_fails` (a competitor genuinely beats the truth on
a covered sample).

## 5. Scope matrix

| Item | Covered by this module | Still open |
|------|------------------------|------------|
| Objective | MB09 §6.1 fixed-external-`N` **product-binomial surrogate** (integer numerator) | true joint multinomial (#256); §6.2 bidirected flows (#260/#261) |
| Candidate length | same-length, fixed finite universe `U` | variable genome length |
| Normalization `N` | fixed external `N`; omitted `∏ choose(n, x_i)` and `N ^ (-n·card U)` are candidate-independent | — |
| Support | truth support `S0 = {i : 0 < A i}`; candidate may have new/zero support on `U`; effective weights computed over full `U` | classes outside the modeled `U` |
| Sample size `n` | free (`n = ∑ x`), bounded below by the baseline `∑ a` | — |
| Coverage | mandatory: every true-supported coordinate observed (`x_i ≥ A_i > 0`, `x_j = 0` off support) | weaker information-theoretic feasibility events |
| Boundary probabilities | zero-weight candidates handled (score `0`); truth weights required positive | `qA` zero on the true support |
| Graph rigidity | not addressed here; the same-support iff specializes to spectrum rigidity under the merged `#259(B)` hypotheses | rigidity as a *necessary* condition for general sample-uniform maximality |

## 6. Independent verification

`scripts/verify_covered_binomial_weights_259.py` (exact `Fraction`/`int`
arithmetic) independently checks, without importing Lean:

1. a brute-force census of the generic iff over small finite `E` and small
   weight/baseline ranges (both directions, including the zero branch);
2. the flooding inequality `qB e0 ^ (a e0 + t) > Q * qA e0 ^ (a e0 + t)` for
   the explicit `t = (Q - 1) * qA e0 + 1`;
3. the two new-support examples of §4, including the `(N - B j)` factors.

The Lean module is the authoritative kernel-checked artifact; the script is
bounded computational evidence that the arithmetic and the iff are correctly
encoded.
