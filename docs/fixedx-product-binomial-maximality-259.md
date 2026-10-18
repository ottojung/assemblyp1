# Fixed-`x` maximality for the MB09 §6.1 product-binomial surrogate (board issue #259, axis A)

_Status: kernel-checked Lean theorem
(`AssemblyP1/FixedXProductBinomialMaximality.lean`, axiom audit in
`AssemblyP1/FixedXProductBinomialMaximalityAudit.lean` reporting only
`propext`, `Classical.choice`, `Quot.sound`), imported by `AssemblyP1.lean`,
with independent exact-arithmetic verification in
`scripts/verify_fixedx_product_binomial_259.py`._

This note closes the **fixed-`x` axis (A)** of the `#259` classification for the
Medvedev–Brudno 2009 §6.1 fixed-external-`N` product-binomial surrogate.  The
sample-uniform axis (B) was closed separately in
`AssemblyP1/ProductBinomialRigidityNecessity.lean` (`robust_iff_unique` plus the
sufficiency refutation `newsupport_rigid_not_maximal`); this module treats the
distinct question of maximality **at one fixed observed count vector `x`**.

## 1. Model

Medvedev and Brudno 2009, J Comput Biol, §6.1 model the read-count objective as
a **product of marginal binomials** with a fixed external genome length `N`.
For a fixed finite read-type universe `E` and candidate spectrum `B : E → ℕ`,
the candidate-dependent integer numerator is

```
q_e(B)          = B e * ∏_{j : E, j ≠ e} (N - B j)          (effective weight)
F_B(x)          = ∏_{e : E} q_e(B) ^ (x e)                  (effective product)
```

The second product defining `q_e(B)` runs over **all** modeled read types,
including zero-observed ones; this is the extra `(1 - B j / N) ^ (n - x j)`
factor that separates the surrogate from the exact joint multinomial read
likelihood of `#256`.  The omitted candidate-constant factors
`∏_e choose(n, x_e)` and `N ^ (-n · card E)` cancel in every comparison.

* **Candidate length:** same-length, fixed finite universe `E`.
* **Normalization `N`:** fixed external; omitted candidate-constant factors
  cancel.
* **Support:** arbitrary; the criterion and the separation witness use
  full-support candidates.
* **Sample size `n = ∑ x`:** fixed by `x`; `n` need not equal `N`.

**Difference from the exact objective (`#256`).**  At a fixed `x` the exact
multinomial numerator is `∏_e B e ^ (x e)` (no unobserved factors).  The §6.1
surrogate additionally multiplies each coordinate by `(N - B e) ^ (n - x e)`,
i.e. retains `(1 - B e / N) ^ (n - x e)` for **every** class, including classes
with `x e = 0`.  Those extra factors are exactly why the two objectives can
rank candidates differently on the same sample (see the merged `#256` ranking
inversion).

## 2. The fixed-`x` objective is separable

> **Theorem (`fixedX_eq_separable`).** For `n = ∑ x`,
> `F_B(x) = ∏_e B e ^ (x e) * (N - B e) ^ (n - x e)`.

This is the retained `(N - B e) ^ (n - x e)` factor made explicit; it is the
integer identity `effectiveProduct_eq_binomialNumerator` of the merged
`FixedNBinomialEffectiveWeights`, restated at the fixed-`x` interface.

## 3. The exact fixed-`x` criterion (necessary and sufficient)

> **Theorem (`fixedX_le_iff`).** At the fixed observation `x` (`n = ∑ x`),
> `F_B(x) ≤ F_A(x)` **iff**
> `∏_e B e ^ (x e) (N - B e) ^ (n - x e) ≤ ∏_e A e ^ (x e) (N - A e) ^ (n - x e)`.

This is the whole classification of axis A for a single competitor: at a fixed
`x` the criterion is the product of independent per-type binomial factors, not a
coordinatewise condition.  The natural sufficient strengthening is:

> **Theorem (`fixedX_le_of_coordwise`).** If every per-type factor of `B` is
> dominated by the corresponding factor of `A`,
> `B e ^ (x e) (N - B e) ^ (n - x e) ≤ A e ^ (x e) (N - A e) ^ (n - x e)` for
> every `e`, then `F_B(x) ≤ F_A(x)`.

Pointwise effective-weight domination is the special sufficient condition used
by the sample-uniform axis:

> **Theorem (`fixedX_le_of_effectiveWeight_le`).** If `q_e(B) ≤ q_e(A)` for
> every `e`, then `F_B(x) ≤ F_A(x)` for every fixed `x`.

## 4. The fixed-`x` criterion is strictly weaker than sample-uniform maximality

> **Theorem (`fixedX_weaker_than_pointwise`).** There are positive equal-total
> vectors `A = (2,2)`, `B = (3,1)` over `Fin 2` with `N = 4` and a **covered**
> sample `x = (2,2)` such that `F_B(x) = 81 ≤ 256 = F_A(x)` while
> `q_0(B) = 9 > 4 = q_0(A)`.

So pointwise effective-weight domination is **sufficient but not necessary**
for fixed-`x` maximality: a truth can win at one fixed covered sample while
failing to be a sample-uniform maximizer.  The two regimes are genuinely
different.

Quantifying the fixed-`x` criterion over *all* covered samples recovers the
sample-uniform axis and the pointwise condition:

> **Theorem (`sampleUniform_iff_pointwise`).** For positive `A`, `B` of the same
> total `N` with every coordinate below `N`,
> `(∀ x, (∀ e, A e ≤ x e) → F_B(x) ≤ F_A(x)) ↔ (∀ e, q_e(B) ≤ q_e(A))`.

This is the axis-A-to-axis-B bridge: the sample-uniform maximality of
`robust_iff_unique` is exactly the pointwise special case of the fixed-`x`
criterion, and is strictly stronger than fixed-`x` maximality at any single
sample.  (The zero-weight disjunct of the merged covered-sample iff is vacuous
here because a positive `B` with `B e < N` has `q_e(B) > 0`.)

## 5. Concrete fixed-`x` classifications

> **Theorem (`fixedX_concentrated_iff`).** If the sample observes only one type
> `e` (`x = c · δ_e`, `c > 0`), then `F_B(x) ≤ F_A(x)` **iff**
> `q_e(B) ≤ q_e(A)`.  The whole product collapses to a single effective-weight
> comparison.

> **Theorem (`fixedX_fin2_full_class`).** Over `Fin 2` with `N = 4` and the
> complete-support sample `x = (2,2)`, the positive total-`4` candidates are
> exactly `(1,3)`, `(2,2)`, `(3,1)`; the truth `(2,2)` beats all of them, and
> every other positive total-`4` truth is strictly beaten at `x` by `(2,2)`.
> This is a full-class fixed-`x` maximality classification for the smallest
> nontrivial instance.

## 6. Scope matrix

| Item | Covered by this module | Still open |
|------|------------------------|------------|
| Objective | MB09 §6.1 fixed-external-`N` **product-binomial surrogate** | true joint multinomial (`#256`); §6.2 bidirected flows (`#260`/`#261`) |
| Axis A | exact fixed-`x` criterion, coordinatewise and pointwise sufficient inequalities, strict separation from axis B, concentrated-sample iff | full-class fixed-`x` maximizer classification at **non-integral** empirical frequency `x_e N / n` |
| Axis B | reduction to the pointwise criterion (`sampleUniform_iff_pointwise`) | full new-support candidate class; variable genome length |
| Candidate length | same-length, fixed finite universe | variable genome length |
| Normalization `N` | fixed external | — |
| Support | arbitrary for the criterion and witness; positive for the axis-B bridge | rigidity sufficiency over new-support candidates |
| Sample size `n = ∑ x` | free; `n` need not equal `N` | weaker information-feasibility coverage events |
| Boundary probabilities | zero-observed factors retained exactly | `q_A` zero on the true support |

## 7. Independent verification

`scripts/verify_fixedx_product_binomial_259.py` (exact `int` arithmetic, no Lean
import) checks:

1. **Part A** — the separable identity `F_B(x) = ∏_e B e ^ (x e)
   (N - B e) ^ (n - x e)` on `144355` exhaustive-small and random cases, with a
   **non-vacuity mutation control** (the self-factor mutation of `eff_weight`
   must break the identity).
2. **Part B** — the exact fixed-`x` criterion on `40000` random cases.
3. **Part C** — the coordinatewise sufficient inequality on `7398` dominated
   cases.
4. **Part D** — the strict separation witness `A = (2,2)`, `B = (3,1)`,
   `x = (2,2)`, `N = 4`.
5. **Part E** — the full-class classification on `Fin 2`, `N = 4`, `x = (2,2)`.
6. **Part F** — the concentrated-sample iff on `20000` random cases.
7. **Part G** — a bounded census finding `6432` distinct positive equal-total
   pairs that win at the truth sample `x = A` while failing pointwise
   domination, confirming the gap is real.

The Lean module is the authoritative kernel-checked artifact; the script is
bounded computational evidence that the arithmetic and the classification are
correctly encoded.

### CI wiring

The `research-docs` job should run the verifier; the one-line step is

```yaml
      - name: Verify #259 fixed-x product-binomial criterion
        run: python3 scripts/verify_fixedx_product_binomial_259.py
```

The push credential used for this branch carries `repo` scope only, so a change
to `.github/workflows/ci.yml` is refused by GitHub ("refusing to allow an OAuth
App to create or update workflow … without `workflow` scope"); the wiring is
left as a one-line follow-up for a workflow-scoped token.  The `build` job
already compiles the module (library glob) and audits its axioms
(`--modules-from AssemblyP1`).  The verifier is deterministic and runs in under
two seconds.
