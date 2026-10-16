# Rigidity is necessary for sample-uniform maximality of the MB09 §6.1 product-binomial surrogate (board issue #259)

_Status: kernel-checked Lean theorem
(`AssemblyP1/ProductBinomialRigidityNecessity.lean`, axiom audit in
`AssemblyP1/ProductBinomialRigidityNecessityAudit.lean` reporting only
`propext`, `Classical.choice`, `Quot.sound`), imported by `AssemblyP1.lean`,
with independent exact-arithmetic verification in
`scripts/verify_product_binomial_rigidity_259.py`._

This note closes the **necessity direction** that the earlier `#259`
covered-sample classification left open: whether **graph rigidity is necessary
for sample-uniform maximality** of the Medvedev–Brudno 2009 §6.1 fixed-external-
`N` product-binomial surrogate.  It answers with a direct theorem (rigidity is
necessary) plus a smallest explicit counterexample to the converse
(sufficiency fails once new-support candidates are admitted).

## 1. Model and what is *not* claimed

Medvedev and Brudno 2009, J Comput Biol, §6.1 model the read-count objective as
a **product of marginal binomials** with a fixed external genome length `N`
(<https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/>).  For a fixed finite
read-type universe `E` and candidate spectrum `B : E → ℕ`, the candidate-
dependent integer numerator is

```
effectiveProduct N B x = ∏_{e : E} (effectiveWeight N B e) ^ (x e),
effectiveWeight N B e = B e * ∏_{j : E, j ≠ e} (N - B j).
```

The second product runs over **all** modeled classes, including zero-observed
ones; this is the extra `(1 - d(w)/N) ^ (n - x(w))` factor that separates the
surrogate from the exact joint multinomial read likelihood (the subject of
`#256`).  The omitted factors `∏_e choose(n, x_e)` and `N ^ (-n·card E)` are
candidate-independent and cancel in every comparison.  These theorems are **not**
statements about the exact multinomial law and **not** statements about the
§6.2 bidirected-flow objective (`#260`/`#261`).

Throughout, a *candidate class* `F` is a set of positive count vectors of the
fixed total `N`, and a *covered sample* is a count vector `x` with `A e ≤ x e`
for every class (so every true-supported class is observed at least once,
matching the earlier `#259` coverage baseline).

## 2. The new arithmetic fact: effective-weight domination is only equality

> **Theorem (`effectiveWeight_le_imp_eq`).** Let `A`, `B : E → ℕ` be positive
> count vectors with `∑ A = ∑ B = N` over at least two classes.  If
> `effectiveWeight N B e ≤ effectiveWeight N A e` for every `e`, then `A = B`.

Equivalently (`exists_effectiveWeight_gt_of_ne`): two **distinct** positive
count vectors of equal total can never be pointwise dominated — there is always
a class on which the competitor strictly exceeds the truth.

The proof is information-theoretic.  Writing `q_i(v) = effectiveWeight N v i`,
the weighted log-ratio identity is

```
∑_e B_e · log (q_e(B) / q_e(A))
   = ∑_e B_e · log (B_e / A_e)  +  ∑_e (N - B_e) · log ((N - B_e)/(N - A_e)).
```

Both right-hand terms are nonnegative **Kullback–Leibler-type divergences**
(apply `x - 1 ≤ x log x` with `x = B_e/A_e` and `x = (N-B_e)/(N-A_e)`, using
`∑ B = ∑ A = N`).  The hypothesis `q_e(B) ≤ q_e(A)` makes the left-hand side
nonpositive.  Hence it is zero, each divergence is zero, and the equality case
of `x - 1 ≤ x log x` forces `B_e = A_e` for every `e`.  The Lean ingredients are
`Real.self_sub_one_le_mul_log` and the reindexing identity
`sum_mul_log_effectiveWeight` (the cross terms of `∏_{j≠e}(N-v_j)` collapse via
`∑ w = N`).

This is exactly the extra step the product-binomial surrogate needs relative to
the exact multinomial `#256`, whose likelihood ratio is simply
`∏_e (B_e/A_e)^{x_e}` and needs no such lemma.

## 3. The classification (necessity)

Combining the lemma with the earlier covered-sample iff
(`AssemblyP1/CoveredBinomialWeightsIff.covered_ambient_effectiveProduct_le_iff`):

> **Theorem (`robust_iff_unique`).** For any candidate class `F` of positive
> count vectors of total `N` containing the positive truth `A` (over at least
> two classes), `A` is a **sample-uniform maximizer** over `F` on every covered
> sample — `∀ x, (∀ e, A e ≤ x e) → ∀ B ∈ F, effectiveProduct N B x ≤
> effectiveProduct N A x` — **iff** `F = {A}`.

*Proof.*  `(⇐)` is immediate.  `(⇒)`: if `B ∈ F` with `B ≠ A`, then by the
lemma some class has `q_e(B) > q_e(A)` and no zero branch applies, so by the
covered-sample iff (`exists_beating_sample`) some covered sample strictly
prefers `B` to `A`, contradicting maximality.

When `F` is the set of **positive balanced circulations of total `N` on
`supp A`** — the same-support candidate spectra of the length-`N` de Bruijn
support graph — `F = {A}` is precisely **rigidity** of `A`: the truth spectrum
is the only same-support circulation.  Hence:

> **Sample-uniform maximality ⟹ rigidity.**  Rigidity is **necessary**.

## 4. Sufficiency fails: a rigid truth beaten by a new-support candidate

The converse is **false** once the candidate class admits spectra with **new
support** (classes outside `supp A`).  The smallest witness
(`newsupport_rigid_not_maximal`, kernel-checked) uses the binary 2-mer universe
`(00,01,10,11)` with `N = 4`:

| role | spectrum | circular word | `q(00)` | `q(01)` | `q(10)` | `q(11)` |
|------|----------|---------------|---------|---------|---------|---------|
| truth `A` | `(2,1,1,0)` | `0001` | `72` | `24` | `24` | `0` |
| candidate `B` | `(1,1,1,1)` | `0011` | `27` | `27` | `27` | `27` |

`A` is **rigid**: the de Bruijn balance conditions on its support `{00,01,10}`
reduce to `01 = 10`, and with total `4` the only positive solution is
`(2,1,1,0)`.  Yet `q_{01}(B) = 27 > 24 = q_{01}(A)`, so `B` beats `A` on a
covered sample: the ambient criterion's failure branch holds with **no zero
weight** on `supp A` (the unobserved `(N - B_{11}) = 3` factor is what lets the
new-support candidate `B` pay less for its extra class).  Rigidity is necessary
but **not sufficient**.

A bounded census (`scripts/verify_product_binomial_rigidity_259.py`, binary
alphabet, read lengths `L ∈ {2,3,4}`, genome lengths `G ≤ 12`, all `1088`
distinct binary-necklace spectra as truths and all same-length spectra as
competitors) reproduces the earlier `#259` finding:

| cell | count |
|------|-------|
| rigid & maximal | 310 |
| **rigid & NOT maximal** | **257** (all beaten only by new-support candidates) |
| **non-rigid & maximal** | **0** (no necessity counterexample) |
| non-rigid & NOT maximal | 521 |

Every one of the `521` non-rigid truths was beaten by a **same-support**
circulation, exactly as the necessity theorem predicts; all `257` rigid-but-not-
maximal truths were beaten only by **new-support** candidates, exactly as §4
predicts.  This is bounded evidence, not a theorem; the theorem is
`robust_iff_unique` over the same-support circulation class.

## 5. Scope matrix

| Item | Covered by this module | Still open |
|------|------------------------|------------|
| Objective | MB09 §6.1 fixed-external-`N` **product-binomial surrogate** (integer numerator) | true joint multinomial (`#256`); §6.2 bidirected flows (`#260`/`#261`) |
| Classification | sample-uniform maximality over a same-support candidate class ⟺ `F = {A}` (rigidity) | maximality over the full **new-support** candidate class |
| Candidate length | same-length, fixed finite universe | variable genome length |
| Normalization `N` | fixed external; omitted candidate-constant factors cancel | — |
| Support | truth support `supp A`; new-support candidates handled only as the §4 counterexample | rigidity **sufficiency** over new-support candidates |
| Sample size `n = ∑ x` | free, bounded below by the truth spectrum (covered samples) | weaker information-feasibility coverage events |
| Boundary probabilities | zero-weight candidates handled by the merged covered-sample iff; truth weights positive on `supp A` | `qA` zero on the true support |
| Graph rigidity | **necessary** for sample-uniform maximality (direct theorem) | **not** sufficient; general bidirected-flow rigidity (`#260`/`#261`) |

## 6. Independent verification

`scripts/verify_product_binomial_rigidity_259.py` (exact `int`/`Fraction`
arithmetic, no Lean import) checks:

1. **Part A** — the necessity lemma on `275380` `(N,k)` pairs (exhaustive for
   `N ≤ 12`, `k ≤ 4`, plus randomized `N ≤ 250`, `k ≤ 8`): zero distinct
   positive equal-total pairs are pointwise dominated.
2. **Part B** — the weighted log-ratio identity and `KL ≥ 0` on `20000` random
   pairs (tight float tolerance, exact weights).
3. **Part C** — `robust_iff_unique` on `2250` `(A, F)` cases: covered-sample
   maximizer status (decided by the merged covered-sample iff) equals `F = {A}`.
4. **Part D** — the smallest sufficiency counterexample `A = (2,1,1,0)` vs
   `B = (1,1,1,1)`, `A`'s rigidity (unique positive circulation), and the
   `1088`-spectrum census (`0` non-rigid maximal, `257` rigid-not-maximal).

The Lean module is the authoritative kernel-checked artifact; the script is
bounded computational evidence that the arithmetic and the classification are
correctly encoded.

### CI wiring

The `research-docs` job should run the verifier; the one-line step is

```yaml
      - name: Verify #259 product-binomial rigidity necessity and sufficiency failure
        run: python3 scripts/verify_product_binomial_rigidity_259.py
```

The push token used for this branch carries `repo` scope only, so a change to
`.github/workflows/ci.yml` is refused by GitHub ("refusing to allow an OAuth App
to create or update workflow … without `workflow` scope"); the wiring is left as
a one-line follow-up for a workflow-scoped token.  The verifier itself is
deterministic and runs in well under a minute.

