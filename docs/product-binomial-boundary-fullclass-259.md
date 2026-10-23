# Full-class sample-uniform maximality of the MB09 §6.1 product-binomial surrogate, boundary coordinates included (board issue #259, axis B)

_Status: kernel-checked Lean theorem
(`AssemblyP1/ProductBinomialBoundaryFullClass.lean`, axiom audit in
`AssemblyP1/ProductBinomialBoundaryFullClassAudit.lean` reporting only
`propext`, `Classical.choice`, `Quot.sound`), imported by `AssemblyP1.lean`,
with independent exact-integer verification in
`scripts/verify_product_binomial_boundary_fullclass_259.py`._

This note closes the **full-class** form of the axis-B question of `#259`: for
the Medvedev–Brudno 2009 §6.1 fixed-external-`N` product-binomial surrogate,
classify the truths that are **sample-uniform maximizers over the entire
same-total candidate class**, including boundary coordinates `d(w) = 0`,
`d(w) = N` and candidates with new support.

## 1. Model and scope

Medvedev and Brudno 2009, J Comput Biol, §6.1 score a candidate read-type
spectrum `B : E → ℕ` over a fixed finite read-type universe `E` by a **product of
marginal binomials** with a fixed external genome length `N`.  For an observed
count vector `x` with `n = ∑ x`, the candidate-dependent integer numerator is

```
q_e(B)          = B e * ∏_{j : E, j ≠ e} (N - B j)          (effective weight)
F_B(x)          = ∏_{e : E} q_e(B) ^ (x e)                  (effective product)
```

The second product defining `q_e(B)` runs over **all** modeled read types,
including zero-observed ones; this is the extra `(1 - B j / N) ^ (n - x j)`
factor that separates the surrogate from the exact joint multinomial read
likelihood of `#256`.  The omitted candidate-constant factors
`∏_e choose(n, x_e)` and `N ^ (-n · card E)` cancel in every comparison.

* **Objective:** MB09 §6.1 fixed-external-`N` product-binomial **surrogate**
  (not the exact multinomial of `#256`, not the §6.2 bidirected flow of
  `#260`/`#261`).
* **Candidate length:** same-length, fixed finite read-type universe `E`.
* **Normalization `N`:** fixed external genome length.
* **Support:** the **full same-total candidate class**
  `FullCandidateClass N = {B : E → ℕ | ∑ B = N}`, so boundary coordinates
  `B e = 0` and `B e = N` and candidates with new support are all admitted.
* **Sample size `n = ∑ x`:** free; a **covered sample** satisfies `A e ≤ x e`
  for every `e` and `x e = 0` whenever `A e = 0` (it visits every true-supported
  read type at least once and observes no off-support type).
* **Graph rigidity:** a truth `A` is rigid when the only positive same-support
  balanced circulation of total `N` is `A` itself.

## 2. The classification

> **Theorem (`fullClass_sampleUniformMax_iff`).**  Let `A : E → ℕ` with
> `∑ A = N`.  Then `A` is a sample-uniform maximizer over
> `FullCandidateClass N` on every covered sample supported on `supp A` **iff**
> `A` is concentrated on a single class (`∃ e, A e = N`) **or** `A` is
> `{0,1}`-valued (`∀ e, A e ≤ 1`).

With `∑ A = N`, the `{0,1}` disjunct says exactly that `A` is the indicator of an
`N`-element support (`fullClass_max_iff_support` restates this in support form).
The two disjuncts overlap only when `N = 1`.

So over the *full* candidate class the only maximal truths are the degenerate
ones: a mass-on-one-class spectrum, or a `{0,1}`-valued spectrum.  In particular
any truth with a supported coordinate `≥ 2` and at least two supported
coordinates is beaten.  This is a strictly stronger conclusion than the merged
per-competitor criterion, and it shows the full-class condition is genuinely
more restrictive than **rigidity**: the rigid truth `(2,1,1,0)` is *not*
maximal.

## 3. Why: two mechanisms

The exact covered-sample criterion of
`AssemblyP1.CoveredBinomialWeightsIff.covered_ambient_effectiveProduct_le_iff`
says that a truth `A` dominates a fixed competitor `B` on every covered sample
iff either `B` has a zero effective weight on `supp A`, or `B`'s effective
weights are pointwise dominated by `A`'s.  The classification follows by
analysing when this holds for *every* `B`.

**(i) Boundary candidates never beat the truth.**  If `B e = 0` for some
true-supported class `e`, then `q_e(B) = 0`; if `B j = N` for some `j`, then
(either `j` is the only mass of `B`, so `B` vanishes on the rest of `supp A`, or
`B = N · δ_j`) again some true-supported effective weight is `0`.  Such a `B` is
in the criterion's zero branch, so its score is `0` on every covered sample while
the truth's score is positive.  This is the precise sense in which the boundary
probabilities `0`/`1` and the zero-count coordinates are **harmless**
(`boundary_candidate_dominated`).

**(ii) A one-unit transfer beats a non-degenerate truth.**  If `A` has two
supported coordinates `i ≠ j` and `A j ≥ 2`, the candidate
`B = A - e_j + e_i` (one unit moved from `j` to `i`) stays positive on `supp A`
and every coordinate stays below `N`, and

```
q_i(B) = (A i + 1) (N - A j + 1) ∏_{l ∉ {i,j}} (N - A l)
      >  A i        (N - A j)     ∏_{l ∉ {i,j}} (N - A l) = q_i(A)
```

because `(A i + 1)(N - A j + 1) - A i (N - A j) = A i + (N - A j) + 1 > 0`.  This
is the kernel lemma `transfer_effectiveWeight_lt` (proved with the
`ℕ`-specialised product strict monotonicity `prod_lt_prod_nat`, since `Nat` lacks
the `MulLeftStrictMono` instance that `Finset.prod_lt_prod` needs).  The
criterion then produces a covered sample strictly preferring `B` to `A`, so a
non-degenerate two-support truth is beaten.  If instead `supp A = {j}` with
`2 ≤ A j < N`, moving all mass to `j` (the candidate `N · δ_j`) strictly raises
`q_j` (`singleton_transfer_effectiveWeight_lt`).

The sufficiency direction is dual: for a mass-on-one-class truth the effective
weight at the single supported class is bounded by `N ^ card E`; for a `{0,1}`
truth, any candidate with all effective weights positive on `supp A` must equal
`A` (`eq_of_effectiveWeight_pos_of_zero_one`), because the support has exactly
`N` classes each carrying at least one unit of mass, forcing `B = A`.

## 4. Relation to the merged necessity result

The merged `AssemblyP1.ProductBinomialRigidityNecessity` proves that over a class
`F` of **positive** same-total vectors, sample-uniform maximality is equivalent to
`F = {A}` (necessity of rigidity), and that rigidity is not sufficient because
`(2,1,1,0)` is beaten by the new-support `(1,1,1,1)`.  The present classification
makes the full-class picture exact:

| truth `A` (∑A = N) | maximal over full class? |
|--------------------|--------------------------|
| `N · δ_e` (mass on one class) | **yes** |
| `{0,1}`-valued, `N` ones (`A e ≤ 1`) | **yes** |
| any supported coordinate `≥ 2`, `≥ 2` supported classes | **no** |

Consequences.

* Rigidity is **necessary but not sufficient**: every maximal truth is rigid (a
  `{0,1}` truth is the unique positive same-total vector on its support, and
  `N · δ_e` is trivially rigid), while `(2,1,1,0)` is rigid and not maximal.
* **Global uniqueness is not necessary**: `(0,1,1)` with `N = 2` is maximal over
  the full class although `(1,1,0)` and `(1,0,1)` are other positive same-total
  vectors (`maximal_two_support`).
* The classification is **non-vacuous**: `(1,1,1,1)` with `N = 4`
  (`maximal_example`) and `(2,1,1,0)` (`nonmaximal_example`) exercise both
  branches.

## 5. Scope matrix

| Item | Covered by this module | Still open |
|------|------------------------|------------|
| Objective | MB09 §6.1 fixed-external-`N` **product-binomial surrogate** | true joint multinomial (`#256`); §6.2 bidirected flows (`#260`/`#261`) |
| Classification | full same-total candidate class, boundary and new support included | the same classification restricted to **realizable (balanced) spectra** rather than all count vectors |
| Candidate length | same-length, fixed finite universe `E` | variable genome length (`#257`) |
| Normalization `N` | fixed external | — |
| Support | arbitrary count vectors of total `N` | balanced circulations on a de Bruijn support graph |
| Sample size `n = ∑ x` | free, covered samples (`A ≤ x`, supported on `supp A`) | weaker information-feasibility coverage events |
| Boundary probabilities | `d(w) = 0`, `d(w) = N` handled (zero branch, dominated) | — |
| Graph rigidity | necessary but not sufficient; exact full-class condition given | general bidirected-flow rigidity (`#260`/`#261`) |

### Additional bounded realizable-spectrum census (binary circular `k=2`)

The executable search `scripts/census_circular_binary_k2_259.py` enumerates
binary circular words modulo rotation for lengths `L = 2,…,16`, forms their
oriented cyclic 2-mer spectra, deduplicates the spectra, and compares every
truth spectrum against every candidate spectrum using exact integer products
for the same fixed-`N` objective (`N=L`, `n=L`, observed `x=A`).  Every truth was
a maximizer at its own observed spectrum in this census.  For each truth it
also checked all complete-support observations `x ≥ A` with total excess at
most 8.  The surviving truths were: all three spectra at `L=2`; two at `L=3`,
namely `(0,1,1,1)` and `(1,1,1,0)`; `(1,1,1,1)` at `L=4`; and none at
`L=5,…,16`.  Thus this family supplies no non-concentrated sample-uniform
counterexample; even the finite excess-box check is not a proof for all
observations.  This complements the prior `k=1` census through `L=11` but does
not close the realizability-restricted theorem.  The script is an exact bounded
census, not a Lean-checked theorem or an assertion about other alphabets,
orders, genome models, or the exact multinomial objective.

## 6. Independent verification

`scripts/verify_product_binomial_boundary_fullclass_259.py` (exact Python
`int`/`Fraction` arithmetic, no Lean import) checks:

1. **Part A** — the classification against the merged exact covered-sample
   criterion on `494` `(m, N, A)` cases.
2. **Part B** — real sample witnesses: for each non-maximal truth an explicit
   flooding witness is produced (`23` witnesses) and for each maximal truth a
   bounded exhaustive search finds no beating sample (`55` cases).
3. **Part C** — boundary candidates (`B i = 0` on `supp A`, or `B j = N`) are
   dominated in `9413` `(A, B)` cases.
4. **Part D** — the one-unit transfer strictly raises the target effective weight
   in `3080` cases.
5. **Part E** — the witnesses `(1,1,1,1)` (maximal), `(0,1,1)` (maximal, not
   globally unique), `(2,1,1,0)` (beaten by `(1,1,1,1)`), plus a self-factor
   mutation control that breaks the transfer strict inequality.

The Lean module is the authoritative kernel-checked artifact; the script is
bounded computational evidence that the arithmetic and the classification are
correctly encoded.

### CI wiring

The `research-docs` job should run the verifier; the one-line step is

```yaml
      - name: Verify #259 full-class product-binomial boundary classification
        run: python3 scripts/verify_product_binomial_boundary_fullclass_259.py
```

The `build` job already compiles the module (library glob) and audits its axioms
(`--modules-from AssemblyP1`); the verifier is deterministic and runs in well
under a minute.
