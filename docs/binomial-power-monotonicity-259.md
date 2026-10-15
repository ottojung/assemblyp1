# Power monotonicity of the exact-iid vs §6.1 ranking inversion (board issue #259)

_Status: kernel-checked Lean theorems (`AssemblyP1/Section62BinomialPowerMonotonicity.lean`
and `AssemblyP1/CoveredBinomialWeightsIffSharpness.lean`), imported by
`AssemblyP1.lean`, with `#print axioms` audits
(`Section62BinomialPowerMonotonicityAudit.lean`,
`CoveredBinomialWeightsIffSharpnessAudit.lean`) reporting only `propext`,
`Classical.choice`, `Quot.sound`.  Independent exact-rational Python
verification in `scripts/verify_binomial_power_monotonicity_259.py`.  This note
records a scoped finite-witness result; it does not close the full board issue
#259, whose general source-faithful statement is the bidirected-flow
classification of #260/#261._

This note complements `covered-binomial-maximality-259.md`, which records the
covered-sample maximality classification
`covered_product_le_iff_zero_or_pointwise` (and its ambient full-universe
adapter).  The two modules added here are **new** and do not restate that
classification:

* `Section62BinomialPowerMonotonicity.lean` strengthens the merged
  single-read ranking-inversion witness to **every sample size `n ≥ 1`**.
* `CoveredBinomialWeightsIffSharpness.lean` records that **neither disjunct**
  of the classification is redundant.

## 1. The two objectives

Medvedev and Brudno 2009, §6.1
(<https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/>) model the read-count
objective as a **product of marginal binomials** with a fixed external genome
length `N`.  For the observed count vector `(n, 0, 0, 0)` (all `n` reads equal
to the oriented word `00`) this surrogate keeps **every** coordinate factor,
including the three zero-count factors `(1 - d_i / N)`:

```
surrogate_C(n) = p_00(C)^n * (1 - p_01(C))^n * (1 - p_10(C))^n * (1 - p_11(C))^n,
```

where `p_i(C) = d_i(C) / N` and `d_i(C)` is the oriented circular `2`-read
count of candidate genome `C`.  This is deliberately distinct from:

* the **exact iid/multinomial** likelihood of the observed reads, which for the
  single-type count vector `(n, 0, 0, 0)` equals `p_00(C)^n`, and
* the **§6.2 bidirected-flow** candidate universe (#260/#261).

## 2. The witness genomes

The merged module `Section62BinomialRealGenomeInversion.lean` gives two genuine
oriented circular binary words of the same fixed length `N = 100`:

| genome | word | oriented circular counts `(00, 01, 10, 11)` |
|--------|------|---------------------------------------------|
| `A` | `0^51 1^49` | `(50, 1, 1, 48)` |
| `B` | `0^50 1^18 (01)^16` | `(49, 17, 17, 17)` |

For the single read `00`:

| model | `A` | `B` | winner |
|-------|-----|-----|--------|
| exact iid | `50 / 100` | `49 / 100` | `A` |
| §6.1 surrogate | `50·99·99·52 / 100^4 = 25482600 / 100^4` | `49·83^3 / 100^4 = 28017563 / 100^4` | `B` |

## 3. Power monotonicity (`n ≥ 1`)

> **Theorem (`ranking_inversion_all_n`).**  For every `n ≥ 1`, `n` identical
> `00` reads make the exact iid/multinomial likelihood strictly favor the true
> circular genome `A` while the full-alphabet §6.1 product-binomial surrogate
> strictly favors the competitor `B`:
> `exactIidB n < exactIidA n` and `surrogateA n < surrogateB n`.

Both are exact rational comparisons over `ℚ`:

* `exactIidA n = 50^n / 100^n` and `exactIidB n = 49^n / 100^n`, so the exact
  ratio is `(50/49)^n > 1` (`exact_ratio_gt_one`);
* `surrogateA n = 25482600^n / 100^(4n)` and
  `surrogateB n = 28017563^n / 100^(4n)`, retaining all three zero-count
  factors in the base.

The proofs are strict power monotonicity of the merged kernel-checked base
inequalities `exactNumB < exactNumA` and `surrogateNumA < surrogateNumB`; the
`n = 1` specialization is `ranking_inversion_one`.

**Scope warning.**  A sample of `n` identical `00` reads has probability
`(1/2)^n` under `A`, so it is exponentially rare.  The corollary shows that the
ranking reversal is not confined to `n = 1`; it does **not** assert that the
§6.1 surrogate misranks `A` and `B` on typical high-coverage data.

## 4. Sharpness of the covered-sample classification

The classification
`covered_product_le_iff_zero_or_pointwise` proves

```
(∀ covered x, ∏ qB e ^ x e ≤ ∏ qA e ^ x e)
  ↔ (∃ e, qB e = 0) ∨ (∀ e, qB e ≤ qA e).
```

`CoveredBinomialWeightsIffSharpness.lean` shows both disjuncts are needed, on
`E = Fin 2` with positive truth weights and a positive coverage baseline:

> **`iff_needs_zero_disjunct`.**  With `qA = (1, 1)`, `qB = (0, 5)`, `a =
> (1, 1)`, the competitor is dominated on every covered sample (coordinate `0`
> is always observed, so `qB 0 ^ x 0 = 0`), but `qB 1 = 5 > 1 = qA 1`, so the
> pointwise inequality fails.  Hence `LHS ↔ (∀ e, qB e ≤ qA e)` is false.

> **`iff_needs_pointwise_disjunct`.**  With `qA = qB = (1, 1)`, `a = (1, 1)`,
> the competitor is dominated on every covered sample with equality and no
> `qB e` is zero, so `LHS ↔ (∃ e, qB e = 0)` is false.

## 5. Scope matrix

| Item | Covered by these modules | Still open |
|------|--------------------------|------------|
| Objective | exact iid/multinomial **vs** MB09 §6.1 product-of-marginal-binomials surrogate, kept distinct | true joint multinomial (#256); §6.2 bidirected flows (#260/#261) |
| Candidate length | same-length, fixed `N = 100`, explicit circular words | variable genome length |
| Normalization `N` | fixed external `N`; all zero-count factors retained | — |
| Support | full `4`-word alphabet, including the three zero-count coordinates | classes outside the modeled alphabet |
| Sample size `n` | all `n ≥ 1` (power monotonicity) | bounded-`n` phase transitions |
| Genome equivalence | `A`, `B` are distinct up to rotation/RC; not primitive P2 at `L = 2` | P2-candidate restriction |
| Classification sharpness | both disjuncts of the covered-sample iff shown necessary | — |
| Graph rigidity | not addressed here (see `covered-binomial-maximality-259.md` and merged PR167) | rigidity necessity for general sample-uniform maximality |

## 6. Independent verification

`scripts/verify_binomial_power_monotonicity_259.py` (exact `int`/`Fraction`
arithmetic, no Lean import) independently checks:

1. the oriented circular `2`-read counts of `A` and `B` recomputed from their
   literal word definitions;
2. the base values `25482600`, `28017563`, `100^4`, and the merged base
   inequalities;
3. the exact iid and §6.1 scores for every `n = 1 … 64`, including the exact
   ratio `(50/49)^n` and the common integer numerators;
4. the two sharpness counterexamples.

The Lean modules are the authoritative kernel-checked artifacts; the script is
bounded computational evidence that the arithmetic and the statements are
correctly encoded.
