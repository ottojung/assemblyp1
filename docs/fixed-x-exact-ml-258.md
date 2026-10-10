# Fixed-`x` exact ML classification (board issue #258, child of #255)

_Status: kernel-checked Lean theorem + independent exact-rational Python verification, 2026-10-10. The module is `AssemblyP1/FixedXExactML.lean`, imported by `AssemblyP1.lean`, so every theorem below is checked by `lake build` and free of `sorry`/`admit`/`axiom` (`#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`). The Python script `scripts/verify_feasible_spectrum_ml_255.py` independently verifies all instance facts and the census using exact arbitrary-precision arithmetic._

This note records the **fixed-`x`** exact multinomial ML classification requested by issue #258. It contrasts with #256 (sample-uniform robustness): here the observed count vector `x` is fixed, and we ask when the truth spectrum maximizes the exact likelihood at that specific `x`. The sample-uniform question (#256) asks whether the truth wins for *every* admissible `x`; the fixed-`x` question is pointwise and does not imply robustness.

## 1. The statement

Fix a circular oriented truth `S` of length `G` and a read length `L` with `G ≥ L ≥ 2`. Let

* `A w = spec_L(S)(w)` be the length-`L` spectrum (the truth's edge multiplicities), and `E = supp(A)` the edge set of the de Bruijn support graph;
* `F` be the set of **all** positive integer balanced circulations `B : E → ℕ` on `E` of total `G` (the same-length oriented feasible spectra);
* `x : (Fin L → α) → ℕ` be a fixed observed count vector whose support lies in `E`.

The exact multinomial factor is `Lik(B;x) = ∏_{e∈E} (B e / G)^{x e}` (the observation-only coefficient `n! / ∏_e x e!` is divided out; it is candidate-independent).

> **Theorem (issue #258, deliverable 1).**
> For fixed `x` with support in `E`:
> `(∀ B ∈ F, Lik(B;x) ≤ Lik(A;x))  ↔  (∀ B ∈ F, ∏_{e∈E} (B e)^{x e} ≤ ∏_{e∈E} (A e)^{x e})`.

In Lean: `fixedX_classification_iff`. The integer product is the exact likelihood factor with the candidate-independent positive denominator `G^n` divided out; the iff holds because `G^n > 0` cancels in every comparison.

> **Theorem (issue #258, deliverable 5).**
> For fixed `x` that is realizable from the truth by a realization whose starts cover the genome (historical coverage), the same iff holds with explicit quantifiers for sampling realizability and coverage.

In Lean: `fixedX_classification_iff_of_realizable`.

## 2. Proof

**Key lemma** (`spectrumLikFactor_eq_likProduct_div`): the exact rational likelihood factor equals the exact integer product divided by `G^n` where `n = totalReads x`. This is `div_pow` plus `Finset.prod_div_distrib` plus `Finset.prod_pow_eq_pow_sum`; the support hypothesis on `x` makes the product over `E` equal the full likelihood factor (off-support factors are `(·/G)^0 = 1`).

**Key lemma** (`exactLik_eq_spectrumLikFactor`): the genome-level `exactLik` equals the exact rational likelihood factor of the candidate's spectrum. Under the support hypothesis on `x`, the off-support factors of `exactLik` are `1`, so the objective is the product over the support; `Rat.cast_prod` moves the `ℚ` product past the cast, and `factor_cast` equates the factors.

**Main iff** (`fixedX_classification_iff`): for each candidate `B`, the per-candidate comparison `Lik(B;x) ≤ Lik(A;x)` is rewritten via the key lemma to `likProduct E B x / G^n ≤ likProduct E A x / G^n`; since `G^n > 0`, `div_le_div_iff_of_pos_right` cancels the denominator, and `Nat.cast_le` removes the `ℕ → ℚ` casts. The universal quantifier over `B ∈ F` is preserved in both directions.

**Realizable form** (`fixedX_classification_iff_of_realizable`): the realizability hypothesis implies the support hypothesis via `observedOf_mem_support`; the coverage hypothesis is stated for every realization producing `x`.

## 3. The AAABBB instance (deliverable 3)

Genome `S = AAABBB` (binary alphabet `{A,B}`, `G = 6`, `L = 2`). The truth spectrum is `A = (AA:2, AB:1, BB:2, BA:1)`. The feasible set `F` consists of exactly four spectra:

| Spectrum | AA | AB | BB | BA | Realized by |
|----------|----|----|----|----|-------------|
| B1 (= A) | 2  | 1  | 2  | 1  | AAABBB (truth) |
| B2       | 1  | 1  | 3  | 1  | BBBBAA |
| B3       | 3  | 1  | 1  | 1  | AAABBA |
| B4       | 1  | 2  | 1  | 2  | AABABB |

Three realizable complete-support samples exhibit all three truth statuses:

| Sample x | AA | AB | BB | BA | Status | Exact products (A,B2,B3,B4) |
|----------|----|----|----|----|--------|-----------------------------|
| x1       | 2  | 1  | 2  | 1  | **unique maximizer** | 16, 9, 9, 4 |
| xT       | 1  | 1  | 1  | 1  | **tie at top** with B4 | 4, 3, 3, 4 |
| x2       | 1  | 2  | 1  | 2  | **strict loss** to B4 (ratio 4) | 4, 3, 3, 16 |

All instance facts are kernel-checked by `decide`/`norm_num` in `AssemblyP1/FixedXExactML.lean` (via `scratch255/Scratch.lean`). The Python script independently verifies:
- the feasible set is exactly `{B1,B2,B3,B4}`, each realized by an explicit circular genome;
- the realizations really produce the samples and their distinct starts cover the genome;
- a brute-force scan over all `2^6 = 64` circular genomes confirms that the genome-level exact-likelihood ranking agrees with the spectrum-level classification at `x1`, `xT`, `x2` (at this instance every feasible spectrum is genome-realizable, so the two candidate universes coincide);
- a census over all binary truths of length `G = 5` and `G = 6` at `L = 2` confirms the trichotomy (unique maximizer / tie at top / strict loss) is exhaustive and mutually exclusive over a grid of realizable samples, and the status computed from the feasible-spectrum certificate always matches the status computed by brute force over all genomes.

## 4. Zero-count edges

Zero-count edges are never omitted: they contribute the factor `1` to every product comparison and still constrain the candidate circulations through balance and positivity on the whole support `E`. The Python script verifies that a zero-count sample `x = (AA:2, BB:1)` (realizable but not covering) still produces a strict loss for the truth (defeat ratio `9/8` to B3), confirming that zero-count edges neither rescue nor harm the truth by themselves.

## 5. Relationship to #256

Issue #256 proves the **sample-uniform** iff: `(∀ x, ∀ B ∈ F, Lik(B;x) ≤ Lik(A;x)) ↔ F = {A}`. The fixed-`x` classification here is the pointwise version: for each individual `x`, the truth may win, tie, or lose depending on `x`. The AAABBB instance shows all three statuses occur at realizable complete-support samples, so the truth is **not** sample-uniformly maximal at this genome (consistent with #256: `F ≠ {A}` here). The fixed-`x` question is strictly weaker than the sample-uniform question and does not imply robustness.

## 6. What is deliberately not proved here

* The Eulerian realization direction (every feasible spectrum is the spectrum of some circular genome) is external (Eulerian-circuit existence / BBT); the genome-level theorems of the AAABBB instance are proved at the four concrete genomes directly.
* The chamber decomposition of deliverable 2 is a real-arrangement statement; its decision content is the finite certificate, which is kernel-checked at the instance.
* Full `I_s` is not assumed anywhere; the coverage hypothesis is the source's `Covers` clause only. The AAABBB instance does not satisfy full `I_s` (bridging a length-`1` triple repeat needs a read of length `≥ 3`), which is exactly why its feasible set is not a singleton.
* Nothing here is transferred to reverse-complement molecule flows or to the §6.1 binomial approximation.

## 7. Remaining open

* The fixed-`x` classification for the MB09 §6.1 fixed-external-N product-binomial objective (issue #259) is open.
* The fixed-`x` classification for general MB09 §6.2 bidirected flows at arbitrary overlap floor `o_min ≤ L-1` (issue #261) is open.
* The fixed-`x` classification for reverse-complement molecule types at arbitrary overlap is open.
- The fixed-`x` classification for variable read lengths is open.
