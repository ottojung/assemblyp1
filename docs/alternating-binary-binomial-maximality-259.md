# Alternating-word infinite gap family (board issue #259)

_Status: theorem in `k` with exact-integer verification
(`scripts/verify_alternating_binary_binomial_maximality_259.py`); no Lean
theorem claimed.  Promotes the observed census pattern of
`docs/realizable-transfer-gap-259.md` (alternating gap cases at
`k = 2, 3, 4, 5`, proof for all `k` explicitly conjectural there) to a proved
infinite family.  Complements the kernel-checked full-class classification
(`docs/product-binomial-boundary-fullclass-259.md`)._

## 1. Statement

Work over the binary 2-mer universe `E = {00, 01, 10, 11}` with the MB09
§6.1 fixed-external-`N` product-binomial surrogate: `q_i(B) = B[i]
∏_{j≠i} (N − B[j])`, `F_B(x) = ∏_i q_i(B)^{x[i]}` (candidate-constant
`choose`/`N` factors cancel in comparisons; this is the surrogate, not the
exact multinomial of `#256`).

> **Theorem.**  For every `k ≥ 2`, the truth `A_k = (0, k, k, 0)` (spectrum of
> the circular word `(01)^k`, total `N = 2k`) is **beaten over the full
> candidate class** but is a **sample-uniform maximizer over the realizable
> class** (binary necklace spectra of length `2k`).  The case `k = 1` is
> genuinely excluded: `A_1 = (0, 1, 1, 0)` is `{0,1}`-valued, hence
> full-class maximal by the kernel-checked iff.

## 2. Proof

**Realizable spectra have `#01 = #10`.**  In a circular binary word every
`01` transition is matched by a `10` transition, so every realizable `B` of
length `2k` is `(a, m, m, d)` with `a + 2m + d = 2k` (Part 1 of the script
checks this exhaustively for even `G ≤ 12`; the transition argument is the
general proof).  The full-class beater `B* = (0, k−1, k+1, 0)` has
`k−1 ≠ k+1`, hence is unrealizable for every `k ≥ 2`.

**Full-class beating (exact).**  At the covered sample `x = (0, k, 2k, 0)`,
`q_01(B*) = 4k²(k−1)²`, `q_10(B*) = 4k²(k+1)²` against `4k⁴` for both
coordinates of `A_k`, so `F_B*(x)/F_A(x) = [((k−1)(k+1)²)²/k⁶]^k > 1`
because `(k−1)(k+1)² − k³ = k²−k−1 ≥ 1` for `k ≥ 2` (Part 3 checks the exact
integer inequality for `2 ≤ k ≤ 200` and the ratio identity as exact
`Fraction`s).

**Realizable maximality (exact inequality).**  Let `B = (a, m, m, d)` be
realizable with `m ≥ 1` (if `m = 0`, `q = 0` on `supp A_k`: zero branch,
dominated).  Since `q_01 = q_10` for both `A_k` and `B`, pointwise domination
on `supp A_k` is the single inequality
`m(2k−a)(2k−m)(2k−d) ≤ 4k⁴`.  With `s = a+d = 2k−2m`,
`(2k−a)(2k−d) = 4k² − 2ks + ad ≤ (k+m)²` since `ad ≤ (s/2)²`; then with
`u = m/k ∈ (0, 1]`, `m(2k−m)(k+m)² = k⁴·u(2−u)(1+u)² ≤ 4k⁴` because
`g(u) = u(2−u)(1+u)²` is strictly increasing on `(0,1]`
(`g′(u) = −4u³+6u+2 = −2(u+1)(2u²−2u−1) > 0` there, as `2u²−2u−1 < 0` on
`(0,1]`) and `g(1) = 4`.  Equality forces `m = k` (hence `s = 0`,
`a = d = 0`, i.e. `B = A_k`).  So no realizable `B ≠ A_k` beats `A_k` on any
covered sample (Part 2 checks all triples exactly for `2 ≤ k ≤ 200`,
equality only at `B = A_k`).

Boundary probabilities `0/1` and zero-count coordinates are handled honestly:
`m = 0` (resp. a mass coordinate) puts `B` in the zero branch of the merged
covered-sample iff, and `a, m, d < N = 2k` whenever `m ≥ 1`, so no
`(1 − d(w)/N)` factor vanishes unexpectedly.

## 3. Scope matrix

| Item | Covered here | Still open |
|------|--------------|------------|
| Objective | MB09 §6.1 fixed-external-`N` product-binomial surrogate | exact multinomial (`#256`); §6.2 bidirected flows (`#260`/`#261`) |
| Candidate length | same-length, binary `L = 2`, truth length `2k` all `k ≥ 2` | ternary `L ≥ 3`, alphabets `≥ 4`, non-alternating truths |
| Normalization `N` | fixed external `N = 2k` | — |
| Support | realizable = necklace spectra (`#01 = #10`); full-class beater outside it | all balanced circulations (disconnected supports) |
| Sample size | free; explicit covered witness `x = (0,k,2k,0)` + uniform domination | — |
| Graph rigidity | `A_k` rigid (unique positive circulation `(k,k)` on `{01,10}`); rigid-and-realizable-maximal, beaten only outside the class | general realizable-class iff; rigidity necessity there |
| Multinomial | not imported; `(1−d(w)/N)^{n−x(w)}` factors kept via `q` | `#256` |

## 4. Independent verification

```
python3 scripts/verify_alternating_binary_binomial_maximality_259.py
```

Exact `int`/`Fraction` arithmetic, no Lean import.  Runs in seconds
(`200` values of `k` in Parts 2–3).

### CI wiring

```yaml
      - name: Verify #259 alternating-word infinite gap family
        run: python3 scripts/verify_alternating_binary_binomial_maximality_259.py
```
