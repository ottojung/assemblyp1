# Alternating-word L=3 infinite gap family (board issue #259)

_Status: theorem in `k` with exact-integer verification
(`scripts/verify_alternating_3mer_binomial_maximality_259.py`); no Lean
theorem claimed.  Promotes the observed census pattern of
`docs/realizable-transfer-gap-259.md` (alternating words `(01)^k` read as
3-mer spectra were gap cases for small `G`, proof conjectural there) to a
proved infinite family for read length `L = 3`, complementing the `L = 2`
family (`docs/alternating-binary-binomial-maximality-259.md`).  The new
mathematical content is a **balance-aware domination lemma**: unlike `L = 2`,
ternary-style rerouting (`0 -> 2 -> 1`) is unavailable here but balance still
couples the two supported coordinates to four background counts, and the
domination inequality needs AM-GM plus Bernoulli, not just one-variable
calculus._

## 1. Statement

Work over the binary 3-mer universe
`E = {000,001,010,011,100,101,110,111}` (indices `0..7` in this order) with
the MB09 §6.1 fixed-external-`N` product-binomial surrogate:
`q_i(B) = B[i] ∏_{j≠i} (N − B[j])`,
`F_B(x) = ∏_i q_i(B)^{x[i]}` (candidate-constant `choose`/`N` factors cancel
in comparisons; this is the surrogate, not the exact multinomial of `#256`).

> **Theorem.**  For every `k ≥ 2`, the truth `A_k = (0,0,k,0,0,k,0,0)`
> (spectrum of the circular word `(01)^k` read as 3-mers: `k` on `010`, `k`
> on `101`, total `N = 2k`) is **beaten over the full candidate class** but
> is a **sample-uniform maximizer over the realizable class** (binary
> necklace 3-mer spectra of length `2k`).  The case `k = 1` is genuinely
> excluded: `A_1` is `{0,1}`-valued, hence full-class maximal by the
> kernel-checked full-class iff.

The reduction to pointwise domination uses the kernel-checked
covered-sample iff
(`AssemblyP1.CoveredBinomialWeightsIff.covered_ambient_effectiveProduct_le_iff`):
`B` is dominated by `A` on all covered samples iff `B` has a zero effective
weight on `supp A` or `q(B) ≤ q(A)` pointwise there.

## 2. Proof

**Balance parametrization.**  A count vector `B` of total `2k` is balanced
(`out = in` at every 2-mer node) iff, writing `a = B_001 = B_100`
(node `00`), `b = B_011 = B_110` (node `11`), `p = B_010`, `q = B_101`,
`c = B_000`, `d = B_111`, the node-`01`/`10` equations both read

```
p + b = a + q,   i.e.  p - q = a - b =: δ (fractions of N).
```

Every necklace spectrum is balanced (circular word: each visit contributes
one in- and one out-edge; Part 1 of the script checks the parametrization
exhaustively over all `516` even-length necklaces `G ≤ 12`).

**Realizable maximality (domination lemma).**  Let `B` be balanced,
`N = 2k`, `α_j = B_j / N` (`Σα = 1`),
`r = Σ_{others} α = c + 2a + 2b + d ≥ 2|δ|` (since `2a + 2b ≥ 2|a − b|`),
`R = ∏_{6 others} (1 − α_j) ≤ (1 − r/6)^6` (AM-GM).  Put
`f = q_010(B)/N^8 = α_p (1 − α_q) R`; the target is
`q_010(A_k)/N^8 = (1/2)(1/2) = 1/4` (and symmetrically for `g = q_101/N^8`).

If `δ ≤ 0`, then `α_p ≤ α_q`, so
`f ≤ α_q (1 − α_q) R ≤ (1/4)·1 = 1/4`.
If `δ > 0`, then `α_p + α_q = 1 − r ≤ 1 − 2δ`, so with `α_p = α_q + δ`,
`2α_p ≤ 1 − δ`, i.e. `α_p ≤ (1−δ)/2`; `t ↦ t(1 − t + δ)` increases up to
`(1+δ)/2 > (1−δ)/2`, hence
`α_p(1 − α_q) ≤ ((1−δ)/2)((1+3δ)/2) = (1 + 2δ − 3δ²)/4 ≤ (1 + 2δ)/4`.
Moreover `R ≤ (1 − r/6)^6 ≤ (1 − δ/3)^6 ≤ 1/(1 + 2δ)`, the last step being
Bernoulli in the form `(1−y)^6 (1+6y) ≤ 1` for `y = δ/3`
(`φ(0) = 1`, `φ′(y) = −42y(1−y)^5 ≤ 0`; feasibility `δ ≤ 1/3` follows from
`δ ≤ α_p ≤ α_p + α_q ≤ 1 − 2δ`).  Hence `f ≤ 1/4`, and symmetrically
`g ≤ 1/4` (applying the same case split to `−δ`).

So no balanced `B ≠ A_k` strictly exceeds `A_k` on either supported
coordinate.  Equality `f = g = 1/4` forces `δ = 0` (else the `-3δ²` term
makes the bound strict), then `α_p(1 − α_p) = 1/4` so `α_p = α_q = 1/2`,
then `r = 0`: i.e. `B = A_k`.  By the covered-sample iff, `A_k` is a
sample-uniform maximizer over the realizable class (Part 2 checks all
`144858` balanced triples for `2 ≤ k ≤ 24` in exact integer arithmetic,
equality-both only at `B = A_k`).

**Full-class beating (exact).**  `B* = A_k − e_010 + e_101`
(`k−1` on `010`, `k+1` on `101`) has node-`01` residual
`(k−1) − (k+1) = −2 ≠ 0`: unbalanced, hence no necklace spectrum realizes
it, for every `k ≥ 2`.  At the covered sample `x` with `x_010 = k`,
`x_101 = 2k` (sample size `n = 3k`),
`q_010(B*) = (k−1)²(2k)^6`, `q_101(B*) = (k+1)²(2k)^6` against `k²(2k)^6`
for both coordinates of `A_k`, so
`F_B*(x)/F_A(x) = [(k−1)(k+1)²/k³]^{2k} > 1` because
`(k−1)(k+1)² − k³ = k² − k − 1 ≥ 1` for `k ≥ 2` (Part 3 checks the exact
integer comparison for `2 ≤ k ≤ 200`).

**Rigidity.**  Positive circulations supported on `{010,101}` satisfy
`B_010 = B_101` (nodes `01`, `10`), so total `2k` forces `(k,k) = A_k`:
`A_k` is rigid, hence rigid-and-realizable-maximal, beaten only outside the
realizable class.

Boundary probabilities `0/1` and zero-count coordinates are handled
honestly: `p = 0` (resp. a mass coordinate `B_j = N`) puts `B` in the zero
branch of the merged covered-sample iff (dominated, since `x ≥ A_k` is
positive on `supp A_k`); otherwise all `(N − B_j)` factors are positive.

## 3. Scope matrix

| Item | Covered here | Still open |
|------|--------------|------------|
| Objective | MB09 §6.1 fixed-external-`N` product-binomial surrogate | exact multinomial (`#256`); §6.2 bidirected flows (`#260`/`#261`) |
| Candidate length | same-length, binary `L = 3`, truth length `2k` all `k ≥ 2` | ternary `L ≥ 3`, alphabets `≥ 4`, non-alternating truths |
| Normalization `N` | fixed external `N = 2k` | — |
| Support | `{010,101}`; realizable = necklace spectra (balanced); full-class beater outside it | all balanced circulations (disconnected supports); realizable-class iff in general |
| Sample size | free; explicit covered witness `n = 3k` + uniform domination | weaker information-feasibility coverage events |
| Graph rigidity | `A_k` rigid (unique positive circulation `(k,k)`); necessity direction is the kernel-checked `robust_iff_unique` | rigidity necessity *within* the realizable class |
| Multinomial | not imported; `(1−d(w)/N)^{n−x(w)}` factors kept via `q` | `#256` |

## 4. Independent verification

```
python3 scripts/verify_alternating_3mer_binomial_maximality_259.py
```

Exact `int` arithmetic, no Lean import.  Runs in about a minute
(Part 2 enumerates `144858` balanced triples for `2 ≤ k ≤ 24`; Parts 3–4
are cheap closed-form checks to `k = 200`).

### CI wiring

```yaml
      - name: Verify #259 alternating-word L=3 infinite gap family
        run: python3 scripts/verify_alternating_3mer_binomial_maximality_259.py
```

(Workflow edits need a workflow-scoped token, so wiring is a one-line
follow-up as in the preceding `#259` notes.)
