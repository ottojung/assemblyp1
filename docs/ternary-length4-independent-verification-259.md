# Independent exact verification of the ternary length-4 census (#259)

**Status: independent exact verification of an unmerged census; finite model
point only, not a general theorem.** This note independently verifies the
ternary circular length-4 census proposed in
`agent/7NHgg8oluzilkxBcRNGcyZ-issue259` (`a022390`: 81 words, 24 spectra,
495 candidates, 96 full-class / 6 realizable-class violations) with a
separately written exact-integer checker plus an explicit beating sample.
It does not merge that branch and proves nothing for `G >= 5`, alphabets of
size 4+, or arbitrary realizable truths.

## Model (MB09 §6.1 fixed-external-N product-binomial surrogate)

Alphabet `{0,1,2}`, oriented 2-mer universe of size 9, circular candidate
length `G = 4`, fixed normalization `N = G = 4`, sample size `n = sum_w x(w)`.
For a count vector `B` of total `N`:

```
q_B(w) = B(w) * prod_{v != w}(N - B(v)),
F_B(x) = prod_w q_B(w)^x(w).
```

Likelihood comparison at fixed `x` uses `F_B`; candidate-independent factors
(`N^(-N·n)` per coordinate scaling and the data-only `choose(n, x_w)`
factors) cancel. The per-coordinate `(1 - d(w)/N)^(n - x(w))` factors —
including zero-count coordinates and boundary probabilities `0/1` — are
retained inside `q` without logarithms or division. The **exact multinomial**
objective of #256 replaces these per-coordinate binomial factors with a
joint multinomial coefficient and is **not** covered here. Neither is the
§6.2 bidirected-flow objective (#260–#261); genuine general bidirected flows
are left untouched.

## Fixed-x (A) vs sample-uniform (B) inequalities

- **(A) Fixed observed `x`.** Truth `A` weakly maximizes against `B` at `x`
  iff `F_B(x) <= F_A(x)`, i.e. with exact integers
  `prod_w q_B(w)^x(w) <= prod_w q_A(w)^x(w)`. A sufficient coordinatewise
  condition is per-type binomial-factor domination; it is strictly weaker
  than pointwise `q` domination (the fixed-x vs uniform gap).
- **(B) Every realizable complete-support `x`.** Covered samples satisfy
  `x(w) >= A(w)` on `supp(A)` and `x(w) = 0` off it. The established
  covered-sample iff (checked, not re-proved, here): `A` weakly maximizes
  against `B` on **every** such `x` iff `q_B` vanishes somewhere on `supp(A)`
  or `q_B(w) <= q_A(w)` for all `w` in `supp(A)`.
- **Graph rigidity.** The kernel-checked necessity theorem on `main`
  (`docs/product-binomial-rigidity-necessity-259.md`) already proves rigidity
  is **necessary** for sample-uniform maximality over same-support
  circulations, and that sufficiency fails once new-support candidates are
  admitted. This note adds no new rigidity claim; it supplies the next finite
  data point (length 4 fails maximality, unlike length 3).

## Independent verification

`scripts/verify_ternary_length4_witness_259.py` (exact `int` arithmetic,
separately written, no import of the census script) checks:

1. Census sizes from scratch: 81 words, 24 realizable spectra, 495 total-4
   candidate vectors; every realizable spectrum is a candidate.
2. Violation counts re-derived via the covered-sample iff: full-class 96,
   realizable-class 6 — matching the claimed census.
3. Smallest witness `A = (0,0,0,0,0,1,0,1,2)` vs
   `B = (0,0,0,0,1,1,0,1,1)` with `q_A`, `q_B` recomputed exactly, plus an
   **explicit** covered sample `x = A + 15·e_5` (`n = 19`) with exact
   integers `F_B(x) > F_A(x)` (threshold `t = 15` verified minimal by exact
   scan `t = 0..19`; `t = 0` control has `A` winning at `x = A`).
4. Mutation control: including the self factor `(N - B_e)` in `q` moves the
   full-class count to 588, so the checker is non-vacuous.

Run: `python3 scripts/verify_ternary_length4_witness_259.py` (seconds).

## Scope matrix

| Item | Covered here | Still open |
|------|--------------|------------|
| Objective | MB09 §6.1 fixed-`N` product-binomial surrogate | exact multinomial (#256); §6.2 flows (#260–#261) |
| Classification | fixed-`x` inequality + covered-sample iff applied at one model point | maximality over full new-support class in general |
| Candidate length | same-length, `G = 4` ternary circular | ternary `G >= 5`, alphabets `>= 4`, variable length |
| Normalization `N` | fixed external `N = 4` | — |
| Support | complete-support covered samples; zeros off support | weaker coverage events |
| Sample size `n` | free above truth spectrum; explicit witness `n = 19` | — |
| Boundary `0/1` | zero weights kept exact, no logs | `q_A` zero on true support |
| Graph rigidity | necessity theorem cited from `main`; no new claim | general rigidity classification beyond bounded census |
