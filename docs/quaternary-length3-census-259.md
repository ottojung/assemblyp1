# Quaternary length-3 product-binomial census (#259)

_Status: independent exact-integer verification in
`scripts/verify_quaternary_length3_census_259.py` (no Lean import, no
floats). Honest negative result: no beating sample exists in this cell._

## 1. Cell

First alphabet-4 cell for #259 (prior census cells were binary/ternary):

| Item | Value |
|------|-------|
| Candidate length `G` | 3 (circular words over `{0,1,2,3}`) |
| Normalization `N` | fixed external `N = G = 3` (MB09 §6.1) |
| Read-type universe `E` | 16 oriented 2-mers |
| Support | full 16-class universe; covered samples per truth (§3) |
| Sample size `n = ∑ x` | free; covered samples have `n ≥ N = 3` |
| Objective | §6.1 fixed-`N` **product-binomial** surrogate, NOT the exact joint multinomial of #256, NOT §6.2 bidirected flows of #260/#261 |

## 2. Census

| Count | Value (asserted from scratch) |
|-------|-------------------------------|
| Circular words | 64 = 4³ |
| Realizable spectra | 24 |
| Full candidate class (total-3 vectors over 16 classes) | 816 = C(18,15) |
| Full-class violations | **0** |
| Realizable-class violations | **0** |

Every realizable truth is sample-uniformly maximal against both classes.
`q_A > 0` on `supp(A)` holds for all 24 truths, so `F_A > 0` on covered
samples and every comparison is meaningful. The verdicts use exact
`Fraction` per-coordinate ratios `q_B/q_A ≤ 1` (plus the zero branch), and
71,720 explicit integer `(pair, covered-sample)` comparisons
`F_B(x) ≤ F_A(x)` at `x = A` and `x = A + 2·e_i` confirm the encoding
end to end.

## 3. Why no witness here (and what was checked instead)

With `N = 3` over 16 classes, each spectrum spreads little mass over many
classes, so the extra `(N - B(v))` factors penalize concentrated
competitors uniformly; the iff's domination branch holds everywhere. There
is therefore no explicit beating sample to exhibit and no minimality scan
to run — this is reported as an honest negative, not filled with a
weaker-sense witness. Sensitivity is demonstrated by the mutation control:
wrongly including the self factor `(N - B(w))` in `q` flips the verdicts
to full = 540 / realizable = 12, so the verifier is not vacuous. (Under
that mutation some `q_A` vanish on `supp(A)`; the script handles that
branch exactly. Under the true `q` it never triggers, by the positivity
check.)

## 4. Rigidity cross-check

All 24 realizable truths are rigid (unique same-support positive
circulation of total 3), hence non-rigid & maximal = 0 — consistent with
the kernel-checked rigidity-necessity theorem
(`docs/product-binomial-rigidity-necessity-259.md`), which predicts exactly
this. This cell therefore contributes bounded evidence *for* necessity and
no counterexample to it.

## 5. Scope matrix

| Item | Covered here | Still open |
|------|--------------|------------|
| Objective | §6.1 product-binomial surrogate | exact multinomial (#256); bidirected flows (#260/#261) |
| Alphabet | 4-letter, `G = 3` | alphabets ≥ 4 at larger `G`; ternary `G ≥ 5` |
| Candidate length | same-length, fixed finite universe | variable genome length |
| Normalization `N` | fixed external `N = G` | — |
| Support | covered complete-support samples | weaker coverage events |
| Sample size `n` | free above the truth spectrum | — |
| Boundary 0/1 | zero-weight branch of the iff | `q_A` zero on true support (does not occur here) |
| Rigidity | necessity consistent (24/24 rigid) | sufficiency over new-support classes; general flows (#260/#261) |

## 6. Reproduce

```sh
python3 scripts/verify_quaternary_length3_census_259.py
python3 -m py_compile scripts/verify_quaternary_length3_census_259.py
```

Runs in well under a minute, deterministic, stdlib only.
Genuine general bidirected flows are untouched (reserved for #260/#261).
