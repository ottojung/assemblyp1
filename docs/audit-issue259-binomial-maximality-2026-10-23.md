# Independent audit: #259 product-binomial maximality

Owner: `agent-lBMcRtoy5GjgxRy41pgGND-grover`  
Repository: <https://github.com/ottojung/assemblyp1>  
Audit date: 2026-10-23

## Reconciliation and scope

The supplied terminal handoff referred to an uncommitted branch
`agent/e2hvZRe07jG1W7Z6hMk0GB-issue259-analytic`, with files
`docs/alternating-binary-binomial-maximality-259.md` and
`scripts/verify_alternating_binary_binomial_maximality_259.py`. Neither remote
branch ref nor file is present in the current `origin`/`main` checkout. Thus the
claimed staged artifact and its stated 3310-candidate run could not be audited
directly. The board/API lookup identifies the verified project as
`https://github.com/ottojung/assemblyp1.git`; board #259 is a merged PR unrelated
by title to the requested open scientific issue. Its latest comments record
axis-A PR #340 already merged, independently reviewed, and validated.

This audit therefore checks the current integrated artifacts for the same
mathematical questions. It concerns only the MB09 §6.1 fixed-external-`N`
product-of-marginal-binomial surrogate, not the exact joint multinomial of #256
and not the genuine §6.2 bidirected-flow objective of #260–#261.

## Exact inequalities

For a finite type set `E`, candidate `C : E → ℕ`, fixed external normalization
`N`, count vector `x`, and `n = Σ_e x_e`, drop candidate-independent binomial
coefficients and powers of `N`. The integer numerator is

```
F_C(x) = ∏_e q_e(C)^(x_e),
q_e(C) = C_e ∏_(j ≠ e) (N - C_j).
```

Since `Σ_e x_e = n`, regrouping factors gives the exact fixed-observation iff:

```
F_B(x) ≤ F_A(x)
iff ∏_e [B_e^(x_e) (N-B_e)^(n-x_e)]
    ≤ ∏_e [A_e^(x_e) (N-A_e)^(n-x_e)].
```

These are **product** inequalities; per-coordinate factor inequalities are
sufficient, not necessary. The `N-C_e` terms, including all zero-count types,
are precisely the extra factors absent from the exact multinomial comparison
`∏ C_e^(x_e)`.

For sample-uniform maximality over every covered `x` (`x_e ≥ A_e` on truth
support, and optionally `x_e=0` off support), the covered-sample theorem gives
the exact pairwise condition

```
(∃ e in supp(A), q_e(B)=0) OR (∀ e in supp(A), q_e(B) ≤ q_e(A)).
```

The zero-weight branch is essential at boundary probabilities 0/1. If `A` and
`B` are both positive equal-total vectors on at least two types, all these
weights are positive, and the exact-sum logarithmic identity plus KL
nonnegativity proves `q(B) ≤ q(A)` coordinatewise implies `A=B`. Thus a
positive candidate class containing `A` has sample-uniform truth maximizer iff
it is the singleton `{A}`. On the same-support balanced-circulation class this
makes graph rigidity **necessary and sufficient**. If the class also admits
new-support candidates, rigidity alone is **not sufficient**.

## Smallest explicit rigidity-converse witness

The current Lean theorem `newsupport_rigid_not_maximal` and Python verifier give
the same exact witness, with four 2-mer types in order `(00,01,10,11)`:

```
N=4; A=(2,1,1,0); B=(1,1,1,1)
q(A)=(72,24,24,0); q(B)=(27,27,27,27).
```

`A` is rigid on support `{00,01,10}`: balance forces `A_01=A_10`, and the
positive integer total-4 solution is uniquely `(2,1,1,0)`. But `q_01(B)=27 >
24=q_01(A)`, with no zero effective weight on the truth support. Hence the
covered-sample iff supplies a realizable integer covered sample where `B`
strictly wins. Both spectra are realized by circular words `0001` and `0011`.
This is the smallest *documented spectrum-level* witness in the integrated
artifact; no claim of global minimality across alphabet/read-length conventions
is made here.

## Independent validation and caveat

Fresh clone at `main` (`234f348`, remote verified), branch
`agent/lBMcRtoy5GjgxRy41pgGND-issue259-audit`; current tree was clean before
adding this audit. Ran:

```
python3 scripts/verify_fixedx_product_binomial_259.py
python3 scripts/verify_product_binomial_rigidity_259.py
python3 scripts/verify_product_binomial_boundary_fullclass_259.py
```

All passed. Fixed-x output: 144355 identity cases, 40000 criterion cases,
7398 coordinatewise cases, strict separation witness, full Fin-2 class result,
20000 concentrated-sample cases, and 6432 census pairs. Rigidity output:
275380 necessity pairs, 20000 log-ratio checks, 2250 class checks, and the
`(2,1,1,0)` / `(1,1,1,1)` converse failure. Boundary/full-class output: 494
classification cases, 55 bounded sample searches (23 explicit witnesses),
9413 boundary pairs, and 3080 transfer checks.

Audit note: the boundary verifier imports `Fraction` only in the non-maximal
witness branch, but computes the held-fixed-coordinate multiplier `C` with
Python `/` at lines 156–159, producing a float before converting it back to
`Fraction`. This does not affect the exact integer classification in Part A or
the exact rational fixed-x and rigidity verifiers, and its small bounded witness
checks passed; however, Part B's claim of exact rational witness construction
is stronger than the implementation. A follow-up should compute `C` as a
`Fraction` product from the outset (or compare integer cross-products). No
mathematical contradiction was found in the theorem or counterexample.

No Lean build was rerun in this audit; the current handoffs record kernel build
and review for the integrated declarations. This note is an independent
computational/repository audit, not a kernel proof of the general results.
