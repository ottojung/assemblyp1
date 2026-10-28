# Finite-read likelihood-ratio exponents and the support boundary

This note documents the paper's Proposition~\`prop:chernoff-refinement\`
and Remark~\`rem:chernoff-sharp\`. Its original symmetric Chernoff
sharpness claim was **incorrect** for asymmetric read-law supports.
The corrected one-sided exponent is classical large-deviation theory,
not a Lean theorem. The Hellinger finite-family result remains
kernel-checked independently.

## Exact sampling model

For a finite alphabet of read types \`W\`, let \`p\` be the truth's read
distribution, \`q\` a competitor, and \`R_1,...,R_n\` iid from \`p\`.
The observed-sample error for this competitor is the **one-sided event**
\`L_q >= L_p\` (ties count as error).

For \`t > 0\`, define
\`\`\`
M_{p,q}(t) = sum_{w:p(w)>0} p(w) (q(w)/p(w))^t,
E_+(p,q) = -log inf_{t>0} M_{p,q}(t), with -log(0)=+infinity.
\`\`\`
Then for each integer \`n>=1\`,
\`\`\`
P_p(L_q>=L_p) <= exp(-n E_+(p,q)).
\`\`\`
A finite union over competitors gives
\`P_p(any wrong q ties/beats p) <= sum_q exp(-n E_+(p,q))\`.

The exponent \`E_+\` is the exact asymptotic rate of this one-sided
event on a finite read alphabet (Cramér's theorem, with boundary
cases interpreted as infinite rates); the minimum of these exponents
is the exact asymptotic rate of a finite competitor-family union.

The conventional, symmetric Chernoff information instead uses
\`0 <= t <= 1\`:
\`\`\`
C_Ch(p,q) = -log inf_{0<t<1} M_{p,q}(t)
            (with appropriate limits at the endpoints).
\`\`\`
We always have \`E_+ >= C_Ch >= -log rho(p,q)\`, where
\`rho(p,q)=sum sqrt(p(w)q(w))\`.
If \`supp(q)\` is contained in \`supp(p)\`, the two exponents are equal:
the derivative of \`log M(t)\` at \`t=1\` is
\`KL(q||p)>=0\`, so convexity places a minimizer in \`(0,1]\`,
possibly approached as \`t -> 0+\`. With extra support, no such
restriction is valid; equality may still occur in particular pairs
but is not automatic.

## Regression: an impossible error missed by the original verifier

Take circular \`S=AAB\`, \`D=AABB\`, oriented reads of length two.
The truth generates \`AA\`, \`AB\`, \`BA\` each with probability \`1/3\`.
The competitor generates each of those and \`BB\` with probability \`1/4\`.
For every nonempty true sample, \`L_D/L_S=(3/4)^n<1\`:
\`\`\`
P_S(L_D>=L_S)=0 for every n>=1,
E_+(p_S,p_D)=+infinity,
C_Ch(p_S,p_D)=log(4/3).
\`\`\`
The usual symmetric Chernoff quantity gives a valid but
**non-sharp** upper bound here. It does not describe the actual
one-sided error exponent.

\`scripts/verify_chernoff_finite_recovery_265.py\` now checks
both this genome example and a law with extra support for which
the optimal \`t\` is strictly larger than one. It still reproduces
the exact finite arithmetic and exponent comparisons below.

## A full-support family: finite-n looseness remains

For the two-symbol family below, every competitor's support is
contained in the truth's support, so its numerical \`C_Ch\` values
equal \`E_+\`. In this special domain the old quantitative tables
and comparisons remain valid.

Take `W = {0,1}`, truth `p = (3/4, 1/4)`, and the two competitors
`q₁ = (1/4, 3/4)` and `q₂ = (0, 1)`. Then

```
ρ(p,q₁) = √3/2 ≈ 0.866025,   C(p,q₁) = ln(2/√3) ≈ 0.143841   (t* = 1/2, C = -ln ρ),
ρ(p,q₂) = 1/2,               C(p,q₂) = ln 4     ≈ 1.386294,
ρ_* = √3/2,                  C_* = 0.143841.
```

The exact error `Pr_p{∃q ∈ {q₁,q₂} : L_q ≥ L_p}` is enumerated with exact
rationals (a sample is summarised by the count `k` of symbol `1`; the error
event is `k ≥ ⌈n/2⌉` for `q₁` and `k = n` for `q₂`):

| `n` | exact error | Hellinger bound | Chernoff bound | Chernoff / exact |
|----:|------------:|----------------:|---------------:|-----------------:|
| 8  | 1.138153e-01 | 3.203125e-01 | 3.164215e-01 | 2.780 |
| 12 | 5.440223e-02 | 1.782227e-01 | 1.779786e-01 | 3.272 |
| 16 | 2.712996e-02 | 1.001282e-01 | 1.001129e-01 | **3.690** |
| 64 | 1.456577e-05 | 1.004524e-04 | 1.004524e-04 | 6.896 |
| 256 | 7.551972e-18 | 1.018220e-16 | 1.018220e-16 | 13.483 |
| 512 | 5.460134e-34 | 1.036772e-32 | 1.036772e-32 | 18.988 |

The recorded headline is the `n = 16` entry: the union bound is about **3.7×**
the exact error. The ratio is not bounded: it grows roughly like `√n`
(3.69 → 6.90 → 13.5 → 19.0 as `n` runs 16, 64, 256, 512), because the exact
error carries a polynomial prefactor the union bound discards. The exact
exponent, meanwhile, converges to `C_*` from above:
`-(1/n) ln P = 0.22545, 0.17401, 0.15400, 0.14959` at `n = 16, 64, 256, 512`,
approaching `C_* = 0.143841` (the gap at `n = 512` is `5.8e-3`). The
odd/even oscillation in the table is the lattice effect of the boundary
`⌈n/2⌉`.

To exhibit the **rate** improvement rather than only the prefactor gap, take the
non-symmetric pair `p = (9/10, 1/10)`, `q = (1/2, 1/2)`:

```
C(p,q) = 0.112377  (t* ≈ 0.5416)   >   -ln ρ(p,q) = 0.111572,
```

with `t* ≠ 1/2`, so the Hellinger exponent is strictly suboptimal. Exact
enumeration of `Pr_p(L_q ≥ L_p)` gives `-(1/n) ln P = 0.115589` at `n = 1024`,
approaching `C(p,q) = 0.112377` rather than `-ln ρ = 0.111572`.

`scripts/verify_chernoff_finite_recovery_265.py` reproduces all of the above
exactly: it checks both union bounds and the termwise ordering for `n = 1..16`,
the `n = 16` ratio, the `C ≥ -ln ρ` relation (equality symmetric, strict
non-symmetric), and the exponent convergence for the family and the binary
comparison through `n = 512`.

## Non-claims

- No claim that the Chernoff (or Hellinger) union bound is tight at finite `n`;
  the `n = 16` gap and its `√n` growth are the opposite.
- No claim that `E_*`, `E_+(p,q)`, `C_Ch(p,q)`, or the
  large-deviation exponent is kernel-checked. These are external standard statistics, cited to textbooks.
  The only kernel-checked constant in this circle is the Hellinger `ρ_*` of
  `AssemblyP1.FiniteReadRecovery` (with `il_confidence_99`).
- No claim of a minimax-optimal or necessary sample size, and no finite `n`
  supplied by the limit theorem.
- No claim about the unrestricted genome universe (all lengths, all models), the
  MB09 §6.1 product-binomial surrogate, or the §6.2 flow model beyond the
  finite-family read-law statement.

## Sources

- Paper: `paper/sections/03-open-question.tex` — Remark `rem:sample-complexity`,
  Corollary `cor:explicit-sample-size`, Proposition `prop:chernoff-refinement`,
  Remark `rem:chernoff-sharp`; `paper/sections/05-population.tex` Theorem
  `thm:finite-recovery` (Hellinger, kernel-checked).
- Kernel: `AssemblyP1/FiniteReadRecovery.lean` (`eventProb_pairwise`,
  `eventProb_wrong_le_sum`, `eventProb_wrong_le_card`, `il_confidence_99`);
  claim index `docs/verification.md`.
- Standard statistics (cited, **not** kernel-checked): Cover & Thomas (2006),
  *Elements of Information Theory*, §11.9; Tsybakov (2009), *Introduction to
  Nonparametric Estimation*, Ch. 2; the large-deviation principle / Sanov's
  theorem.
- Verifier: `scripts/verify_chernoff_finite_recovery_265.py`.
