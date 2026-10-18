# The Chernoff refinement of the finite-family recovery bound, and its finite-`n` gap (#265)

Status: 2026-10-18. Owner: agent `df84a657ae4a`. Base: `main` @ `c52be5a`.

This note accompanies the paper's Proposition `prop:chernoff-refinement` and
Remark `rem:chernoff-sharp` in `paper/sections/03-open-question.tex`. It records

1. the exact statement and proof of the **Chernoff union bound** that replaces
   the Hellinger constant `-ln rho_*` of the kernel-checked
   `AssemblyP1.FiniteReadRecovery` bound by the Chernoff information `C_*`;
2. the standard large-deviation fact that `C_*` is the **exact exponent** of the
   finite-family exact-ML error, so the refinement genuinely improves the rate;
3. the **precise finite-`n` gap**: the union bound stays loose because of its
   prefactor, quantified by exact enumeration on a worked family.

It does **not** claim a tight finite-`n` bound, a minimax sample size, any
kernel-checked status for the external Chernoff/large-deviation facts, or any
statement about the unrestricted genome universe. It is the quantitative
companion to `docs/sample-complexity-265.md`.

## Model and assumptions (exact)

Fix a finite read alphabet `W`; a true read law `p` on `W`; a finite competitor
family `Θ` of read laws `q`, each `q ≠ p` (so `Θ` is a set of read laws /
rotation classes, not literal spellings); and `R_1, …, R_n` i.i.d. `~ p`. The
exact product likelihood is `L_q(R_1,…,R_n) = ∏_j q(R_j)`, with ties counted as
errors. Write

```
ρ(p,q) = Σ_{w∈W} √(p(w) q(w)),        ρ_* = max_{q∈Θ} ρ(p,q) < 1,
C(p,q) = sup_{t∈[0,1]} ( -ln Σ_{w: p(w)>0} p(w)^{1-t} q(w)^t )  ≥ 0,
C_*    = min_{q∈Θ} C(p,q) > 0.
```

The sum defining `C` is over the support of `p`; terms with `p(w)=0` are
omitted, matching the `p`-almost-sure integrand `p(w)(q(w)/p(w))^t`. `C` is the
Chernoff information; `C(p,q)>0` exactly when `p ≠ q`.

## The Chernoff refinement

**Proposition (paper `prop:chernoff-refinement`).** In the model above, for every
`t ∈ [0,1]` and every `q ∈ Θ`,

```
Pr_p{ L_q(R_1,…,R_n) ≥ L_p(R_1,…,R_n) }
      ≤ ( Σ_{w: p(w)>0} p(w)^{1-t} q(w)^t )^n ,
```

and hence, taking the infimum over `t` and the union bound,

```
Pr_p{ ∃q∈Θ : L_q ≥ L_p }  ≤  Σ_{q∈Θ} exp(-n C(p,q))  ≤  |Θ| · exp(-n C_*) .
```

Moreover `C(p,q) ≥ -ln ρ(p,q)`, with equality **iff** the supremum is attained
at `t = 1/2` (in particular when `q` is obtained from `p` by exchanging two
symbols, so the sum is symmetric about `t = 1/2`); consequently
`C_* ≥ ln(1/ρ_*) > 0`, and for every `δ ∈ (0,1]`,

```
n ≥ ⌈ ln(|Θ| / δ) / C_* ⌉     ⟹     Pr_p{ ∃q∈Θ : L_q ≥ L_p } ≤ δ .
```

**Proof.** For i.i.d. reads, `E_p[(L_q/L_p)^t] = ∏_j E_p[(q(R_j)/p(R_j))^t] =
(Σ_{w: p(w)>0} p(w)^{1-t} q(w)^t)^n`. Under `p`, `L_p > 0` almost surely, so on
`{L_q ≥ L_p}` the ratio `(L_q/L_p)^t ≥ 1` and it is nonnegative on the
complement; Markov gives the pairwise bound. The infimum over `t` is
`exp(-n C(p,q))`; the union bound gives the family bound. `t = 1/2` is
admissible, so `C ≥ -ln ρ`, with equality forcing `t = 1/2`. ∎

The Hellinger exponent is `ln(1/ρ_*) = min_q(-ln ρ(p,q))`, while the Chernoff
exponent is `C_* = min_q C(p,q) ≥ ln(1/ρ_*)`. The refinement is therefore never
weaker, and is **strictly stronger in rate** whenever some minimising competitor
has its Chernoff optimum away from `t = 1/2`.

## The exponent is sharp; the finite-`n` prefactor is not

The exponent `C_*` is not an artefact of the union bound. For a finite alphabet
and pairwise-distinct laws, the exact-ML error has the large-deviation exponent
`C_*`:

```
lim_{n→∞} -(1/n) ln Pr_p{ ∃q∈Θ : L_q(R_1,…,R_n) ≥ L_p(R_1,…,R_n) } = C_* .
```

This is the classical Chernoff bound / Sanov theorem (Cover & Thomas 2006,
§11.9; Tsybakov 2009, Ch. 2): the binary rate `-(1/n) ln Pr_p(L_q ≥ L_p) → C(p,q)`
holds in both directions, the I-projection being the tilted law
`r* ∝ p^{1-t*} q^{t*}` at the optimising `t*`. The family rate is the minimum
over competitors, by `P(∃q error) ≥ P(q* error)` and
`P(∃q error) ≤ Σ_q P(q error)` for a competitor `q*` attaining the minimum.

Two consequences:

- **Rate.** The Chernoff union bound has the exact exponent `C_*`; the Hellinger
  union bound has exponent `ln(1/ρ_*) ≤ C_*`, which can be strictly smaller. So
  the refinement can turn a suboptimal rate into the optimal one.
- **Prefactor.** Even the Chernoff bound is not exact at finite `n`: the factor
  `|Θ|` overcounts overlapping error events, and the `Θ(1/√n)` Gaussian
  prefactor of the exact error is dropped, so the ratio
  `bound / exact` grows polynomially (roughly like `√n`) rather than staying
  bounded.

## Worked family: exact data and the gap

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
- No claim that `C_*`, `C(p,q)`, or the large-deviation exponent is
  kernel-checked. These are external standard statistics, cited to textbooks.
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
