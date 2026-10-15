# A scoped sample-complexity bound for finite distinguishable read families (#265)

Status: 2026-10-15. Owner: agent `819f7aeb0f2d`. Base: `main` @
`67e1de76b4bf63c6bca625aaec98bb0b38fd9a18`.

This note records **one** rigorously scoped sample-complexity result for the
#265 arc: an explicit, *sufficient* number of i.i.d. reads that drives the
union/Bhattacharyya upper bound on exact maximum-likelihood (ML) error below a
target tolerance. It is an elementary algebraic inversion of the already
kernel-checked finite-family Hellinger union bound. It is not a new rate, not a
tight or minimax-optimal sample size, and not a claim about the unrestricted
universe of genome candidates.

It is the quantitative companion to the paper's Theorem `thm:finite-recovery`
and Remark `rem:sample-complexity`, and it is the closed-form generalisation of
the kernel-checked numerical illustration `il_confidence_99`.

## Model and assumptions (exact)

Fix:

- a finite read alphabet `W`;
- a true read law `p` on `W` (the law of a single read from the true genome);
- a finite candidate family `Θ` of read laws `q` on `W`, each `q ≠ p`;
- `R_1, …, R_n` i.i.d. `~ p`;
- the exact product likelihood `L_q(R_1,…,R_n) = ∏_{j=1}^n q(R_j)`, with ties
  counted as errors (so the statement covers every ML tie-breaking rule).

Definitions:

```
ρ(p,q) = Σ_{w∈W} √(p(w) q(w)) ∈ [0,1],      ρ_* = max_{q∈Θ} ρ(p,q).
```

The identity `Σ_w (√p(w) − √q(w))² = 2(1 − ρ(p,q))` gives `ρ(p,q) = 1` iff
`p = q`. Hence `ρ_* < 1` whenever `Θ` is nonempty and every member is distinct
from `p` (the empty family has an empty error event).

## The proved union bound (kernel-checked)

**Theorem (FiniteReadRecovery; paper Theorem `thm:finite-recovery`).** Under the
model above,

```
Pr_p{ ∃q∈Θ : L_q(R_1,…,R_n) ≥ L_p(R_1,…,R_n) }
      ≤ Σ_{q∈Θ} ρ(p,q)^n
      ≤ |Θ| · ρ_*^n .
```

The Lean endpoints are `AssemblyP1.FiniteReadRecovery.eventProb_pairwise`,
`eventProb_wrong_le_sum`, and `eventProb_wrong_le_card`; the asymptotic form is
`eventProb_wrong_tendsto_zero` and `exists_n_for_confidence`. The genome-level
adapter is in `AssemblyP1.FiniteReadRecoveryGenome`, and the primitive-P2
transport is in `AssemblyP1.FiniteReadRecoveryP2Complete`.

## New corollary: explicit sufficient sample size

**Corollary.** Under the model above, for every tolerance `δ ∈ (0,1]`,

```
n ≥ ⌈ ln(|Θ| / δ) / ln(1/ρ_*) ⌉     ⟹
      Pr_p{ ∃q∈Θ : L_q(R_1,…,R_n) ≥ L_p(R_1,…,R_n) } ≤ δ .
```

Consequently ML selection over the augmented family `{p} ∪ Θ` identifies `p`
strictly (no tie) with probability at least `1 − δ`.

**Proof.** Because `ρ_* < 1`, we have `ln(1/ρ_*) > 0` and

```
|Θ| · ρ_*^n = |Θ| · exp(−n · ln(1/ρ_*)) ≤ δ
```

exactly when `n ≥ ln(|Θ|/δ) / ln(1/ρ_*)`. Apply the kernel-checked union bound.
The recovered object is the read law `p`; transporting this to a genome rotation
class is the separate identifiability step of Corollary `cor:p2-finite-recovery`.
∎

### What this is, and what it is not

- It is a **sufficient** sample size obtained by inverting a union bound. It is
  not necessary, not minimal, and not a minimax-optimal rate.
- It is **conservative**: the union bound ignores that the competitors' error
  events overlap, and the Bhattacharyya factor `−ln ρ` is at most the optimal
  Chernoff exponent `C(p,q) = −min_{0≤t≤1} ln Σ_w p(w)^t q(w)^{1−t} ≥ −ln ρ(p,q)`
  (Cover & Thomas 2006, §11.9; Tsybakov 2009, Thm 2.4). Substituting a uniform
  `C_*` for `ln(1/ρ_*)` gives a bound at least as strong, but `C_*` is not the
  quantity kernel-checked here.
- It applies **only** to a finite family with a uniform separation `ρ_* < 1`.
  It does **not** cover the unrestricted universe of genome candidates (all
  lengths, all models); a sharp uniform sample-size guarantee there remains the
  genuinely open quantitative problem.
- The limit theorem supplies no finite `n`. This corollary does, but only under
  the stated finite-family hypotheses.

## Worked exact example (read-law level)

Take `W = {0,1}`, `p = (3/4, 1/4)`, and the single competitor `Θ = {q}` with
`q = (1/4, 3/4)`. Then

```
ρ(p,q) = 2 √((3/4)(1/4)) = √3 / 2 ≈ 0.866025,      ρ² = 3/4 .
```

For `δ = 0.01`:

```
n ≥ ln(1 / 0.01) / ln(2 / √3) = ln(100) / 0.143841 ≈ 32.014   ⟹   n = 33 .
```

Check: `ρ^33 ≈ 0.008680 ≤ 0.01`, while `ρ^32 ≈ 0.010023 > 0.01`. So 33 reads make
the union-Bhattacharyya bound at most `1%` for this single-competitor family.
The true per-truth ML error can be smaller; the corollary bounds the *bound*,
which is exactly what the theorem provides. `scripts/verify_sample_complexity_265.py`
reproduces these numbers and independently re-checks the union inequality by
exhaustive enumeration.

This is an illustration at the read-law level, not a claim about a particular
genome class. The affinity of any two concrete genome read laws must be computed
or bounded separately; no numerical worst-case affinity for the primitive-P2
class is computed here.

A second kernel-checked instance already in the library is
`AssemblyP1.FiniteReadRecovery.il_confidence_99`: `|Θ| = 3`, uniform affinity
`9/10`, and `n = 55` give `3·(9/10)^55 < 1/100`, matching the closed form
`⌈ ln(300)/ln(10/9) ⌉ = 55`.

## Sources

- Kernel: `AssemblyP1/FiniteReadRecovery.lean` (`eventProb_pairwise`,
  `eventProb_wrong_le_sum`, `eventProb_wrong_le_card`,
  `eventProb_wrong_tendsto_zero`, `exists_n_for_confidence`, `il_confidence_99`);
  `AssemblyP1/FiniteReadRecoveryGenome.lean`; `AssemblyP1/FiniteReadRecoveryP2Complete.lean`.
  Claim index: `docs/verification.md`.
- Paper: `paper/sections/05-population.tex` Theorem `thm:finite-recovery` and
  Corollary `cor:p2-finite-recovery`; Remark `rem:sample-complexity` and
  Corollary `cor:explicit-sample-size` in `paper/sections/03-open-question.tex`.
- Standard statistics (cited, **not** kernel-checked here): Cover & Thomas
  (2006), *Elements of Information Theory*, §11.9; Tsybakov (2009),
  *Introduction to Nonparametric Estimation*, Thm 2.4; Lehmann & Casella (1998)
  for the underlying consistency framework.
- Verifier: `scripts/verify_sample_complexity_265.py`.

## Non-claims

- No claim that this sample size is tight, minimal, or achievable.
- No claim that the general (non-equal-length) ML characterization is settled.
- No claim about the MB09 §6.1 product-binomial surrogate or the §6.2 flow
  model beyond the finite-family read-law statement above.
- No claim that the closed-form threshold itself is kernel-checked; it is
  elementary arithmetic on the kernel-checked union bound, and the concrete
  instance `il_confidence_99` is kernel-checked.
