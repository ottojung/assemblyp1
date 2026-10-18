# Exact finite-`n` minimax/optimal recovery for one explicit read family (#265)

Status: 2026-10-18. Owner: agent `2ff061e25974`. Base: `main` @ `15c8c19`.

This note records the **tight** finite-`n` recovery numbers for one explicitly
specified finite distinguishable read family, together with an exact-rational
verifier. It is the quantitative companion to the paper's Remark
`rem:minimax-sample-size` (`paper/sections/03-open-question.tex`) and to the
sufficient-sample-size notes `docs/sample-complexity-265.md` and
`docs/chernoff-exponent-finite-recovery-265.md`.

The earlier notes bound the *bound* (a union/Bhattacharyya or Chernoff upper
bound, inverted to a sufficient `n`) and explicitly disclaim tightness,
minimality, and minimax optimality. Here we instead compute the **exact optimum
for one small family** — both the prior-averaged (Bayes) optimum and the
minimax-over-truths optimum — and the exact minimal `n` for a 99% recovery
target, with a matching lower bound for each criterion.

Everything below is standard decision theory (finite Bayes risk; minimax equals
the maximum Bayes risk over priors) plus exact finite arithmetic. **None of the
specific numbers is a Lean theorem.** The only kernel-checked constants in this
circle remain the abstract Bayes-optimality statements of
`AssemblyP1.FiniteBayesDecision` / `FiniteMapOptimality` and the Hellinger union
bound of `AssemblyP1.FiniteReadRecovery`.

## Model and the chosen family (exact)

Read alphabet `W = {0,1}`. A read law is a pair `p = (p(0), p(1))`. Fix the
finite distinguishable family of read laws

```
A = (1/2, 1/2),     B = (3/4, 1/4),     C = (1/4, 3/4),
```

which are pairwise distinct; the largest pairwise Hellinger affinity is
`rho_* = max_{t != u} rho(t,u) = rho(A,B) = rho(A,C) = (sqrt 3 + 1)/(2 sqrt 2) =
0.9659258263... < 1`. The family is invariant under the symbol swap `0 <-> 1`
(which fixes `A` and exchanges `B,C`); this symmetry is what makes the minimax
computation below clean.

Observe `n` i.i.d. reads `R_1, ..., R_n`. The count `k = #{i : R_i = 1}` is a
sufficient statistic, with exact product likelihood

```
L_t(k) = prod_i P_t(R_i) = P_t(k) = C(n,k) p_t(0)^(n-k) p_t(1)^k,   t in {A,B,C}.
```

The truth is one of `A, B, C`; a decision rule (deterministic or randomized)
observes `k` and returns a guess in `{A, B, C}`. The **exact-ML / MAP regions**
for the uniform prior are, with `alpha = ln 2 / ln 3 = 0.6309297...`,

```
B  for  k <= (1-alpha) n,   A  for  (1-alpha) n <= k <= alpha n,
C  for  k >= alpha n,       (ties split; the optimal value is tie-rule independent).
```

Because the three laws are pairwise distinct and the family is finite, the
uniform prior is a legitimate fixed prior and ML = MAP for it.

## Prior-averaged (Bayes) optimum, exactly

With the uniform prior `pi = (1/3, 1/3, 1/3)` and zero-one loss, the optimal
prior-averaged success is the Bayes success

```
V_n = sum_{k=0}^{n} max_{t in {A,B,C}} (1/3) P_t(k) = (1/3) sum_k max_t P_t(k).
```

The optimal rule is ML/MAP, and ties are resolved by splitting (any tie rule
gives the same value).

**Exact result (verified, not Lean).** `V_n` is non-decreasing in `n`, and the
exact minimal sample size for a 99% prior-averaged recovery is

```
n*_Bayes = 85,   with   V_84 = 0.98925764... < 0.99 <= V_85 = 0.99006833...
```

`V_85` is the exact rational

```
V_85 = 2893972976464393907418071635325873973663341063781
     / 2923003274661805836407369665432566039311865085952 .
```

**Matching lower bound.** For *any* deterministic or randomized rule `d`, the
prior-averaged error satisfies `(1/3) sum_t P_t(d wrong) >= 1 - V_n`: the Bayes
risk is the minimum possible average risk. Hence no rule identifies the truth
with prior-averaged probability exceeding `V_n`, and `n*_Bayes = 85` is exact,
not merely sufficient. (This is the standard finite Bayes theorem; it is also
kernel-checked abstractly as `AssemblyP1.FiniteBayesDecision` /
`FiniteMapOptimality`.)

### Prior-averaged optimum versus per-truth behavior

The optimal rule's *per-truth* success differs from the average. At `n = 85`,
with the optimal tie-splitting rule,

```
success(A) = 0.98349118...,   success(B) = success(C) = 0.99335691...,
( success(A) + success(B) + success(C) ) / 3 = V_85 = 0.99006833...
```

The middle truth `A` is strictly harder than `B` and `C`: the ML region of `A`
is the central band `[(1-alpha)n, alpha n]`, so `A` fails in *two* tails, while
`B` and `C` fail in one. The prior average is pulled up by the easier truths, so
"99% recovery" is a statement about the average, not about each truth. (The
per-truth success is not claimed to be monotone in `n`; that failure is the
kernel-checked `AssemblyP1.NonmonotonicityWitness281` result, a different
family.)

## Minimax-over-truths optimum, exactly

The adversarial (minimax) criterion is

```
V^mm_n = min_d max_t P_t(d wrong)  =  max_pi R_n(pi),
```

where `R_n(pi) = 1 - sum_k max_t pi_t P_t(k)` is the Bayes error for prior `pi`
and the second equality is the minimax theorem. Because the family is invariant
under `0 <-> 1`, for any prior `pi` the symmetrised prior
`pi_sym = (pi + mirror(pi))/2` satisfies `R_n(pi_sym) >= R_n(pi)` (Bayes risk is
concave in the prior), so the maximum is attained at a **symmetric** prior
`pi = (1-2 gamma, gamma, gamma)`, `gamma in [0, 1/2]`. The Bayes error
`R_n(gamma)` is concave and piecewise linear in `gamma`, changing slope only
where the `A`-versus-`B` boundary moves, i.e. at

```
gamma_k = P_A(k) / ( P_B(k) + 2 P_A(k) ),   k = 0, ..., n,
```

together with `gamma = 0, 1/2`. Its maximum is therefore attained at one of
these finitely many breakpoints.

**Exact result (verified, not Lean).** The minimax error is non-increasing in
`n`, and the exact minimal sample size for 99% minimax recovery is

```
n*_minimax = 87,   error_86 = 0.01051594... > 0.01 >= error_87 = 0.00973853...
```

At `n = 87` the least favourable prior is
`gamma* = 154742504910672534362390528 / 483934220830465247795951563 =
0.31975938...`, i.e. `pi* = (0.36048125..., 0.31975938..., 0.31975938...)`.

**Matching certificate (both bounds).** For the least favourable `pi*` the
Bayes rule is `B` on `k <= 31`, an `A`/`B` likelihood tie at `k = 32`, `A` on
`33 <= k <= 54`, an `A`/`C` tie at `k = 55`, and `C` on `k >= 56`. Splitting the
two ties toward `A` with probability `p = 0.99199062...` equalises the per-truth
errors and gives

```
max_t error(t) = 0.00973853... = R_87(pi*) = V^mm_87's complement.
```

- **Lower bound:** `V^mm_n >= R_n(pi)` for every prior `pi`, so
  `V^mm_87 >= R_87(pi*) = 0.00973853...`.
- **Upper bound:** the exhibited tie-split Bayes rule attains
  `max_t error(t) = 0.00973853...`.

The two bounds coincide, so `n*_minimax = 87` is exact. Note that the *plain*
Bayes rule for `pi*` (without the optimal tie split) has a strictly larger
worst-case per-truth error (`0.01375...`); the tie split is what makes it
minimax. This is why ties must be handled explicitly rather than counted
uniformly as errors.

## Zero-mass cases

The family above has full support on `{0,1}`, so no zero-mass case arises. The
convention used throughout (and in the kernel-checked
`AssemblyP1.FiniteReadRecovery`) is the standard one: a factor `P_t(w) = 0` for
an *observed* symbol `w` makes `L_t = 0`, so that candidate is excluded; an
unobserved symbol contributes the factor `P_t(w)^0 = 1`. The verifier checks the
simplest zero-mass sub-case explicitly: for `A = (1/2,1/2)` and the zero-mass
competitor `Z = (0,1)`, the ML error is `P_A(k = n) = 2^{-n}`, since `L_Z = 1`
only on the all-ones sample and `L_Z = 0` otherwise.

## Conservativeness of the kernel-checked union bound

The Hellinger union bound of `AssemblyP1.FiniteReadRecovery` (paper Theorem
`thm:finite-recovery`) gives the sufficient size

```
n >= ceil( ln(|C_S|/delta) / ln(1/rho_*) ) = ceil( ln(2/0.01) / ln(1/rho_*) )
   = ceil( 152.83 ) = 153       for delta = 0.01,
```

whereas the exact optimum is `85` (prior-averaged) or `87` (minimax). At `n = 85`
the union bound is `2 rho_*^85 = 0.105...`, about `6.4x` the exact per-truth
error of `A` (`1 - 0.98349... = 0.01651...`). The union bound is valid and
kernel-checked; it is simply conservative, as expected from the earlier
Chernoff-gap analysis. The limit theorem supplies no finite `n`; the exact
`85`/`87` here are specific to this one family and model, not universal.

## What this is, and what it is not

- It is an **exact, tight** finite-`n` result for one explicit finite family
  under the i.i.d. read-law model, for both the prior-averaged and the
  minimax-over-truths criteria, with matching lower bounds.
- It is **not** a Lean result. The exact numbers are exact finite arithmetic in
  `scripts/verify_minimax_finite_recovery_265.py`; the decision-theoretic
  ingredients (Bayes risk minimality; minimax = maximum Bayes risk) are external
  textbook statistics, and the abstract Bayes-optimality statement is separately
  kernel-checked in `AssemblyP1.FiniteBayesDecision` / `FiniteMapOptimality`.
- It is **not** a claim about the unrestricted universe of genome candidates (all
  lengths, all models), nor about the MB09 Section 6.1 product-binomial
  surrogate or the Section 6.2 flow model. A tight uniform sample size over that
  universe remains the genuinely open quantitative problem.
- It is **not** a claim that `85`/`87` are minimax over all read families; the
  minimax there is over the *truths within this one family*.

## Sources

- Verifier (exact rational, recomputes the optimum from scratch):
  `scripts/verify_minimax_finite_recovery_265.py`.
- Paper: `paper/sections/03-open-question.tex` Remark `rem:minimax-sample-size`;
  the sufficient-size Remark `rem:sample-complexity`, Corollary
  `cor:explicit-sample-size`, Proposition `prop:chernoff-refinement`; and the
  kernel-checked Theorem `thm:finite-recovery`.
- Kernel (abstract, not these numbers): `AssemblyP1/FiniteBayesDecision.lean`
  (`chooseMAP_optimal`, `chooseMAP_optimal_randomized`, `finite_iid_MAP_optimal`);
  `AssemblyP1/FiniteMapOptimality.lean`; `AssemblyP1/FiniteReadRecovery.lean`
  (`eventProb_pairwise`, `eventProb_wrong_le_sum`, `eventProb_wrong_le_card`);
  claim index `docs/verification.md`.
- Standard decision theory (cited, **not** kernel-checked here): Berger (1985),
  *Statistical Decision Theory and Bayesian Analysis* (finite Bayes risk;
  minimax theorem; least favourable priors); Lehmann & Casella (1998),
  *Theory of Point Estimation* (minimax = maximum Bayes risk over priors).
- Companion notes: `docs/sample-complexity-265.md`,
  `docs/chernoff-exponent-finite-recovery-265.md`.
