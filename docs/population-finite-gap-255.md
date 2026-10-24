# Population-to-finite gap: a lens on when truth maximizes finite likelihood

_Status: 2026-10-14. Child of #255. Drafted by agent 91e0bcccb63a;
reviewed, corrected, and scoped by agent 4ba67d3247d8._

This note records an elementary mathematical observation that unifies the
population and finite-sample exact-multinomial objectives. It is a lens, not
a classification: it does not decide the fixed-`x` problem (A) or the
every-admissible-sample problem (B), and it closes no child issue.

## Setting

Fix a finite read-type universe `W`, the exact multinomial objective for one
observed count vector `x : W → ℕ` with total `n = ∑_w x(w) > 0`, the true
read distribution `p_S`, and a candidate read distribution `p_D`. Assume
`p_S` and `p_D` are positive on `W`. The empirical distribution is
`p̂(w) = x(w)/n`.

## Bridge identity

The candidate-dependent part of the exact finite-sample log-likelihood is

```
logLik(D; x) = ∑_w x(w)·log p_D(w) + const(x),
```

where `const(x)` is the candidate-independent multinomial coefficient. Since
`x(w) = n·p̂(w)`,

```
∑_w x(w)·log p_D(w) = n · ∑_w p̂(w)·log p_D(w).
```

So the finite-sample objective is exactly `n` times the **empirical**
population objective: the true distribution `p_S` is replaced by the
empirical distribution `p̂`.

## Fixed-sample equivalence (restatement, not a classification)

For the fixed observation `x`, subtracting the truth's empirical score from
a candidate's and using the bridge identity gives

```
truth maximizes the exact finite-sample likelihood for x
  ⟺ ∑_w p̂(w)·log p_S(w) ≥ ∑_w p̂(w)·log p_D(w)  for every candidate D
  ⟺ D_KL(p̂ ‖ p_S) ≤ D_KL(p̂ ‖ p_D)               for every candidate D.
```

That is, the truth is the KL-projection of the empirical distribution onto
the candidate set. This is an algebraic rewriting of the fixed-`x`
comparison, i.e. the (A)-regime halfspace-inequality condition already
recorded for #258/#259(A); it is **not** itself a classification of (A).

## Separation: population maximality does not imply finite-sample maximality

Population maximality always holds (Gibbs inequality, kernel-checked in
`AssemblyP1/PopulationGibbs.lean`): for every candidate `p_D`,
`ℓpop_S(D) = ∑_w p_S(w)·log p_D(w) ≤ ℓpop_S(S)`. The gap is that the
finite-sample objective uses `p̂`, not `p_S`.

Concrete two-type witness:

- `p_S = (1/2, 1/2)`, `p_D = (1/4, 3/4)`, empirical `p̂ = (1/4, 3/4)`
  (e.g. one read of type `A` and three of type `B`, `n = 4`).
- Population: `ℓpop_S(S) = log(1/2) ≈ −0.693 > ℓpop_S(D) ≈ −0.837`, so the
  truth maximizes at the population level.
- Finite sample: `∑ p̂ log p_D = (1/4)log(1/4)+(3/4)log(3/4) ≈ −0.562`,
  while `∑ p̂ log p_S = log(1/2) ≈ −0.693`; equivalently, the exact
  likelihood ratio is `(1/2)^1(3/2)^3 = 27/16 > 1`. Thus the candidate
  strictly beats the truth.

The exact-rational script `scripts/verify_255_population_finite_gap.py`
checks this witness without floating-point logarithms and adds the reversed
sample `x=(3,1)`, where the competitor/truth likelihood ratio is `3/16`.
Thus, even with truth and candidate distributions fixed, the outcome in (A)
depends on the observed counts; the population ordering does not decide it.
The script is a finite numerical check, not a proof for arbitrary candidate
sets or read-generation models.

## Relationship to #274

The #274 support-inclusion repair changed the population likelihood to be
`⊥` only when `supp p_S ⊄ supp p_D`. It does not affect this gap: the gap is
between the true distribution (population) and the empirical distribution
(finite sample), not between two population semantics. A candidate with
extra positive support still has finite population likelihood, and the Gibbs
inequality and tie characterization are unchanged.

## Scope and open questions

- The bridge identity and the separation witness are elementary and can be
  kernel-checked (finite sums, the Gibbs inequality, and one numeric
  comparison). **No kernel-checked artifact is claimed here.** The earlier
  draft `AssemblyP1/PopulationFiniteGap.lean` does not currently compile and
  is deliberately **not** landed; a corrected Lean formalization remains a
  possible follow-up.
- The condition `D_KL(p̂‖p_S) ≤ D_KL(p̂‖p_D) ∀D` is the fixed-`x` condition;
  when it holds for *every* admissible sample is the (B)-regime problem,
  already partly settled in the landed scopes (#256, #167) and otherwise
  OPEN.
- The `n → ∞` closure of the gap (empirical → true distribution) is the law
  of large numbers and is standard; it is not claimed as a new result.
- Nothing here concerns the MB09 §6.1 fixed-N product-binomial surrogate or
  the §6.2 bidirected-flow candidate domain.
