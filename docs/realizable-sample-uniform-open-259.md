# Realizable sample-uniform MB09 maximality: exact finite criterion (#259)

This note makes explicit the quantifier reduction for the remaining
sample-uniform question. It is a general necessary-and-sufficient criterion,
but not yet a structural classification in terms of rigidity; the latter is
left open rather than inferred from finite censuses.

## Model and exact criterion

Fix an alphabet `Σ` with `|Σ|=s`, read length `L`, universe `U=Σ^L` (so
`|U|=s^L`), a circular candidate genome of fixed length `G≥L`, and fixed
external normalization `N=G`. For each candidate word `g∈Σ^G`, let `d_g(i)`
be the number of its `G` circular length-`L` windows equal to `i`; then
`∑_{i∈U}d_g(i)=G`. Let `C_G={d_g:g∈Σ^G}` be the finite set of distinct
realizable candidate spectra (including candidates with new support), and let
`A∈C_G` be the truth. An observation `x` is separately a realizable length-`G`
spectrum, so `∑_i x_i=n=G`; its complete-truth-support family is
`X(A)={x∈C_G : x_i>0 for all i∈supp(A)}`. This is the fixed-size,
source-faithful observation family used here; other sample sizes require a
separately defined observation class `X_n(A)` and are not silently included in
this theorem. The MB09 §6.1 approximation is a product of binomial marginals
with fixed external `N`, not the exact joint multinomial likelihood. After
deleting factors common to candidates, its objective is

```
F_B(x) = product_{i in U} [ B_i * product_{j != i}(N-B_j) ] ^ x_i.
```

Here `B_i=d_g(i)` and the term `N-B_j` represents the failure factor
`1-d_g(j)/N`, after clearing common denominators. This keeps the failure
probabilities for all zero-count coordinates. It is not the exact multinomial
likelihood, whose candidate-dependent numerator is `product_i B_i^x_i` and
whose normalization is candidate-independent when `N` and `n` are fixed.
Boundary values use `0^0=1` and `0^k=0` for `k>0`.

For the specified realizable complete-support observation family `X(A)`, the
exact necessary-and-sufficient test is

```
A uniformly maximizes on X(A)
 iff for every B in C_G and every x in X(A), F_B(x) <= F_A(x).
```

Equivalently, let `q_i(B)=B_i product_{j != i}(N-B_j)`. For each competitor
`B`, restrict to `S=supp(A)`. If some `q_i(B)=0` for `i in S`, that competitor
scores zero on every complete-support observation and cannot defeat the
truth. Otherwise the exact test is the finite family of log-linear
inequalities

```
sum_{i in S} x_i log(q_i(B)/q_i(A)) <= 0   for every x in X(A).
```

For this finite `X(A)`, the pairwise-score equivalence is an immediate iff,
not a conjecture. The log form is used only when all truth weights `q_i(A)` on
`S` are positive; otherwise use the exact integer-product comparison above.
If a candidate has `q_i(B)=0` on `S`, its score is zero on every `x∈X(A)`;
when the truth score is positive there, it cannot defeat the truth. It retains
realizability explicitly; replacing `X(A)` by all integer vectors above a
coverage baseline is generally stronger and is not justified for fixed-size
realizable samples. The covered-sample theorem documented in
`covered-binomial-maximality-259.md` supplies a simpler coordinatewise iff
only for that enlarged, arbitrary-sample family.

## Structural question still open

The criterion does not imply that a non-rigid realizable truth must lose on
some realizable complete-support observation. Rigidity concerns alternative
balanced spectra on the truth support, whereas the inequalities above are
tested only on the realizable observation set `X(A)` and also involve
new-support competitors through their full-universe `q_i`. A proof needs a
construction of a realizable `x` that violates one of the inequalities, or a
smallest exact counterexample showing that such a construction is impossible.
Neither is asserted here. In particular, all finite census results remain
bounded evidence, not a general rigidity necessity theorem.

## Scope

| Axis | Fixed here | Remaining |
|---|---|---|
| Objective | MB09 §6.1 fixed-external-`N` product of binomial marginals | Exact multinomial and §6.2 bidirected-flow objectives are distinct |
| Length and normalization | circular candidates with `G≥L`, same fixed length, `N=G`; `|U|=|Σ|^L` | Other normalizations/model interpretations |
| Support | truth support for observation coverage; competitors may have new support; all `U` factors retained | Structural simplification across support patterns |
| Sample size | observation and candidate spectra are length `G`, hence `n=sum x=G`; membership in realizable `X(A)` | Other `n`, and a theorem uniform over arbitrary `G,L,Σ` |
| Boundary | exact integer objective includes probabilities 0 and 1 | None in the pairwise test |
| Rigidity | no implication claimed | Necessity or smallest counterexample for realizable complete-support samples |

This is a quantifier/score criterion and a research reduction, not closure of
issue #259.
