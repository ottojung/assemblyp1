# Review: alternating binary 2-mer truth in #259

The branch artifact at commit `3086d71` correctly parameterizes balanced
competitors to the circular binary alternating spectrum, but its calculation
only evaluates the single sample `x=A`. The claimed goal of all covered samples
can be settled more directly from the general effective-weight criterion.

Let the genome length and fixed external normalizer be `N=G=2m`, with `m≥1`,
and truth `A=(0,m,m,0)` in class order `(00,01,10,11)`. For every candidate
`B=(a,t,t,d)` of the same length, `a+d+2t=2m`. On the true support the exact
integer effective weights of the MB09 §6.1 product-binomial surrogate are

```
q_N(B,01)=t(2m-a)(2m-t)(2m-d),
q_N(B,10)=t(2m-a)(2m-t)(2m-d).
```

At the truth these both equal `m^3`. Since `a+d=2m-2t`, at least one of `a,d`
is positive whenever `t<m`. Thus one factor among `(2m-a),(2m-d)` is at most
`2m-1`; also `t≤m` and `2m-t≤2m`. Consequently

```
q_N(B,01)=q_N(B,10) ≤ m · 2m · (2m-1) < m^3
```

is not valid as written for general `m`; a sharper product bound is required.
This elementary attempted bound is insufficient and this review does not claim
an all-`m` theorem. (For example, the factor bound loses the relation between
the two endpoint factors.)

The exact covered-sample criterion for finite weights says that `A` dominates
`B` for every `x≥A` iff either a true-supported candidate effective weight
vanishes or both are pointwise no larger than the corresponding truth weights.
Here both candidate supported weights are equal, so all-covered-sample
dominance reduces to the single integer inequality

```
t(2m-a)(2m-t)(2m-d) ≤ m^3.
```

This reduction is proved once the criterion's hypotheses are instantiated; the
remaining inequality is open in this note. The branch's finite exact check for
`x=A` through `m=100` is evidence only, not a proof for all `m` or all covered
samples. Candidate lengths, normalizer, complete four-class universe and
sample-size convention are as stated above; this is the §6.1 surrogate, not
the exact multinomial or §6.2 bidirected-flow objective.

## Scope

This is a diagnostic review and a reduction, not a classification result. It
does not address arbitrary observed samples, other read lengths/alphabets, or
the full realizability-constrained issue. The correctness of the branch's
balanced-spectrum parameterization remains useful: every circular binary
2-mer spectrum has form `(a,t,t,d)`, and realizability must still exclude
`t=0` with both `a,d>0`.
