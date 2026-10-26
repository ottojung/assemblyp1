# Alternating binary 2-mer competitors: exact parameterization (#259)

This note records a bounded exact check at the alternating truth and a useful
complete parameterization. It does **not** prove sample-uniform maximality.

For a circular binary genome of length `G=2m`, the truth `0101...` has
2-mer spectrum `A=(0,m,m,0)` in class order `(00,01,10,11)`. Every circular
binary word has equally many `01` and `10` transitions: crossing a `0→1`
edge must be balanced by a `1→0` edge around the cycle. Thus every realizable
competitor has the form

```
B=(a,t,t,d),   a,d,t >= 0,   a+d+2t=G=2m.
```

For `t>0`, every such triple is realizable: concatenate `t` positive zero-runs
and `t` positive one-runs cyclically, distributing `a` extra zero symbols and
`d` extra one symbols among their respective runs. For `t=0`, the length
constraint forces exactly one of `a,d` to equal `G`, giving the two constant
words; the impossible case `a,d>0` is excluded. Thus the realizability
parameterization is `a,d>=0`, `a+d` even, `t=m-(a+d)/2`, with `(a,d)=(0,2m)`
or `(2m,0)` when `t=0`. The unconstrained parameter set of triples has
`(m+1)^2` elements, of which the `t=0, a,d>0` cases are not spectra.

The objective used here is MB09 §6.1's fixed-external-`N` product-binomial
surrogate, with `N=G` and integer score

```
q_N(B,i) = B_i ∏_{j≠i}(N-B_j),   F_N(B,x)=∏_{i=0}^3 q_N(B,i)^{x_i}.
```

The product includes zero-count classes, hence retains the binomial failure
factors. `N` is the common genome length for all candidates; the observed
sample size is `n=∑x` and is not assumed equal to `N`. The omitted binomial
coefficients and powers of `N` are candidate-independent. This is not the exact
joint multinomial objective (#256) or the MB09 §6.2 bidirected-flow model
(#260/#261).

For the covered sample `x=A`, `q_N(A)=(0,m^3,m^3,0)`. If `t=0`, the candidate
has no `01`/`10` support and scores zero at `A`; if `t>0`, direct substitution
gives

```
q_N(B,01) = t (N-a)(N-t)(N-d),
q_N(B,10) = t (N-a)(N-t)(N-d),
F_N(B,A) / F_N(A,A)
  = [ t (N-a)(N-t)(N-d) / m^3 ]^(2m).
```

This expression, together with `a+d+2t=N=2m`, is the remaining elementary
inequality to establish for a proof at `x=A`; even that would not imply
maximality for every covered `x>=A`, which also varies the exponents of all
four effective weights.

## Exact bounded evidence

`scripts/verify_alternating_balanced_259.py` uses `Fraction` arithmetic to
enumerate every balanced parameter triple for `1<=m<=100` (348,550 triples
total) and compares the exact product-binomial score at `x=A`.
Observed result: no strict beat. This is only a finite check at the single
covered sample `x=A`, not a proof for arbitrary `m` and not a check of all
covered samples `x>=A`.

Scope: same-length circular binary 2-mer spectra, fixed `N=G`, complete
candidate class universe of four 2-mers, true support `{01,10}`, and covered
samples satisfying `x_01,x_10>=m`, `x_00=x_11=0`; `n` is free. General
alphabets, larger read lengths, full-class observed support, and the
realizability-constrained all-sample iff remain open. No conclusion about
necessity of graph rigidity is drawn.
