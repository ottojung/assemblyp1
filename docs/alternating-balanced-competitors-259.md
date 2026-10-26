# Balanced 2-mer competitors to the alternating spectrum

This note concerns only oriented 2-mers over the binary alphabet, with
coordinates ordered `(AA, AB, BA, BB)`. Fix `m >= 1` and the alternating
candidate `A=(0,m,m,0)`, of total mass `2m`.

## Complete balance parameterization

For `B=(a,b,c,d)` the endpoint-balance equations are

\[
a+b=a+c,\qquad c+d=b+d.
\]

Both equations are equivalent to `b=c`. With fixed total mass `2m`, this
gives `a+d+2b=2m`. In particular `a+d` is even; write `b=c=t` and
`a+d=2(m-t)`, where `0<=t<=m`. Thus the complete set is

\[
B=(u,t,t,2(m-t)-u),\quad 0\le t\le m,\quad 0\le u\le2(m-t),
\]
with integer parameters. This allows off-support AA and BB mass and has
`sum_{t=0}^m (2(m-t)+1)=(m+1)^2` members.

The exhaustive verifier `scripts/verify_alternating_balanced_competitors_259.py`
enumerates all nonnegative quadruples of mass `2m` and independently filters
the two balance equations, comparing the resulting set to this parameterized
set for `m=1,...,8`.

## Exact MB09 §6.1 consequence for this family

For any observed nonnegative count vector `x=(x_AA,x_AB,x_BA,x_BB)`, sample
size `n=sum x`, and fixed external normalization `N`, the product-binomial
objective is

\[
Q_N(C;x)=\prod_w (C_w/N)^{x_w}(1-C_w/N)^{n-x_w},
\]
with the usual boundary convention (a zero exponent contributes 1). It is
defined for these candidates when `N>=2m`; this is the MB09 §6.1 approximation
with fixed external `N`, not the exact joint multinomial likelihood.

The alternating candidate has zero AA and BB probabilities. Consequently,
if either `x_AA<n` or `x_BB<n`, its objective is zero. Every balanced
competitor above has both AB and BA counts equal to `t`; a competitor has
positive objective only if its zero/nonzero support is compatible with the
observed zero-count factors. This parameterization alone does not imply
maximality or non-maximality: the outcome depends on `x`, including its
zero-count coordinates and on `N`. In particular, the competitors with
`t=m,u=0` give exactly `A`, while other choices can put mass on AA/BB.

This is a classification of balanced integer competitors, not a claim that
every such vector is a realizable spectrum of a genome, nor a general
fixed-sample or sample-uniform ML theorem. It does not settle the graph
rigidity necessity question.
