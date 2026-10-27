# Issue #261: fixed-support pairwise flow comparison criterion

This note records a bounded consequence of the fixed-`n` count-vector theorem
for any proposed pair of feasible flows. It does **not** characterize which
throughputs are realizable in the source-faithful reduced bidirected graph.

## Model and statement

Fix the full molecule-type universe `T`, external genome size `N`, observed
support `I ⊆ T` with `m=|I|≥1`, and sample size `n≥m`. For a candidate
throughput vector `d:T→{0,…,N}`, define the integer effective weights

`q_i(d) = d_i ∏_{j∈T, j≠i}(N-d_j)`

and `P_d=∏_{i∈I}q_i(d)`. For an observation `x` with support exactly `I`
and total `n`, the §6.1 fixed-external-`N` product-binomial likelihood, after
discarding candidate-independent factors, is

`K(d;x)=∏_{i∈I}q_i(d)^{x_i}`.

Assume the truth `a` has `q_i(a)>0` for every `i∈I`. For any fixed proposed
candidate `b`, it never strictly beats `a` on any such observation **iff**

`∀k∈I,  P_b q_k(b)^(n-m) ≤ P_a q_k(a)^(n-m)`.

This includes `n=m`, where the condition is simply `P_b≤P_a`, and candidates
with a zero effective weight. The comparison is exact over integers; no
floating-point logarithms are needed. For a specified candidate set `C` of
throughputs (for example the image of a flow set under its throughput map),
uniform maximality of `a` is therefore equivalent to this finite family of
inequalities holding for every `b∈C`. This is a necessary-and-sufficient
criterion for that specified finite-`n`, fixed-support class, but may still
require examining every candidate in `C`; it is not asserted to be an
efficient structural or Graver certificate.

## Proof

Write `x_i=1+y_i` for `i∈I`; then `y_i≥0` and `∑y_i=t=n-m`. The likelihood
ratio is

`K(b;x)/K(a;x) = (P_b/P_a) ∏_{i∈I}(q_i(b)/q_i(a))^{y_i}`.

All denominators are positive by the truth-interiority hypothesis. If any
`q_k(b)=0`, then `P_b=0`, every admissible observation gives candidate score
zero, and all displayed inequalities hold. Otherwise the maximum over all
nonnegative integer allocations `y` of total `t` occurs by assigning all `t`
units to an index with greatest ratio `q_i(b)/q_i(a)`: a product of these
ratios is bounded by the largest ratio to the power `t`, and that bound is
attained by the corresponding concentrated allocation. Thus no observation
has ratio greater than one exactly when
`(P_b/P_a)(q_k(b)/q_k(a))^t≤1` for every `k∈I`, which is the stated
integer inequality.

## Scope and source boundary

The likelihood is the MB09 §6.1 separable product-binomial approximation with
fixed external `N`; it is not the exact variable-length multinomial and does
not by itself define candidate genome length. Candidates here are throughput
vectors with coordinates in the binomial probability domain, not necessarily
spelled circuits or circular genomes. Truth is admitted. The full type universe
is retained in each `q_i`, including unobserved types; replacing it by observed
coordinates changes the objective.

This proves no candidate-set inclusion, no transitive-reduction invariance, and
no orientation/reverse-complement quotient statement. In particular, one may
apply the criterion to a concrete finite flow image only after that image and
its throughput map have been specified. The unrestricted source-faithful
flow-level maximality and reduction/RC questions remain OPEN as recorded in
`docs/issue261-general-bidirected-flow-ml.md`.

## Validation

The existing exact-integer verifier
`scripts/verify_261_binomial_extreme_samples.py` exhaustively checks the
factorization and fixed-`n` extreme-sample equivalence over its stated finite
ranges, including boundary candidates. It reports 611,824 factorizations and
30,708 fixed-`n` comparisons passing. This is a computational regression, not
a proof of source-graph realizability; the argument above supplies the
mathematical proof for arbitrary finite `T`, `I`, `n`, `a`, and `b` satisfying
the stated hypotheses.
