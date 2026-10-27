# Independent review: realizable sample-uniform criterion (#259)

Reviewed commit `175f1d1288a0dcc76bbaa51b95e54eb6d820d4d0` (the note is not
currently present on `origin/main`; the branch containing it is
`agent/2ZjlRi7TJE7EPuaLL4RGE6-issue259-review`). The note is a sound finite
quantifier reduction for its stated model, not a rigidity classification.

## Pairwise criterion check

For fixed `N` and candidate spectrum `B`, define
`q_i(B)=B_i ∏_{j≠i}(N-B_j)`. The product-binomial likelihood, after deleting
factors common to candidates, is `∏_i q_i(B)^{x_i}`. Thus its exact comparison
with truth `A` on the realizable complete-support family `X(A)` is precisely
`∀B∈C_G ∀x∈X(A), ∏q_i(B)^{x_i} ≤ ∏q_i(A)^{x_i}`. This argument includes
zero-count universe coordinates and boundary probabilities using `0^0=1`.
When every truth effective weight on `supp(A)` is positive, taking logs gives
log-domain caveat is handled correctly. A competitor with zero effective
weight on any required truth-support type has zero score on every member of
`X(A)`.

The declared observation family is specifically `x∈C_G`, hence `n=G`, even
though the general binomial score formula allows any `n`. Conclusions do not
extend to arbitrary sample sizes without changing `X(A)`. The note correctly
distinguishes the MB09 §6.1 fixed-external-`N` product of binomial marginals
from the exact multinomial objective.

## Relation to rigidity

The note does not prove rigidity necessity and appropriately says so. The
existing matrix theorem for the larger full-start-covered family uses samples
`A+y` with arbitrary nonnegative extras; that domain is not interchangeable
with the note's fixed-size realizable `X(A)`. In particular, a proof of
necessity must exhibit a violating `x` in that realizable family, not merely
an arbitrary count vector or a covered sample of unrestricted total size.

No arbitrary-`G,L,Σ,n` necessity theorem or smallest exact counterexample is
established by this review. The bounded L=2 and ternary L=3 censuses remain
finite evidence only. No claim is made for #260/#261 bidirected flows.

## Repository/integration observation

Verified remote: `https://github.com/ottojung/assemblyp1.git`. Current
`origin/main` at review time is `3decc39b4f8b5e187dc3df1b8c56720b4615045a`;
`175f1d1` is not an ancestor and the reviewed document is absent from main.
This is review evidence only; no integration or arbitrary rigidity result is
claimed.
