# Exact fixed-n extreme-sample iff for §6.1 (#261)

**Formalized theorem:** `AssemblyP1.Section62FiniteNExtremeSamples.binomial_fixed_n_extreme_iff`.
This settles the formerly numerically audited *fixed-n count-vector* criterion;
it does not settle all §6.2 bidirected-flow maximality questions.

Let `I` be the nonempty observed-support set, `n=|I|+t` the fixed
number of reads with exactly one or more observations of every class in
`I`, and `A,B` full-universe candidate count vectors. Fix the external
genome-size parameter `N` in Medvedev–Brudno §6.1. Require only
`q_i(A)>0` for each observed class; allow any nonnegative candidate
weights, including zeros. As in the existing kernel-checked model,

`q_i(C) = d_i(C) ∏_{j≠i}(N-d_j(C))`, including all **unobserved** classes,
and `K(C;x)=∏_{i∈I}q_i(C)^{x_i}` for exactly supported samples.

Write `P_C=∏_{i∈I}q_i(C)`. Then the following are equivalent:

1. For **every** integer observation vector `x` with exactly support
   `I` and total read count `n`, `K(B;x)≤K(A;x)`.
2. For **each** `k∈I`, `P_B q_k(B)^t ≤ P_A q_k(A)^t`.

These `|I|` inequalities are precisely the extremal observations with
one read from every observed class and the remaining `t` reads all
concentrated on the distinguished class `k`. **No other allocations
need to be enumerated.** It covers ties, `t=0`, and zero candidate
weights without dividing by zero.

The proof is composed of three general nonnegative-product extremal
lemmas (`product_le_extreme`, `rational_extreme_iff`,
`weighted_extreme_iff`), plus the finite-sample decomposition
`surplus_sum_of_fullcoverage` and `binomCoreNat_factor_surplus`,
then the exact §6.1 `binomCoreNat_eq_prod_qFac` identity.
It is fully Lean-kernel-checked, with standard axioms only
(`propext`, `Classical.choice`, `Quot.sound`), no `sorry`.

**Nonvacuity regressions.** At external N=3, truth A=(1,2), candidate
B=(1,1) have effective weights q(A)=(1,4), q(B)=(2,2).
For exactly n=2 covered reads the likelihood ties (4 vs 4);
for n=3 a covered sample (2,1) prefers B (8 vs 4). Lean proves the
fixed-n classification in both cases, and separately the zero-weight
candidate boundary. These demonstrate why fixed-n and all-n criteria
are different.

**Scope:** exact fixed-N **count-vector** product-binomial pseudo-
likelihood over a full finite type universe; truth has positive observed
q weights. This does **not** infer that every full count vector comes
from one genome, or that every feasible signed biflow can be realized as
a single genome. Reverse-complement molecule-type semantics are a
separate graph/model adapter obligation. The independent finite audit
`scripts/verify_261_binomial_extreme_samples.py` remains as a regression.
