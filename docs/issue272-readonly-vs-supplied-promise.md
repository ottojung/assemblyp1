# Exact witness: read-only versus supplied promise

Fix two distinct orbit classes `g₀,g₁`, one read `r`, prior
`π(g₀)=π(g₁)=1/2`, and likelihood `p_g(r)=1` for both. The read-only posterior
at `r` is therefore `(1/2,1/2)`. No decoder that sees only `r` can be correct
with probability one under this joint law: its single output must disagree
with one positive-prior truth.

Now define the truth-dependent promise `E(g,r) := (g=g₀)`. If and only if the
promise is supplied as the auxiliary observation `E=true`, condition the joint
mass `π(g)p_g(r)1_E(g,r)` on `(r,E=true)`. Its only supported truth is `g₀`, so
the conditional posterior is one. The event holding at the unknown truth is
not itself an observation: without supplying it, the original posterior stays
`1/2` on each orbit. The verifier
[`scripts/verify_272_readonly_vs_supplied_promise.py`](../scripts/verify_272_readonly_vs_supplied_promise.py)
uses exact rational arithmetic and checks both cases.

This is a minimal counterexample separating read-only decoder certainty from
certainty under a truth-dependent external promise. It is intentionally an
abstract finite Bayesian experiment, not an AssemblyP1 read-string model or a
claim about the historical Not-So-Greedy algorithm.
