# Exact witness: a proper promise can be informative but insufficient

Take three distinct truth-orbit classes `g₀,g₁,g₂`, a single read `r`, the
uniform prior `π(gᵢ)=1/3`, and deterministic likelihood `p_{gᵢ}(r)=1` for every
class. With no supplied side observation, each posterior is `1/3`.

Supply the truth-dependent promise `E(g,r) := (g∈{g₀,g₁})`, and condition the
joint mass `π(g)p_g(r)1_E(g,r)` on `(r,E=true)`. This removes the supported
competitor `g₂`, but leaves two classes with posterior `1/2` each: a proper
promise can be strictly informative without making recovery certain. A
strictly stronger supplied promise `F(g,r) := (g=g₀)` leaves posterior one on
`g₀`. Both updates require the event to be supplied; its truth at the unknown
world alone leaves the read-only posterior unchanged.

The exact-rational verifier
[`scripts/verify_272_intermediate_promise.py`](../scripts/verify_272_intermediate_promise.py)
checks the `1/3 → 1/2 → 1` sequence and zero posterior on excluded classes.
This finite Bayesian witness separates levels of information only; it does
not identify a least sufficient promise within any source-defined family and
is not an AssemblyP1 read-string example.
