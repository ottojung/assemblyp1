# Minimal throughput sign-clash witness (#263)

This two-vertex, four-edge example makes the obstruction in
[`issue263-graver-throughput-bridge.md`](issue263-graver-throughput-bridge.md)
concrete. It is a diagnostic for the naive lift, not a theorem about all
throughput maps or a solution to the general bridge.

Let the vertices be `v₀,v₁`. There are four distinct directed loop edges
`a₀,a₁` at `v₀` and `b₀,b₁` at `v₁`. Distinct edge identities matter even though
the endpoints coincide. In edge order `(a₀,a₁,b₀,b₁)`, define

```
g₁ = (+1, 0, -1, 0)
g₂ = (0, -1, 0, +1)
δ  = g₁ + g₂ = (+1, -1, -1, +1).
```

Every edge is a loop, so all balance rows vanish. Both displacements have total
zero, and `g₁,g₂` are edge-coordinate conformal to `δ`. The exact finite
verifier exhaustively checks that each is Graver-minimal for the balance-plus-
total kernel: a conformal kernel summand of either two-coordinate vector can
only select a subset of its nonzero coordinates, and no nonempty proper subset
has total zero.

For the genuine source-oriented throughput `T_v(f) = outflow_f(v)`, loops count
once as outgoing. Thus `T(g₁)=(1,-1)`, `T(g₂)=(-1,1)`, while `T(δ)=(0,0)`.
In particular, at `v₀`, the two lifted throughput coordinates have opposite
strict signs although their sum is zero. They are not sign-compatible.

For the box `0 ≤ w_e ≤ 2`, take `z=(1,1,1,1)` and
`y=z+δ=(2,0,0,2)`. Both vectors are bounded, balanced, and have total 4. Their
throughputs agree: `T(z)=T(y)=(2,2)`. The Lean artifact
`AssemblyP1.ThroughputSignClash263` kernel-checks the kernel decomposition,
edge conformality, lifted throughput signs, and this bounded feasible pair.
The independent exact-integer verifier is
`scripts/verify_263_throughput_sign_clash.py`; it additionally checks
Graver-minimality by exhaustive bounded enumeration and rejects a mutated sign
claim.

This witness does **not** prove that a `T`-sign-compatible Graver decomposition
always exists or fails under additional modeling restrictions. The general
bridge remains **OPEN**; the #261 historical signed-graph adapter is separate
and untouched.
