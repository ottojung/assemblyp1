# Edge-flow / vertex-throughput Graver bridge (issue #263)

This note documents the kernel-checked Lean artifact
[`AssemblyP1/GraverThroughputBridge.lean`](../AssemblyP1/GraverThroughputBridge.lean)
and its axiom audit
[`AssemblyP1/GraverThroughputBridgeAudit.lean`](../AssemblyP1/GraverThroughputBridgeAudit.lean).

## What is proved

The module discharges the `HasGraverDecomposition` hypothesis consumed by the
already-merged separable-convex Graver optimality certificate
(`AssemblyP1.SeparableConvexGraver.graver_optimal_iff_no_improving`, PR #331),
**reusing** the integer-kernel conformal decomposition
`AssemblyP1.GraverRigidity.graver_decomposition` (#257). It does **not** reprove
that decomposition, the convex-objective half, or the historical signed-graph
adapter (#261, deliberately left open).

### The edge-flow system

With `E` the finite edge type, `V` the finite vertex type and `tail head : E → V`
the endpoint maps, the edge-flow map is

```
flowLin tail head f : (V ⊕ Unit) → ℤ
flowLin f (inl v) = (out-flow at v) - (in-flow at v)      -- balance row
flowLin f (inr _) = ∑ e, f e                              -- fixed-total row
```

* `flowLin_eq_zero_iff` — its kernel is exactly `BalancedZ f ∧ ZeroSum f`, i.e.
  the lattice `L₀ = ker_ℤ[M; 1ᵀ]` of `AssemblyP1.GraverRigidity`.
* `hasGraverDecomposition_flow` — the edge-flow system satisfies
  `HasGraverDecomposition`. A feasible displacement `y - z` is balanced and
  zero-sum (`flowLin (y - z) = 0`), so `graver_decomposition` returns a conformal
  Graver decomposition; `conformal_same_sign` shows that conformality to the
  common displacement gives the coordinatewise sign-compatibility required by
  `HasGraverDecomposition`.
* `graver_optimal_flow` — `graver_optimal_iff_no_improving` instantiated on the
  edge-flow system, with the decomposition hypothesis discharged, so the
  certificate is unconditional there.

### The augmented `[A 0; -T I]` system

The augmented system adds one throughput variable `s_v` per vertex and the
coupling row `s_v - (T f)_v = 0`:

```
augLin tail head T w : ((V ⊕ Unit) ⊕ V) → ℤ
augLin w (inl r)   = flowLin (fun e => w (inl e)) r        -- the [A 0] block
augLin w (inr v)   = w (inr v) - T (fun e => w (inl e)) v  -- the [-T I] block
```

* `augLin_eq_zero_iff` — its kernel is the graph `{(δ, T δ) : δ ∈ L₀}` of the
  throughput map `T` over the edge lattice; the identity block makes `s` a
  *dependent* slack, so the kernel projects isomorphically onto `L₀`.
* `hasGraverDecomposition_aug` — if `T` is additive and annihilates every Graver
  move (equivalently annihilates `L₀`), then the augmented system satisfies
  `HasGraverDecomposition`, by lifting the edge-flow decomposition
  `g ↦ (g, T g)`. In this case the throughput coordinate of every lifted Graver
  move is `0`, so the augmented sign-compatibility reduces to the edge one.

## The remaining open obstruction

The hypothesis `hT` of `hasGraverDecomposition_aug` says `T` is a linear
functional of the flow constraints (it vanishes on `L₀`). This is the case in
which the augmented system genuinely reduces to the edge-flow system.

For the *genuine* vertex-throughput map of the #261 flow model
(`T_v f = out-flow at v`) `hT` is **false**: `T` does not vanish on `L₀`, and the
throughput coordinates of the lifted Graver moves need not be sign-compatible.
Concretely, a conformal Graver decomposition `δ = Σ g_i` has every Graver move
`g_i` balanced, so `(T g_i)_v = out_{g_i}(v)`; at a vertex whose incident edges
carry both signs of `δ`, distinct Graver moves can have opposite-sign throughput
values, so the naive lift `g ↦ (g, T g)` does **not** automatically satisfy the
full augmented sign-compatibility. The correct general statement — a
`T`-sign-compatible conformal Graver decomposition for every `T` — is left
explicitly **OPEN**.

What the artifact establishes is the honest conditional bridge: the
certificate's decomposition hypothesis is a theorem for the edge-flow system, and
it lifts to the augmented `[A 0; -T I]` system precisely when the throughput
coordinates are redundant.

## Relation to the neighbouring fronts

* **#257 / #264** (`AssemblyP1/GraverRigidity.lean`): supplies
  `graver_decomposition`; this module consumes it and does not duplicate the
  integer-kernel conformal-minimal existence proof.
* **#259 / #261**: this module makes no claim about likelihood maximizers or the
  signed-graph adapter; it only wires the Graver decomposition hypothesis into
  the augmented flow/throughput matrix.
* **PR #331** (`AssemblyP1.SeparableConvexGraver.lean`): the conditional
  certificate is consumed as-is, not reproved.

## Cross-reference fix (product-binomial counterexample)

The same PR lands the small cross-reference fix noted in the issue:
`AssemblyP1/ProductBinomialMonotonicityCounterexample.lean` and
[`docs/issue263-product-binomial-monotonicity-counterexample.md`](issue263-product-binomial-monotonicity-counterexample.md)
now record that the coordinatewise-nonmonotonicity of the MB09 §6.1
product-binomial kernel is **already kernel-checked** as
`AssemblyP1.GeneralBidirectedFlowML.binomial_not_coordinatewise` (core `8 > 4`,
`docs/issue261-general-bidirected-flow-ml.md`), rather than attributing the
"8-vs-4" instance to the board. The genuinely new content of that module — the
single-coordinate sign-compatible Positive Sum Property (`HasPSS`) failure — is
foregrounded.

## Axioms

Every endpoint of `GraverThroughputBridge.lean` depends only on the standard
axioms `{propext, Classical.choice, Quot.sound}` (see the audit module). No
`sorry`, `admit`, `axiom`, or `native_decide` is used.
