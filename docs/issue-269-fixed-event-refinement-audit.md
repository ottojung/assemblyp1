# Issue #269: fixed-event refinement boundary

## Kernel-checked extension

`AssemblyP1.ConditionalRefinementAudit.event_refinement_success_monotone`
proves a finite refinement lemma for finite hypothesis space `Θ`, old sample
space `X`, and added observation space `Y`. Given old joint mass `J θ x`, new
joint mass `K θ x y`, consistent marginalization
`∑ y, K θ x y = J θ x`, an old policy `old`, a pointwise maximizing refined
policy `new`, and a fixed predicate `A : X → Prop`, success mass restricted to
`A` cannot decrease. The theorem is algebraic over `ℝ`; probabilistic
interpretation additionally requires genuine nonnegative normalized joint
masses.

For a *fixed old-sample event* `A`, event probability has the same value before
and after refinement: sum `hmarg` over `θ` and `x ∈ A`, then interchange the
finite sums. Consequently, when that common event probability is positive, the
conditional success inequality follows by dividing both event-restricted
success masses by that common positive denominator. The Lean theorem currently
checks the unnormalized event-restricted inequality; the division is this
one-line order-preserving normalization, not an independently exported
conditional-ratio theorem.

This extension does **not** establish monotonicity conditional on a
sample-size-dependent event. For example, `A_n = "every symbol was observed"`
is not a fixed event on the old sample space whose lift ignores the new read;
its probability and conditioning population can change between `n` and `n+1`.
No claim is made for that setting without additional hypotheses/comparison of
the two conditioning events. It also does not overlap the event-conditional
inference theorem in #266.

## Verifier

From the repository root, `lake build AssemblyP1.ConditionalRefinementAudit`
builds the exact module. The module's `#print axioms` reports
`[propext, Classical.choice, Quot.sound]` for the endpoint, with no
`sorryAx`/`admit` or added axiom. `python3 scripts/check-research-docs.py` is the
research-document integrity check. The theorem and its proof use finite sums,
the marginal equality, and the pointwise maximizing inequality; no external
computation or `native_decide` is involved.
