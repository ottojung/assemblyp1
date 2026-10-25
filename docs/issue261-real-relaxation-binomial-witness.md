# Real-flow relaxation: an explicit §6.1 binomial gap (#261)

This closes a narrow implication left open in
`docs/issue261-half-integral-source-ml.md`: on the stated `AAATT` instance,
the continuous real-flow relaxation of the fixed-external-`N` §6.1 binomial
objective strictly beats every integer flow. It does not give a general
maximality criterion or settle source-fidelity of every reduction convention.

## Candidate class and objective

Use the non-palindromic observed support `{AAA,AAT,TAA}`, the `L=3`,
`o_min=1` overlap graph of `Section62NonSpelledFlow`, its full `graph1`, and
zero terminals. Candidates are nonnegative real edge flows satisfying the
same signed-incidence balance and vertex throughput lower bound `1` as
`Feasible62`. Truth is admitted. The score is the MB09 §6.1 product of
binomial marginals, external length `N=5`, read counts
`x=(2,1,1)`, with `0≤d_v≤5`; it is the approximation used in §6.2, not the
exact variable-length multinomial. Off-support throughputs are zero.

## Exact witness and proof

The already kernel-checked integer feasible flows `starFlow21` and
`starFlow31` have throughputs `(2,1,1)` and `(3,1,1)`. Their edge vectors
differ only by one extra unit on the `AAA→AAA` self-overlap. Their midpoint
is therefore a real flow, with edge values

```text
AAA→AAA: 3/2,  AAA→AAT: 1,  AAT→TAA (overlap 1): 1,  TAA→AAA: 1,
all other edges: 0.
```

Feasibility follows by convexity of every constraint: nonnegative edge
values, linear signed balance equalities, and throughput lower bounds are
preserved by averaging the two feasible endpoint flows. Its throughput is
`(5/2,1,1)`, still inside the binomial probability domain. The `AAT` and
`TAA` factors are unchanged from `(2,1,1)`. For `AAA`, with `x_AAA=2` and
`n=4`, the marginal is proportional to `d²(5-d)²`; hence

```text
M(5/2)/M(2) = ((5/2)^2(5/2)^2)/(2^2·3^2) = 625/576 > 1.
```

The exact integer argmax theorem `star_argmax` in
`Section62NonSpelledFlow` shows every integral throughput in the declared
domain that attains the best score has `d_AAA∈{2,3}` and the other two
coordinates equal to `1`. The displayed function is symmetric under
`d_AAA ↦ 5-d_AAA`, so both integer maxima have the same value as `d_AAA=2`.
Consequently this real feasible point strictly beats the entire integer
flow optimum, not merely the truth or one selected integer competitor.

This uses an especially direct relaxation argument: it is a convex mixture
of two source-predicate integer feasible flows, rather than an inference from
the score-only half-integral arithmetic. `scripts/verify_261_real_relaxation_binomial.py`
independently checks the rational edge values, balances, throughputs, binomial
domain, score ratio, and the two integer endpoint scores.

## Status boundary

Resolved: the real relaxation has a strict gap over integer flows for this
finite, explicitly specified graph and fixed-`N` binomial score. Open: whether
such a gap occurs under the exact variable-length multinomial; a general
necessary-and-sufficient criterion; arbitrary supports/overlap thresholds;
and invariance under a source-faithful transitive reduction. This witness is
on the full overlap graph and is not claimed to prove reduction invariance.
