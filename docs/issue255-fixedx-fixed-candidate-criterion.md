# Fixed-candidate criterion for exact finite likelihood

This is a checkable fixed-`x` reduction, not a solution of the general
classification problem. Fix a finite read-type set `E`, a positive genome
length `G`, truth spectrum `A : E → ℕ`, candidate spectrum `B : E → ℕ`, and
observed counts `x : E → ℕ`. Assume `A` and `B` have total mass `G` and that
every observed type lies in `E` (counts outside `E` are zero).

For the exact multinomial likelihood factor

`P(C;x) = ∏ e ∈ E, (C(e)/G)^(x(e))`,

the candidate-independent denominator cancels:

`P(B;x) ≤ P(A;x)  ↔  ∏ e ∈ E B(e)^(x(e)) ≤ ∏ e ∈ E A(e)^(x(e))`.

Indeed, each likelihood is its corresponding integer product divided by
`G^(∑e x(e))`; this denominator is positive since `G > 0`. The multinomial
coefficient also cancels because it depends only on the fixed observation `x`.
If `B(e)=0` for an observed type, the left product is zero, so the same
criterion handles support holes without logarithms or positivity assumptions
on the candidate.

Thus for a fixed finite candidate class `F`, truth maximality is exactly the
finite conjunction of these pairwise integer-product inequalities over `B ∈
F`. The inequality is sample-dependent; this algebraic reduction supplies no
structure-only verdict on truth maximality. It says nothing about whether the
chosen `E`, candidate class, or observation domain models historical `I_s`,
reverse-complement molecules, fixed-`N` binomial scores, or MB09 §6.2 flows.

The repository's kernel-checked `FixedXExactML.specLik_le_iff_likProduct` and
`fixedX_classification_iff` in `AssemblyP1/FixedXExactML.lean` establish this
reduction for the formal oriented same-length spectrum domain. Existing
`fixedX_four_chamber_iff_258` then evaluates the resulting finite conjunction
for one AAABBB instance; this note makes explicit the general fixed-candidate
interpretation and its boundary. It does not close the broader #255 fixed-`x`
or §6.2 classification.
