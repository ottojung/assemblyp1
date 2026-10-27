# Issue #255 audit/status (2026-10-27)

This is a scoped audit, not a resolution of the research program. Project remote
verified as `https://github.com/ottojung/assemblyp1`; current audited base is
`origin/main` at `3decc39`.

## Claim check: fixed observation, exact multinomial

For a fixed count vector `x`, the multinomial coefficient `N!/∏x_i!` is
independent of the candidate. Thus comparing candidates is exactly comparing
`∏ p_i(candidate)^x_i`. If a truth-supported coordinate has `x_i=0`, its
factor is `p_i^0=1`, including when `p_i=0`; only positive-count coordinates
constrain support (a zero probability at positive count makes likelihood zero).
This calculation assumes the exact multinomial on a common oriented read-type
universe, with the same fixed read length and candidate probabilities given by
normalized oriented spectra. It is not the fixed-N product-binomial objective,
an RC-molecule-flow model, variable-length comparison, or historical read-string
`I_s` interpretation.

For a checkable instance, `S=AAABBB`, `D=AABBBB`, oriented length-2 types
`(AA,AB,BA,BB)`, and `x=(1,0,1,4)`, the likelihoods recorded in
`docs/issue255-fixedx-second-witness.md` are `P(S;x)=1/1458` and
`P(D;x)=1/576`, so `P(D;x)/P(S;x)=81/32>1`: truth strictly loses for this
fixed observation. The zero-count `AB` coordinate contributes `p_AB^0=1` to
both products. This is a witness, not a universal classification.

Evidence: `AssemblyP1/FixedXExactML.lean` (`fixedX_classification_iff`,
`specLik_le_iff_likProduct`) gives a kernel-checked product-inequality
criterion on its stated spectrum domain; the specific rational witness is
independently checked by `scripts/verify_255_fixedx_second_witness.py`.

## Status rows

| Status | Scoped claim | Evidence / remaining boundary |
|---|---|---|
| PROVED | Population exact likelihood is maximized by truth for every circular genome; repeats affect uniqueness, not maximality. | `PopulationUniqueness.population_maximizer_unrestricted`; population result only, not finite samples. |
| PROVED | For fixed `x`, exact multinomial comparison reduces to the candidate product inequality, including zero-count coordinates under `0^0=1`. | `AssemblyP1/FixedXExactML.lean`; fixed-length oriented spectrum domain only. |
| REFUTED | A structural claim that truth maximizes every finite exact-multinomial sample in the `AAABBB` oriented same-length setting. | The strict-loss witness above (`81/32`); no broader model claim follows. |
| PROVED (restricted) | Oriented same-length sample-uniform maximality iff support-spectrum rigidity, under the positive-support hypotheses. | `AssemblyP1/RobustSameLengthIff.lean`; does not transfer automatically to RC or §6.2 flows. |
| REFUTED (restricted) | Bridging alone suffices for historical molecule-flow full-overlap maximality. | Existing W1/W2 counterexamples; scope is historical molecule-flow semantics and full overlap. |
| OPEN | General fixed-observation structural characterization beyond exact pairwise product inequalities; general RC, variable-length, and §6.2 bidirected-flow/overlap-floor cases; historical literal `I_s` versus project placement `I_s`. | See `docs/remaining-open-matrix-255.md` and child fronts #257/#259/#261. No conjecture promoted. |

Child status cross-check from current main's matrix: #257 has scoped rigidity
results but broader taxonomy remains open; #259 has fixed-`x` product-binomial
criterion and several restricted sample-uniform results but full candidate
universe remains open; #261 has scoped §6.2 flow results, but general
bidirected-flow classification remains open. These are not duplicated here.
