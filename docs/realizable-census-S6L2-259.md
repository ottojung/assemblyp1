# Senary-L2 realizable complete-support census (board issue #259)

_Status: independent exact-integer verification in
`scripts/verify_realizable_census_S6L2_259.py` (no Lean import, no floats
in any comparison)._

This note covers the first `alphabet>=6` cell for the MB09 §6.1
fixed-external-`N` product-binomial surrogate: senary (alphabet 6)
`L=2`, `G=4..5`.

| cell | genomes | distinct truth spectra | rigid & maximal | rigid & NOT maximal | non-rigid & maximal | non-rigid & NOT maximal |
|------|---------|------------------------|-----------------|---------------------|---------------------|-------------------------|
| senary L=2, G=4 | necklaces | 336 | 306 | 30 | **0** | 0 |
| senary L=2, G=5 | necklaces | 1500 | 1290 | 120 | **0** | 90 |

Total: **1836** new truth spectra, **0** non-rigid maximal
(rigidity-necessity holds in this cell), **150** rigid-but-beaten
(sufficiency fails, each beaten only by new-support candidates with an
explicit exact-integer witness).

## Method (exact)

Candidate length, normalization, support, sample size, and the
§6.1-vs-exact distinction are as in `docs/fixedx-product-binomial-259.md`
and `docs/product-binomial-rigidity-necessity-259.md` (same-length
universe `E` of `6^2 = 36` classes, fixed external `N = G`, truth
support `supp A`, free covered sample size `n >= N`, extra `(N-B_j)`
factors retained, including zero-count coordinates and boundary
probabilities `0`/`1` handled by the exact reduced comparison with a
dedicated `zero_on_support` guard).

Maximality is decided by the kernel-checked covered-sample iff: `A`
beats `B` iff `B` has a zero effective weight on `supp A` or is
pointwise dominated there. The comparison uses the exact reduction of
the earlier realizable census scripts (classes outside
`supp A ∪ supp B` contribute factor `N` on both sides and cancel), so
each comparison needs only `|supp A ∪ supp B| <= 2G` multiplications on
the 36-class universe.

Every recorded violation carries an explicit exact-integer witness
sample `x = A + t*e_i` with `F_B(x) > F_A(x)` (single-coordinate boost
on a strictly-beating class; `t` solved analytically from the log-ratio
then verified with exact integers). Examples: `G=4`, covered sample at
`n=19` (`t=15`); `G=5`, covered sample at `n=31` (`t=26`). A self-comparison
plus a one-symbol-mutant pin prove the verifier is not vacuous, and a
comparison counter asserts the census decided real cross-genome pairs.

## Reading of the results

- **Necessity holds**: zero non-rigid maximal truths in all 1836 spectra,
  confirming the Lean theorem `robust_iff_unique` computationally in a
  new `alphabet>=6` cell.
- **Sufficiency fails**: 150 rigid truths are beaten by new-support
  candidates — rigidity is necessary but not sufficient, as predicted.
- Unlike the quinary-L3 cell (all truths rigid), the `G=5` sub-cell
  contains 90 non-rigid truths, all correctly classified NOT maximal —
  so both sides of the necessity implication are exercised here
  (non-rigid truths exist and none is maximal).

## Scope matrix

| Item | Covered here | Still open |
|------|--------------|------------|
| Objective | MB09 §6.1 product-binomial surrogate | exact multinomial (`#256`); §6.2 flows (`#260`/`#261`, untouched) |
| Cells | senary L2 G=4..5 (this note); earlier: quinary L3 G=5..6, binary L5, ternary L5, binary L7, binary/ternary L6, quaternary L4 (unmerged chain) | larger L/G, alphabets>=7, senary L2 G>=6 |
| Classification | realizable complete-support maximality via covered-sample iff | full new-support class theorem (sufficiency fails; no converse) |
| Verification | exact-integer census + explicit witnesses + mutation pins | kernel Lean theorem for the new cell (bounded evidence only) |
