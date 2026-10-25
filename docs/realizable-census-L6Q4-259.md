# Realizable complete-support census for L>=6 and alphabets>=4 (board issue #259)

_Status: independent exact-integer verification in
`scripts/verify_realizable_census_L6Q4_259.py` (no Lean import, no floats
in any comparison)._

This note extends the `#259` realizable-class census beyond the ternary
L4/L5 handoffs, covering three previously open cells for the MB09 §6.1
fixed-external-`N` product-binomial surrogate:

| cell | genomes | distinct truth spectra | rigid & maximal | rigid & NOT maximal | non-rigid & maximal | non-rigid & NOT maximal |
|------|---------|------------------------|-----------------|---------------------|---------------------|-------------------------|
| binary L=6, G=6..12 | necklaces | 764 | 734 | **30** | **0** | 0 |
| ternary L=6, G=6..9 | necklaces | 3474 | 3474 | 0 | **0** | 0 |
| quaternary L=4, G=4..8 | necklaces | 11540 | 11444 | **96** | **0** | 0 |

Total: **15778** new truth spectra, **0** non-rigid maximal
(rigidity-necessity holds in every new cell), **126** rigid-but-beaten
(sufficiency fails, all beaten only by new-support candidates).

## Method (exact)

Candidate length, normalization, support, sample size, and the
§6.1-vs-exact distinction are as in `docs/fixedx-product-binomial-259.md`
and `docs/product-binomial-rigidity-necessity-259.md` (same-length
universe `E`, fixed external `N = G`, truth support `supp A`, free covered
sample size `n >= N`, extra `(N-B_j)` factors retained).

Maximality is decided by the kernel-checked covered-sample iff: `A`
beats `B` iff `B` has a zero effective weight on `supp A` or is
pointwise dominated there. The comparison uses an exact reduction:
classes outside `supp A ∪ supp B` contribute factor `N` on both sides
and cancel, so each comparison needs only `|supp A ∪ supp B| <= 2G`
multiplications — this is what makes the 729-class ternary-L6 and
256-class quaternary-L4 universes tractable with exact integers.

Every recorded violation carries an explicit exact-integer witness
sample `x = A + t*e_i` with `F_B(x) > F_A(x)` (single-coordinate boost
on a strictly-beating class; `t` solved analytically from the log-ratio
then verified with exact integers). Example: binary L=6, `G=10`,
covered sample at `n=81` (`t=71`); quaternary L=4, `G=7`, covered sample
at `n=47` (`t=40`). A self-comparison mutation control proves the
verifier is not vacuous.

## Reading of the results

- **Necessity holds generally**: zero non-rigid maximal truths in all
  three new cells (15778 spectra), confirming the Lean theorem
  `robust_iff_unique` computationally beyond its binary-L2..L4 census.
- **Sufficiency fails generally**: 30 binary-L6 and 96 quaternary-L4
  rigid truths are beaten by new-support candidates — rigidity is
  necessary but not sufficient, as predicted.
- **Ternary L=6 is an honest negative cell**: all 3474 truths rigid and
  maximal (consistent with the quaternary-L3 negative cell on the
  `4213d70` branch). No violation is fabricated; the cell is reported
  as-is.
- Non-rigid truths are absent in these `G` ranges (small genomes yield
  rigid spectra); non-rigid coverage remains with the earlier binary
  L2..L4 census (521 non-rigid, all non-maximal).

## Scope matrix

| Item | Covered here | Still open |
|------|--------------|------------|
| Objective | MB09 §6.1 product-binomial surrogate | exact multinomial (`#256`); §6.2 flows (`#260`/`#261`, untouched) |
| Cells | binary L6, ternary L6, quaternary L4 | L>=7, alphabets>=5, larger G |
| Classification | realizable complete-support maximality via covered-sample iff | full new-support class theorem (sufficiency fails; no converse) |
| Verification | exact-integer census + explicit witnesses + mutation control | kernel Lean theorem for the new cells (bounded evidence only) |

## CI wiring

```yaml
      - name: Verify #259 L6/Q4 realizable census
        run: python3 scripts/verify_realizable_census_L6Q4_259.py
```

(Runs in ~2 min; workflow-scope token needed for `.github/workflows/ci.yml`,
as noted in earlier `#259` docs.)
