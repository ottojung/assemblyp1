# Fixed-x vs sample-uniform gap: ternary-L6 and quaternary-L4 cells (board issue #259)

_Status: independent exact-integer verification in
`scripts/verify_fixedx_gap_extended_cells_259.py` (no Lean import, no floats
in any comparison). Extends `docs/fixedx-vs-uniform-gap-L6-259.md`
(binary-L6: 30/30 gap) to the remaining census cells of
`docs/realizable-census-L6Q4-259.md`. Companion census repro
(`scripts/verify_realizable_census_L6Q4_259.py` full run) matches 4703a6f
exactly, including the quaternary-L4 cell:
truths=11540, rigid_max=11444, rigid_notmax=96, nonrigid_max=0._

## 1. Results

| cell | rigid-beaten | win at own sample (gap) | lose at own sample | rigid-maximal (fixed-x spot-checked) |
|------|--------------|-------------------------|--------------------|--------------------------------------|
| ternary-L6 (G 6..9) | 0 | 0 | 0 | 3474 (12 spot-checked, all win) |
| quaternary-L4 (G 4..8) | 96 | **96** | 0 | 11444 (15 spot-checked, all win) |

* Ternary-L6: the gap population is empty -- every rigid realizable truth
  is already a sample-uniform maximizer, so axis A and axis B coincide on
  this cell. The 12 fixed-x spot-checks (up to 3 maximal truths per G,
  each against every same-length competitor) confirm the covered-sample
  implication (x = A is itself covered: n = G = N) on realizable spectra.
* Quaternary-L4: all 96 rigid-but-beaten truths win the exact separable
  fixed-x inequality at x = A yet lose sample-uniformly -- 96 further live
  gap instances. The beaten count 96 cross-matches the census
  `rigid_notmax=96` exactly (independent re-enumeration, not shared state).
* Combined with binary-L6 (30/30), the full realizable census yields
  126 rigid-but-beaten truths, every one a fixed-x/uniform gap instance,
  and 0 non-rigid maximal truths (rigidity necessity holds in all cells).

## 2. Conventions (same as binary-L6 note)

* **Candidate length:** same-length genomes; ternary-L6: alphabet 3,
  read length `L = 6` (universe 729 k-mer classes), `G = 6..9`;
  quaternary-L4: alphabet 4, `L = 4` (universe 256), `G = 4..8`.
* **Normalization `N`:** fixed external, `N = G`.
* **Support:** competitors range over all same-length spectra (new-support
  admitted); reduced comparisons over `supp A ∪ supp B`.
* **Sample size `n`:** axis A at truth sample `n = sum(A) = G`; axis B free
  covered samples `n >= N`, `x >= A` coordinatewise.
* **MB09 §6.1 vs exact:** separable surrogate retains
  `(N - V_e)^(n - x_e)` for every class including zero-count ones; exact
  multinomial (`#256`) not imported. Separable kernel
  `separable_at_truth` is byte-identical to the binary-L6 script
  (diff-check clean).

## 3. Verification

`scripts/verify_fixedx_gap_extended_cells_259.py` re-enumerates both cells
with the census's exact reduced arithmetic, decides the separable fixed-x
inequality at x = A for every beaten truth (strict-coordinate cross-check
per gap instance, explicit-witness path for any non-gap), and spot-checks
fixed-x wins for sampled maximal truths. Mutation control (self-domination
plus separable self-tie) included. Observed output tail:

```text
cell ternary-L6: rigid-beaten=0 (win-own=0 lose-own=0) rigid-maximal=3474 (fixed-x spot-checked=12)
cell quaternary-L4: rigid-beaten=96 (win-own=96 lose-own=0) rigid-maximal=11444 (fixed-x spot-checked=15)
OK
```

Ternary cell runs in minutes; quaternary-L4 is the costliest cell
(~20 min; same class as its census cell).

## 4. Scope matrix

| Item | Covered here | Still open |
|------|--------------|------------|
| Objective | MB09 §6.1 product-binomial surrogate | exact multinomial (`#256`); §6.2 flows (`#260`/`#261`, untouched) |
| Axis A | fixed-`x` verdicts at truth samples for all 126 beaten truths (30 + 96) + 27 maximal spot-checks | fixed-`x` at non-truth covered samples |
| Axis B | sample-uniform failure reproduced (census match in all 3 cells) | full new-support class theorem |
| Rigidity | necessity re-confirmed (0 non-rigid maximal of 15778 truths); sufficiency fails 126x with gap detail | Lean kernel replay for the new cells |
| CI wiring | one-line step (below; workflow-scope token needed) | `L>=7`, alphabets `>=5`, larger `G` |

```yaml
      - name: Verify #259 fixed-x/uniform gap, extended cells
        run: python3 scripts/verify_fixedx_gap_extended_cells_259.py
```
