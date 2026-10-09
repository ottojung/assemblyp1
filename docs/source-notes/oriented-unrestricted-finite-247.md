# Oriented unrestricted finite ML counterexample (board issue #247, lane 247b)

This note records the NEW oriented unrestricted finite historical-coverage ML
counterexample proposed in board issue #247 parts 7-8 and kernel-checked in
`AssemblyP1/OrientedUnrestrictedFinite247.lean`.  The independent exact-rational
verification script is `scripts/verify_oriented_unrestricted_247.py`.

## Instance

| object | value |
| --- | --- |
| alphabet | `{A, B}` (rename `B ↦ C` for literal DNA) |
| read length `L` | `3` (oriented, single-strand; 8 oriented types) |
| truth `S` | `AAABBABB` (circular, `G = 8`) |
| competitor `D` | `AAAABABB` (circular, same length `8`) |
| sample | each of the `8` starts of `S` once, plus **four** extra copies of start `0` (`AAA`) |
| total reads `n` | `12` |
| observed `x` | `{AAA:5, AAB:1, ABB:2, BBA:2, BAB:1, BAA:1}` |
| truth spectrum `d_S` | `{AAA:1, AAB:1, ABB:2, BBA:2, BAB:1, BAA:1}` |
| competitor spectrum `d_D` | `{AAA:2, AAB:1, ABA:1, ABB:1, BBA:1, BAB:1, BAA:1}` |

## Kernel-checked results

1. **Briding hypothesis `I_s`** (old base coverage, every maximal triple repeat
   all-bridged, every interleaved pair bridged) holds for the truth with all
   eight realized starts, by finite `decide`.  Because every start is sampled,
   the old base coverage holds and the sample is start-dense.

2. **Exact intrinsic multinomial** §6.1 objective (candidate-intrinsic length
   `N(D) = |D| = 8`):

   `Lik(D)/Lik(S) = 31185/67108864  ÷  31185/134217728  =  2  >  1`.

3. **Fixed-`N = 8` product-of-binomial-marginals** objective, zero-count factors
   retained over all eight oriented types (including the unobserved `ABA` of
   `D`):

   `Lik(D)/Lik(S) = 1341068619663964900807/448762029294263205888
                   = 2.9883736415332867…  >  1`.

4. **4-letter DNA binomial** objective (alphabet `{A, C, G, T}`, `64` oriented
   types, zero-count factors retained): the **same** ratio
   `1341068619663964900807/448762029294263205888`, because the fifty-seven types
   outside the relevant seven `{A, C}`-words all have `x = d_S = d_D = 0` and
   contribute factor `1`.

5. **`D` is NOT a §6.2 support-equality / spelled / flow candidate.**  `D`
   contains the **unobserved** window `ABA` (`d_D(ABA) = 1` but `x(ABA) = 0`).
   `D` satisfies the **weak** §6.2 per-vertex lower bound `1` (every observed
   type occurs in `D`), but fails the support-equality form
   `∀ c, 0 < d c ↔ 0 < x c`.

## Scope

This is a counterexample among **all circular candidates of the true length**
(the unrestricted candidate class `F0`).  It is **not** a §6.2 support-equality /
bidirected-flow statement and must not be used to settle the §6.2 molecule row.

## Coordination

The historical read-string coverage predicate `HistoricalCovers`, the
`DenseSampledStarts` certificate, and the `DenseSampledStarts ⇒
HistoricalCovers` adapter are owned by lane 247a and are **not** defined in the
Lean module (no duplication).  The sample here is start-dense (every start
sampled), so the 247a historical coverage predicate holds trivially; the two
lanes coordinate the final historical-predicate import.
