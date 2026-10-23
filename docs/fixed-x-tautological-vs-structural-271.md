# Fixed-sample tautological vs structural ML characterization (issue #271, goal 4)

_Status: research comparison note with an independent exact-integer Python
check (`scripts/verify_271_fixedx_link.py`). All Lean theorems cited here are
previously merged and kernel-checked elsewhere; this note proves nothing new
in Lean and does not fork the #255/#258/#256/#260 classification._

## 1. The distinction

Fix the observed count vector `x` (`R = x`). For the exact multinomial
objective, the statement

> the truth `A` is an ML maximizer at `x` iff `Lik(B;x) <= Lik(A;x)` for all
> feasible `B`

is **tautological**: it restates the score comparison that defines the
maximizer. The Lean form is
`AssemblyP1.FixedXExactML.fixedX_classification_iff`, which cancels the
candidate-independent denominator `G^n` (`spectrumLikFactor_eq_likProduct_div`)
to give the integer-product form `∏ B^x <= ∏ A^x`. The iff carries no
structural information beyond the definition of "maximizer at `x`".

The **structural** content at fixed `x` is everything the tautology
quantifies over without describing:

* the feasible-set census — which spectra `B` are even candidates
  (`AssemblyP1.FixedXExactML.feasibleSpectrum_iff_258`: exactly
  `{B1, B2, B3, B4}` for AAABBB, via balance `B wAB = B wBA`, mass 6,
  positivity);
* the chamber reduction — the all-candidates maximizer claim at fixed `x`
  reduces to finitely many integer comparisons once the census is known
  (`fixedX_four_chamber_iff_258`);
* the genome-realization bridge — every feasible spectrum here is spelled by
  an explicit circular genome (`feasibleSpectrum_realizable_258`), so the
  spectrum-level verdict is also a genome-level verdict at this instance.

## 2. Reused (not re-proved) instance: AAABBB has all three statuses

`S = AAABBB`, `G = 6`, `L = 2`, truth `B1 = (AA:2, AB:1, BB:2, BA:1)`.
The independent script recomputes the exact integer products:

| Sample `x` | A | B2 | B3 | B4 | Truth status (Lean) |
|------------|---|----|----|----|---------------------|
| xWin = B1  | 16 | 9 | 9 | 4 | unique maximizer (`fixedX_unique_at_xWin258`) |
| xTie = all-ones | 4 | 3 | 3 | 4 | tie at top with B4 (`fixedX_top_tie_at_xTie258`) |
| xLose = B4 | 4 | 3 | 3 | 16 | strict loss to B4 (`fixedX_strict_loss_at_xLose258`) |

The script also checks the denominator-cancellation tautology explicitly:
rational-factor ranking agrees with integer-product ranking at all three
samples.

## 3. Link to the sample-uniform iff (#256) and the #271 boundary

The sample-uniform question asks whether the truth wins at **every**
admissible `x`. `AssemblyP1.RobustSameLengthIff.robust_iff_unique_spectrum`
answers it: sample-uniform maximality holds iff the feasible set is the
singleton `{A}`. Here `F = {B1, B2, B3, B4} != {A}`, so the truth is correctly
**not** sample-uniformly maximal — and the three rows above exhibit the
pointwise reason why. The fixed-`x` verdicts are strictly weaker than
robustness and do not imply it.

For the #271 comparison, the xLose row is the Goal-4 witness in the precise
sense allowed: at a fixed sample supported entirely on the truth's windows
(xLose = B4, spelled by `S4_258 = AABABB`), ordinary R-only ML strictly
prefers the wrong candidate. Weaker information-theoretic necessary
conditions — sampling realizability, support containment, base coverage —
hold at this sample yet do **not** guarantee (B). This reuses the merged #258
instance; no new genome-level ML claim is made here.

## 4. What is open / not claimed

* No conditional-Bayes `(A)`-side claim is made at these samples: the fixed-`x`
  model carries no prior and no side event `E`.
* Nothing is transferred to reverse-complement molecule flows, the §6.1
  binomial surrogate, or arbitrary §6.2 models (#259/#261 remain open).
* The `E -> B` implication question for general `L/G` remains open.
