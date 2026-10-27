# Issue #255 axis matrix (source-notes, 2026-10-27)

Bounded umbrella record. Each row is one declared axis × regime cell with
status PROVED / REFUTED / OPEN and the exact artifact. No conjecture is
promoted beyond its evidence. Scoped to what is cited; everything else OPEN.

| Axis / regime | Status | Exact artifact |
|---|---|---|
| (A) fixed-x, oriented, same-length, exact multinomial (AAABBB instance) | PROVED (certificate + 3 chambers) | `AssemblyP1/FixedXExactML.lean`: `specLik_le_iff_likProduct`, `fixedX_classification_iff`, `fixedX_four_chamber_iff_258`, `fixedX_unique_at_xWin258`, `fixedX_top_tie_at_xTie258`, `fixedX_strict_loss_at_xLose258`; reproducers `scripts/verify_255_fixedx_vs_everysample.py`, `scripts/verify_255_fixedx_fourchamber.py` (this branch family @ `940623f`) |
| (A) fixed-x, general structural criterion beyond pairwise products | OPEN | No general theorem; `fixedX_classification_iff` is a pairwise-inequality restatement, not a structure-only verdict |
| (B) every-sample, oriented same-length exact multinomial | PROVED (iff) | `AssemblyP1/RobustSameLengthIff.lean` (#256 CLOSED); pointwise covered-sample generalization `AssemblyP1/FiniteSampleIidEnvelope.lean:197` `truth_maximizer_forall_covered_iff` (PR #251) |
| (A)-vs-(B) separation (win at one x, loss at another) | PROVED (instance) | Same `FixedXExactML` chambers: `x_win=(2,1,1,2)` 16>9,9,4 vs `x_lose=(1,2,2,1)` 4<16; `docs/issue255-fixedx-vs-everysample-separation.md`, `docs/issue255-fixedx-fourchamber-reconciliation.md` |
| Oriented vs RC molecule types | SPLIT: oriented cells above PROVED; RC general OPEN; RC full-overlap equal-support (B) PROVED | `AssemblyP1/FullOverlapMoleculeML.lean` (#260 CLOSED); general RC classification OPEN |
| Exact multinomial vs fixed-N product-binomial | SPLIT: exact cells above PROVED; surrogate scoped partials PROVED; full (A)/(B) OPEN | `AssemblyP1/FixedNBinomialEffectiveWeights.lean`, `AssemblyP1/FixedXProductBinomialMaximality.lean` (`fixedX_le_iff`, `sampleUniform_iff_pointwise`, `fixedX_weaker_than_pointwise`), `AssemblyP1/Section62FiniteNExtremeSamples.lean`; full classification OPEN (#259 PARTIAL) |
| Same vs variable length | SPLIT: same-length cells above PROVED; variable-length sufficiency REFUTED (scoped) | `AssemblyP1/ShortFiniteMLCounterexamples.lean` (PR #229, AT/AAT/AAAT ratios 32/27, 81/64, 4096/3125); general variable-length classification OPEN (#300 OPEN) |
| Spelled genomes vs MB09 §6.2 flows + overlap floor | SPLIT: full-overlap lift PROVED; spelled-vs-surrogate separation PROVED; general §6.2 OPEN | `AssemblyP1/Section62FullOverlapLift.lean` (PR #202, #262 CLOSED); `AssemblyP1/Section62NonSpelledFlow.lean` (PRs #179/#182, AAATT/AAATA 65536/50625 vs 1); L3 transports `AssemblyP1/Section62PhysicalOrbitObjective.lean`, uniqueness non-transport `...Uniqueness` (`MixedLoop.physUniqueMaximal_not_transported`); general flow classification OPEN (#261 OPEN) |
| Truth candidacy | PROVED inside landed cells only | `feasibleSpectrum_realizable_258`, `FiniteSampleIidEnvelope` hypotheses; extended domains must re-establish |
| Historical `I_s` (literal match) vs project placement `I_s` | SPLIT: literal bridging sufficiency REFUTED; project predicate cells above PROVED; historical-referent remainder OPEN | W1/W2 refutation (PR #142, merge `49b2903`); remaining historical semantics OPEN |

Smallest open subclaim selected: none closed here. The tie chamber
`x_tie=(1,1,1,1)` with products `B1=B4=4 > B2=B3=3` (`P=1/324`) is already
kernel-checked as `fixedX_top_tie_at_xTie258` and reproduced by
`scripts/verify_255_fixedx_fourchamber.py` (PASS). General fixed-x structural
criterion, historical `I_s` semantics, and general §6.2 flow classification
stay explicitly OPEN.
