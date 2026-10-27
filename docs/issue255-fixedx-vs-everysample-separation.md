# Fixed-x win does not imply every-sample maximality (AAABBB separation)

This is a bounded (A)-vs-(B) separation, not a general classification.
Scoped to the oriented same-length exact-multinomial domain of
`AssemblyP1/FixedXExactML.lean` (`S=AAABBB`, `G=6`, `L=2`).

* `x_win = B1 = (AA:2, AB:1, BB:2, BA:1)`: integer products
  `B1:16 > B2,B3:9 > B4:4`, so the truth spectrum is the unique fixed-`x`
  maximizer. Kernel-checked as `fixedX_unique_at_xWin258`.
* `x_lose = B4 = (AA:1, AB:2, BB:1, BA:2)`: integer products
  `B1:4 < B4:16`, so the truth spectrum strictly loses. Kernel-checked as
  `fixedX_strict_loss_at_xLose258` (`decide`).
* Both samples use six reads supported entirely on the truth window support,
  so both are admissible fixed observations in the same candidate universe
  (`feasibleSpectrum_iff_258` exhausts it; `feasibleSpectrum_realizable_258`
  spells every member).

Hence sample dependence is unavoidable: truth maximality at one admissible
fixed `x` does not transfer to another, and a fortiori not to every admissible
finite sample. This separates axis (A) from axis (B) on this instance. It says
nothing about reverse-complement molecules, fixed-`N` binomial scores, variable
length, spelled-vs-flow candidacy beyond this instance, historical `I_s`
semantics, or MB09 §6.2 flows. All broader classification claims stay OPEN.

Reproducer: `scripts/verify_255_fixedx_vs_everysample.py` (exact integers and
rationals, denominator `6^6 = 46656`).
