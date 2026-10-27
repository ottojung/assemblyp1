# Fixed-`x` four-chamber reconciliation (AAABBB instance)

Bounded (A)-side reconciliation, not a general classification. Scoped to the
oriented same-length exact-multinomial domain of
`AssemblyP1/FixedXExactML.lean` (`S=AAABBB`, `G=6`, `L=2`).

Kernel-checked `fixedX_four_chamber_iff_258` reduces truth maximality at any
fixed `x` to the conjunction of three exact integer-product comparisons
against `B2,B3,B4` (exhaustiveness via `feasibleSpectrum_iff_258`; bridge via
`specLik_le_iff_likProduct` + `fixedX_classification_iff`). The general
fixed-`x` structural criterion beyond these pairwise inequalities stays OPEN.

Three admissible chambers, all with six (or four) reads supported on the truth
window support, hence in the same candidate universe:

* `x_win = B1 = (AA:2,AB:1,BB:2,BA:1)`: integer products `B1:16 > B2,B3:9 >
  B4:4`. Truth uniquely maximizes (kernel: `fixedX_unique_at_xWin258`).
* `x_tie = (1,1,1,1)`: integer products `B1=B4=4 > B2=B3=3`. Truth ties `B4`
  at the global maximum (kernel: `fixedX_top_tie_at_xTie258`).
* `x_lose = B4 = (AA:1,AB:2,BB:1,BA:2)`: integer products `B1:4 < B4:16`.
  Truth strictly loses (kernel: `fixedX_strict_loss_at_xLose258`).

So the four-chamber iff is witnessed in all three regimes (unique win, shared
maximum, strict loss) inside one feasible universe. Sample dependence is
unavoidable; no structure-only verdict follows. Says nothing about
reverse-complement molecules, fixed-`N` binomial scores, variable length,
spelled-vs-flow candidacy beyond this instance, historical `I_s` semantics,
or general MB09 section 6.2 flows. All broader classification claims stay OPEN.

Reproducer: `scripts/verify_255_fixedx_fourchamber.py` (exact integers and
rationals, denominators `6^6 = 46656` for six-read samples and `6^4 = 1296`
for the four-read tie sample).
