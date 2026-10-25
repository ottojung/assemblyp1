# Fixed-`x` exact-ML: same-length maximality does not transfer to variable length (#255)

Frozen axis: **same vs variable genome length**. Exact multinomial objective,
fixed observation `x` (regime (A)). Umbrella #255 stays OPEN; this is one
scoped refutation on the fixed-`x` slice.

## Falsifiable lemma (kernel-checked)

Conjecture (now REFUTED): *if the truth uniquely maximizes the exact fixed-`x`
likelihood among same-total spectra at `x`, then it maximizes among all totals
at that `x`.*

Witness on two read types, fixed `x = (2, 1)`:

* truth `A = (3, 1)`, total `G = 4`, spectrum factor `9/64`;
* `A` is the UNIQUE maximizer among all five count vectors of total `4`
  (`(4,0): 0`, `(3,1): 9/64`, `(2,2): 1/8`, `(1,3): 3/64`, `(0,4): 0`);
* competitor `B = (2, 1)` of total `G' = 3` gives `4/27 > 9/64` at the same `x`.

`B` attains the continuous simplex optimum `q = x/n = (2/3, 1/3)`, so no
spectrum of ANY total beats `B` at this `x` (checked exactly for totals 1–8;
the optimum argument is total-independent).

## Why it matters

At fixed `x` the multinomial coefficient cancels, so the comparison depends
only on normalized spectra `c i / G`. Nothing in the formula forces equal
totals — variable length enters only through normalization. A same-length
rigidity/unique-maximality result therefore cannot by itself classify the
variable-length fixed-`x` problem: the (A)-side classification must range over
all totals jointly, or carry an explicit total constraint.

## Artifacts

* `AssemblyP1/FixedXVariableLengthSeparation.lean`
  (`AssemblyP1.FixedXVariableLengthSeparation.samelen_does_not_imply_varlen255`,
  plus `samelen_unique_max255`, `varlen_beats_samelen255`), root-imported with
  `AssemblyP1/FixedXVariableLengthSeparationAudit.lean` (`#print axioms`:
  `[propext, Classical.choice, Quot.sound]` only).
* `scripts/verify_255_variable_length_fixedx.py` (exact `Fraction` checks, exit 0).

## Scope (explicitly NOT claimed)

Regime (B) untouched; §6.1 product-binomial surrogate untouched (its
candidate-dependent `N` factors make length enter differently); §6.2
bidirected flows untouched; spelled-genome realizability of `A`/`B` untouched
(the witness is at spectrum level). Closes no child issue. All broader
conjectures remain OPEN.
