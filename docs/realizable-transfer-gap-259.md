# Realizable-class transfer balance and the full-vs-realizable gap (board issue #259)

_Status: bounded exact-arithmetic evidence (`scripts/verify_realizable_transfer_gap_259.py`);
no Lean theorem claimed. Complements the kernel-checked full-class classification
(`docs/product-binomial-boundary-fullclass-259.md`) on the explicitly open
realizable (balanced-spectrum) restriction._

## 1. Question

The full-class theorem says a truth `A` (total `N`) is sample-uniform maximal
over **all** count vectors iff `A` is concentrated or `{0,1}`-valued, via the
one-unit transfer `B = A - e_j + e_i`.  Over the **realizable** class (spectra
of circular binary words, i.e. balanced circulations), the transfer witness may
be inadmissible.  This note records two exact finite checks:

1. **Transfer-balance classification.**  A transfer `B = A - e_j + e_i` between
   distinct supported `k`-mers preserves balance on `supp A` iff the endpoint
   multisets agree: `{pre(i), suf(j)} = {pre(j), suf(i)}`.  In particular every
   loop-to-loop transfer (`00 -> 11`) preserves balance, while `01 -> 10`
   (or `10 -> 01`) breaks it.  Both directions verified over all `1794`
   one-unit transfers on binary necklace spectra (`L in {2,3}`, `G <= 10`);
   `98` preserve balance, `0` mismatches with the multiset condition.
   Proof sketch of the condition: the residual shift at node `v` is
   `[v==pre(i)] - [v==pre(j)] - [v==suf(i)] + [v==suf(j)]`, which vanishes for
   all `v` exactly under the multiset equality.

2. **Full-vs-realizable gap census.**  For each realizable truth with positive
   effective weights on its support, the full-class verdict (concentrated or
   `{0,1}`-valued) is compared against maximality over the realizable class
   (all necklace spectra of the same total, decided by the merged #259
   covered-sample iff, which quantifies over **all** covered samples, not a
   bounded excess box).  Result (`L in {2,3}`, `G <= 10`): `50` maximal in
   both senses, `216` beaten in both, **`14` gap cases** (full-class-beaten
   yet realizable-maximal), `0` skipped.  A full-class-maximal truth is never
   realizable-beaten (the realizable class is a subclass; asserted in code).

## 2. Smallest gap witness (exact)

Truth `A = (0,2,2,0)`, spectrum of the circular word `0101` (`G = 4`, `L = 2`).
Full-class transfer beater `Bs = (0,1,3,0)` (`01 -> 10` move): not a necklace
spectrum (`#01 = 1 ≠ 3 = #10`, unbalanced, hence unrealizable), while no
necklace spectrum of length `4` beats `A` (exhaustive search).  Covered sample
`x = (0,2,4,0)` (flooding coordinate `10`) satisfies `F_Bs(x) > F_A(x)` as exact
integers; the script cross-checks the exact product comparison.  `A` is rigid
(unique positive circulation `(2,2)` on `{01,10}`), so this is also a
rigid-and-realizable-maximal cell beaten only outside the realizable class.

Observed pattern (bounded, not proved in general): the alternating words
`(01)^k` with spectra `(0,k,k,0)` are gap cases for `k = 2,3,4,5`, with
unbalanced transfer beaters `(0,k-1,k+1,0)`; the `L = 3` gap cases are the same
words read as 3-mer spectra.  Generalizing to all `k` is conjectural and NOT
claimed here.

## 3. Scope

| Item | Covered here | Still open |
|------|--------------|------------|
| Objective | MB09 §6.1 fixed-external-`N` product-binomial surrogate | exact multinomial (`#256`); §6.2 flows (`#260`/`#261`) |
| Candidate class | realizable = binary necklace spectra, same total | all balanced circulations (non-binary, disconnected supports); proof for all `G` |
| Transfer mechanism | exact balance iff (endpoint multisets) in range | use in a general realizable-class theorem |
| Gap | 14 exact witnesses, `L in {2,3}`, `G <= 10` | infinite-family proof (alternating words); non-binary alphabets |

## 4. Verification

```
python3 scripts/verify_realizable_transfer_gap_259.py
```

Exact `int`/`Fraction` arithmetic, no Lean import.  Runs in seconds.
