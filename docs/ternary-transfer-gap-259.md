# Ternary-alphabet full-vs-realizable gap (board issue #259)

_Status: bounded exact-arithmetic evidence
(`scripts/verify_ternary_transfer_gap_259.py`); no Lean theorem claimed.
First ternary cell of the scope matrix left open by
`docs/realizable-transfer-gap-259.md` (binary only)._

## 1. Question

Does the full-vs-realizable gap (full-class-beaten yet realizable-maximal
truths) persist over non-binary alphabets?  This note records the smallest
ternary (`{0,1,2}`) 2-mer cell.

## 2. Smallest ternary gap witness (exact)

Universe `U = {0,1,2}^2` in lexicographic order
(`(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)`), total `N = G = 4`.

- Truth `A = (0,0,0,0,0,2,0,2,0)`, spectrum of the circular word `1212`
  (alternating pair `(12)^2`, the ternary analogue of binary `(01)^2`).
- Full-class transfer beater `Bs = (0,0,0,0,0,1,0,3,0)` (`12 -> 21` move):
  `#12 = 1 ≠ 3 = #21`, unbalanced, hence not a necklace spectrum; no
  ternary necklace spectrum of total `4` beats `A` (exhaustive search over
  the 24 spectra).
- Covered sample `x = (0,0,0,0,0,2,0,4,0)` (flooding coordinate `21`):
  with `N = 4`, `q_A = (65536, 65536)` and `q_Bs = (16384, 147456)` on
  `supp A`, so `F_Bs(x) = 126908196839865312243955531776 > 79228162514264337593543950336 = F_A(x)`
  as exact integers; the script cross-checks the exact product comparison.

`A` is rigid (unique positive circulation `(2,2)` on `{12,21}`), so this is
a rigid-and-realizable-maximal cell beaten only outside the realizable
class — the same mechanism as the binary smallest witness.

## 3. Census (bounded, not a theorem)

Ternary `L = 2`, `G <= 6`: `65` maximal in both senses, `89` beaten in
both, **`30` gap cases**, `0` skipped.  Transfer-balance iff
(endpoint-multiset condition) holds on all `438` one-unit transfers
(`30` preserve, `0` mismatches).  Generalizing the alternating-word family
to all `k` and all alphabet pairs, and alphabets `>= 4`, remain open.

## 4. Scope delta

| Item | Before (binary note) | This note |
|------|----------------------|-----------|
| Alphabet | `{0,1}` | `{0,1,2}` (`L=2`, `G<=6`) |
| Smallest witness | `A=(0,2,2,0)`, word `0101` | `A=(0,0,0,0,0,2,0,2,0)`, word `1212` |
| Still open | non-binary alphabets | alphabets `>= 4`; `L >= 3` ternary; infinite-family proof |

## 5. Verification

```
python3 scripts/verify_ternary_transfer_gap_259.py
```

Exact `int`/`Fraction` arithmetic, no Lean import.  Runs in seconds.
