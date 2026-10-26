# Binary L=8, G=N=9 uniform-loss resolution (#259)

Follow-up to `docs/binary-L8-G9-one-extra-259.md`, which reported 3600
ordered pairs with `uniform_beats=3592` and `uniform_losses=8` under the
covered-uniform pointwise `q_e` decision, with no beating claim. The
verifier `scripts/verify_binary_L8_G9_loss_resolution_259.py` resolves all
8 loss pairs: none is a sample-uniform beating witness.

## Lemma (finite, exact integer)

For each of the 8 ordered loss pairs `(A, B)` over the 256 8-mer universe
at external normalization `N = 9`:

- `supp(A)` is not contained in `supp(B)`: there is a killing coordinate
  `k` with `A_k >= 1` and `B_k = 0` (checked explicitly per pair).
- Every covered sample `x` (`x_e >= 1` for all `e in supp(A)`) has
  `x_k >= 1`, so the MB09 section 6.1 fixed-external-`N` product-binomial
  numerator `F_N(B, x) = ∏_e B_e^x_e (N-B_e)^(n-x_e)` is exactly `0`.
- Truth counts on support satisfy `1 <= A_e <= 8 < N`, so `F_N(A, x) > 0`
  on every covered sample (no zero base with positive exponent and no
  zero failure factor on a positive-count coordinate).

Hence `F_N(B, x) = 0 < F_N(A, x)` for **every** covered `x`: truth wins
everywhere covered, including the fixed-`x` sample `x = A` and every
one-extra sample `x = A + 1_i` (each checked exactly, `F_B == 0`).

## Reading

The pointwise `q_e` uniform criterion is sufficient-only for
sample-uniform maximality: it can fire a loss on a coordinate where the
competitor is strong while the exact likelihood is killed by the
competitor's zero elsewhere in the covered support. All 8 losses here are
of this new-support kind.

Two failed-then-fixed controls are recorded: repairing a single killing
zero does not make `F_B` positive (remaining killing zeros still kill),
and repairing all killing zeros still leaves `F_B = 0` when the competitor
sits on the `N` boundary elsewhere (`B_e = N` gives a zero failure
factor). The committed mutation control clamps every coordinate off the
`0`/`N` boundary, which does make `F_B > 0`, so the zero conclusion is
non-vacuous.

## Validation

```text
python3 scripts/verify_binary_L8_G9_loss_resolution_259.py
binary L=8 G=N=9 spectra=60 pairs=3600
uniform losses=8; all resolve: F_B==0 < F_A on x=A
and on every one-extra x=A+1_i; structural kill holds for all
covered x via supp(A)-not-subset-supp(B) coordinates.
mutation control: clamping B off the 0/N boundary makes F_B>0; OK
```

Finite consistency/resolution evidence only; no general theorem claimed.
#260/#261 flows untouched.
