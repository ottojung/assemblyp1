# Audit of the direct circular P2 proof's maximal-extension step

_Status: mathematical counterexample to one proof step; **not** a counterexample to the P2 spectrum-uniqueness theorem._

The direct proof on `agent/p2-circular-uniqueness-direct-0921` argues that a crossing between two transpositions of the transition involution `rho` gives two interleaved maximal repeats: each transposition pairs two occurrences of an `(L-1)`-mer, and the proof extends each pair maximally left/right while claiming that the four starts remain interleaved.

That implication is false. Maximal left extension shifts both starts of a pair by a pair-specific amount. Different crossing pairs can shift by different amounts, and can even collapse to the same maximal repeat pair.

## Explicit witness

Take

- `S = AABCBCBAB`,
- `T = AABABCBCB`,
- `L = 3`.

Direct exact enumeration gives:

- `S` and `T` are primitive circular words of length 9;
- they have the same circular length-3 spectrum;
- they are not cyclic shifts;
- every length-2 window of `S` occurs at most twice (the multiplicity regime used to make `rho` an involution);
- under a fixed occurrence matching by length-3 type, `rho` contains crossing transpositions pairing raw length-2 occurrences at starts `(2,4)` and `(3,5)`;
- the `(2,4)` pair has zero common left extension, while `(3,5)` has one-symbol common left extension;
- therefore both raw pairs extend to the **same** maximal repeat pair with starts `(2,4)`, rather than to two interleaved maximal pairs.

So the inference

> crossing raw `(L-1)`-mer occurrence pairs => their maximal repeat extensions remain interleaved

is invalid.

## Why this does not refute the theorem

The same witness has `TRF(S,3)` but fails `ILF(S,3)`: among its actual maximal repeats, the length-2 pairs at starts `(1,7)` and `(6,8)` are interleaved. Hence `P2(S,3)` is false. The witness therefore attacks only the direct proof step, not the theorem `P2 => ordinary circular L-spectrum uniqueness`.

A broader exact search during this audit found many instances where a crossing raw pair does not itself extend to crossing maximal repeats, while the corresponding word still fails P2 for some other maximal interleaving. This explains why the earlier verifier could pass: it checked that every alternate-spelling instance was `not P2`, but did not verify the proof's stronger local assertion that the particular crossing supplied by the matching lemma survives maximal extension.

## Consequence for issue #45

Do not use the current direct matching/cycle proof as a mathematical proof of circular P2 spectrum uniqueness without an additional argument repairing this gap. The population/KL reduction and the scaling-plus-primitivity reduction are logically separate; they may continue to reduce population uniqueness to the ordinary circular P2 spectrum-uniqueness lemma. That lemma can still be supported by an independently verified source theorem or by a repaired direct proof.
