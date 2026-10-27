# Fixed-observation truth maximality: precise status

For a fixed count vector `x`, an exact multinomial likelihood is a number
assigned to every candidate. Consequently, truth maximality over a candidate
family `C` has the exact necessary-and-sufficient criterion

`∀ D ∈ C, likelihood(D; x) ≤ likelihood(S; x)`.

This statement is elementary, but its quantifiers and model matter. For the
oriented, same-length spectrum family, this is formalized by
`AssemblyP1.FixedXExactML.fixedX_classification_iff`. Its
`specLik_le_iff_likProduct` lemma removes the common denominator
`G^(sum x)`, giving an exact integer-product test over *all* feasible
positive balanced spectra. In the AAABBB binary length-2 instance,
`feasibleSpectrum_iff_258` enumerates the whole feasible class and
`fixedX_four_chamber_iff_258` reduces truth maximality for every fixed `x`
to three exact product comparisons. This is an exhaustive fixed-`x` answer for
that finite instance, not a structural theorem for arbitrary truth genomes.

## Sample dependence (same truth, same candidate)

Take circular truth `S=AAABBB`, candidate `D=AABBBB`, and oriented pair-type
order `(AA, AB, BA, BB)`. Their spectra are respectively
`(2,1,1,2)` and `(1,1,1,3)`. For `x₁=(1,0,0,5)`,
`P(D;x₁)/P(S;x₁)=243/64 > 1`, so truth is not a maximizer. For
`x₂=(1,0,1,4)`, the ratio is `81/32 > 1`, another truth-supported loss.
The same finite class also has a truth-winning sample and a top tie, as
formalized by `fixedX_unique_at_xWin258` and `fixedX_top_tie_at_xTie258`.
Thus truth structure and candidate alone do not determine the answer in (A);
the observed counts are essential.

## Scope and remaining work

This product-inequality criterion is useful as a decision procedure when the
candidate class can be enumerated, but is not a closed-form structural
classification of the winning count vectors for arbitrary truth/candidate
universes. Generalizing the AAABBB chamber description to arbitrary supports,
genome lengths, and realized candidates remains open. Reverse-complement
molecule types, fixed-`N` binomial likelihood, variable-length candidates,
literal historical `I_s` versus project placement `I_s`, and MB09 §6.2
bidirected flows with overlap floor are separate axes and are not covered.
The known historical full-overlap molecule-flow counterexamples remain
counterexamples to bridging sufficiency, not a general flow classification.

Reproduce the exact finite witnesses with
`python3 scripts/verify_255_fixedx_second_witness.py`; the full AAABBB
64-genome exact enumeration is separately documented in
`docs/remaining-open-matrix-255.md` and is computational evidence, not a
kernel-checked general theorem.
