# Bounded RC/orientation search at length five (#261)

**Status: negative bounded search; does not establish RC-invariance.** The
already recorded `AAATT`/`AAATA` witness shows a pairwise verdict change at
`L=3`, `o_min=1`, but a search for a genuinely second same-size example found
no other truth/competitor/sample triple of the same form in the entire
canonical binary length-five circular-genome universe.

## Search universe and conventions

Candidates are circular genomes modulo rotation and reverse-complement, over
`{A,T}`, length exactly five. There are four canonical candidates. Reads are length-three windows, sampled
independently with replacement from the five uniform circular start positions.
Truth is admitted. For a sample `x_1,...,x_m`, the exact likelihood is
`Π_i count_G(x_i)/5`; the RC-class likelihood replaces each word by the
representative `min(word, rc(word))`. All computations use exact rational
arithmetic. This is not fixed-external-`N` product-binomial scoring and does
not include arbitrary flows.

The complete verifier enumerates each truth, each competitor, every sample
multiset of size four from truth's five oriented windows, and computes both
likelihood ratios. The zero-versus-one pattern occurs in seven pair/sample
tuples, all from the same genome-class pair represented as `AAATT` and
`AAAAT` (the latter is rotation/RC-equivalent to `AAATA`), with distinct
samples. The census also detects other ratio changes. This demonstrates a
family of exact pairwise convention changes, not a second distinct genome
pair and not a maximality claim. It does not exclude other behavior at other
sample sizes, lengths, alphabets, or candidate classes.

## Source interpretation

The source convention split is oriented single-strand reads versus
reverse-complement molecule classes, exactly as specified in
`issue261-rc-orientation-class-20261026.md`.

Run `python3 scripts/verify_261_rc_orientation_search.py` for the exhaustive
bounded census and exact likelihood comparison. General orientation/RC
candidate-set relationships and maximality remain OPEN, as do the broader
flow/circuit questions in #261 and parent #255.
