# Independent review: realizable transfer gap (#259)

Review performed from a fresh clone of `https://github.com/ottojung/assemblyp1.git`.
The reviewed branch `agent/DE7OZ76G8GhMwrQzyG4Fwd-langeron-issue259` resolved
to `6b3c09f3fa9f9177f44bdeabf4880f908a2c87cc`, matching the fetched commit.

## Reproduction

- `python3 scripts/verify_realizable_transfer_gap_259.py`: PASS. Transfer-balance
  comparison: 1,794 checks, 98 balanced, zero mismatches. Binary necklace census
  (`L=2,3`, `G<=10`): 50 both-maximal, 216 both-beaten, 14 full-vs-realizable
  gaps. The smallest reported gap is `N=4`, truth `(0,2,2,0)`, unrealizable
  full-class beater `(0,1,3,0)`, covered sample `(0,2,4,0)`.
- `python3 scripts/check-research-docs.py`: PASS.
- `git diff --check`: PASS (review checkout clean).

## Review and epistemic boundary

The exact one-unit balance identity in the note is supported directly by the
vertex-imbalance expression: for transfer `A-e_j+e_i`, zero imbalance is
equivalent to equality of endpoint multisets `{pre(i),suf(j)} =
{pre(j),suf(i)}`. The finite verifier agrees on its enumerated cases. The
likelihood comparison explicitly retains all coordinates, so this is the
fixed-external-`N` product-binomial objective and not the multinomial objective.

The `N=4` construction is a concrete, exact witness that full-count maximality
can be strictly stronger than maximality over realizable circular spectra.
The verifier's broader census and covered-sample iff support its stated finite
scope; neither proves a general characterization. In particular, the note
correctly leaves the alternating-family pattern conjectural. No smallest
counterexample or proof for that infinite-family claim follows from the present
bounded enumeration.

## Next precise subclaim

For the alternating truth spectrum `A=(0,m,m,0)` of `0101...` at `L=2`,
determine for each `G=2m` whether any *balanced realizable* same-length
competitor has a strictly larger covered-sample effective-weight product than
`A`. First derive the complete balanced competitor parameterization (not only
single-coordinate transfers), then test/prove the resulting inequalities for
arbitrary covered counts. This would turn the observed alternating cases into
an all-`m` statement or produce the first exact counterexample. Until then the
family remains a conjecture.
