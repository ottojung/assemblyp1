# Independent review: binary 2-mer sample-uniform slice (#259)

This note records an independent exact-arithmetic review of commit
`d173767378ff8a33ee735c8dad7f78546bd350ef` and its artifact
`docs/sample-uniform-rigidity-slice-259.md` plus
`scripts/verify_sample_uniform_rigidity_slice_259.py`. The result is a bounded
census, not a general classification or proof that rigidity is necessary for
all realizable sample classes.

## Reproduced claim and scope

The verifier constructs all binary circular genomes of lengths `G=3,4,5,6`,
quotients observations and candidates to their oriented circular 2-mer spectra,
sets the fixed external MB09 §6.1 normalizer `N=G`, and uses sample size `n=G`.
For each truth spectrum `A`, it tests every realizable same-length candidate
spectrum and every realizable same-length observation spectrum `x` with
`x_e >= 1` on `supp(A)`. It evaluates

```text
F_C(x) = ∏_e C(e)^x(e) (N-C(e))^(n-x(e)),  with 0^0 = 1.
```

The zero-count-coordinate failure terms are included. This is the MB09 §6.1
product-binomial surrogate, not the exact multinomial objective; candidates
with support beyond `supp(A)` are included. Rigidity is tested by enumerating
positive integer circulations of total `G` on the truth-support de Bruijn
subgraph.

Independent execution of the committed verifier returned:

| `G` | distinct spectra | sample-uniform maximizers |
|---:|---:|---:|
| 3 | 4 | 2 |
| 4 | 6 | 1 |
| 5 | 8 | 0 |
| 6 | 11 | 0 |

Across the 29 truth spectra it found 3 rigid maximizers, 12 rigid nonmaximizers,
14 nonrigid nonmaximizers, and 0 nonrigid maximizers. The `G=5,6` necessity
cells are vacuous because there are no maximizers. The minimum-length rigid
nonmaximizer is `G=N=n=3`: truth `A=(3,0,0,0)` (word `000`), observation
`x=(1,1,1,0)` (word `001`), and candidate `B=x`. Exact integer scores are
`F_A(x)=0 < 1728=F_B(x)`.

## Verification and limits

I ran `python3 scripts/verify_sample_uniform_rigidity_slice_259.py` from the
artifact commit; all census assertions and the exact witness passed. I also
ran `python3 scripts/check-research-docs.py` and
`git diff --check` on the source commit; both passed. The independent run
confirms this finite cell only. It does not establish rigidity necessity or a
necessary-and-sufficient structural criterion for arbitrary genome/read
length, alphabet, or sample size, and it does not settle the complete issue.

The verifier is ready for the `research-docs` CI job. I attempted to add the
workflow steps for both fixed-`x` and sample-uniform verifiers, but GitHub
rejected the branch push because the available credential lacks `workflow`
scope. CI wiring therefore remains a concrete follow-up; no workflow change is
included in this branch.

The checked-in verifier itself is exact integer arithmetic, rather than a
separate rational-ratio computation; strict comparison in the witness has a
zero truth score. The earlier fixed-`x` review and exact quinary rational
witness remain distinct artifacts and scopes.
