# Independent review checkpoint: fixed-sample witness PR #405

Review date: 2026-10-27. Repository: `https://github.com/ottojung/assemblyp1`.

## Scope and result

PR #405 (`a024033c41763d856e1314db3a935c20c7df4a5e`, base
`62c0e789d33a79d5daefe4fafe8d1cc2b78c42dc`) corrects the BB multiplicity of
`AABBBB` and checks both already scoped fixed-sample witnesses. Independent
review confirms the arithmetic and confirms the claims stay within circular,
oriented, same-length, exact-multinomial spelled genomes. This is sound bounded
evidence for axis A, not a general criterion or closure of #255.

For `S=AAABBB`, `D=AABBBB`, type order `AA,AB,BA,BB`, the spectra are
`(2,1,1,2)` and `(1,1,1,3)`. Therefore for `x=(1,0,0,5)`, the exact likelihoods
are `1/729` and `1/192`, ratio `243/64`. For `x=(1,0,1,4)`, they are
`1/1458` and `1/576`, ratio `81/32`. The common multinomial coefficient
cancels. `AABBBB` has three BB edges, correcting the prior erroneous count of
four.

## Independent validation and integration state

- Fetched the exact PR head and verified its remote branch points to the
  claimed SHA; GitHub reports the commits' signatures verified.
- Ran `python3 scripts/verify_255_fixedx_second_witness.py`: PASS for both
  exact `Fraction` ratios.
- Ran `python3 scripts/check-research-docs.py`: PASS.
- Ran `git diff --check origin/main...a024033c41763d856e1314db3a935c20c7df4a5e`:
  PASS.
- GitHub exact-head checks: build, research-docs, PDFs, signed-commits all
  SUCCESS; deploy and white-paper publish SKIPPED.
- GitHub API reports PR #405 open and mergeable. It is not an ancestor of
  current `origin/main` (`62c0e78`) and is not integrated. No merge was
  performed in this review.

The broad fixed-`x` classification, every-sample claims outside their proved
scopes, frozen molecule/objective/length/flow/candidacy/`I_s` distinctions, and
all other conjectures remain OPEN. Next: an authorized integrator can merge
PR #405 after rechecking its exact head and green required checks; then continue
with a distinct unowned classification cell.
