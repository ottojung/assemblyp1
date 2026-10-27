# Issue #272 bounded verification inventory

This check records the starting state for the isolated follow-up clone at
`main` commit `234f3480d7589c8fc4e056c91dda91343fe64ece` and the earlier
supplied-promise branch `agent/6I8zVlFeghwupUKxsB36OK-verse-issue272` at
`b1b173d751eafeda056baef86920f7a88c0d2f1c` (remote heads confirmed with
`git ls-remote`). It is not a replacement for the kernel-checked posterior
theorem or the merged read-string adapter.

At the earlier branch head, the exact-rational read-only/supplied-promise
witness, connected census, minimal-sufficient and source-defined checks pass;
the necessity verifier also passes on a separate retry. The research-documents
integrity check passes there. The combined first invocation reached and passed
the source-defined script but exceeded its 120-second timeout before starting
the slower necessity search; the isolated retry completed with `ALL CHECKS
PASS`.

The following scripts named by the earlier handoff are **not present on the
verified `main` head**: `scripts/verify_272_readonly_vs_supplied_promise.py`
and `scripts/verify_272_connected_census.py`. They are present on the verified
agent branch above. Main does contain `verify_272_minimal_sufficient.py`,
`verify_272_source_defined.py`, and `verify_272_is_necessity.py`.

The added `scripts/verify_272_posterior_support_corners.py` is an exact
rational micro-check: with positive predictive mass, a supplied event leaves
one positive-prior, positive-likelihood truth and yields posterior one; zero
prior and zero likelihood candidates contribute no posterior mass; an event
with zero predictive mass has no defined posterior. This is computational
evidence for these finite values, not a general theorem proof.

## Follow-up handoff artifact verification (2026-10-27)

The terminal checkpoint naming commit `82173746544f92267741bec1b1e2361cceac2d23`
and branch `research/272-is-compare-VJ0Ttaxksx27FdwuEGIrya-inter` did not match
the current origin branch head. `git ls-remote` reported that branch at
`054fd2b7d8dbab7e06712101aa559ef4e8bcb7c0`; the branch history contains
`82173746` followed by `054fd2b7`, whose title is `research(272): census ternary
literal I_s fibres`. Both commits and the note/script were fetched and inspected.
The updated note describes an exhaustive ternary census over `3 ≤ G ≤ 5`,
`2 ≤ L < G`, all placement subsets, and the distinct-read-string adapter; it
reports zero shared nonrotation fibres. The claimed branch artifact is therefore
verified, while its census remains bounded computational evidence rather than a
Lean theorem.

The verifier `scripts/verify_272_aligned_is.py` and its note are **not present
on this `main` checkout**, so the ternary census was not rerun here. Independent
available checks did run: `python3 scripts/verify_272_posterior_support_corners.py`
passed, and `lake build AssemblyP1.FiniteBreslerObstructionGapAudit` completed
(8,935 jobs), printing only `[propext, Classical.choice, Quot.sound]` for its
endpoints. The first Lean invocation timed out at 120 seconds during dependency
build; retrying with a 600-second timeout passed.
