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
