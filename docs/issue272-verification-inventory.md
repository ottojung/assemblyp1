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

## Probability-endpoint audit (2026-10-27)

The delegated endpoint question is resolved for the generic finite posterior
iff theorem: no strict-positivity assumption on every candidate is needed.
`jointMass_pos_iff` identifies positive support exactly as
`π g > 0 ∧ p_g(r) > 0 ∧ E(g,r)`. Thus zero-prior, zero-likelihood, and
promise-excluded candidates contribute zero; ties remain possible only among
positive supported candidates. `posteriorMass_eq_one_iff` requires
`predictiveMass > 0`, which is the exact domain restriction preventing an
undefined `0/0` posterior. For a decoder and the a.s. theorem, the pointwise
quantification is likewise restricted to `predictiveMass > 0`; observations
with zero predictive mass do not affect a.s. certainty.

Independent targeted validation at main `3decc39b`:

* `lake env lean AssemblyP1/FiniteBayesianSideInformationAudit.lean` passes;
  the printed dependencies for the core iff, excluded-competitor, read-only,
  side-channel, and a.s./pointwise theorems are exactly
  `[propext, Classical.choice, Quot.sound]`.
* `python3 scripts/verify_272_posterior_support_corners.py` passes its exact
  rational cases for positive mass, zero prior, zero likelihood, and zero
  predictive mass. This is a targeted example check, not the proof; the Lean
  theorem supplies the general proof.

No code change was required. Endpoint validity is already covered by the
existing theorem and positivity-domain hypotheses. This is a bounded audit;
it does not close the full issue's explicitly open AssemblyP1 bridge or
algorithm-specific necessity questions.
