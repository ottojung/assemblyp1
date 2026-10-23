# #255 checkpoint audit — 2026-10-23

This is a bounded verification/handoff note, not a classification or closure
of #255. The project was resolved as `https://github.com/ottojung/assemblyp1`;
the fresh clone was at `origin/main` `234f3480d7589c8fc4e056c91dda91343fe64ece`
(the remote `HEAD` verified by `git ls-remote`).

## Prior handoff reconciliation

The newest public #255 terminal-handoff comment available through the GitHub
issues-comments API is agent `Ft1tsPU7eW1Tr9nuzh8ZJN-promoting`, dated
2026-10-22. Its commit `99a310065579c65b492ed7190b7ac69be903f9e9` and document
`docs/handoff-255-independent-front-audit-2026-10-22.md` were checked. That
handoff found no distinct theorem front due to active #261/#284 source/objective
work and #263 sign work; it specifically said not to duplicate the then-live
finite-likelihood verification. It is a coordination audit, not a Lean proof.

The separately supplied checkpoint at `a0ffac3` is **not verifiable on this
remote head**: `git cat-file -t a0ffac3` reports an invalid object name, and
`AssemblyP1/FiniteMLMonotoneTransform.lean` plus its audit are absent from
`origin/main`. Therefore its claimed local-only theorem and validation cannot
be counted as a current repository artifact or exact-head CI result. No claim
is made here that those files are unsound; their contents simply were not
available to audit.

## Verified scope on this head

The current `docs/remaining-open-matrix-255.md` records these scoped results:

* **#256 (CLOSED, scoped):** exact multinomial, same-length oriented,
  sample-uniform support-spectrum rigidity iff (`RobustSameLengthIff.lean`).
* **#258 (CLOSED, scoped):** fixed-observation exact-multinomial product
  criterion and four-chamber finite instance (`FixedXExactML.lean`).
* **#260 (CLOSED, scoped):** fixed-length reverse-complement molecule,
  full-overlap sample-uniform iff (`FullOverlapMoleculeML.lean`).
* **#257 (PARTIAL):** positive fixed-total oriented integer-circulation
  rigidity/Graver criteria are proved; broader graph universes remain open.
* **#259 (PARTIAL):** fixed-N §6.1 effective-weight algebra, several
  covered-sample iff results, and a fixed-x product criterion are on main.
  Specifically, `FixedXProductBinomialMaximality.fixedX_le_iff` gives the
  exact product comparison at a fixed `x`, and `fixedX_weaker_than_pointwise`
  supplies the rational/integer separation witness. Full candidate-universe
  non-integral-frequency classification and unrestricted §6.1 (B) remain
  open.
* **#261 / general §6.2 (OPEN):** physical RC graph/source correspondence,
  exact flow-to-spelled-genome objective transport, and general flow
  classification remain open. The matrix records level-specific partial
  transport and counterexamples, not a solution.
* **Historical string `I_s` versus placement `I_s`:** no inference from the
  placement-based results is counted as proving the literal historical
  condition; source/model matching remains a separate unresolved axis.

The matrix explicitly distinguishes exact multinomial from fixed-N
product-binomial and oriented read types from reverse-complement molecule
types. Neither the full-overlap result nor the historical W1/W2 refutations
settle arbitrary overlap or §6.2. These are repository-documented claims;
this run did not reproduce their exact-head CI history.

## Checks attempted

* Both existing Python verifiers passed:
  `scripts/verify_fixedx_product_binomial_259.py` (including 144,355 exact
  separable-identity cases, 40,000 fixed-x cases, and the strict separation
  witness) and `scripts/verify_covered_binomial_weights_259.py` (47,988 cases).
* `git diff --check` passed for this note.
* Targeted `lake build AssemblyP1.FixedXProductBinomialMaximality
  AssemblyP1.FixedXProductBinomialMaximalityAudit` plus `leanchecker` was
  attempted. The clean clone had to fetch and compile pinned Mathlib from
  scratch; the attempt timed out first at 120 seconds, then at 600 seconds
  during Mathlib dependency compilation (roughly 1,200/8,900 jobs). The target
  modules were not reached. Thus this run provides no fresh Lean or kernel
  replay result and no exact-head CI assertion.
* `gh` is not installed. Public GitHub API reads worked, but no authenticated
  board comment or CI status query was performed.

## Remaining work

Verify whether the missing `FiniteMLMonotoneTransform` local-only artifact can
be recovered from its owner or a published branch; otherwise do not attribute
its theorems to `main`. Re-run the targeted Lean build and both `leanchecker`
commands once the pinned dependencies are available. Then obtain exact-head CI
and an independent proof/scope review. The umbrella and all broader conjectures
remain OPEN.
