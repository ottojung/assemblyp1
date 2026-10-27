# Issue #272 target 5: independent re-verification of the Bresler obstruction gap (2026-10-27)

Scope: no new theorem. Independent re-verification of the existing endpoint
`AssemblyP1/FiniteBreslerObstructionGap.lean` (+ audit) and its companion
`docs/issue272-bresler-obstruction-gap.md`, which states:

- **Necessity** (`sourceObstruction_necessary_of_bresler`): from the attributed
  Bresler--Bresler--Tse (2013, Theorem 1) equal-likelihood premise, an
  all-unbridged interleaved pair or triple repeat yields a same-length
  competitor with identical read likelihood, so the read-only posterior is not 1.
  The external construction enters only as a theorem hypothesis, not an axiom.
- **Non-sufficiency** (`sourceObstruction_not_sufficient_for_readOnly_certainty`):
  unconditional kernel-checked counterexample — an obstruction-absent model
  whose read-realizable support spans more than one rotation orbit.

## Checks run (isolated clone, origin/main `3decc39`)

- `python3 scripts/verify_272_posterior_support_corners.py` — PASS
  (positive-mass support and zero-support corners).
- `python3 scripts/verify_272_bresler_obstruction.py` — PASS
  (AABB/L=2 witness; exhaustive G<=7 binary search finds 5
  obstruction-absent ambiguous models, so the all-unbridged obstruction
  is not sufficient for read-only certainty).
- `python3 scripts/check-research-docs.py` — PASS.
- `rg -n "sorry|admit|^axiom "` over `FiniteBreslerObstructionGap.lean`,
  `FiniteBreslerObstructionGapAudit.lean`, `FiniteBayesianSideInformation.lean` —
  sole hit is a docstring sentence ("No `axiom`, `sorry`, or `admit` is
  introduced"); no `sorry`/`admit`/`axiom` declarations.
- `git diff --check` — clean.
- `lake build AssemblyP1.FiniteBreslerObstructionGapAudit` — NOT verified here:
  cold-cache build exceeded the 600s run limit before compiling Mathlib
  dependencies. Prior checkpoints report this audit target passing with the
  standard axiom set `{propext, Classical.choice, Quot.sound}`; that claim is
  inherited, not re-established by this run.

## Status

Target 5 (obstruction necessary but not sufficient) remains verified at the
script + source-audit level. Remaining open work: warm-cache Lean rebuild of
the gap audit, exact-head full CI, signed PR, and independent review.
The literal 2016 decoder behaviour and general random-read adapters stay open
per the issue deliverable.
