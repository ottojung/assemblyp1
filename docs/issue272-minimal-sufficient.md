# Issue #272, target 4: minimum and minimal sufficient promises in the source-defined family

_Status: 2026-10-20. Mathematical formalization front. Answers the
minimum / minimal half of the "weakest conditioning" question of #272,
complementing the weakest-member characterization of
[`AssemblyP1/FiniteSourceDefinedWeakest.lean`](../AssemblyP1/FiniteSourceDefinedWeakest.lean)
(PR #371). Companion Lean module:
[`AssemblyP1/FiniteSourceDefinedMinimal.lean`](../AssemblyP1/FiniteSourceDefinedMinimal.lean),
axiom-audited by
[`AssemblyP1/FiniteSourceDefinedMinimalAudit.lean`](../AssemblyP1/FiniteSourceDefinedMinimalAudit.lean)._

This document does not re-derive the weakest-member results. It reuses the exact
posterior semantics of
[`AssemblyP1/FiniteBayesianSideInformation.lean`](../AssemblyP1/FiniteBayesianSideInformation.lean),
the promise-order results of
[`AssemblyP1/FiniteSideInformationOrder.lean`](../AssemblyP1/FiniteSideInformationOrder.lean),
the source-defined family of
[`AssemblyP1/FiniteSourceDefinedWeakest.lean`](../AssemblyP1/FiniteSourceDefinedWeakest.lean),
and the minimum-promise machinery of
[`AssemblyP1/FiniteReadOnlyDecoderCertainty.lean`](../AssemblyP1/FiniteReadOnlyDecoderCertainty.lean)
unchanged.

## The question

The issue asks to *distinguish a minimal sufficient promise from a minimum* and to
avoid claiming an intrinsic least event without establishing it. Within the fixed
structural family `AdmSourceDefined` (promises built only from the observed read or
only from the truth), what is the **minimum / minimal additional information**
that certifies posterior-1 recovery?

## The answer

| notion | status in the source-defined family | certificate |
|---|---|---|
| minimum sufficient promise | **always exists**, is the **vacuous empty promise** | `fun _ _ => False` |
| weakest sufficient promise | exists **iff** `∀ r, Unambiguous` (PR #371) | `True` when it exists |
| non-vacuous sufficient promise | exactly the **candidate designations** `g = g₀` | truth-only singletons |

The key correction is that the empty promise is *always* sufficient
(vacuously), so the "minimum additional information" is trivially **nothing**
(`minimum_vacuous`). The meaningful certificates are the **non-vacuous**
sufficient promises, and within the source-defined family those are exactly the
candidate designations.

## The theorem (kernel-checked)

On the ambiguous `TwoCandidate` model (two candidates, one read, both realizable,
distinct orbits):

**Theorem (`three_way_distinction`, kernel-checked).** A minimum sufficient
promise exists (the vacuous empty promise); every non-vacuous sufficient promise is
a candidate designation; and the source-defined family has no weakest member.

- `sufficient_iff_not_both` — a promise is sufficient iff it does not admit both
  candidates.
- `nonvacuous_sufficient_is_designation` — every non-vacuous sufficient promise is
  a designation `g = 0` or `g = 1`.
- `designation_nonvacuous_sufficient` — every designation is non-vacuous and
  sufficient.
- `designations_incomparable` — the two designations are incomparable, so there is
  no single weakest certificate: you must be *told a candidate*, and there is no
  canonical choice.

This distinguishes a **minimum** (the vacuous empty promise, always present) from
a **minimal / irreducible certificate** (a candidate designation) from a
**weakest** (least informative, may not exist).

## Genuinely open

Subclaims (a) (`I_s` necessity for the specific Not-So-Greedy decoder) and (c)
(the decoder-level certainty endpoint) remain OPEN and unchanged; they require the
external Not-So-Greedy guarantee as an attributed premise. Nothing here asserts
that external theorem.
