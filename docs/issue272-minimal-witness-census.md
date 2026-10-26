# Issue #272: minimal exact witness — full 4-promise census on the ambiguous TwoCandidate model

_Agent: eaftAXWamOaLJ33XFqXhto-safeguard. Companion to
[`docs/issue272-minimal-sufficient.md`](./issue272-minimal-sufficient.md) and
[`AssemblyP1/FiniteSourceDefinedMinimal.lean`](../AssemblyP1/FiniteSourceDefinedMinimal.lean).
No new Lean definitions; this note records the complete checkable instance
behind `three_way_distinction` so a reader can verify the minimum / minimal /
weakest distinction by hand._

## Instance

Two genome-orbit candidates `{0, 1}` (distinct orbits), one read `{0}`,
uniform prior `π ≡ 0.5`, full-support likelihood `p ≡ 1`. A promise is a pair
`(E 0 0, E 1 0)`; there are exactly 4. Posterior-1 recovery (sufficiency) holds
iff the promise does not admit both candidates at the read
(`sufficient_iff_not_both`, kernel-checked).

## Census (exact: 2² = 4 promises, enumerated by `scripts/verify_272_minimal_sufficient.py`)

| E 0 0 | E 1 0 | promise | sufficient? | non-vacuous? | role |
|---|---|---|---|---|---|
| F | F | empty (`fun _ _ => False`) | yes (vacuous) | no | **minimum** sufficient promise (`minimum_vacuous`) |
| T | F | designation `g = 0` | yes | yes | minimal / irreducible certificate |
| F | T | designation `g = 1` | yes | yes | minimal / irreducible certificate |
| T | T | `True` (union) | **no** | yes | blocks any weakest member |

Reading the table:

- **Minimum exists and is trivial**: the empty promise is the least element and
  is vacuously sufficient — "minimum additional information" is nothing.
- **Minimal certificates are exactly the designations**: the two non-vacuous
  sufficient promises (`nonvacuous_sufficient_is_designation`,
  `designation_nonvacuous_sufficient`).
- **No weakest certificate**: the two designations are incomparable
  (`designations_incomparable`), and their union `True` is insufficient, so no
  least-informative sufficient promise exists in the source-defined family
  (`three_way_distinction`, reusing `no_weakest` from PR #371).

## Validation

- `python3 scripts/verify_272_minimal_sufficient.py` — all 5 checks PASS
  (re-ran 2026-10-26 on this branch).
- No `sorry`/`admit`/`axiom` in `FiniteSourceDefinedMinimal(Audit).lean`
  (grep-clean; prose mentions only).
- Full `lake build` of the audit modules not re-run here (cold build cache,
  >10 min); previously validated per prior handoff
  (`FiniteSourceDefinedMinimalAudit`, `FiniteSideInformationOrderAudit` PASS,
  8934 jobs).

## Still open (unchanged)

Subclaims (a) (`I_s` necessity for the specific Not-So-Greedy decoder) and (c)
(decoder-level certainty endpoint) remain OPEN; they need the external
Shomorony et al. guarantee as an attributed premise. Nothing here asserts it.
