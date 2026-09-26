# Issue #88: wraparound contrapositive — historical note

## Status

This line of attack is **retired**.

An earlier formalization used an endpoint-only notion of a read bridging a repeated
copy. That predicate was too weak: it could count a read as bridging a copy without
requiring the read to contain the copy itself. Under that semantics, finite searches
and Lean lemmas exposed an apparent “wraparound” residual regime.

The source-faithful predicate now used in the repository requires a selected read to
contain the repeated copy and extend strictly across both of its flanks. With that
correction, the apparent wraparound regime disappears.

## Kernel-checked replacement

The live proof surface is:

- `SourceFaithfulIs.InformationFeasible` for the source-faithful (I_s) predicate;
- `BridgingBridge.informationFeasible_no_long_triple_repeat`, showing that full
  (I_s) excludes the long maximal triple repeats needed by the escape argument;
- `MLEscape.informationFeasible_no_escape`;
- `MLEscape.informationFeasible_62_spelledML`, stated on the actual realized start
  set;
- `SameLength62Maximizer.informationFeasible_62_maximizer`;
- `OrientedSameLengthML.informationFeasible_exactLik_maximizer`.

The old `EscapeForcesMidRangeRepeat` / wraparound-band conjectural step is not a
remaining hypothesis of the final theorem.

## Why the old AAAAB example disappeared

For the circular truth `AAAAB` at the parameters studied in the old note, the
relevant repeated copies are not all bridged under the corrected definition. Thus
that genome is not (I_s)-feasible and cannot witness a residual case of the
source-faithful theorem.

## Verification

The integrated #88/#92 tree was independently built with the repository-pinned
Lean toolchain. The exported #88 theorems use only the standard axioms reported by
Mathlib/Lean in this repository (`propext`, `Classical.choice`, and
`Quot.sound`); no `sorry`, `admit`, or new project axiom is used.

For the detailed source-semantics audit, see
`docs/bridging-source-semantics-fix.md` and `docs/bridging-lift-audit.md`.
