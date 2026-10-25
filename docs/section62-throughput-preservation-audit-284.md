# §6.2 vertex-throughput preservation audit (#284, requirement 5, finite step)

Finite audit on the `Section62SpellingReductionCandidate` regression instance
(reads `[0,1,2]`, `[1,2,3]`, `[2,3,4]`; direct `1`-overlap `0→2` removed,
detour legs `0→1`, `1→2` with overlap `2` surviving).

Mechanical companion: `scripts/verify_284_throughput_preservation.py` (exit 0).

## Result

- Spelled word identical: direct spells `[0,1,2,3,4]`, two-hop detour spells
  `[0,1,2,3,4]` (Lean defs `spellDirect` = `sx ++ sy.drop l`,
  `spellPath` = `sx ++ m.drop l1 ++ sy.drop l2`).
- Rerouting one unit of flow direct → leg1 + leg2 preserves outer-endpoint
  usage: source-class departures `1 → 1`, sink-class arrivals `1 → 1`.
- **Documented boundary (not a preservation claim):** the intermediate
  molecule class gains exactly `+1` departure and `+1` arrival. Pointwise
  vertex throughput in the sense of Observation 7 is therefore NOT preserved
  by the single-edge reroute. What is preserved is the spelled word and the
  outer-endpoint usages — local language preservation, not Observation 7
  throughput equivalence.

## Scope

This is one finite audit step, not a general throughput-equivalence proof.
Global Observation 7 throughput equivalence for the simultaneous reduction
remains an open front, as stated in
`AssemblyP1.Section62SpellingReductionCandidate`. The old predicate
`Section62BidirectedFlow.isReducibleB` is untouched by this note; the audit
concerns only the corrected spelling-preserving reduction.
