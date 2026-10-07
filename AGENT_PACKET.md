# Agent packet: physical component to ladder coordinates

Read `AGENTS.md`, `docs/skills/itinerary-assemblyp1.md`, and current issue #94 modules first.

## Scope
Finish the concrete bridge from one **physical interlace component** to a finite set of **unique valid coordinates on one common maximal-repeat ladder**.

Relevant modules:
- `Issue94PhysicalChord`
- `Issue94PhysicalComponent`
- `Issue94CoordinateValidity`
- `Issue94InterlaceComponents`
- `BBTLadder`

Already established:
- physical chords are counted once;
- graph reachability transports to `InterlaceConnected`;
- a connected component lies inside one `SameExtension`/maximal-repeat ladder;
- every support chord has valid coordinate `pairBack + (L-1) <= maxPairLen`.

Goal:
1. choose a reference physical chord/component;
2. assign each chord its natural coordinate on the same ladder;
3. prove its unordered AltF pair is the aligned swap at that coordinate;
4. prove coordinate uniqueness/injectivity enough to transfer component cardinality to a coordinate Finset/cardinality.

## Guardrails
- Do **not** prove the unused converse `ShiftPairInterlace` / block=component unless the proof truly needs it.
- Raw repeated-(L-1)-mer chords are not noncrossing; `00101, L=3` is a kernel-checked counterexample to that route.
- Reuse `InterlaceComponents_ladder`, `maxPairStart_rotAdd`, and `support_chord_coordinate_valid`.
- No `sorry`/new axioms. Commit/push and open draft PR when durable.
