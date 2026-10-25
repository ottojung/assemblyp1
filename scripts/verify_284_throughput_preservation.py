#!/usr/bin/env python3
"""Vertex-throughput preservation audit for #284 §6.2 spelling reduction.

Issue #284 requirement (5) asks for a language / Observation 7
vertex-throughput preservation audit of the *corrected* spelling-preserving
reduction (`isReducibleSpellingB` / `transitivelyReducedSpelling` in
`AssemblyP1.Section62SpellingReductionCandidate`), on the same finite
regression instance used by `verify_284_reduction_survival_matrix.py`:

  reads (length 3): strand 0 = [0,1,2], strand 1 = [1,2,3], strand 2 = [2,3,4]
  direct edge : 0 -> 2 with overlap 1 (REMOVED by the corrected reduction)
  detour legs : 0 -> 1 and 1 -> 2 with overlap 2 (both SURVIVE)

Throughput model (mirrors `Section62BidirectedFlow.throughput`): the flow
through a read-vertex molecule class `v` is the total flow on graph edges
departing from class `v` (departures), and dually arrivals count edges
entering class `v`. Observation 7 identifies these with walk visit counts.

Audited claims (all checked on the finite instance, exit 0 iff all hold):

  1. SPELLING: `spellDirect(sx, sy, e) == spellPath(sx, m, sy, l1, l2)`
     (Lean defs: `sx ++ sy.drop l` vs `sx ++ m.drop l1 ++ sy.drop l2`).
  2. ENDPOINT USAGE PRESERVED: rerouting one unit of flow from the direct
     edge onto the two detour legs preserves departures from the outer
     source class and arrivals at the outer sink class.
  3. DOCUMENTED BOUNDARY (not hidden): the intermediate molecule class
     gains exactly +1 departure and +1 arrival. Pointwise vertex throughput
     is therefore NOT preserved by the reroute; the honest preserved
     quantities are the spelled word and the outer-endpoint usages, i.e.
     local language preservation, not Observation 7 throughput equivalence.
     Global Observation 7 throughput equivalence remains an open front
     (as stated in `Section62SpellingReductionCandidate`).
  4. GRAPH MEMBERSHIP: direct edge and both legs are members of the complete
     `overlapEdges` graph; the direct edge is removed and both legs survive
     the corrected reduction (cross-check of the survival-matrix claim).
"""

from __future__ import annotations

import sys
from collections import Counter

STRAND = {0: [0, 1, 2], 1: [1, 2, 3], 2: [2, 3, 4]}
VERTS = [0, 1, 2]
READLEN = 3
OMIN = 1


def rc(w: int) -> int:
    return (w + 3) % 6


def rep(w: int) -> int:
    return w if w < 3 else w - 3


def strands_of(verts: list[int]) -> list[int]:
    return verts + [rc(v) for v in verts]


def pre(lst: list[int], k: int) -> list[int]:
    return lst[:k]


def suf(lst: list[int], k: int) -> list[int]:
    return lst[len(lst) - k:] if k <= len(lst) else lst


def spell_direct(sx: list[int], sy: list[int], length: int) -> list[int]:
    return sx + sy[length:]


def spell_path(sx: list[int], m: list[int], sy: list[int], l1: int, l2: int) -> list[int]:
    return sx + m[l1:] + sy[l2:]


def bd_edge(sx: int, sy: int, length: int) -> tuple:
    return (sx, sy, length)


def overlap_edges(verts: list[int], readlen: int, omin: int) -> list[tuple]:
    out: list[tuple] = []
    for length in range(readlen):
        if length < omin:
            continue
        for sx in strands_of(verts):
            for sy in strands_of(verts):
                if suf(STRAND.get(sx, []), length) == pre(STRAND.get(sy, []), length):
                    if sx in STRAND and sy in STRAND:
                        out.append(bd_edge(sx, sy, length))
    return out


def is_reducible_spelling(e: tuple, verts: list[int], readlen: int, omin: int) -> bool:
    for m in strands_of(verts):
        if m not in STRAND:
            continue
        for l1 in range(readlen):
            for l2 in range(readlen):
                if (
                    omin <= l1
                    and omin <= l2
                    and suf(STRAND[e[0]], l1) == pre(STRAND[m], l1)
                    and suf(STRAND[m], l2) == pre(STRAND[e[1]], l2)
                    and l1 + l2 == readlen + e[2]
                ):
                    return True
    return False


def departures(flow: Counter, classes: list[int]) -> dict[int, int]:
    return {v: sum(f for (sx, _sy, _l), f in flow.items() if rep(sx) == v) for v in classes}


def arrivals(flow: Counter, classes: list[int]) -> dict[int, int]:
    return {v: sum(f for (_sx, sy, _l), f in flow.items() if rep(sy) == v) for v in classes}


def main() -> int:
    errors: list[str] = []
    graph = overlap_edges(VERTS, READLEN, OMIN)
    direct = bd_edge(0, 2, 1)
    leg1 = bd_edge(0, 1, 2)
    leg2 = bd_edge(1, 2, 2)
    classes = [0, 1, 2]

    # (4) membership cross-check.
    for label, edge in (("direct", direct), ("leg1", leg1), ("leg2", leg2)):
        if edge not in graph:
            errors.append(f"{label} edge {edge} not in overlapEdges graph")
    reduced = [e for e in graph if not is_reducible_spelling(e, VERTS, READLEN, OMIN)]
    if direct in reduced:
        errors.append("corrected reduction failed to remove the direct edge")
    if leg1 not in reduced or leg2 not in reduced:
        errors.append("corrected reduction removed a detour leg")

    # (1) spelling preservation for the witness (l1 = l2 = 2, e = 1).
    w_direct = spell_direct(STRAND[0], STRAND[2], 1)
    w_path = spell_path(STRAND[0], STRAND[1], STRAND[2], 2, 2)
    if w_direct != [0, 1, 2, 3, 4]:
        errors.append(f"unexpected direct spelling {w_direct}")
    if w_path != w_direct:
        errors.append(f"detour spelling {w_path} != direct spelling {w_direct}")

    # (2)/(3) throughput audit: reroute one unit direct -> leg1 + leg2.
    f0: Counter = Counter({direct: 1})
    f1: Counter = Counter({leg1: 1, leg2: 1})
    dep0, dep1 = departures(f0, classes), departures(f1, classes)
    arr0, arr1 = arrivals(f0, classes), arrivals(f1, classes)
    if dep0[0] != dep1[0]:
        errors.append(f"outer-source departures not preserved: {dep0[0]} vs {dep1[0]}")
    if arr0[2] != arr1[2]:
        errors.append(f"outer-sink arrivals not preserved: {arr0[2]} vs {arr1[2]}")
    # Documented boundary: intermediate class gains exactly one visit each way.
    if not (dep1[1] - dep0[1] == 1 and arr1[1] - arr0[1] == 1):
        errors.append(
            f"intermediate-class delta != +1/+1: dep {dep0[1]}->{dep1[1]}, "
            f"arr {arr0[1]}->{arr1[1]}"
        )
    if not (dep0[2] == dep1[2] == 0 and arr0[0] == arr1[0] == 0):
        errors.append("unexpected flow touches uninvolved endpoint classes")

    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    print(
        "§6.2 throughput audit verified: spelled word [0,1,2,3,4] identical; "
        f"outer-source departures {dep0[0]}->{dep1[0]}, outer-sink arrivals "
        f"{arr0[2]}->{arr1[2]} preserved; intermediate class +1/+1 "
        "(pointwise Observation 7 throughput NOT preserved -- documented boundary)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
