#!/usr/bin/env python3
"""Issue #257, section 22: directed-cycle sufficiency and the AATT boundary.

Self-contained, exact integer arithmetic, deterministic. Re-derives from
scratch (no repository imports):

1. Directed n-cycle supports (n = 2..6) with uniform multiplicity k = 1..4
   are rigid (balance forces constancy; the total pins the constant).
2. The S = AATT, L = 2 read graph (2 vertices, 4 edges, cycle rank 3, NOT a
   single directed cycle) is rigid at A = (1,1,1,1), G = 4 -- so "single
   directed cycle" is sufficient but NOT necessary (kernel-checked in
   AssemblyP1/RigiditySimpleCycle.lean as `aatt_rigid`).
3. Mutation-red control: the same AATT support at A = (2,1,1,1), G = 5 is
   NON-rigid (witnesses (1,1,2,1)/(1,1,1,2)-style splits), so the harness
   discriminates.
4. Complexity record: decider search space (G+1)^|E| tabulated against the
   zero-sum circulation rank r = |E| - |V| + c - 1.
5. Genome realization: circular S = AATT has L = 2 spectrum
   {AA:1, AT:1, TT:1, TA:1}.
"""

from __future__ import annotations

from itertools import product


def spectrum_circular(s: str, L: int) -> dict:
    n = len(s)
    t = s + s[: L - 1]
    d: dict = {}
    for i in range(n):
        w = t[i : i + L]
        d[w] = d.get(w, 0) + 1
    return d


def brute_rigid(edges, balance_eqs, A, G):
    """Exact brute force: all B in [1..G]^m satisfying balance + total.

    edges: list of edge names; balance_eqs: list of (out_idx, in_idx) groups
    as (list_out, list_in) index lists; returns (rigid, witnesses).
    """
    m = len(edges)
    wit = []
    for vals in product(range(1, G + 1), repeat=m):
        if sum(vals) != G:
            continue
        ok = True
        for out, inn in balance_eqs:
            if sum(vals[i] for i in out) != sum(vals[i] for i in inn):
                ok = False
                break
        if ok:
            wit.append(vals)
    rigid = wit == [tuple(A)]
    return rigid, wit


def check_cycle(n, k):
    # directed n-cycle: vertex v has out {v}, in {(v-1) % n}
    eqs = [([v], [(v - 1) % n]) for v in range(n)]
    A = [k] * n
    return brute_rigid(list(range(n)), eqs, A, n * k)


def main() -> int:
    fails = 0

    # 1. directed n-cycles rigid at uniform multiplicity
    n_cycle_cases = 0
    for n in range(2, 7):
        for k in range(1, 5):
            rigid, wit = check_cycle(n, k)
            n_cycle_cases += 1
            if not rigid:
                print(f"FAIL: {n}-cycle k={k} not rigid: {wit}")
                fails += 1
    print(f"directed cycles n=2..6, k=1..4: {n_cycle_cases} cases, all rigid")

    # 2. AATT support: edges 0:AA (0->0), 1:AT (0->1), 2:TT (1->1), 3:TA (1->0)
    aatt_eqs = [([0, 1], [0, 3]), ([2, 3], [1, 2])]  # balance at A=0, T=1
    rigid, wit = brute_rigid([0, 1, 2, 3], aatt_eqs, [1, 1, 1, 1], 4)
    print(f"AATT A=(1,1,1,1) G=4: rigid={rigid} witnesses={wit}")
    if not rigid:
        print("FAIL: AATT should be rigid")
        fails += 1

    # rank check: |E|-|V|+c-1 = 4-2+1-1 = 2 > 0, so not a single cycle
    r = 4 - 2 + 1 - 1
    print(f"AATT cycle rank r={r} (single cycle would need r=0)")

    # 3. mutation-red control: A=(2,1,1,1), G=5 non-rigid
    rigid5, wit5 = brute_rigid([0, 1, 2, 3], aatt_eqs, [2, 1, 1, 1], 5)
    print(f"AATT A=(2,1,1,1) G=5: rigid={rigid5} witnesses={wit5}")
    if rigid5 or len(wit5) < 2:
        print("FAIL: mutated AATT should be non-rigid (control has no power)")
        fails += 1

    # 4. complexity record
    print("search-space table (G+1)^|E| vs rank r:")
    for name, E, V, c, G in [("cycle2 k=3", 2, 2, 1, 6), ("AATT", 4, 2, 1, 4),
                             ("AATT mut", 4, 2, 1, 5), ("cycle6 k=4", 6, 6, 1, 24)]:
        print(f"  {name}: |E|={E} G={G} space={(G + 1) ** E} r={E - V + c - 1}")

    # 5. genome realization
    spec = spectrum_circular("AATT", 2)
    print(f"circular AATT L=2 spectrum: {spec}")
    if spec != {"AA": 1, "AT": 1, "TT": 1, "TA": 1}:
        print("FAIL: AATT spectrum mismatch")
        fails += 1

    # ATATAT genome control (2-cycle, rigid despite triples)
    spec3 = spectrum_circular("ATATAT", 3)
    print(f"circular ATATAT L=3 spectrum: {spec3}")
    if spec3 != {"ATA": 3, "TAT": 3}:
        print("FAIL: ATATAT spectrum mismatch")
        fails += 1

    if fails:
        print(f"RESULT: {fails} FAILURES")
        return 1
    print("RESULT: all section-22 checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
