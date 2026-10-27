#!/usr/bin/env python3
"""Exhaustive shortest-overlap boundary for the ACA/CAC flow cell.

Reuses the literal graph, signed balance, throughput and likelihood definitions
from verify_261_flow_cell_acac.py. The binomial probability restriction d_i<=N
also bounds every nonnegative edge flow by N, since each edge contributes to the
throughput of its source RC class. Thus enumerating [0,N]^8 is exhaustive for
the stated finite candidate domain.
"""
import itertools
import runpy
from pathlib import Path


BASE = runpy.run_path(str(Path(__file__).with_name("verify_261_flow_cell_acac.py")))
EDGES = BASE["EDGES"]
VERTS = BASE["VERTS"]
N, X = 3, (2, 1)


def maxima(forbidden):
    best = -1
    vectors = set()
    count = 0
    for flow in itertools.product(range(N + 1), repeat=len(EDGES)):
        if any(flow[i] for i in forbidden) or not BASE["feasible"](flow):
            continue
        d = tuple(BASE["throughput"](flow, v) for v in VERTS)
        if any(value > N for value in d):
            continue
        score = BASE["K"](d, X, N)
        if score > best:
            best, vectors, count = score, {d}, 1
        elif score == best:
            vectors.add(d)
            count += 1
    return best, vectors, count


def main():
    short = {i for i, edge in enumerate(EDGES) if edge[2] == 1}
    long = {i for i, edge in enumerate(EDGES) if edge[2] == 2}
    assert len(EDGES) == 8 and len(short) == len(long) == 4
    assert not any(BASE["isReducible"](edge) for edge in EDGES)

    all_best = maxima(set())
    no_short_best = maxima(short)
    long_only_best = maxima(short)
    assert all_best[0] == 16 and all_best[1] == {(2, 1)}
    assert no_short_best[0] == 8 and no_short_best[1] == {(1, 1), (2, 2)}
    assert long_only_best == no_short_best

    print("ALL CHECKS PASSED")
    print(f"all 8 edges: max K={all_best[0]}, throughput vectors={sorted(all_best[1])}")
    print(f"length-2 edges only: max K={no_short_best[0]}, throughput vectors={sorted(no_short_best[1])}")
    print("Conclusion: this cell's strict flow defeater requires a length-1 edge.")


if __name__ == "__main__":
    main()
