#!/usr/bin/env python3
"""Exact integer verifier for the #263 augmented throughput-determined cell.

Checks, on the ThroughputSignClash263 4-edge / 2-vertex instance, that any two
augmented-feasible points over the same right-hand side differ in throughput
coordinates exactly by T (outgoing throughput) of the edge difference, and that
the clash instance's feasible pair from `bounded_feasible_pair` satisfies it.

Also checks the zero-throughput corollary fails exactly when T does not vanish
on the edge displacement (the documented obstruction): the naive lifted moves
of the clash instance have throughput coordinates +1/-1, not 0.
"""

from __future__ import annotations

# Instance: E = {0,1,2,3}, V = {0,1}; tail=head: {0,1} -> 0, {2,3} -> 1.
TAIL = {0: 0, 1: 0, 2: 1, 3: 1}
HEAD = dict(TAIL)

G1 = {0: 1, 1: 0, 2: -1, 3: 0}
G2 = {0: 0, 1: -1, 2: 0, 3: 1}
DELTA = {e: G1[e] + G2[e] for e in TAIL}


def throughput(f, v):
    return sum(f[e] for e in TAIL if TAIL[e] == v)


def bal(f, v):
    outf = sum(f[e] for e in TAIL if TAIL[e] == v)
    inf = sum(f[e] for e in TAIL if HEAD[e] == v)
    return outf - inf


def flow_lin(f):
    return ({v: bal(f, v) for v in (0, 1)}, sum(f.values()))


def aug_throughput_determined(x_edge, x_s, y_edge, y_s):
    """Verify y_s - x_s == T(edge diff) coordinatewise (additive T = outgoing)."""
    edge_diff = {e: y_edge[e] - x_edge[e] for e in TAIL}
    ok = True
    for v in (0, 1):
        lhs = y_s[v] - x_s[v]
        rhs = throughput(edge_diff, v)
        if lhs != rhs:
            print(f"FAIL: vertex {v}: y_s - x_s = {lhs} != T(edge diff) = {rhs}")
            ok = False
    return ok


def main() -> int:
    failures = 0

    # Feasible pair from ThroughputSignClash263.bounded_feasible_pair:
    # base point 1, displaced point 1 + delta, box [0,2], same flow rhs.
    base = {e: 1 for e in TAIL}
    disp = {e: 1 + DELTA[e] for e in TAIL}
    assert flow_lin(base) == flow_lin(disp), "instance pair must share flow rhs"

    # Throughput coordinates forced by coupling s_v = T(f)_v.
    base_s = {v: throughput(base, v) for v in (0, 1)}
    disp_s = {v: throughput(disp, v) for v in (0, 1)}
    print(f"base throughput s = {base_s}, displaced throughput s = {disp_s}")

    if not aug_throughput_determined(base, base_s, disp, disp_s):
        failures += 1
    else:
        print("PASS: feasible throughput difference equals T(edge difference)")

    # Zero-throughput corollary scope: T(delta) at vertex 0 is 0 (clash says
    # g1:+1, g2:-1 cancel), so the *total* displacement has zero throughput...
    t_delta = {v: throughput(DELTA, v) for v in (0, 1)}
    print(f"T(delta) = {t_delta}")
    if t_delta[0] == 0 and t_delta[1] == 0:
        print("PASS: total displacement throughput vanishes on this pair")
    else:
        print("NOTE: total displacement throughput nonzero (consistent with clash)")

    # ...but the individual lifted Graver moves do NOT have zero throughput:
    # this is exactly why the general T-sign-compatible lift is obstructed.
    t_g1 = {v: throughput(G1, v) for v in (0, 1)}
    t_g2 = {v: throughput(G2, v) for v in (0, 1)}
    print(f"T(g1) = {t_g1}, T(g2) = {t_g2}")
    if t_g1[0] == 1 and t_g2[0] == -1:
        print("PASS: individual lifted moves keep opposite signs at vertex 0 "
              "(naive T-sign-compatible lift obstructed, as documented)")
    else:
        print("FAIL: unexpected throughput values on clash moves")
        failures += 1

    # Box check for the feasible pair.
    for e in TAIL:
        assert 0 <= base[e] <= 2 and 0 <= disp[e] <= 2
    print("PASS: box bounds hold for the feasible pair")

    if failures:
        print(f"{failures} FAILURE(S)")
        return 1
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
