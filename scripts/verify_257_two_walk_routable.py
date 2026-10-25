#!/usr/bin/env python3
"""Exhaustive cross-check for issue #257: two-walk criterion + routing.

For four small supports (directed 2-cycle, figure-eight, doubled 2-cycle,
directed 3-cycle) and all small positive multiplicity vectors A, checks:

1. brute-force rigidity (complete enumeration of alternative circulations B)
   agrees with the exact delta criterion (nonzero balanced zero-sum
   delta with delta >= 1 - A);
2. for every NONRIGID (A, B): the explicit closed-form routing flow from
   `AssemblyP1.TwoWalkRoutable` (per-lobe max-pairing) builds a valid
   two-closed-walk certificate (f, g) -- this computationally mirrors the
   Lean proof `exists_two_nonneg_circ_of_nonrigid` on every enumerated case;
3. for every RIGID A: bounded search (entries 0..2G) finds no two-walk
   certificate (evidence, not a completeness proof);
4. the Lean-claimed instances: ATATAT (3,3) rigid; figure-eight (1,1,1,1)
   rigid and (2,2,1,1) nonrigid with the exact Lean witness
   f=(0,0,1,1), g=(1,1,0,0).

Exit nonzero on any mismatch.
"""

import itertools
import sys

# Supports: list of (tail, head) per edge index.
SUPPORTS = {
    # ATATAT L=3 graph: single directed 2-cycle.
    "cycle2": ([0, 1], [1, 0]),
    # Figure-eight: lobes {0,1} and {2,3} sharing vertex 0.
    "fig8": ([0, 1, 0, 2], [1, 0, 2, 0]),
    # Doubled 2-cycle (theta): two parallel edges each way.
    "dbl2": ([0, 0, 1, 1], [1, 1, 0, 0]),
    # Directed 3-cycle.
    "cycle3": ([0, 1, 2], [1, 2, 0]),
}

NVERT = {"cycle2": 2, "fig8": 3, "dbl2": 2, "cycle3": 3}


def balanced(tail, head, nv, f):
    for v in range(nv):
        if sum(f[e] for e in range(len(f)) if tail[e] == v) != \
                sum(f[e] for e in range(len(f)) if head[e] == v):
            return False
    return True


def compositions(total, parts, lo=0):
    """All `parts`-tuples of ints >= lo summing to total."""
    if parts == 1:
        if total >= lo:
            yield (total,)
        return
    for x in range(lo, total - lo * (parts - 1) + 1):
        for rest in compositions(total - x, parts - 1, lo):
            yield (x,) + rest


def circulations(name, bound):
    """All nonnegative circulations with entries <= bound (parametrized)."""
    R = range(bound + 1)
    if name == "cycle2":
        return [(k, k) for k in R]
    if name == "fig8":
        return [(a, a, b, b) for a in R for b in R]
    if name == "dbl2":
        out = []
        for a in R:
            for b in R:
                for c in R:
                    d = a + b - c
                    if 0 <= d <= bound:
                        out.append((a, b, c, d))
        return out
    if name == "cycle3":
        return [(k, k, k) for k in R]
    raise AssertionError(name)


def route(tail, head, nv, name, p):
    """Explicit routing flow h >= 0 with p + h balanced (mirrors Lean)."""
    h = [0] * len(p)
    if name == "cycle2":
        if p[1] > p[0]:
            h[0] = p[1] - p[0]
        if p[0] > p[1]:
            h[1] = p[0] - p[1]
    elif name == "fig8":
        if p[1] > p[0]:
            h[0] = p[1] - p[0]
        if p[0] > p[1]:
            h[1] = p[0] - p[1]
        if p[3] > p[2]:
            h[2] = p[3] - p[2]
        if p[2] > p[3]:
            h[3] = p[2] - p[3]
    elif name == "dbl2":
        s0, s1 = p[0] + p[1], p[2] + p[3]
        if s1 > s0:
            h[0] = s1 - s0
        if s0 > s1:
            h[2] = s0 - s1
    elif name == "cycle3":
        m = max(p)
        h = [m - p[e] for e in range(3)]
    else:
        raise AssertionError(name)
    assert all(x >= 0 for x in h), (name, p, h)
    ph = [p[e] + h[e] for e in range(len(p))]
    assert balanced(tail, head, nv, ph), (name, p, h)
    return h


def main():
    failures = []
    rigid_count = nonrigid_count = 0
    for name, (tail, head) in SUPPORTS.items():
        nv = NVERT[name]
        E = len(tail)
        # Multiplicity grid: 1..3 everywhere (feasibility filters below).
        grids = list(itertools.product([1, 2, 3], repeat=E))
        seen = set()
        for A in grids:
            if A in seen:
                continue
            seen.add(A)
            # Rigidity is only defined for feasible truth circulations.
            if not balanced(tail, head, nv, A):
                continue
            G = sum(A)
            # --- brute-force rigidity (complete) ---
            alts = [B for B in compositions(G, E, lo=1)
                    if balanced(tail, head, nv, B) and B != A]
            rigid = not alts
            # --- exact delta criterion (complete over same enumeration) ---
            deltas = []
            for B in compositions(G, E, lo=1):
                if not balanced(tail, head, nv, B) or B == A:
                    continue
                d = tuple(B[e] - A[e] for e in range(E))
                assert sum(d) == 0
                assert all(d[e] >= 1 - A[e] for e in range(E))
                deltas.append(d)
            if rigid == (len(deltas) > 0):
                failures.append(f"{name} A={A}: rigidity/delta mismatch")
            # --- two-walk certificates ---
            if not rigid:
                nonrigid_count += 1
                for B in alts:
                    d = [B[e] - A[e] for e in range(E)]
                    pos = [max(x, 0) for x in d]
                    neg = [max(-x, 0) for x in d]
                    h = route(tail, head, nv, name, pos)
                    f = tuple(pos[e] + h[e] for e in range(E))
                    g = tuple(neg[e] + h[e] for e in range(E))
                    ok = (balanced(tail, head, nv, f)
                          and balanced(tail, head, nv, g)
                          and sum(f) == sum(g) and f != g
                          and all(f[e] - g[e] >= 1 - A[e] for e in range(E)))
                    if not ok:
                        failures.append(
                            f"{name} A={A} B={B}: routing cert invalid")
            else:
                rigid_count += 1
                # bounded no-cert search (evidence only; entries 0..2G)
                circs = circulations(name, 2 * G)
                found = False
                for f in circs:
                    for g in circs:
                        if (f != g and sum(f) == sum(g)
                                and all(f[e] - g[e] >= 1 - A[e]
                                        for e in range(E))):
                            found = True
                            break
                    if found:
                        break
                if found:
                    failures.append(
                        f"{name} A={A}: rigid but bounded cert found")
    # --- Lean-claimed instances ---
    t, h = SUPPORTS["cycle2"]
    assert balanced(t, h, 2, (3, 3))
    assert not [B for B in compositions(6, 2, lo=1)
                if balanced(t, h, 2, B) and B != (3, 3)], "ATATAT not rigid"
    t, h = SUPPORTS["fig8"]
    assert not [B for B in compositions(4, 4, lo=1)
                if balanced(t, h, 3, B) and B != (1, 1, 1, 1)], \
        "fig8 (1,1,1,1) not rigid"
    f, g = (0, 0, 1, 1), (1, 1, 0, 0)
    A = (2, 2, 1, 1)
    assert balanced(t, h, 3, f) and balanced(t, h, 3, g)
    assert sum(f) == sum(g) and f != g
    assert all(f[e] - g[e] >= 1 - A[e] for e in range(4)), "Lean witness bad"
    print(f"supports={len(SUPPORTS)} rigid={rigid_count} "
          f"nonrigid={nonrigid_count} instances-ok")
    if failures:
        print("FAILURES:")
        for x in failures:
            print("  " + x)
        return 1
    print("verify_257_two_walk_routable: all cross-checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
