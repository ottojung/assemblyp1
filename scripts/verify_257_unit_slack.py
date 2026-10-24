#!/usr/bin/env python3
"""Exact verifier for the unit-slack rigidity lemma (issue #257).

`AssemblyP1/RigidityUnitSlack.lean` proves: on any finite support, every
positive balanced circulation B of total G = |E| is the all-ones vector
(hence rigid). This script recomputes that claim from scratch by brute force:
it enumerates ALL positive integer circulations of total G on each support in
scope and checks that at G = |E| each one is all-ones.

Scope (exhaustive in scope; all supports Eulerian so all-ones is feasible):
  * directed cycles C_n, n = 1..4
  * bouquets B_n (one vertex, n loops), n = 1..4
  * figure-eight (two loops sharing a vertex)
  * symmetric theta (two vertices, two antiparallel pairs)
  * bidirectional square (4-cycle with all reverse arcs)

Controls (discriminating power — the harness is not vacuous):
  * at G = |E| at least one feasible circulation exists (all-ones), and
  * at G = 2|E| a non-all-ones feasible circulation exists (all-twos).

Self-contained, exact integer arithmetic, deterministic.
"""

from __future__ import annotations


def compositions(total, parts):
    """All tuples of `parts` positive ints summing to `total`."""
    if parts == 1:
        if total >= 1:
            yield (total,)
        return
    for first in range(1, total - parts + 2):
        for rest in compositions(total - first, parts - 1):
            yield (first,) + rest


def feasible_circulations(edges, nodes, tail, head, total):
    """All B : E -> Z, B >= 1, balanced at every node, sum = total."""
    out = {v: [e for e in edges if tail[e] == v] for v in nodes}
    inn = {v: [e for e in edges if head[e] == v] for v in nodes}
    found = []
    for combo in compositions(total, len(edges)):
        b = dict(zip(edges, combo))
        if all(sum(b[e] for e in out[v]) == sum(b[e] for e in inn[v]) for v in nodes):
            found.append(b)
    return found


def check(supports):
    mismatches = 0
    for name, edges, nodes, tail, head in supports:
        n = len(edges)
        feas = feasible_circulations(edges, nodes, tail, head, n)
        ok = len(feas) >= 1 and all(all(v == 1 for v in b.values()) for b in feas)
        print(f"{name}: |E|={n} G={n} feasible={len(feas)} -> {'ALL-ONES' if ok else 'MISMATCH'}")
        if not ok:
            mismatches += 1
        feas2 = feasible_circulations(edges, nodes, tail, head, 2 * n)
        ctrl = any(any(v != 1 for v in b.values()) for b in feas2)
        print(f"  control G={2 * n}: feasible={len(feas2)} non-all-ones-present={ctrl}")
        if not ctrl:
            print("  CONTROL-FAIL (harness vacuous here)")
            mismatches += 1
    return mismatches


def main():
    supports = []
    for n in (1, 2, 3, 4):
        edges = list(range(n))
        nodes = list(range(n))
        tail = {e: e for e in edges}
        head = {e: (e + 1) % n for e in edges}
        supports.append((f"cycle-C{n}", edges, nodes, tail, head))
    for n in (1, 2, 3, 4):
        edges = list(range(n))
        nodes = [0]
        tail = {e: 0 for e in edges}
        head = {e: 0 for e in edges}
        supports.append((f"bouquet-B{n}", edges, nodes, tail, head))
    supports.append(("figure-eight", [0, 1], [0], {0: 0, 1: 0}, {0: 0, 1: 0}))
    supports.append(("sym-theta", [0, 1, 2, 3], [0, 1],
                     {0: 0, 1: 0, 2: 1, 3: 1}, {0: 1, 1: 1, 2: 0, 3: 0}))
    supports.append(("bidir-square", list(range(8)), [0, 1, 2, 3],
                     {0: 0, 1: 1, 2: 2, 3: 3, 4: 1, 5: 2, 6: 3, 7: 0},
                     {0: 1, 1: 2, 2: 3, 3: 0, 4: 0, 5: 1, 6: 2, 7: 3}))
    bad = check(supports)
    print(f"supports={len(supports)} mismatches={bad}")
    raise SystemExit(1 if bad else 0)


if __name__ == "__main__":
    main()
