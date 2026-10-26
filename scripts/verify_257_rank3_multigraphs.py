#!/usr/bin/env python3
"""Bounded exact enumeration of arbitrary directed multigraph circulations.

Enumerates support multigraphs on at most four labelled vertices with cycle
rank |E|-|V|+1 at most three (loops and parallel edges allowed), and positive
integer circulations of total mass at most six. Rigidity is decided directly
by checking every other positive integer circulation with the same incidence
balance and total. This is a finite cross-check, not a general algorithm.
"""
from itertools import combinations_with_replacement


def connected(n, edges):
    reach = [{i} for i in range(n)]
    for u, v in edges:
        reach[u].add(v)
        reach[v].add(u)
    changed = True
    while changed:
        changed = False
        for i in range(n):
            merged = set().union(*(reach[j] for j in tuple(reach[i])))
            if merged != reach[i]:
                reach[i] = merged
                changed = True
    return len(set.union(*reach)) == n


def balanced(n, edges, flow):
    div = [0] * n
    for (u, v), x in zip(edges, flow):
        div[u] += x
        div[v] -= x
    return not any(div)


def compositions(total, parts):
    if parts == 1:
        if total >= 1:
            yield (total,)
        return
    for x in range(1, total - parts + 2):
        for rest in compositions(total - x, parts - 1):
            yield (x,) + rest


def circulation_set(n, edges, total):
    return {f for f in compositions(total, len(edges)) if balanced(n, edges, f)}


def enumerate_supports():
    count = 0
    by_support = {}
    for n in range(1, 5):
        possible = [(u, v) for u in range(n) for v in range(n)]
        for m in range(1, min(7, n + 3 + 1)):
            if m - n + 1 > 3:
                continue
            for edges in combinations_with_replacement(possible, m):
                if not connected(n, edges):
                    continue
                # Restrict to supports admitting a positive circulation; the
                # data domain in question is an actual positive support.
                for total in range(m, 7):
                    fs = circulation_set(n, edges, total)
                    positive = tuple(f for f in fs if all(x >= 1 for x in f))
                    if not positive:
                        continue
                    count += 1
                    # Rigid truth means the support/total has one positive
                    # circulation; non-rigid truths are the other members.
                    # Rigidity is invariant among truth flows at fixed support
                    # and total. Save labels across totals for a support-level
                    # multiplicity collision.
                    by_support.setdefault((n, edges), []).append(
                        (total, positive[0], len(positive) == 1))
    collision = next(((n, edges, vals) for (n, edges), vals in by_support.items()
                      if {rigid for _, _, rigid in vals} == {False, True}), None)
    return count, collision


def direct_rigid(n, edges, truth):
    total = sum(truth)
    alternatives = [f for f in compositions(total, len(edges))
                    if balanced(n, edges, f) and f != truth]
    return not alternatives


def mutation_control():
    # Two directed self-loops: unit flow is rigid at total 2, while the same
    # support with truth (2,1) at total 3 is non-rigid via (1,2).
    edges = ((0, 0), (1, 1))
    rigid_truth, flexible_truth = (1, 1), (2, 1)
    rigid_answer = direct_rigid(2, edges, rigid_truth)
    flexible_answer = direct_rigid(2, edges, flexible_truth)
    assert rigid_answer and not flexible_answer
    # Mutation: an erroneous support-only classifier says both statuses equal.
    mutated_rigid, mutated_flexible = False, False
    assert (mutated_rigid, mutated_flexible) != (rigid_answer, flexible_answer)
    print("[mutation] support-only false classifier rejected by loops: ",
          f"{rigid_truth}->{rigid_answer}, {flexible_truth}->{flexible_answer}")


def main():
    count, collision = enumerate_supports()
    # Independent direct incidence checks on representative witness/control.
    assert collision is not None
    n, edges, vals = collision
    rigid = next((f for t, f, r in vals if r), None)
    flexible = next((f for t, f, r in vals if not r), None)
    assert rigid is not None and flexible is not None
    assert direct_rigid(n, edges, rigid)
    assert not direct_rigid(n, edges, flexible)
    print(f"[scope] connected directed multigraph support/total cells: {count}")
    print(f"[collision] same support n={n}, edges={edges}: rigid truth={rigid}; non-rigid truth={flexible}")
    mutation_control()
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
