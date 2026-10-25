#!/usr/bin/env python3
"""Connectivity-filtered census for issue #272; not the historical pruned graph."""
import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from verify_272_is_necessity import (  # noqa: E402
    all_windows, bridges_copy, canon, failing_clause, readset, window,
)


def connected(reads):
    reads = list(reads)
    if len(reads) <= 1:
        return True
    seen, stack = {reads[0]}, [reads[0]]
    while stack:
        a = stack.pop()
        for b in reads:
            if b not in seen and (a[1:] == b[:-1] or b[1:] == a[:-1]):
                seen.add(b)
                stack.append(b)
    return len(seen) == len(reads)


def check_witness():
    s, L, R = (0, 0, 0, 1), 3, (1, 2, 3)
    Y = readset(s, L, R)
    assert Y == frozenset({(0, 0, 1), (0, 1, 0), (1, 0, 0)})
    assert failing_clause(s, L, R) == "triple"
    assert connected(Y)
    edge = lambda a, b: a[1:] == b[:-1]
    assert edge((1, 0, 0), (0, 0, 1))
    assert edge((0, 0, 1), (0, 1, 0))
    assert edge((0, 1, 0), (1, 0, 0))
    real = [t for t in itertools.product(range(2), repeat=4)
            if Y <= all_windows(t, L)]
    assert {canon(t) for t in real} == {canon(s)} and len(real) == 4
    print("AAAB L=3 R=(1,2,3): connected triple-failing singleton orbit verified")


def strongly_connected(reads):
    """Directed (L-1)-overlap strong connectivity: edge a->b iff a[1:]==b[:-1].

    Elementary graph notion only; NOT the historical pruned Not-So-Greedy graph.
    """
    reads = list(reads)
    if len(reads) <= 1:
        return True
    for s in reads:
        seen, stack = {s}, [s]
        while stack:
            a = stack.pop()
            for b in reads:
                if b not in seen and a[1:] == b[:-1]:
                    seen.add(b)
                    stack.append(b)
        if len(seen) != len(reads):
            return False
    return True


def check_directed_vs_undirected():
    """ONE distinguishing cell: undirected-connected but not strongly connected.

    Witness AAAB, L=3, R={0,1}: Y={AAA,AAB} is undirected-connected yet the
    directed overlap graph has no AAB->AAA edge. Certainty still holds (the
    read-realizable support is the single AAAB orbit), so elementary
    undirected connectivity is strictly weaker than directed strong
    connectivity on certainty-holding I_s-failing cells.
    """
    s, L, R = (0, 0, 0, 1), 3, (0, 1)
    Y = readset(s, L, R)
    assert Y == frozenset({(0, 0, 0), (0, 0, 1)})
    assert failing_clause(s, L, R) == "coverage"
    assert connected(Y)
    assert not strongly_connected(Y)
    real = [t for t in itertools.product(range(2), repeat=4)
            if Y <= all_windows(t, L)]
    assert {canon(t) for t in real} == {canon(s)} and len(real) == 4
    print("AAAB L=3 R={0,1}: undirected-connected, NOT strongly connected, "
          "singleton orbit verified")


def census_strong(G_values, alphabets):
    """Count certainty-holding I_s-failing cells that are undirected-connected
    but not directed-strongly-connected, by failing clause."""
    weak_only = {"coverage": 0, "triple": 0, "interleaved": 0}
    for G in G_values:
        for k in alphabets:
            if k ** G > 3000:
                continue
            genomes = list(itertools.product(range(k), repeat=G))
            canonical = {g: canon(g) for g in genomes}
            windows = {(g, L): all_windows(g, L) for g in genomes
                       for L in range(2, G)}
            for s in genomes:
                if canonical[s] != s or len(set(s)) == 1:
                    continue
                for L in range(2, G):
                    for mask in range(1, 1 << G):
                        R = tuple(i for i in range(G) if mask & (1 << i))
                        clause = failing_clause(s, L, R)
                        if clause is None:
                            continue
                        Y = readset(s, L, R)
                        if all(canonical[t] == canonical[s] or
                               not Y <= windows[(t, L)] for t in genomes):
                            if connected(Y) and not strongly_connected(Y):
                                weak_only[clause] += 1
    return weak_only


def census(G_values, alphabets):
    total = {c: 0 for c in ("coverage", "triple", "interleaved")}
    conn = dict.fromkeys(total, 0)
    for G in G_values:
        for k in alphabets:
            if k ** G > 3000:
                continue
            genomes = list(itertools.product(range(k), repeat=G))
            canonical = {g: canon(g) for g in genomes}
            windows = {(g, L): all_windows(g, L) for g in genomes
                       for L in range(2, G)}
            for s in genomes:
                if canonical[s] != s or len(set(s)) == 1:
                    continue
                for L in range(2, G):
                    for mask in range(1, 1 << G):
                        R = tuple(i for i in range(G) if mask & (1 << i))
                        clause = failing_clause(s, L, R)
                        if clause is None:
                            continue
                        Y = readset(s, L, R)
                        if all(canonical[t] == canonical[s] or
                               not Y <= windows[(t, L)] for t in genomes):
                            total[clause] += 1
                            if connected(Y):
                                conn[clause] += 1
    return total, conn


def main():
    check_witness()
    total, conn = census((4, 5, 6), (2, 3))
    print("G<=6 total:", total)
    print("G<=6 connected:", conn)
    assert total == {"coverage": 3807, "triple": 4584, "interleaved": 0}
    assert conn == {"coverage": 2370, "triple": 2128, "interleaved": 0}
    total7, conn7 = census((7,), (2,))
    print("G=7,k=2 total:", total7)
    print("G=7,k=2 connected:", conn7)
    assert total7 == {"coverage": 396, "triple": 2100, "interleaved": 0}
    assert conn7 == {"coverage": 228, "triple": 810, "interleaved": 0}
    check_directed_vs_undirected()
    weak6 = census_strong((4, 5, 6), (2, 3))
    print("G<=6 connected-but-not-strong:", weak6)
    assert weak6 == {"coverage": 2370, "triple": 1802, "interleaved": 0}
    weak7 = census_strong((7,), (2,))
    print("G=7,k=2 connected-but-not-strong:", weak7)
    assert weak7 == {"coverage": 228, "triple": 752, "interleaved": 0}


if __name__ == "__main__":
    main()
