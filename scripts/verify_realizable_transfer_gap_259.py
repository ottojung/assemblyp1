#!/usr/bin/env python3
"""Exact bounded verification of the #259 realizable/full-class gap.

No Lean import. Checks the endpoint-multiset characterization of transfer
balance and a binary-necklace census; it does not claim an all-length result.
"""

from __future__ import annotations

import itertools
from collections import defaultdict
from fractions import Fraction


def eff(N, B, i):
    value = B[i]
    for j, bj in enumerate(B):
        if j != i:
            value *= N - bj
    return value


def score(N, B, x):
    value = 1
    for i, xi in enumerate(x):
        value *= eff(N, B, i) ** xi
    return value


def support(A):
    return [i for i, ai in enumerate(A) if ai]


def beats_on_some_covered_sample(N, A, B):
    S = support(A)
    if any(eff(N, B, i) == 0 for i in S):
        return False
    return any(eff(N, B, i) > eff(N, A, i) for i in S)


def full_class_max(A):
    return len(support(A)) == 1 or all(a <= 1 for a in A)


def necklaces(G):
    seen = set()
    for word in itertools.product((0, 1), repeat=G):
        if word not in seen:
            seen.update(word[k:] + word[:k] for k in range(G))
            yield word


def spectrum(word, L, universe):
    counts = defaultdict(int)
    G = len(word)
    for i in range(G):
        counts[tuple(word[(i + t) % G] for t in range(L))] += 1
    return tuple(counts[w] for w in universe)


def realizable(L, G, universe):
    by_spectrum = {}
    for word in necklaces(G):
        by_spectrum.setdefault(spectrum(word, L, universe), word)
    return by_spectrum


def balance(edges, values):
    nodes = {}
    for edge in edges:
        nodes.setdefault(edge[:-1], len(nodes))
        nodes.setdefault(edge[1:], len(nodes))
    residual = [0] * len(nodes)
    for edge, count in zip(edges, values):
        residual[nodes[edge[:-1]]] += count
        residual[nodes[edge[1:]]] -= count
    return residual


def check_transfer_balance(L, G, universe):
    checked = preserved = 0
    for A_tuple in realizable(L, G, universe):
        A = list(A_tuple)
        edges = [w for w, count in zip(universe, A) if count]
        S = support(A)
        for j in S:
            if A[j] < 2:
                continue
            for i in S:
                if i == j:
                    continue
                B = A.copy()
                B[i] += 1
                B[j] -= 1
                balanced = not any(balance(edges, [B[universe.index(w)] for w in edges]))
                wi, wj = universe[i], universe[j]
                endpoint_condition = sorted((wi[:-1], wj[1:])) == sorted((wj[:-1], wi[1:]))
                assert balanced == endpoint_condition, (L, G, A, i, j, B)
                checked += 1
                preserved += int(balanced)
    return checked, preserved


def flood_witness(N, A, B):
    i = next(i for i in support(A) if eff(N, B, i) > eff(N, A, i))
    ratio = Fraction(1)
    for j, aj in enumerate(A):
        if j != i:
            # Off-truth-support coordinates have exponent zero.  Avoid forming
            # 0/0 there: only truth-supported factors enter the ratio.
            if aj:
                ratio *= Fraction(eff(N, B, j), eff(N, A, j)) ** aj
    step = Fraction(eff(N, B, i), eff(N, A, i))
    x = A.copy()
    while ratio * step ** x[i] <= 1:
        x[i] += 1
    assert score(N, B, x) > score(N, A, x)
    return x


def check_census(L, G, universe):
    spectra = realizable(L, G, universe)
    vectors = list(spectra)
    categories = {"both_max": 0, "both_beaten": 0, "gap": 0}
    gap_witnesses = []
    for A_tuple in vectors:
        A = list(A_tuple)
        assert all(eff(G, A, i) > 0 for i in support(A))
        real_max = not any(
            B_tuple != A_tuple and beats_on_some_covered_sample(G, A, list(B_tuple))
            for B_tuple in vectors
        )
        full_max = full_class_max(A)
        if full_max and real_max:
            categories["both_max"] += 1
        elif not full_max and not real_max:
            categories["both_beaten"] += 1
        elif not full_max and real_max:
            categories["gap"] += 1
            transfer = None
            S = support(A)
            for j in S:
                if A[j] < 2:
                    continue
                for i in S:
                    if i != j:
                        B = A.copy()
                        B[i] += 1
                        B[j] -= 1
                        if beats_on_some_covered_sample(G, A, B):
                            transfer = B
                            break
                if transfer is not None:
                    break
            if transfer is not None:
                assert tuple(transfer) not in spectra
                gap_witnesses.append((A, spectra[A_tuple], transfer, flood_witness(G, A, transfer)))
        else:
            raise AssertionError(f"subclass maximality contradiction: {A}")
    return categories, gap_witnesses


def main():
    transfer_checks = transfer_preserved = 0
    totals = {"both_max": 0, "both_beaten": 0, "gap": 0}
    smallest = None
    for L in (2, 3):
        universe = list(itertools.product((0, 1), repeat=L))
        for G in range(L, 11):
            count, preserved = check_transfer_balance(L, G, universe)
            transfer_checks += count
            transfer_preserved += preserved
            categories, witnesses = check_census(L, G, universe)
            for key, value in categories.items():
                totals[key] += value
            if witnesses and smallest is None:
                A, word, B, x = witnesses[0]
                smallest = (L, G, A, word, B, x)

    assert transfer_checks == 1794 and transfer_preserved == 98
    assert totals == {"both_max": 50, "both_beaten": 216, "gap": 14}, totals
    assert smallest is not None
    L, G, A, word, B, x = smallest
    assert (L, G, A, B, x) == (2, 4, [0, 2, 2, 0], [0, 1, 3, 0], [0, 2, 4, 0])
    assert score(G, B, x) > score(G, A, x)
    print("transfer balance: 1794 checks, 98 balanced, 0 endpoint-condition mismatches")
    print("binary necklace census L=2,3 G<=10: both_max=50 both_beaten=216 gap=14")
    print(f"smallest gap: L={L} G=N={G} truth={A} word={''.join(map(str, word))}")
    print(f"  unrealizable beater={B}, covered x={x}, exact F_B(x)>F_A(x)")
    print("OK")


if __name__ == "__main__":
    main()
