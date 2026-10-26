#!/usr/bin/env python3
"""Independent exact witness check for a rigid-but-beaten truth in #259."""
from __future__ import annotations

import itertools
from fractions import Fraction
import sys


ALPHABET = range(5)
L = 3
N = 6
UNIVERSE = list(itertools.product(ALPHABET, repeat=L))
INDEX = {word: i for i, word in enumerate(UNIVERSE)}
TRUTH_WORD = (0, 0, 0, 0, 0, 1)
CANDIDATE_WORD = (0, 0, 0, 1, 0, 1)


def spectrum(genome: tuple[int, ...]) -> tuple[int, ...]:
    counts = [0] * len(UNIVERSE)
    for start in range(len(genome)):
        read = tuple(genome[(start + offset) % len(genome)] for offset in range(L))
        counts[INDEX[read]] += 1
    return tuple(counts)


def effective_weight(candidate: tuple[int, ...], i: int) -> int:
    weight = candidate[i]
    for j, count in enumerate(candidate):
        if j != i:
            weight *= N - count
    return weight


def positive_circulations_on_support(truth: tuple[int, ...]):
    edges = [word for word, count in zip(UNIVERSE, truth) if count]
    nodes = {node for edge in edges for node in (edge[:-1], edge[1:])}
    solutions = []
    for values in itertools.product(range(1, N + 1), repeat=len(edges)):
        if sum(values) != N:
            continue
        balance = {node: 0 for node in nodes}
        for edge, value in zip(edges, values):
            balance[edge[:-1]] += value
            balance[edge[1:]] -= value
        if all(value == 0 for value in balance.values()):
            solutions.append(values)
    return solutions


def main() -> int:
    truth = spectrum(TRUTH_WORD)
    candidate = spectrum(CANDIDATE_WORD)
    assert sum(truth) == sum(candidate) == N
    assert [(UNIVERSE[i], v) for i, v in enumerate(truth) if v] == [
        ((0, 0, 0), 3), ((0, 0, 1), 1), ((0, 1, 0), 1), ((1, 0, 0), 1)
    ]
    assert [(UNIVERSE[i], v) for i, v in enumerate(candidate) if v] == [
        ((0, 0, 0), 1), ((0, 0, 1), 1), ((0, 1, 0), 2),
        ((1, 0, 0), 1), ((1, 0, 1), 1)
    ]

    truth_support = {i for i, count in enumerate(truth) if count}
    sample = list(truth)
    sample[INDEX[(0, 0, 1)]] += 32
    sample = tuple(sample)
    assert {i for i, count in enumerate(sample) if count} == truth_support
    assert all(sample[i] >= truth[i] for i in truth_support)
    assert sum(sample) == 38

    # Direct full-universe §6.1 objective ratio; every powered factor is an
    # integer effective weight, including all zero-observation coordinates.
    ratio = Fraction(1)
    for i, count in enumerate(sample):
        if count:
            ratio *= Fraction(effective_weight(candidate, i),
                              effective_weight(truth, i)) ** count
    assert ratio == Fraction(
        2000000000000000000000000000000000000,
        1824800363140073127359051977856583921,
    )
    assert ratio > 1

    circulations = positive_circulations_on_support(truth)
    assert circulations == [(3, 1, 1, 1)]

    print("verify_quinary_rigid_counterexample_259.py")
    print("  alphabet=5, read length=3, candidate length=6, fixed external N=6")
    print("  truth=000001, candidate=000101; both spectra verified from circular words")
    print("  truth is rigid: unique positive same-support circulation (3,1,1,1)")
    print("  covered sample n=38: x(000)=3, x(001)=33, x(010)=1, x(100)=1")
    print(f"  exact §6.1 ratio F_B/F_A={ratio.numerator}/{ratio.denominator} > 1")
    print("OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
