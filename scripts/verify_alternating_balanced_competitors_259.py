#!/usr/bin/env python3
"""Exact exhaustive check for balanced 2-mer competitors to (0,m,m,0)."""

from itertools import product


def parameterized(m):
    # Coordinates are (AA, AB, BA, BB). Endpoint balance gives AB=BA=t;
    # mass 2m then leaves AA+BB=2(m-t), freely split.
    return [
        (u, t, t, 2 * (m - t) - u)
        for t in range(m + 1)
        for u in range(2 * (m - t) + 1)
    ]


def brute_force(m):
    out = []
    for aa, ab, ba, bb in product(range(2 * m + 1), repeat=4):
        if aa + ab + ba + bb != 2 * m:
            continue
        if aa + ab != aa + ba or ba + bb != ab + bb:
            continue
        out.append((aa, ab, ba, bb))
    return sorted(out)


def main():
    for m in range(1, 9):
        formula = sorted(parameterized(m))
        exhaustive = brute_force(m)
        assert formula == exhaustive, (m, formula, exhaustive)
        print(f"m={m}: {len(exhaustive)} balanced competitors; all match formula")


if __name__ == "__main__":
    main()
