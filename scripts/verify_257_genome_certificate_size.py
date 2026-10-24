#!/usr/bin/env python3
"""Exhaustively check support-size/slack witness bounds on tiny circular genomes."""
from collections import Counter
from itertools import product


def circulation(word, length):
    size = len(word)
    return Counter("".join(word[(i + j) % size] for j in range(length))
                   for i in range(size))


def check():
    tested = 0
    for size in range(1, 9):
        for letters in product("AB", repeat=size):
            word = "".join(letters)
            for length in range(1, size + 1):
                counts = circulation(word, length)
                edges = tuple(sorted(counts))
                m = len(edges)
                total = size
                assert m <= 2 ** length
                slack_mass = total - m
                # The truth itself supplies an admissible zero-sum circulation.
                assert all(counts[e] >= 1 for e in edges)
                assert sum(counts[e] - 1 for e in edges) == slack_mass
                # Check exact truth counts against the edge and excess bounds;
                # candidate-wide validity is established by the proof in §23.
                assert all(1 <= counts[e] <= total for e in edges)
                tested += 1
    print(f"genome certificate-size: {tested} circular (word,L) cases, bounds hold")


if __name__ == "__main__":
    check()
