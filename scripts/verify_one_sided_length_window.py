#!/usr/bin/env python3
"""Exhaustive small-genome tests of the one-sided P2 length threshold."""
from collections import Counter
from itertools import product


def spectrum(word, length):
    return Counter("".join(word[(i+j) % len(word)]
                           for j in range(length))
                   for i in range(len(word)))


def rotation_equivalent(a, b):
    return len(a) == len(b) and a in b+b


def same_law(a, b, length):
    x, y = spectrum(a, length), spectrum(b, length)
    return all(len(b)*x[w] == len(a)*y[w] for w in x.keys() | y.keys())


# Each truth is primitive, meets P2 for L=3, and branches at its read support.
for alphabet, truth in (("AT", "AAATT"), ("AC", "AAACAC")):
    L = 3
    G = len(truth)
    assert len({truth[i:]+truth[:i] for i in range(G)}) == G
    assert max(spectrum(truth, L-1).values()) <= 2
    checked, boundary_twins = 0, 0
    for size in range(1, 2*G+3):
        for letters in product(alphabet, repeat=size):
            candidate = "".join(letters)
            checked += 1
            if not same_law(truth, candidate, L):
                continue
            if size < 2*G:
                assert rotation_equivalent(truth, candidate), (truth,candidate)
            if size == 2*G and not rotation_equivalent(truth, candidate):
                boundary_twins += 1
    assert boundary_twins >= 1  # Includes truth doubled.
    print(f"{truth}: {checked} candidates; no nonrotation law twin below 2G; "
          f"{boundary_twins} length-2G law twins")
print("Finite candidate-universe and exact law-scaling tests: PASS")
