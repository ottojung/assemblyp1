#!/usr/bin/env python3
"""Exact independent arithmetic for an observed-read molecule-class ML witness.

This script intentionally does not import the project's Lean theorems.
They supply the bridge/flow feasibility certificates separately.
"""
from collections import Counter
from fractions import Fraction
from math import comb

ALPHABET = "AT"
L = 3
S = "AAATT"
D = "AAATA"
READ_STARTS = (0, 0, 1, 4)
N = len(S)

def reverse_complement(word: str) -> str:
    return word.translate(str.maketrans("AT", "TA"))[::-1]

def molecule_class(word: str) -> str:
    return min(word, reverse_complement(word))

def circular_windows(genome: str, read_len: int) -> list[str]:
    return ["".join(genome[(i + j) % len(genome)] for j in range(read_len))
            for i in range(len(genome))]

def spectrum(genome: str) -> Counter[str]:
    return Counter(map(molecule_class, circular_windows(genome, L)))

def full_binomial_score(x: Counter[str], d: Counter[str], n: int, N: int) -> Fraction:
    classes = {molecule_class("".join((a, b, c)))
               for a in ALPHABET for b in ALPHABET for c in ALPHABET}
    score = Fraction(1)
    for cls in classes:
        count = x[cls]
        copies = d[cls]
        assert 0 <= count <= n and 0 <= copies <= N
        p = Fraction(copies, N)
        score *= comb(n, count) * p**count * (1-p)**(n-count)
    return score

def exact_iid_score(x: Counter[str], d: Counter[str], N: int) -> Fraction:
    score = Fraction(1)
    for cls, count in x.items():
        score *= Fraction(d[cls], N)**count
    return score

def run() -> None:
    assert len(S) == len(D) == N == 5
    sample = [circular_windows(S, L)[i] for i in READ_STARTS]
    x = Counter(map(molecule_class, sample))
    ds, dd = spectrum(S), spectrum(D)
    assert x == Counter({"AAA": 2, "AAT": 1, "TAA": 1})
    assert ds == Counter({"AAA": 1, "AAT": 2, "TAA": 2})
    assert dd == Counter({"AAA": 2, "AAT": 1, "ATA": 1, "TAA": 1})
    assert sum(ds.values()) == sum(dd.values()) == 5
    assert sum(x.values()) == len(READ_STARTS) == 4

    # Walk with one skipped unobserved 3-molecule ATA.
    walk = ("AAA", "AAA", "AAT", "TAA")
    overlap = (2, 2, 1, 2)
    for u,v,l in zip(walk, walk[1:] + walk[:1], overlap):
        assert u[-l:] == v[:l], (u,v,l)
    assert sum(L-l for l in overlap) == N
    assert Counter(map(molecule_class, walk)) == (dd - Counter({"ATA":1}))

    truth = full_binomial_score(x, ds, len(sample), N)
    competitor = full_binomial_score(x, dd, len(sample), N)
    ratio = competitor / truth
    assert ratio == Fraction(65536, 50625)
    assert ratio > 1
    # If the unobserved ATA is wrongly assigned zero mass, the surrogate
    # gives the flow-only optimum that does NOT equal the candidate genome.
    truncated = Counter(dd)
    del truncated["ATA"]
    flow_ratio = full_binomial_score(x, truncated, len(sample), N) / truth
    assert flow_ratio == Fraction(256,81)
    assert ratio == flow_ratio * Fraction(4,5)**4

    true_iid = exact_iid_score(x, ds, N)
    decoy_iid = exact_iid_score(x, dd, N)
    assert decoy_iid / true_iid == 1
    assert ds != dd  # rotation/RC leave the molecule spectrum invariant
    print(f"truth={S}, decoy={D}, sample={sample}")
    print(f"observed={dict(x)}, true_spectrum={dict(ds)}, decoy_spectrum={dict(dd)}")
    print(f"binomial_full_ratio={ratio}; flow_truncated_ratio={flow_ratio}")
    print(f"iid_multinomial_ratio={decoy_iid / true_iid}")
    print("PASS: all exact-rational assertions")

if __name__ == "__main__":
    run()
