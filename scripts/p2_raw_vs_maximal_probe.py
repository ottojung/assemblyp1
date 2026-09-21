#!/usr/bin/env python3
"""Probe: can two repeated K-mers interleave as raw occurrences while their
*maximal* extensions fail to interleave (so P2/ILF passes)?  If so, does the
Euler tour become non-unique?"""
from collections import defaultdict
from itertools import combinations
from p2_eulerian_attack import (
    lyndon_words, is_primitive, has_interleaved, p2, spectrum_key, canonical,
)


def repeated_kmers(w, K):
    """dict kmer -> sorted occurrence list, for kmers occurring >= 2 times."""
    n = len(w)
    g = defaultdict(list)
    for i in range(n):
        g[tuple(w[(i + j) % n] for j in range(K))].append(i)
    return {k: v for k, v in g.items() if len(v) >= 2}


def raw_two_interleave(w, K):
    """Two distinct K-mers v,w each occurring >=2 times with interleaved
    occurrence sets (not necessarily maximal)."""
    reps = repeated_kmers(w, K)
    items = list(reps.items())
    for (v, av), (u, au) in combinations(items, 2):
        # every pair of occurrences, check alternation
        for a, b in combinations(av, 2):
            for c, d in combinations(au, 2):
                four = sorted({a, b, c, d})
                if len(four) != 4:
                    continue
                lab = [0 if p in (a, b) else 1 for p in four]
                if lab in ([0, 1, 0, 1], [1, 0, 1, 0]):
                    return (v, u, a, b, c, d)
    return None


def main():
    N = 18
    gap = 0
    examples = []
    for n in range(4, N + 1):
        for w in lyndon_words("AB", n):
            if not is_primitive(w):
                continue
            for L in range(2, n + 1):
                K = L - 1
                r = raw_two_interleave(w, K)
                if r is None:
                    continue
                # raw interleave exists; does maximal ILF also catch it?
                if not has_interleaved(w, K):
                    gap += 1
                    examples.append((w, L, r))
    print(f"primitive binary n<={N}: raw-two-K-mer-interleave but NOT maximal "
          f"interleaving: {gap}")
    for e in examples[:20]:
        w, L, r = e
        print("  ", w, "L=", L, "raw=", r, "p2=", p2(w, L))
    # Also: how often does raw interleave occur when P2 holds?
    both = 0
    only_raw = 0
    for n in range(4, N + 1):
        for w in lyndon_words("AB", n):
            if not is_primitive(w):
                continue
            for L in range(2, n + 1):
                K = L - 1
                r = raw_two_interleave(w, K)
                if r is None:
                    continue
                if p2(w, L):
                    only_raw += 1
    print("P2 words with raw two-K-mer interleaving (n<=18):", only_raw)


if __name__ == "__main__":
    main()
