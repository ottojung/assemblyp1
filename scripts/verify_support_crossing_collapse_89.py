#!/usr/bin/env python3
"""Search for the *collapse* regime of the #89 support-permutation route (#89).

Setup, as in `scripts/verify_support_chord_dichotomy_89.py`: a word `S` of
length `G`, read length `L` (`K = L - 1`), and the support-permutation
dichotomy of `AssemblyP1.BBTSupportChords`:

    f != id  ==>  (W) some label occurs at three distinct positions
                or (X) two doubled pairs whose four endpoints interleave.

Read at the *real* objects of the Eulerian setting (`W = vtx`, so a "label" is
a `(L-1)`-mer and a "doubled pair" is a pair of starts spelling the same
`(L-1)`-mer), clause (W) is a triple of starts spelling the same
`(L-1)`-mer, and clause (X) is two *doubled* `(L-1)`-mer pairs that
interleave.

This script tests the naive attempt at Lemma 2 of
`AssemblyP1.BBTUniqueEulerian`, namely

    (X)  ==>  (T) a maximal triple repeat of length >= K
          or  (I) two interleaved maximal repeats, both of length >= K,

i.e. whether clause (X) alone forces the second clause of
`AssemblyP1.P2.P2`.  It is **false**, and every row printed below is a
counterexample; the smallest is `S = 1101010`, `G = 7`, `K = 4`, which is the
kernel-checked instance `AssemblyP1.BBTSupportCrossing.S7`.

Usage:  python3 scripts/verify_support_crossing_collapse_89.py [Gmax] [alphabet]
"""

import sys
from itertools import product


def win(S, e, r):
    G = len(S)
    return tuple(S[(r + i) % G] for i in range(e))


def prec(S, t):
    return S[(t - 1) % len(S)]


def foll(S, e, t):
    return S[(t + e) % len(S)]


def is_repeat(S, e, a, b):
    G = len(S)
    return (1 <= e < G and a != b and win(S, e, a) == win(S, e, b)
            and prec(S, a) != prec(S, b) and foll(S, e, a) != foll(S, e, b))


def is_triple(S, e, a, b, c):
    G = len(S)
    if not (1 <= e < G and a != b and a != c and b != c):
        return False
    if win(S, e, a) != win(S, e, b) or win(S, e, a) != win(S, e, c):
        return False
    if prec(S, a) == prec(S, b) == prec(S, c):
        return False
    if foll(S, e, a) == foll(S, e, b) == foll(S, e, c):
        return False
    return True


def in_arc(G, a, b, p):
    return 0 < (p - a) % G < (b - a) % G


def interleaved(G, a, b, c, d):
    return (a != b and a != c and a != d and b != c and b != d and c != d
            and in_arc(G, a, b, c) != in_arc(G, a, b, d))


def has_triple(S, K):
    G = len(S)
    return any(is_triple(S, e, a, b, c)
               for e in range(K, G) for a in range(G) for b in range(G)
               for c in range(G))


def has_interleaved_maximal_pair(S, K):
    G = len(S)
    reps = [(a, b) for e in range(K, G) for a in range(G) for b in range(G)
            if is_repeat(S, e, a, b)]
    return any(interleaved(G, a, b, c, d)
               for (a, b) in reps for (c, d) in reps)


def is_primitive(S):
    G = len(S)
    for p in range(1, G):
        if all(S[i] == S[(i + p) % G] for i in range(G)):
            return False
    return True


def crossed_doubled_pairs(S, K):
    G = len(S)
    W = [win(S, K, i) for i in range(G)]
    pairs = [(a, b) for a in range(G) for b in range(G) if a != b and W[a] == W[b]]
    return [(a, b, c, d) for (a, b) in pairs for (c, d) in pairs
            if interleaved(G, a, b, c, d)]


def max_repeat_at(S, a, b):
    G = len(S)
    for e in range(1, G):
        if is_repeat(S, e, a, b):
            return e
    return None


def main():
    Gmax = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    q = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    ncase = 0
    bad = []
    for G in range(1, Gmax + 1):
        for S in product(range(q), repeat=G):
            S = list(S)
            if not is_primitive(S):
                continue
            for K in range(1, G + 1):
                cr = crossed_doubled_pairs(S, K)
                if not cr:
                    continue
                ncase += 1
                if has_triple(S, K) or has_interleaved_maximal_pair(S, K):
                    continue
                # the pairs coalesce: no maximal repeat at the second pair's
                # own starts, and the first pair carries the whole repeat
                mr = [max_repeat_at(S, a, b) for (a, b, c, d) in cr[:1]]
                bad.append((''.join(map(str, S)), G, K, cr[0], mr[0]))
                if len(bad) <= 3:
                    print("counterexample S=%s G=%d K=%d first crossing pair=%s "
                          "maximal repeat length at that pair=%s"
                          % (''.join(map(str, S)), G, K, cr[0], mr[0]))
                    sys.stdout.flush()
        print("G=%2d: crossing cases so far %d, counterexamples %d"
              % (G, ncase, len(bad)))
        sys.stdout.flush()
    print("total crossing cases: %d, counterexamples to the naive crossing "
          "clause: %d" % (ncase, len(bad)))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
