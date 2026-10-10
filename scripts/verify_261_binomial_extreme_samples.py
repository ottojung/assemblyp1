#!/usr/bin/env python3
"""Exact integer audit for #261 product-binomial fixed-support comparisons.

This checks count-vector identities only; it is not a proof that an abstract
vector is realizable by the historical reduced bidirected flow graph.
"""
from itertools import product
from math import prod
from collections import Counter

COMP = dict(zip("ACGT", "TGCA"))

def rc(w):
    return "".join(COMP[c] for c in reversed(w))

def molecules(s, length):
    return Counter(min(w, rc(w)) for w in
                   ("".join(s[(i + j) % len(s)] for j in range(length))
                    for i in range(len(s))))

def core(d, x, n_external):
    n = sum(x)
    return prod(d[i] ** x[i] * (n_external - d[i]) ** (n - x[i])
                for i in range(len(d)))

def q(d, n_external):
    return tuple(d[i] * prod(n_external - d[j] for j in range(len(d))
                             if j != i) for i in range(len(d)))

def q_core(d, x, n_external):
    z = q(d, n_external)
    return prod(z[i] ** x[i] for i in range(len(d)))

def supported_samples(types, support, n):
    for x in product(range(1, n + 1), repeat=len(support)):
        if sum(x) != n:
            continue
        y = [0] * types
        for i, v in zip(support, x):
            y[i] = v
        yield tuple(y)

def fixed_n_extreme_iff(a, b, n_external, n):
    support = tuple(i for i, v in enumerate(a) if v > 0)
    m = len(support)
    assert 1 <= m <= n
    qa, qb = q(a, n_external), q(b, n_external)
    pa, pb = prod(qa[i] for i in support), prod(qb[i] for i in support)
    extreme = all(pb * qb[i] ** (n - m) <= pa * qa[i] ** (n - m)
                  for i in support)
    brute = all(core(b, x, n_external) <= core(a, x, n_external)
                for x in supported_samples(len(a), support, n))
    return extreme, brute

def audit():
    identities = criteria = boundaries = 0
    for N in range(1, 6):
        for m in range(1, 5):
            for d in product(range(N + 1), repeat=m):
                for x in product(range(4), repeat=m):
                    assert core(d, x, N) == q_core(d, x, N), (N, d, x)
                    identities += 1
    for N in range(1, 6):
        for m in (2, 3):
            # True spectrum mass N; candidates may have zero or N counts.
            for a in product(range(N + 1), repeat=m):
                if sum(a) != N:
                    continue
                support = sum(v > 0 for v in a)
                for b in product(range(N + 1), repeat=m):
                    for n in range(support, support + 4):
                        e, brute = fixed_n_extreme_iff(a, b, N, n)
                        assert e == brute, (N, a, b, n, e, brute)
                        criteria += 1
                        if any(v in (0, N) for v in b):
                            boundaries += 1

    # Genuine (but variable-candidate-length) circular-genome pair.
    S, D, L = "ACA", "ACAACA", 2
    A, B = molecules(S, L), molecules(D, L)
    assert A == {"AA": 1, "AC": 1, "CA": 1}
    assert B == {"AA": 2, "AC": 2, "CA": 2}
    for counts in product(range(1, 6), repeat=3):
        a = core((1, 1, 1), counts, 3)
        b = core((2, 2, 2), counts, 3)
        assert a == 2 ** sum(counts) * b, counts

    # Boundary counterexample to an interior-only all-n criterion.
    a, b, N = (1, 1, 1), (0, 2, 2), 3
    assert q(b, N)[1] > q(a, N)[1]
    assert all(core(b, x, N) == 0 for x in product(range(1, 4), repeat=3))

    # Two longer overlaps do NOT imply equal spelling.
    direct = "AAAC" + "CAAA"[1:]
    via = "AAAC" + "ACCA"[2:] + "CAAA"[2:]
    assert (direct, via) == ("AAACAAA", "AAACCAAA")

    print(f"PASS {identities:,} exact binomial/q factorizations")
    print(f"PASS {criteria:,} finite-n extreme tests ({boundaries:,} boundary cases)")
    print("PASS 125 genuine circular competitor observations")
    print("PASS candidate-zero boundary and transitive-reduction regressions")

if __name__ == "__main__":
    audit()
