#!/usr/bin/env python3
"""Exact one-extra covered-sample probe for binary L=8, G=N=9 spectra (#259).

Adjacent cell to the L=G=N=8 probe: for every realizable truth A (circular
binary genome length G=9, 8-mer spectrum over a 256-class universe), every
competitor B, and every supported coordinate i, the complete-support sample
x = A + 1_i (n = N+1 = 10) is checked against the literal MB09 section 6.1
fixed-external-N product-binomial integer numerator, including all x_e = 0
coordinates, and independently compared with the effective-weight product.
Also records the covered-uniform (pointwise q_e) decision for each pair.
Finite identity/evidence check only; no general theorem claimed.
"""

import itertools


def spectra(G, L):
    seen, result = set(), set()
    for word in itertools.product(range(2), repeat=G):
        if word in seen:
            continue
        seen.update(word[k:] + word[:k] for k in range(G))
        counts = [0] * (2 ** L)
        for i in range(G):
            edge = 0
            for t in range(L):
                edge = (edge << 1) | word[(i + t) % G]
            counts[edge] += 1
        result.add(tuple(counts))
    return sorted(result)


def literal_score(N, B, x):
    n = sum(x)
    value = 1
    for e in range(len(B)):
        value *= B[e] ** x[e] * (N - B[e]) ** (n - x[e])
    return value


def effective_weight(N, B, e):
    value = B[e]
    for j in range(len(B)):
        if j != e:
            value *= N - B[j]
    return value


def main():
    L, N = 8, 9
    candidates = spectra(N, L)
    assert len(candidates) > 0
    identities = 0
    samples = 0
    uniform_beats = 0
    uniform_losses = 0
    for A in candidates:
        support = [e for e, c in enumerate(A) if c]
        for B in candidates:
            qA = [effective_weight(N, A, e) for e in support]
            qB = [effective_weight(N, B, e) for e in support]
            if all(b <= a for a, b in zip(qA, qB)):
                uniform_beats += 1
            else:
                uniform_losses += 1
            for i in support:
                x = list(A)
                x[i] += 1
                x = tuple(x)
                assert sum(x) == N + 1
                assert all(v >= 1 for v, c in zip(x, A) if c)
                direct = literal_score(N, B, x)
                factored = 1
                for e, count in enumerate(x):
                    factored *= effective_weight(N, B, e) ** count
                assert direct == factored, (A, B, i)
                identities += 1
                samples += 1
    # Mutation control: omitting zero-count failure factors changes the score
    # on a small witness with an intermediate count at an unobserved type.
    A = (2, 1, 1, 0)
    B = (1, 1, 1, 1)
    x = list(A)
    x[next(e for e, c in enumerate(A) if c)] += 1
    x = tuple(x)
    mN = sum(A)
    full = literal_score(mN, B, x)
    omit = 1
    n = sum(x)
    for e in range(len(A)):
        omit *= B[e] ** x[e]
        if A[e] > 0:
            omit *= (mN - B[e]) ** (n - x[e])
    assert full != omit
    print(f"binary L=8 G=N=9 spectra={len(candidates)} universe=256")
    print(f"pairs={len(candidates)**2} uniform_beats={uniform_beats} uniform_losses={uniform_losses}")
    print(f"one-extra samples={samples} exact identities={identities}")
    print("mutation control: omitting zero-count failure factors changes score; OK")


if __name__ == "__main__":
    main()
