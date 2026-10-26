#!/usr/bin/env python3
"""Resolve the 8 covered-uniform q_e losses of the binary L=8 G=N=9 probe (#259).

Follow-up to scripts/verify_binary_L8_G9_one_extra_259.py, which reported
3600 ordered pairs with uniform_beats=3592 and uniform_losses=8 (pointwise
q_e comparison only, no beating claim). This script shows each of the 8
loss pairs resolves as truth-wins on every covered sample by an exact
zero-factor argument, so none is a sample-uniform beating witness:

  F_N(B,x) = prod_e B_e^x_e (N-B_e)^(n-x_e),  n = sum(x), N = 9.

For every loss pair (A,B): there is a killing coordinate k with A_k >= 1
and B_k = 0. Any covered sample x (x_e >= 1 for all e in supp(A)) then has
x_k >= 1 and hence F_N(B,x) = 0 exactly. Meanwhile F_N(A,x) > 0 on every
covered sample, because on supp(A) counts satisfy 1 <= A_e <= 8 < N = 9
(asserted), and off supp(A) both A_e = 0 and x_e = 0 contribute (N-0)^n.
Hence F_N(B,x) = 0 < F_N(A,x): A wins everywhere covered, including the
fixed-x sample x = A and every one-extra sample x = A + 1_i (checked
exactly as well). The pointwise q_e loss is a sufficient-only criterion:
it fires on a coordinate where B is strong while the exact likelihood is
killed by B's zero elsewhere in the covered support.

Finite exact-integer check; no general theorem claimed.
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
    assert len(candidates) == 60, len(candidates)
    losses = []
    for A in candidates:
        support = [e for e, c in enumerate(A) if c]
        for B in candidates:
            qA = [effective_weight(N, A, e) for e in support]
            qB = [effective_weight(N, B, e) for e in support]
            if all(b <= a for a, b in zip(qA, qB)):
                continue
            losses.append((A, B))
    # Cross-pin with the prior probe's reported counts.
    assert len(losses) == 8, len(losses)
    assert len(candidates) ** 2 == 3600

    for A, B in losses:
        support = [e for e, c in enumerate(A) if c]
        # Truth counts on support stay strictly below N, so F_N(A, x) > 0
        # on every covered sample (no zero base with positive exponent,
        # no zero failure factor on a positive-count coordinate).
        assert all(1 <= c <= N - 1 for c in A if c), [c for c in A if c]
        kills = [k for k in support if B[k] == 0]
        assert kills, "expected a zero-factor killing coordinate"
        # Fixed-x sample x = A is covered; B scores exactly 0 there.
        x0 = tuple(A)
        assert literal_score(N, B, x0) == 0
        assert literal_score(N, A, x0) > 0
        # Every one-extra sample x = A + 1_i is covered; B scores 0.
        for i in support:
            x = list(A)
            x[i] += 1
            x = tuple(x)
            assert literal_score(N, B, x) == 0, (A, B, i)
            assert literal_score(N, A, x) > 0, (A, B, i)
        # Structural cover-all: any covered x has x_k >= 1 at each killing
        # coordinate k, so F_N(B, x) = 0 < F_N(A, x) without enumeration.
        assert all(A[k] >= 1 for k in kills)

    # Mutation control: the zero conclusion depends on the boundary factors;
    # clamping every coordinate of the first loss-pair competitor away from
    # the 0/N boundary (0 -> 1, N -> N-1) makes the fixed-x B score positive.
    A, B = losses[0]
    B2 = tuple(min(max(b, 1), N - 1) for b in B)
    assert any(b2 != b for b2, b in zip(B2, B))
    assert literal_score(N, B2, tuple(A)) > 0
    assert literal_score(N, B, tuple(A)) == 0

    print(f"binary L=8 G=N=9 spectra={len(candidates)} pairs=3600")
    print(f"uniform losses={len(losses)}; all resolve: F_B==0 < F_A on x=A")
    print("and on every one-extra x=A+1_i; structural kill holds for all")
    print("covered x via supp(A)-not-subset-supp(B) coordinates.")
    print("mutation control: clamping B off the 0/N boundary makes F_B>0; OK")


if __name__ == "__main__":
    main()
