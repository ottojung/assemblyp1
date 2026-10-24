#!/usr/bin/env python3
"""Exact bounded ternary L=3 transfer-gap census for issue #259.

Candidates are circular words over {0,1,2}; their spectra are length-3
window-count vectors.  The sample space for likelihood comparisons is every
integral x >= A on supp(A), with N=G, by the covered-sample criterion.
This is a finite census, not a general theorem.  All comparisons use Python
integers/Fractions; no floating point is used.
"""
from __future__ import annotations

import itertools
import sys
from collections import defaultdict
from fractions import Fraction


def necklaces(g: int):
    seen = set()
    for word in itertools.product(range(3), repeat=g):
        if word in seen:
            continue
        seen.update(word[k:] + word[:k] for k in range(g))
        yield word


def spectra(g: int, universe: list[tuple[int, ...]]):
    result = {}
    for word in necklaces(g):
        counts = defaultdict(int)
        for i in range(g):
            counts[tuple(word[(i + j) % g] for j in range(3))] += 1
        result.setdefault(tuple(counts[w] for w in universe), word)
    return result


def support(a):
    return [i for i, v in enumerate(a) if v]


def q(n, a, i):
    """N-scaled product-binomial effective factor, omitting common N^-m."""
    value = a[i]
    for j, other in enumerate(a):
        if j != i:
            value *= n - other
    return value


def beats(n, a, b):
    # Exact covered-sample iff: one supported effective factor increases,
    # and none of the truth-support factors of B vanishes.
    return all(q(n, b, i) > 0 for i in support(a)) and any(
        q(n, b, i) > q(n, a, i) for i in support(a))


def full_max(a):
    return len(support(a)) == 1 or max(a) <= 1


def balance(universe, a):
    b = defaultdict(int)
    for w, count in zip(universe, a):
        b[w[:-1]] += count
        b[w[1:]] -= count
    return all(v == 0 for v in b.values())


def endpoint_condition(iword, jword):
    return sorted((iword[:-1], jword[1:])) == sorted((jword[:-1], iword[1:]))


def transfer_checks(universe, all_spectra):
    checked = preserved = 0
    for a in all_spectra:
        assert balance(universe, a)
        s = support(a)
        for j in s:
            if a[j] < 2:
                continue
            for i in s:
                if i == j:
                    continue
                b = list(a)
                b[j] -= 1
                b[i] += 1
                actual = balance(universe, b)
                predicted = endpoint_condition(universe[i], universe[j])
                assert actual == predicted, (a, i, j, b, actual, predicted)
                checked += 1
                preserved += actual
    return checked, preserved


def flood(n, a, b):
    i = next(i for i in support(a) if q(n, b, i) > q(n, a, i))
    x = list(a)
    base = Fraction(1)
    for j in support(a):
        if j != i:
            base *= Fraction(q(n, b, j), q(n, a, j)) ** a[j]
    r = Fraction(q(n, b, i), q(n, a, i))
    while base * r ** x[i] <= 1:
        x[i] += 1
    return tuple(x), i


def likelihood(N, n, d, x):
    """Exact product-binomial objective, with common binomial coefficients omitted."""
    value = Fraction(1)
    for count, copies in zip(x, d):
        value *= Fraction(copies, N) ** count
        value *= Fraction(N - copies, N) ** (n - count)
    return value


def census(g, universe):
    by_spec = spectra(g, universe)
    rows = sorted(by_spec.items())
    all_keys = {a for a, _ in rows}
    counts = dict(both_max=0, both_beaten=0, gap=0, skipped=0)
    smallest = None
    for a, word in rows:
        if any(q(g, a, i) == 0 for i in support(a)):
            counts["skipped"] += 1
            continue
        fmax = full_max(a)
        real_max = not any(b != a and beats(g, a, b) for b in all_keys)
        if fmax and real_max:
            counts["both_max"] += 1
        elif not fmax and not real_max:
            counts["both_beaten"] += 1
        elif not fmax and real_max:
            counts["gap"] += 1
            if smallest is None:
                candidates = []
                for j in support(a):
                    if a[j] >= 2:
                        for i in support(a):
                            if i != j:
                                b = list(a)
                                b[j] -= 1
                                b[i] += 1
                                if beats(g, a, b):
                                    candidates.append(tuple(b))
                if not candidates:
                    raise AssertionError(f"no full-class transfer for gap truth {a}")
                b = min(candidates)
                assert not balance(universe, b) and b not in all_keys
                x, i = flood(g, a, b)
                assert all(x[k] >= a[k] for k in support(a))
                n = sum(x)
                fa, fb = likelihood(g, n, a, x), likelihood(g, n, b, x)
                assert fb > fa
                smallest = (a, word, b, x, i, fb, fa)
        else:
            raise AssertionError(f"full-max truth beaten by realizable candidate: {a}")
    return counts, by_spec, smallest


def main():
    universe = list(itertools.product(range(3), repeat=3))
    totals = dict(both_max=0, both_beaten=0, gap=0, skipped=0)
    tchecks = tpreserved = spectra_count = 0
    witness = None
    per_length = {}
    # L=3 has 27 coordinates. G<=7 gives a bounded, reproducible census;
    # longer lengths and all alphabets >=4 are explicitly left open.
    for g in range(3, 8):
        c, by_spec, w = census(g, universe)
        per_length[g] = c
        spectra_count += len(by_spec)
        tc, tp = transfer_checks(universe, by_spec)
        tchecks += tc
        tpreserved += tp
        for key in totals:
            totals[key] += c[key]
        if witness is None and w is not None:
            witness = (g, w)
    assert witness is not None
    g, (a, word, b, x, i, lhs, rhs) = witness
    # Independent formula for the full objective, with n=sum(x)=6 and N=G=4.
    n = sum(x)
    assert g == 4 and n == 6
    assert likelihood(g, n, a, x) == Fraction(1, 4096)
    assert likelihood(g, n, b, x) / likelihood(g, n, a, x) == Fraction(6561, 4096)
    print("verify_ternary_L3_transfer_gap_259.py")
    print(f"  ternary L=3, G=3..7: {spectra_count} distinct necklace spectra")
    print(f"  transfer-balance: {tchecks} one-unit transfers; {tpreserved} preserve; 0 mismatches")
    print("  per-G census: " + "; ".join(
        f"G={g0} {v}" for g0, v in per_length.items()))
    print(f"  total census: {totals}")
    print(f"  smallest gap: G={g}, A={a}, word={''.join(map(str, word))}, "
          f"B={b}, x={x}, flood-coordinate={universe[i]}, "
          f"F_B/F_A={lhs / rhs} (>1)")
    print(f"  exact product cross-check (n={n}): F_B/F_A=6561/4096; B is unbalanced and non-realizable")
    print("verify_ternary_L3_transfer_gap_259: ALL OK")


if __name__ == "__main__":
    sys.exit(main())
