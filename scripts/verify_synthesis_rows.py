#!/usr/bin/env python3
"""Independent verifier for docs/synthesis-finite-rows-and-repairs-2026-09-21.md.

Exact integer / fractions.Fraction arithmetic, deterministic, no repository
imports. Exits non-zero on any failed assertion.

Checks:
  A. Fact 2: AABAB is P2-admissible (I_s shadow) but not P1 (STRONG).
  B. Section 2.3: AABABB and AABBAB share an L=3 spectrum (tie) but are not
     cyclic shifts, and both are P2-inadmissible via an interleaved pair.
  C. N-R1: S=AABBC, D=AABC, L=3, x={AAB,BCA} has free-length exact ratio 25/16
     and population value 0.
  D. N-R2: S=AABBC, D=ABABC, L=2, x={AB,BC,CA} has fixed-length ratio 2.
  E. N-R3: S=AAATT, D=AAAATT, L=3, x=spec_3(S)+e_AAA has free-length ratio
     15625/11664 and population value 3125/3888.
  F. No cross-length proportional-spectrum collisions and no same-length
     same-spectrum collisions among primitive P2 words in the tested scopes.
"""

from fractions import Fraction
from itertools import combinations, product

BASE = ("A", "B", "C", "D")


def canonical(s):
    return min(s[i:] + s[:i] for i in range(len(s)))


def primitive(s):
    n = len(s)
    return not any(n % p == 0 and s == s[:p] * (n // p) for p in range(1, n))


def spec(s, L):
    n = len(s)
    d = {}
    for t in range(n):
        w = "".join(s[(t + i) % n] for i in range(L))
        d[w] = d.get(w, 0) + 1
    return d


def p1(s, L):
    if L - 1 < 1:
        return True
    return all(v <= 1 for v in spec(s, L - 1).values())


def maximal_pairs(s, ell):
    n = len(s)
    occ = {}
    for t in range(n):
        occ.setdefault("".join(s[(t + i) % n] for i in range(ell)), []).append(t)
    out = []
    for ts in occ.values():
        for a, b in combinations(ts, 2):
            if s[(a - 1) % n] != s[(b - 1) % n] and s[(a + ell) % n] != s[(b + ell) % n]:
                out.append((a, b, ell))
    return out


def triples(s, ell):
    n = len(s)
    occ = {}
    for t in range(n):
        occ.setdefault("".join(s[(t + i) % n] for i in range(ell)), []).append(t)
    res = []
    for ts in occ.values():
        for g in combinations(ts, 3):
            if len({s[(t - 1) % n] for t in g}) >= 2 and len({s[(t + ell) % n] for t in g}) >= 2:
                res.append(g)
    return res


def interleaved(s):
    n = len(s)
    allp = []
    for ell in range(1, n):
        allp += maximal_pairs(s, ell)
    res = []
    for i in range(len(allp)):
        a, b, ll = allp[i]
        for j in range(i + 1, len(allp)):
            c, d, mm = allp[j]
            ts = sorted([a, b, c, d])
            if len(set(ts)) < 4:
                continue
            if ({a, b} == {ts[0], ts[2]} and {c, d} == {ts[1], ts[3]}) or (
                {c, d} == {ts[0], ts[2]} and {a, b} == {ts[1], ts[3]}
            ):
                res.append((ll, mm))
    return res


def p2(s, L):
    """The I_s shadow (WEAK): no long triple repeat, no long interleaved pair."""
    n = len(s)
    for ell in range(L - 1, n):
        if triples(s, ell):
            return False
    for ll, mm in interleaved(s):
        if ll >= L - 1 and mm >= L - 1:
            return False
    return True


def words(sigma, n):
    seen = set()
    for tup in product(sigma, repeat=n):
        s = "".join(tup)
        c = canonical(s)
        if c in seen:
            continue
        seen.add(c)
        yield c


def free_ratio(S, D, L, x):
    """Exact free-length multinomial ratio, 0 if a candidate omits an observed type."""
    G, n = len(S), len(D)
    dS, dD = spec(S, L), spec(D, L)
    r = Fraction(1)
    for w, c in x.items():
        if dD.get(w, 0) == 0:
            return Fraction(0)
        r *= Fraction(G * dD[w], n * dS[w]) ** c
    return r


def fixed_ratio(S, D, L, x):
    """Exact fixed-length multinomial ratio, 0 if a candidate omits an observed type."""
    dS, dD = spec(S, L), spec(D, L)
    r = Fraction(1)
    for w, c in x.items():
        if dD.get(w, 0) == 0:
            return Fraction(0)
        r *= Fraction(dD[w], dS[w]) ** c
    return r


def main():
    # A. Fact 2
    assert p2("AABAB", 3) and not p1("AABAB", 3)
    print("A. AABAB is P2-admissible but not P1 (P1 does not follow from I_s)")

    # B. spectrum tie but not word-unique
    s1, s2 = "AABABB", "AABBAB"
    assert spec(s1, 3) == spec(s2, 3)
    assert canonical(s1) != canonical(s2)
    assert not p2(s1, 3) and not p2(s2, 3)
    print("B. AABABB/AABBAB: equal L=3 spectrum, non-rotation, P2-inadmissible")

    # C. N-R1 free-length, P1, finite vs population
    S, D, L, x = "AABBC", "AABC", 3, {"AAB": 1, "BCA": 1}
    assert primitive(S) and primitive(D) and p1(S, L) and p1(D, L)
    assert free_ratio(S, D, L, x) == Fraction(25, 16)
    assert free_ratio(S, D, L, spec(S, L)) == 0
    print("C. N-R1 finite ratio 25/16; population ratio 0")

    # D. N-R2 fixed-length, P2, sequence-level
    S, D, L, x = "AABBC", "ABABC", 2, {"AB": 1, "BC": 1, "CA": 1}
    assert primitive(S) and primitive(D) and p2(S, L) and p2(D, L)
    assert fixed_ratio(S, D, L, x) == 2
    print("D. N-R2 fixed-length ratio 2 (both P2, sequence-level)")

    # E. N-R3 FLOW free-length
    S, D, L = "AAATT", "AAAATT", 3
    x = dict(spec(S, L))
    x["AAA"] += 1
    assert set(spec(S, L)) == set(spec(D, L)) == set(x)
    assert free_ratio(S, D, L, x) == Fraction(15625, 11664)
    assert free_ratio(S, D, L, spec(S, L)) == Fraction(3125, 3888)
    print("E. N-R3 finite ratio 15625/11664; population ratio 3125/3888")

    # F. proportional / same-spectrum collisions among primitive P2 words
    for sigma, gmax in (("AB", 12), ("ABC", 7)):
        for L in range(2, 5):
            groups = {}
            for n in range(L, gmax + 1):
                for w in words(sigma, n):
                    if not (primitive(w) and p2(w, L)):
                        continue
                    key = tuple(sorted((k, Fraction(v, n)) for k, v in spec(w, L).items()))
                    groups.setdefault(key, []).append((n, w))
            cross = [v for v in groups.values() if len({n for n, _ in v}) > 1]
            same = [v for v in groups.values() if len(v) > 1 and len({n for n, _ in v}) == 1]
            assert not cross, (sigma, L, cross[:2])
            assert not same, (sigma, L, same[:2])
            total = sum(len(v) for v in groups.values())
            print(f"F. sigma={sigma} L={L}: {total} primitive P2 words, 0 collisions")

    print("ALL ASSERTIONS PASSED")


if __name__ == "__main__":
    main()
