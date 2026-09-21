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
  G. Addendum section 9: PO vs FN0 for the five addendum witnesses (including
     the N2 correction); Lemma F1 bounded exhaustive check; FLOW support
     equality of S=AAB, D=AB; and the MOL collision AACAGT/AACTGT.
"""

from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product

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


def rc(w):
    return w.translate(str.maketrans("ACGT", "TGCA"))[::-1]


def mol_class(w):
    return min(w, rc(w))


def observed_counts(s, starts, L):
    n = len(s)
    d = {}
    for t in starts:
        w = "".join(s[(t + i) % n] for i in range(L))
        d[w] = d.get(w, 0) + 1
    return d


def rotate_min(w):
    return min(w[i:] + w[:i] for i in range(len(w)))


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

    # G1. Addendum section 9: PO vs FN0 (only AABBC->ABABC strict under both;
    #     AABBC->AABC, AABB->AAB and the FLOW witness AAB->AB are PO-only).
    cases = [
        ("N1 AABBC->AABC flag", "AABBC", "AABC", 3, {"AAB": 1, "BCA": 1},
         Fraction(25, 16), Fraction(1)),
        ("N2 AABB->AAB flag", "AABB", "AAB", 3, {"AAB": 1, "BAA": 1},
         Fraction(16, 9), Fraction(1)),
        ("FLOW AAB->AB flag", "AAB", "AB", 2, {"AB": 1, "BA": 1},
         Fraction(9, 4), Fraction(1)),
        ("N-R2 AABBC->ABABC fixed", "AABBC", "ABABC", 2, {"AB": 1, "BC": 1, "CA": 1},
         Fraction(2), Fraction(2)),
    ]
    for name, S, D, L, x, po, fn0 in cases:
        assert free_ratio(S, D, L, x) == po, (name, free_ratio(S, D, L, x))
        assert fixed_ratio(S, D, L, x) == fn0, (name, fixed_ratio(S, D, L, x))
        print(f"G1. {name}: PO={po} FN0={fn0}")

    # G2. FLOW support equality of the addendum witness S=AAB, D=AB, L=2.
    S, D, L, x = "AAB", "AB", 2, {"AB": 1, "BA": 1}
    assert set(spec(D, L)) == set(x) == set(spec(S, L)) - {"AA"}
    assert primitive(S) and primitive(D) and p2(S, L) and p1(D, L)
    print("G2. AAB->AB is support-equal FLOW; truth WEAK, candidate STRONG")

    # G3. Lemma F1 bounded exhaustive check: STRONG D with supp(obs) subset of
    #     supp(D) has FN0 ratio <= 1 for any realized read placement.
    f1_ok = True
    for L in (2, 3):
        for nD in range(L, 7):
            for dtup in product("AB", repeat=nD):
                D = "".join(dtup)
                if not p1(D, L):
                    continue
                suppD = set(spec(D, L))
                for G in range(L, 7):
                    for stup in product("ABC", repeat=G):
                        S = "".join(stup)
                        for N in (1, 2, 3):
                            for starts in combinations_with_replacement(range(G), min(N, G)):
                                obs = observed_counts(S, starts, L)
                                if not set(obs).issubset(suppD):
                                    continue
                                if fixed_ratio(S, D, L, obs) > 1:
                                    f1_ok = False
                                    print("  FAIL F1", S, D, starts, L)
    assert f1_ok
    print("G3. F1 exhaustive small check: pass (FN0 <= 1 for STRONG support-contained)")

    # G4. Molecule-panel boundary: primitive STRONG population collision.
    S, T, L = "AACAGT", "AACTGT", 3
    def mol_spec(w, L):
        d = {}
        for i in range(len(w)):
            c = mol_class("".join(w[(i + j) % len(w)] for j in range(L)))
            d[c] = d.get(c, 0) + 1
        return d
    assert primitive(S) and primitive(T)
    assert all(v <= 1 for v in spec(S, L - 1).values())
    assert all(v <= 1 for v in spec(T, L - 1).values())
    assert mol_spec(S, L) == mol_spec(T, L)
    assert rotate_min(S) != rotate_min(T)
    assert rotate_min(S) != rotate_min(rc(T))
    print("G4. AACAGT/AACTGT: primitive STRONG MOL collision, dihedrally inequivalent")

    print("ALL ASSERTIONS PASSED")


if __name__ == "__main__":
    main()
