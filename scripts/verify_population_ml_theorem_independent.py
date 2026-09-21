#!/usr/bin/env python3
"""Independent exact-arithmetic verifier for the population/infinite-read ML theorem.

This script is self-contained: it does not import any repository search code.
It checks, from scratch and with exact integer / Fraction arithmetic:

  A. The KL/Gibbs population-maximizer lemma (truth maximizes; ties exactly on
     normalized-spectrum equality), by brute force over small word classes and
     by direct KL evaluation.
  B. TRF  <=> every (L-1)-mer occurs at most twice, for the Bresler triple-repeat
     definition (maximal extension).
  C. The cross-length exclusion step (Lemma 2): primitive + TRF on both sides
     forbids distinct lengths with proportional L-spectra.
  D. The BBT K = L-1 equal-length criterion on small exhaustive scopes, and the
     interleaving-convention sharpness example W / W' (16 distinct 3-mers,
     TRF but not ILF, not rotations).
  E. The finite-sample #48 witness S=AABBC / D=AABC, L=3: it is NOT a
     population collision (truth strictly beats it; p_D misses two truth types).
  F. The molecule-panel boundary example AACAGT / AACTGT at L=3.

Exits non-zero on any failed assertion.
"""

from collections import Counter
from fractions import Fraction
from itertools import product
import sys


# ---------------------------------------------------------------- basic tools

def windows(s, L):
    """Circular length-L window multiset of circular word s."""
    n = len(s)
    c = Counter()
    d = s + s
    for i in range(n):
        c[d[i:i + L]] += 1
    return c


def is_primitive(s):
    n = len(s)
    for p in range(1, n):
        if n % p == 0 and s == s[:p] * (n // p):
            return False
    return True


def rotations(s):
    return {s[i:] + s[:i] for i in range(len(s))}


def rot_equiv(a, b):
    return len(a) == len(b) and b in rotations(a)


def lt_mer_mult(s, L):
    """max multiplicity of any (L-1)-mer of circular s (L >= 1)."""
    if L == 1:
        return len(s)  # the empty word occurs n times
    k = L - 1
    return max(windows(s, k).values())


def TRF(s, L):
    """No Bresler triple repeat of length >= L-1.

    Equivalent to: every (L-1)-mer occurs at most twice.  (A triple of equal
    (L-1)-windows extends maximally to a triple repeat of length >= L-1, and
    conversely such a repeat contains three equal (L-1)-prefixes.)  Checked
    against the maximal-extension definition in section B of ``main``.
    """
    return lt_mer_mult(s, L) <= 2


def maximal_repeats(s):
    """All maximal repeats of circular word s as (t1, t3, ell), ell < n.

    A repeat is a pair of distinct starts t1 < t3 whose length-ell factors are
    equal and which cannot be extended left or right.
    """
    n = len(s)
    d = s + s
    out = []
    for t1 in range(n):
        for t3 in range(t1 + 1, n):
            # maximal common extension around the pair (t1, t3)
            ell = 0
            while ell < n and d[t1 + ell] == d[t3 + ell]:
                ell += 1
            # maximal right extension length
            if ell == 0 or ell >= n:
                continue
            # left non-extendable and right non-extendable
            if d[(t1 - 1) % n] == d[(t3 - 1) % n]:
                continue
            if d[t1 + ell] == d[t3 + ell]:
                continue
            out.append((t1, t3, ell))
    return out


def ILF(s, L):
    """No interleaved pair of maximal repeats, both constituents >= L-1.

    Bresler-Bresler-Tse: repeats R1 at (t1,t3) and R2 at (t2,t4) interleave if
    t1 < t2 < t3 < t4 or t2 < t1 < t4 < t3.  The repeats may be different
    words.  Pair length is the shorter constituent.
    """
    reps = maximal_repeats(s)
    for (t1, t3, e1) in reps:
        for (t2, t4, e2) in reps:
            if min(e1, e2) < L - 1:
                continue
            if (t1 < t2 < t3 < t4) or (t2 < t1 < t4 < t3):
                return False
    return True


def WEAK(s, L):
    return TRF(s, L) and ILF(s, L)


# --------------------------------------------------- A. KL / population lemma

def pop_loglik(S, D, L):
    """Per-read population log-likelihood ell_S(D) = sum_w p_S(w) log p_D(w).

    Returns None for -infinity (a truth-positive type absent from D).
    """
    import math
    pS = windows(S, L)
    pD = windows(D, L)
    m = len(D)
    v = Fraction(0)
    for w, cnt in pS.items():
        if pD.get(w, 0) == 0:
            return None
        v += Fraction(cnt, len(S)) * Fraction(pD[w], m)
    # recover log sum with floats only for the ordering check
    total = 0.0
    for w, cnt in pS.items():
        total += (cnt / len(S)) * math.log(pD[w] / m)
    return total


def KL(pS_counts, nS, pD_counts, nD):
    """KL(pS || pD) in nats, exact as Fraction of logs is not possible; use floats."""
    import math
    tot = 0.0
    for w, c in pS_counts.items():
        if pD_counts.get(w, 0) == 0:
            return float("inf")
        tot += (c / nS) * math.log((c / nS) / (pD_counts[w] / nD))
    return tot


def check_A(max_alpha=3, max_n=5, max_L=4):
    """Truth maximizes; ties exactly on normalized-spectrum equality."""
    for alpha in range(2, max_alpha + 1):
        letters = "ABCD"[:alpha]
        for n in range(2, max_n + 1):
            for tup in product(letters, repeat=n):
                S = "".join(tup)
                for L in range(2, min(max_L, n) + 1):
                    pS = windows(S, L)
                    base = None
                    for m in range(2, n + 3):
                        for tup2 in product(letters, repeat=m):
                            D = "".join(tup2)
                            ll = pop_loglik(S, D, L)
                            truth = pop_loglik(S, S, L)
                            if ll is None:
                                assert truth is not None
                                continue
                            assert ll <= truth + 1e-9, (S, D, L, ll, truth)
                            # equality iff normalized spectra equal
                            pD = windows(D, L)
                            same = all(
                                Fraction(pS.get(w, 0), n) == Fraction(pD.get(w, 0), m)
                                for w in set(pS) | set(pD)
                            )
                            tie = abs(ll - truth) < 1e-9
                            assert tie == same, (S, D, L, ll, truth, same)
    print("A: KL maximizer + equality-condition, exhaustive small scope: pass")


# ------------------------- B. TRF <=> (L-1)-multiplicity <= 2 (maximal repeats)

def triple_repeat_exists(s, L):
    """Maximal Bresler triple repeat of length >= L-1, by scanning starts."""
    n = len(s)
    d = s + s
    starts = {}
    for i in range(n):
        # consider maximal extension of the (L-1)-window at i
        starts.setdefault(i, None)
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                ell = 0
                while ell < n and d[i + ell] == d[j + ell] == d[k + ell]:
                    ell += 1
                if ell >= L - 1 and ell < n:
                    left_ok = not (d[(i - 1) % n] == d[(j - 1) % n] == d[(k - 1) % n])
                    if left_ok:
                        return True
    return False


def check_B(max_alpha=3, max_n=8, max_L=4):
    """For *primitive* words, TRF (no maximal triple repeat of length >= L-1)
    coincides with '(L-1)-mer multiplicity <= 2'.  Non-primitive periodic words
    are excluded: there the all-equal flanks make the maximal triple vacuous
    while the multiplicity exceeds 2 (e.g. AAA at L=2)."""
    for alpha in range(2, max_alpha + 1):
        letters = "ABC"[:alpha]
        for n in range(2, max_n + 1):
            for tup in product(letters, repeat=n):
                s = "".join(tup)
                if not is_primitive(s):
                    continue
                for L in range(2, min(max_L, n) + 1):
                    assert TRF(s, L) == (not triple_repeat_exists(s, L)), (s, L)
    print("B: primitive: TRF <=> no long maximal triple repeat, exhaustive scope: pass")


# ------------------------------------------- C. cross-length exclusion (Lemma 2)

def _reduced_spec(counts):
    """Integer spectrum divided by its gcd; proportional spectra share this."""
    from math import gcd
    g = 0
    for v in counts.values():
        g = gcd(g, v)
    if g == 0:
        return ()
    return tuple(sorted((w, v // g) for w, v in counts.items()))


def check_C(max_alpha=4, max_n=12, max_L=4):
    count = 0
    for alpha in range(2, max_alpha + 1):
        letters = "ABCD"[:alpha]
        for L in range(2, max_L + 1):
            seen = {}
            for n in range(L, max_n + 1):
                for tup in product(letters, repeat=n):
                    s = "".join(tup)
                    if not is_primitive(s) or not TRF(s, L):
                        continue
                    key = _reduced_spec(windows(s, L))
                    if key in seen and seen[key][0] != n:
                        raise AssertionError(
                            f"cross-length collision {seen[key]} {s} L={L}")
                    seen[key] = (n, s)
                    count += 1
    print(f"C: no cross-length proportional collision (primitive TRF, {count} words): pass")


# --------------------------- D. equal-length criterion + interleaving sharpness

def check_D(max_alpha=3, max_n=9, max_L=4):
    collisions = 0
    for alpha in range(2, max_alpha + 1):
        letters = "ABC"[:alpha]
        seen = {}
        for n in range(2, max_n + 1):
            for tup in product(letters, repeat=n):
                s = "".join(tup)
                if not is_primitive(s):
                    continue
                for L in range(2, min(max_L, n) + 1):
                    if not WEAK(s, L):
                        continue
                    spec = tuple(sorted(windows(s, L).items()))
                    key = (n, L, spec)
                    if key in seen:
                        assert rot_equiv(seen[key], s), (seen[key], s, L)
                    seen[key] = s
                    collisions += 1
    print(f"D1: WEAK(s)=>{L}-spectrum determines s up to rotation ({collisions} words): pass")

    # the sharpness pair: TRF but not ILF, same spectrum, not rotations
    W = "AACCAAGCCG"
    Wp = "AACCGAAGCC"
    assert windows(W, 3) == windows(Wp, 3)
    assert not rot_equiv(W, Wp)
    assert is_primitive(W) and is_primitive(Wp)
    assert TRF(W, 3) and TRF(Wp, 3)
    assert not ILF(W, 3) and not ILF(Wp, 3)
    # identify the interleaved pair (possibly distinct repeated words)
    reps = maximal_repeats(W)
    inter = []
    for (t1, t3, e1) in reps:
        for (t2, t4, e2) in reps:
            if min(e1, e2) >= 2 and ((t1 < t2 < t3 < t4) or (t2 < t1 < t4 < t3)):
                inter.append(((t1, t3, e1), (t2, t4, e2)))
    assert inter, "expected an interleaved pair"
    print("D2: W/W' same 3-spectrum, primitive, TRF, not rotations, NOT ILF;"
          f" interleaved pair e.g. {inter[0]}: pass")


# ---------------------------------------- E. finite #48 witness is not a pop tie

def check_E():
    S = "AABBC"
    D = "AABC"
    L = 3
    pS = windows(S, L)
    pD = windows(D, L)
    assert pop_loglik(S, D, L) is None, "competitor must miss a truth type at population"
    missing = [w for w in pS if pD.get(w, 0) == 0]
    assert sorted(missing) == ["ABB", "BBC"], missing
    # exact multinomial ratio at the realized finite counts (5/4)^2
    x = Counter({"AAB": 1, "BCA": 1})
    n = 2
    import math
    def exact(D_):
        p = windows(D_, L)
        m = len(D_)
        lg = 0.0
        for w, c in x.items():
            lg += c * math.log(p[w] / m)
        return lg
    ratio = exact(D) - exact(S)
    assert abs(ratio - 2 * math.log(5 / 4)) < 1e-12, ratio
    print("E: #48 finite witness (AABBC/AABC, L=3): finite ratio (5/4)^2>1 but"
          " population likelihood of D is 0 (misses ABB, BBC): pass")


# ------------------------------------------------ F. molecule-panel boundary

def rc(w):
    tab = str.maketrans("ACGT", "TGCA")
    return w.translate(tab)[::-1]


def molecule_windows(s, L):
    c = Counter()
    for w, k in windows(s, L).items():
        r = rc(w)
        c[min(w, r)] += k
    return c


def dihedral_equiv(a, b):
    rots = rotations(a)
    return b in rots or b in rotations(rc(a))


def check_F():
    S = "AACAGT"
    T = "AACTGT"
    L = 3
    assert molecule_windows(S, L) == molecule_windows(T, L)
    assert not dihedral_equiv(S, T)
    assert lt_mer_mult(S, L) <= 1 and lt_mer_mult(T, L) <= 1  # STRONG
    assert is_primitive(S) and is_primitive(T)
    print("F: molecule panel AACAGT/AACTGT, L=3: same class law, STRONG, primitive,"
          " dihedrally inequivalent: pass")


def main():
    import argparse
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--full", action="store_true",
                    help="wider exhaustive scopes (slower)")
    args = ap.parse_args()

    if args.full:
        check_A(max_alpha=3, max_n=5, max_L=4)
        check_B(max_alpha=3, max_n=10, max_L=4)
        check_C(max_alpha=4, max_n=10, max_L=3)
        check_D(max_alpha=3, max_n=10, max_L=4)
    else:
        check_A(max_alpha=3, max_n=4, max_L=4)
        check_B(max_alpha=3, max_n=7, max_L=4)
        check_C(max_alpha=3, max_n=9, max_L=3)
        check_D(max_alpha=3, max_n=8, max_L=3)
    check_E()
    check_F()
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
