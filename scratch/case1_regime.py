#!/usr/bin/env python3
"""CASE 1: the two OPEN REGIMES of the residual, with the Lean's exact
`BackAgrees` index semantics.

    BackAgrees S x y q  ==  forall d < q, S[(x-d-1) mod G] == S[(y-d-1) mod G]
    (the q positions STRICTLY PRECEDING x and y; so p is the number of
    agreeing preceding positions and the pair steps back to (x-p, y-p))

Everything else is transcribed from the Lean sources:
  vtx(S,L,i)           = (S[i+k] for k < L-1)
  Preceding(S,i)       = S[i-1]
  IsRepeat(e,a,b)      = 1<=e<G, a!=b, agree e, prec differ, foll differ
  IsTripleRepeat       = 1<=e<G, 3 distinct, pairwise agree, precs not all
                         equal, folls not all equal
  InOpenArc(a,b,p)     = 0 < (p-a)%G < (b-a)%G
  Interleaved(a,b,c,d) = four distinct and (c in arc) != (d in arc)
  LongObstruction(L)   = maximal triple repeat of length >= L-1, or two
                         interleaved maximal repeats both of length >= L-1

Normalised coordinates: rotate so that a = 0, then c = u, b = t, d = t+w with
0 < u < t and w > 0.  The target `case1_landing` is `p = u = w`.
Regimes:  p < min(u,w)  (discharged by interleaving) | u < p < w |
p > max(u,w)  (the two OPEN regimes)  | p == min | p == max.

EVIDENCE, NOT PROOF.  Usage: case1_regime.py [Kmax] [nocrux]
"""
import sys
from itertools import product, combinations, permutations

sys.setrecursionlimit(10000)


def agree(S, e, a, b):
    G = len(S)
    return all(S[(a + i) % G] == S[(b + i) % G] for i in range(e))


def prec(S, x):
    return S[(x - 1) % len(S)]


def foll(S, e, x):
    return S[(x + e) % len(S)]


def isrepeat(S, e, a, b):
    G = len(S)
    return (1 <= e < G and a != b and agree(S, e, a, b)
            and prec(S, a) != prec(S, b) and foll(S, e, a) != foll(S, e, b))


def istriple(S, e, a, b, c):
    G = len(S)
    return (1 <= e < G and len({a, b, c}) == 3 and agree(S, e, a, b)
            and agree(S, e, b, c) and len({prec(S, a), prec(S, b), prec(S, c)}) > 1
            and len({foll(S, e, a), foll(S, e, b), foll(S, e, c)}) > 1)


def inarc(a, b, p, G):
    return 0 < (p - a) % G < (b - a) % G


def inter(a, b, c, d, G):
    if len({a, b, c, d}) != 4:
        return False
    return inarc(a, b, c, G) != inarc(a, b, d, G)


def inter_any(p, q, G):
    a, b = p
    c, d = q
    return any(inter(*z, G) for z in permutations((a, b, c, d)))


def obstruction(S, L):
    G = len(S)
    K = L - 1
    for t in combinations(range(G), 3):
        for e in range(K, G):
            if istriple(S, e, *t):
                return True
    reps = []
    for e in range(K, G):
        for a, b in combinations(range(G), 2):
            if isrepeat(S, e, a, b):
                reps.append((e, a, b))
    for (e1, a, b), (e2, c, d) in combinations(reps, 2):
        if inter_any((a, b), (c, d), G):
            return True
    return False


def vtx(S, L, i):
    G = len(S)
    return tuple(S[(i + k) % G] for k in range(L - 1))


def back_p(S, x, y):
    G = len(S)
    p = 0
    while p < G and S[(x - p - 1) % G] == S[(y - p - 1) % G]:
        p += 1
    return p


def ext_len(S, a, b):
    """length of the maximal two-sided repeat at (a,b), or None if the pair is
    blocked on the left (precedings agree) or periodic."""
    G = len(S)
    if prec(S, a) == prec(S, b):
        return None
    e = 0
    while e < G - 1 and S[(a + e) % G] == S[(b + e) % G]:
        e += 1
    return e


def regime(u, w, p):
    lo, hi = min(u, w), max(u, w)
    if p < lo:
        return "A:p<min"
    if p == lo:
        return "B:p=min"
    if lo < p < hi:
        return "C:OPEN-between"
    if p == hi:
        return "D:p=max"
    return "E:OPEN-above"


def main():
    Gmax = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    nocrux = len(sys.argv) > 2 and sys.argv[2] == "nocrux"
    counts = {}
    bad = []
    ncfg = 0
    periodic = 0
    for G in range(4, Gmax + 1):
        for L in range(2, G + 2):
            for S in product((0, 1), repeat=G):
                fib = {}
                for i in range(G):
                    fib.setdefault(vtx(S, L, i), []).append(i)
                obst = obstruction(S, L)
                for (v1, st1), (v2, st2) in combinations(fib.items(), 2):
                    if v1 == v2:
                        continue
                    if len(st1) < 2 or len(st2) < 2:
                        continue
                    if not nocrux and (len(st1) != 2 or len(st2) != 2):
                        continue
                    a, b = st1[0], st1[1]
                    c, d = st2[0], st2[1]
                    if not inter(a, b, c, d, G):
                        continue
                    if prec(S, a) == prec(S, b):
                        continue
                    if prec(S, c) != prec(S, d):
                        continue
                    ncfg += 1
                    p = back_p(S, c, d)
                    if p >= G:
                        periodic += 1
                        continue
                    u, w = (c - a) % G, (d - b) % G
                    r = regime(u, w, p)
                    key = ("obst" if obst else "FREE") + " " + r
                    counts[key] = counts.get(key, 0) + 1
                    if not obst and p != u and p != w:
                        bad.append((G, L, "".join(map(str, S)), (a, b), (c, d),
                                    p, u, w,
                                    ext_len(S, a, b), ext_len(S, c, d)))
    print("G max", Gmax, "no fibre restriction" if nocrux else "crux shape")
    print("case-1 configurations:", ncfg, "periodic (p >= G):", periodic)
    for k in sorted(counts):
        print(f"  {k:28} {counts[k]}")
    print("FREE genomes with p != u or p != w:", len(bad))
    for v in bad[:20]:
        print("  G=%d L=%d S=%s (a,b)=%s (c,d)=%s p=%d u=%d w=%d "
              "extlen(a,b)=%s extlen(c,d)=%s" % v)


if __name__ == "__main__":
    main()