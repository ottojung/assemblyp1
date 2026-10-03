#!/usr/bin/env python3
"""Census for the CASE-1 LANDING statement, transcribed from the Lean
definitions with the *exact* index semantics:

  BackAgrees S x y q  ==  forall i < q, S[(x-i) mod G] == S[(y-i) mod G]
  (i = 0 included, so BackAgrees 1 is "S[x] == S[y]")
  p is maximal:  BackAgrees p and not BackAgrees (p+1),
  so S[(x-p) mod G] != S[(y-p) mod G] and p >= 1 whenever S[x] == S[y].

  vtx(S,L,i)          = (S[i+k] for k < L-1)
  Preceding(S,i)      = S[i-1]
  Following(S,e,i)    = S[i+e]
  IsRepeat(e,a,b)     = 1<=e<G, a!=b, agree e, prec differ, foll differ
  IsTripleRepeat      = 1<=e<G, 3 distinct, pairwise agree, precs not all equal,
                        folls not all equal
  InOpenArc(a,b,p)    = 0 < (p-a)%G < (b-a)%G
  Interleaved(a,b,c,d)= four distinct and (c in arc) != (d in arc)
  LongObstruction(L)  = maximal triple repeat of length >= L-1, or two
                        interleaved maximal repeats both of length >= L-1

EVIDENCE, NOT PROOF.  Usage: case1_p.py [Kmax] [nocrux]
"""
import sys
from itertools import product, combinations, permutations


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
    """Lean `BackAgrees` index semantics: maximal q with
    BackAgrees q (i.e. S[x-i] == S[y-i] for 0 <= i < q)."""
    G = len(S)
    p = 0
    while p < G and S[(x - p) % G] == S[(y - p) % G]:
        p += 1
    return p


def back_q(S, x, y):
    """number of agreeing PRECEDING positions = back_p - 1; this is the
    number of backward steps of the maximal repeat containing x,y."""
    G = len(S)
    q = 0
    while q < G and S[(x - q - 1) % G] == S[(y - q - 1) % G]:
        q += 1
    return q


def max_rep(S, a, b):
    G = len(S)
    if prec(S, a) == prec(S, b):
        return None
    e = 0
    while e < G - 1 and S[(a + e) % G] == S[(b + e) % G]:
        e += 1
    return e


def main():
    Gmax = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    nocrux = len(sys.argv) > 2 and sys.argv[2] == "nocrux"
    stat = {}
    pstat = {}
    ex = {}
    ncfg = 0
    for G in range(4, Gmax + 1):
        for L in range(2, G + 2):
            for S in product((0, 1), repeat=G):
                fib = {}
                for i in range(G):
                    fib.setdefault(vtx(S, L, i), []).append(i)
                obst = obstruction(S, L)
                items = [(v, st) for v, st in fib.items()
                         if (nocrux and len(st) >= 2) or len(st) == 2]
                for (v1, st1), (v2, st2) in combinations(items, 2):
                    a, b = st1[0], st1[1]
                    c, d = st2[0], st2[1]
                    if v1 == v2:
                        continue
                    if not inter(a, b, c, d, G):
                        continue
                    if prec(S, a) == prec(S, b):
                        continue
                    if prec(S, c) != prec(S, d):
                        continue
                    ncfg += 1
                    p = back_p(S, c, d)
                    q = back_q(S, c, d)
                    if p < G:
                        assert q == p - 1, (p, q)
                    P = ((c - q) % G, (d - q) % G)
                    if p >= G:
                        stat["periodic"] = stat.get("periodic", 0) + 1
                        continue
                    if obst:
                        stat["obstructed"] = stat.get("obstructed", 0) + 1
                        pstat[p] = pstat.get(p, 0) + 1
                    A, Pp = {a, b}, set(P)
                    if A == Pp:
                        k = "same"
                    elif Pp == {b, a}:
                        k = "cross"
                    elif A & Pp:
                        k = "share1"
                    elif inter_any((a, b), P, G):
                        k = "disjoint+in"
                    else:
                        k = "disjoint-in"
                    kk = ("obst" if obst else "free") + ":" + k
                    stat[kk] = stat.get(kk, 0) + 1
                    ex.setdefault((obst, k), (G, L, "".join(map(str, S)), (a, b),
                                              (c, d), p, P,
                                              max_rep(S, *P)))
    print("G max", Gmax, "no fibre restriction" if nocrux else "crux shape")
    print("case-1 configurations:", ncfg, " stats:", stat)
    print("p values on obstructed genomes:", dict(sorted(pstat.items())))
    for k, v in sorted(ex.items(), key=str):
        print(f"  obst={k[0]} {k[1]:12} G={v[0]} L={v[1]} S={v[2]} "
              f"(a,b)={v[3]} (c,d)={v[4]} p={v[5]} P={v[6]} ext-len={v[7]}")


if __name__ == "__main__":
    main()