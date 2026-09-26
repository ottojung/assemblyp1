#!/usr/bin/env python3
"""Exhaustive B-level search for a counterexample to
`AssemblyP1.MLEscape.EscapeForcesMidRangeRepeat`:

    HasSpectralEscape hG S L  ->  HasMidRangeTripleRepeat hG S L

Exact transcription of the Lean definitions (OrientedRigidity.cyc/window/
nodeWindow/specCount/support/Balanced, MLEscape.IsMassGPositiveCirculation /
BeatsTruthSpectrum / HasSpectralEscape / HasMidRangeTripleRepeat,
RepeatAdapter.TripleAgree / IsMaximalTriple).  No approximation: the
circulation `B` ranges over *all* assignments, not only word spectra.

Usage: issue88-blevel-search.py [G] [alphabet] [Lmin]
"""
import sys
from itertools import product, combinations

def cyc(S, i, G):
    return S[i % G]

def window(S, r, G, L):
    return tuple(cyc(S, r + d, G) for d in range(L))

def nodewindow(S, r, G, L):
    return tuple(cyc(S, r + d, G) for d in range(L - 1))

def specCount(S, w, G, L):
    return sum(1 for r in range(G) if window(S, r, G, L) == w)

def support(S, G, L):
    return set(window(S, r, G, L) for r in range(G))

def genomeNodes(S, G, L):
    return set(nodewindow(S, r, G, L) for r in range(G))

def balanced(B, sup, nodes, L):
    # Balanced f: for all v in nodes, sum of f over support edges with
    # winPrefix e = v equals sum over edges with winSuffix e = v.
    for v in nodes:
        pre = tuple(w[:L - 1] for w in sup)
        suf = tuple(w[1:] for w in sup)
        outv = sum(B[w] for w in sup if w[:L - 1] == v)
        inv = sum(B[w] for w in sup if w[1:] == v)
        if outv != inv:
            return False
    return True

def IsMassGPositiveCirculation(B, S, G, L):
    sup = support(S, G, L)
    if set(B) != sup:
        return False
    if any(B[w] < 1 for w in sup):
        return False
    if not balanced(B, sup, genomeNodes(S, G, L), L):
        return False
    if sum(B.values()) != G:
        return False
    return True

def BeatsTruth(B, S, G, L):
    return any(B[w] > specCount(S, w, G, L) for w in B)

def TripleAgree(S, a, b, c, l, G):
    for d in range(l):
        if not (cyc(S, a + d, G) == cyc(S, b + d, G)
                and cyc(S, b + d, G) == cyc(S, c + d, G)):
            return False
    return True

def IsMaximalTriple(S, a, b, c, l, G):
    if not TripleAgree(S, a, b, c, l, G):
        return False
    if (cyc(S, a + G - 1, G) == cyc(S, b + G - 1, G)
            and cyc(S, b + G - 1, G) == cyc(S, c + G - 1, G)):
        return False
    if (cyc(S, a + l, G) == cyc(S, b + l, G)
            and cyc(S, b + l, G) == cyc(S, c + l, G)):
        return False
    return True

def HasMidRangeTripleRepeat(S, G, L):
    if not (L - 1 <= G - L - 1):   # band empty
        return False
    for a, b, c, l in product(range(G), range(G), range(G), range(L - 1, G - L)):
        if a % G == b % G or b % G == c % G or a % G == c % G:
            continue
        if IsMaximalTriple(S, a, b, c, l, G):
            return True
    return False

def compositions(n, k):
    # k positive parts summing to n
    if k == 1:
        yield (n,)
        return
    for first in range(1, n - k + 2):
        for rest in compositions(n - first, k - 1):
            yield (first,) + rest

def circulations(S, G, L):
    sup = sorted(support(S, G, L))
    s = len(sup)
    if s == 0 or s > G:
        return
    for vals in compositions(G, s):
        B = dict(zip(sup, vals))
        if IsMassGPositiveCirculation(B, S, G, L):
            yield B

def main():
    G = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    k = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    Lmin = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    viol = []
    tot_S = 0
    tot_esc = 0
    for S in product(range(k), repeat=G):
        for L in range(Lmin, G + 1):
            tot_S += 1
            mid = HasMidRangeTripleRepeat(S, G, L)
            esc = False
            for B in circulations(S, G, L):
                if BeatsTruth(B, S, G, L):
                    esc = True
                    break
            if not esc:
                continue
            tot_esc += 1
            if not mid:
                viol.append((S, L, B))
    print(f"G={G} k={k} Lmin={Lmin}: (S,L) pairs={tot_S}, "
          f"with a mass-G escape={tot_esc}, "
          f"counterexamples to EscapeForcesMidRangeRepeat={len(viol)}")
    for S, L, B in viol[:10]:
        print("  VIOLATION S=", "".join(map(str, S)), "L=", L, "B=", B)
    return 1 if viol else 0

if __name__ == "__main__":
    sys.exit(main())
