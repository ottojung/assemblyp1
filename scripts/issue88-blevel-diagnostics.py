#!/usr/bin/env python3
"""Diagnostics for the B-level escape instances: what do they look like?"""
import sys
from itertools import product
import importlib.util
_spec = importlib.util.spec_from_file_location("blevel", "scripts/issue88-blevel-search.py")
_m = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_m)
circulations = _m.circulations
BeatsTruth = _m.BeatsTruth
specCount = _m.specCount
IsMaximalTriple = _m.IsMaximalTriple

def triple_lengths(S, G, L):
    out = {}
    for a, b, c, l in product(range(G), range(G), range(G), range(0, G)):
        if len({a % G, b % G, c % G}) < 3:
            continue
        if IsMaximalTriple(S, a, b, c, l, G):
            out.setdefault(l, []).append((a, b, c))
    return out

def is_word_spectrum(B, G, L, k):
    for T in product(range(k), repeat=G):
        sup = set()
        ok = True
        for w in B:
            if specCount(T, w, G, L) != B[w]:
                ok = False
                break
        if ok and sum(specCount(T, w, G, L) for w in B) == G:
            return T
    return None

def main():
    G = int(sys.argv[1]); k = int(sys.argv[2])
    seen = 0
    nonword = 0
    for S in product(range(k), repeat=G):
        for L in range(2, G + 1):
            tl = triple_lengths(S, G, L)
            band = sorted(l for l in tl if L - 1 <= l < G - L)
            for B in circulations(S, G, L):
                if not BeatsTruth(B, S, G, L):
                    continue
                seen += 1
                if is_word_spectrum(B, G, L, k) is None:
                    nonword += 1
                if seen <= 25:
                    print("S=", "".join(map(str, S)), "L=", L,
                          "triplelens=", sorted(tl), "band=", band,
                          "Bdiff=", {w: (B[w], specCount(S, w, G, L))
                                     for w in sorted(B) if B[w] != specCount(S, w, G, L)})
                break
    print("escape instances (one B each):", seen, "B not a word spectrum:", nonword)

main()
