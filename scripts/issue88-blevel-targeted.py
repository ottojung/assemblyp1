#!/usr/bin/env python3
"""Targeted B-level search: larger G at fixed L, and the `L = 2` band
`[1, G-2)`, plus a report of escaping circulations that are not the
spectrum of any word (invisible to candidate-level searches)."""
import importlib.util
import sys
from itertools import product

_s = importlib.util.spec_from_file_location("b", "scripts/issue88-blevel-search.py")
m = importlib.util.module_from_spec(_s)
_s.loader.exec_module(m)


def triple_lengths(S, G):
    out = set()
    for a, b, c, l in product(range(G), range(G), range(G), range(0, G)):
        if len({a % G, b % G, c % G}) < 3:
            continue
        if m.IsMaximalTriple(S, a, b, c, l, G):
            out.add(l)
    return out


def is_word_spectrum(B, G, L, k):
    for T in product(range(k), repeat=G):
        if all(m.specCount(T, w, G, L) == B[w] for w in B) and sum(B.values()) == G:
            return T
    return None


def main():
    G = int(sys.argv[1]); k = int(sys.argv[2])
    Ls = [int(x) for x in sys.argv[3].split(",")]
    viol = 0
    esc = 0
    nonword = 0
    for S in product(range(k), repeat=G):
        tl = triple_lengths(S, G)
        for L in Ls:
            band = [l for l in sorted(tl) if L - 1 <= l < G - L]
            for B in m.circulations(S, G, L):
                if not m.BeatsTruth(B, S, G, L):
                    continue
                esc += 1
                if is_word_spectrum(B, G, L, k) is None:
                    nonword += 1
                    if nonword <= 5:
                        print("  escaping B that is NOT a word spectrum: S=",
                              "".join(map(str, S)), "L=", L, B)
                if not band:
                    viol += 1
                    print("  VIOLATION S=", "".join(map(str, S)), "L=", L,
                          "triplelens=", sorted(tl), "B=", B)
                break
    print(f"G={G} k={k} L={Ls}: escape instances={esc}, "
          f"non-word escaping B={nonword}, violations={viol}")


main()
