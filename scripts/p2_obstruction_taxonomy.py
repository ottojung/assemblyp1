#!/usr/bin/env python3
"""Which obstructions actually create a non-rotation alternate spelling?

For primitive binary words up to n, and each L, tabulate:
  T = maximal triple repeat of length >= K
  I = interleaved pair of maximal repeats, both >= K
  C = existence of a non-rotation same-spectrum partner
and report the joint distribution.  This separates "non-unique Euler tour"
from "non-unique spelled word"."""
from collections import defaultdict
from p2_eulerian_attack import (
    lyndon_words, is_primitive, has_maximal_triple, has_interleaved,
    spectrum_key,
)
from itertools import combinations


def main():
    nmax = 18
    stats = defaultdict(int)
    ex = defaultdict(list)
    for L in range(2, nmax + 1):
        K = L - 1
        table = defaultdict(list)
        for n in range(L, nmax + 1):
            for w in lyndon_words("AB", n):
                if not is_primitive(w):
                    continue
                table[spectrum_key(w, L)].append(w)
        collided = set()
        for ws in table.values():
            if len(ws) >= 2:
                for w in ws:
                    collided.add((L, w))
        for n in range(L, nmax + 1):
            for w in lyndon_words("AB", n):
                if not is_primitive(w):
                    continue
                T = has_maximal_triple(w, K)
                I = has_interleaved(w, K)
                C = (L, w) in collided
                key = (T, I, C)
                stats[key] += 1
                if len(ex[key]) < 4:
                    ex[key].append((w, L))
    print("(T=triple, I=interleaved, C=collision) : count   examples")
    for key in sorted(stats, key=lambda k: (-stats[k], k)):
        print(f"  {key}: {stats[key]:8d}   {ex[key]}")
    print()
    print("Interpretation:")
    print("  (*,*,False) = Euler tours may be non-unique but spelled word unique")
    print("  (False,False,True) would refute P2 => uniqueness")
    print("  (True,*,True) / (False,True,True): which obstruction actually collides")


if __name__ == "__main__":
    main()
