#!/usr/bin/env python3
"""Fast broad scan: group primitive words by exact same-length spectrum, then
test P2 only on non-singleton classes.  Reports any P2 word with a
non-rotation partner (a counterexample to P2 => circular spectrum uniqueness).

Works for alphabets up to size 5 over modest ranges.  Bounded evidence only.
"""
import sys
from collections import defaultdict
from p2_eulerian_attack import lyndon_words, spectrum_key, p2, is_primitive


def scan(alpha, nmax, maxL):
    hits = []
    tested = 0
    for L in range(2, maxL + 1):
        table = {}
        coll = []
        for n in range(L, nmax + 1):
            for w in lyndon_words(alpha, n):
                if not is_primitive(w):
                    continue
                key = spectrum_key(w, L)
                if key in table:
                    coll.append((table[key], w))
                else:
                    table[key] = w
        seen = set()
        for w1, w2 in coll:
            for w in (w1, w2):
                if w in seen:
                    continue
                seen.add(w)
                tested += 1
                if p2(w, L):
                    hits.append((L, w, w1 if w is w2 else w2))
        print(f"  |Sigma|={len(alpha)} L={L} n<={nmax}: "
              f"{len(table)} classes, {len(coll)} collisions, {len(hits)} P2-hits",
              flush=True)
    return hits


def main():
    print("fast broad P2 collision scan")
    ranges = [
        ("ABCD", 11, 3),
        ("ABCD", 10, 4),
        ("ABCDE", 9, 3),
        ("ABCDE", 8, 4),
    ]
    for alpha, nmax, maxL in ranges:
        hits = scan(alpha, nmax, maxL)
        for h in hits[:10]:
            print("   COUNTEREXAMPLE", h)


if __name__ == "__main__":
    main()
