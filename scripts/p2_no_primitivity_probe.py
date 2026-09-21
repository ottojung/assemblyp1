#!/usr/bin/env python3
"""Exact-hypothesis probe: does P2 => spectrum uniqueness hold without
primitivity?  Enumerate ALL binary words (canonical reps), group by spectrum,
and report P2 members with non-rotation partners."""
from collections import defaultdict
from itertools import product
from p2_eulerian_attack import canonical, spectrum_key, p2, is_primitive


def main():
    for nmax in (14, 16):
        total = 0
        hits = []
        for n in range(2, nmax + 1):
            classes = {}
            for tup in product("AB", repeat=n):
                c = canonical(tup)
                classes[c] = tup
            for L in range(2, n + 1):
                groups = defaultdict(list)
                for c in classes:
                    groups[spectrum_key(c, L)].append(c)
                for key, ws in groups.items():
                    if len(ws) < 2:
                        continue
                    for w in ws:
                        if p2(w, L):
                            hits.append((L, n, w, [x for x in ws if x != w]))
                total += sum(1 for c in classes if p2(c, L))
        print(f"binary all words n<={nmax}: P2 words={total}, "
              f"P2 in non-singleton spectrum classes={len(hits)}")
        for h in hits[:10]:
            print("   ", h)
        if hits:
            # inspect primitivity of the offending pairs
            for h in hits[:10]:
                print("      prim:", is_primitive(h[2]),
                      [is_primitive(x) for x in h[3]])


if __name__ == "__main__":
    main()
