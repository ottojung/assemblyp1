#!/usr/bin/env python3
"""The two closing steps of the `#89` coalescence induction, checked directly.

Given a collision `sh j = sh i` (a chord appears twice on the backward
chains of `a, b` and `c, d`), we must conclude that the two chains are the
*same* chain, and hence that the heads (`maxPairStart`) coincide.  The
mechanism: the backward chain of a chord is the orbit of a single step, so if
`{a-j, b-j} = {c-i, d-i}` then the two chords are the same point of the same
orbit, and the head of the orbit is a function of the orbit, not of the entry
point.  The two ways the unordered pairs can match are checked separately.

Usage:  python3 scripts/verify_collision_head_89.py [--bin G]
"""

import argparse
import itertools
import sys

from verify_crossing_coalesce_89 import (P2, is_primitive, vtx, Interleaved,
                                         pairBack, maxPairStart, SameExtension)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bin", type=int, default=9)
    args = ap.parse_args()
    n_coll = 0
    n_bad = 0
    for n in range(2, args.bin + 1):
        for tup in itertools.product("01", repeat=n):
            w = "".join(tup)
            if not is_primitive(w):
                continue
            for L in range(2, n + 1):
                if not P2(w, L):
                    continue
                chords = [(a, b) for a in range(n) for b in range(n)
                          if a != b and vtx(w, a, L) == vtx(w, b, L)]
                for (a, b) in chords:
                    for (c, d) in chords:
                        if not Interleaved(w, a, b, c, d):
                            continue
                        beta, delta = pairBack(w, a, b), pairBack(w, c, d)
                        found = False
                        for j in range(beta + 1):
                            for i in range(delta + 1):
                                J = {(a - j) % n, (b - j) % n}
                                I = {(c - i) % n, (d - i) % n}
                                if J & I:
                                    n_coll += 1
                                    found = True
                                    if not SameExtension(w, a, b, c, d):
                                        n_bad += 1
                                        print("BAD", w, L, a, b, c, d, j, i)
                        if not found:
                            print("no collision for", w, L, a, b, c, d)
                            return 1
    print("collisions: %d, of which non-coalescing: %d" % (n_coll, n_bad))
    return 1 if n_bad else 0


if __name__ == "__main__":
    sys.exit(main())
