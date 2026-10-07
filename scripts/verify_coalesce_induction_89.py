#!/usr/bin/env python3
"""Step-by-step replay of the *intended* proof of `CrossingPairsCoalesce`.

This checks the argument itself (not merely the statement): for every crossing
doubled pair of chords, the shift-left induction is replayed step by step and
each of the four exits of the induction is classified:

  * `collide`   -- some shifted endpoint meets a fixed endpoint; the collision
                   step (`three_starts_ne`) then identifies the chords;
  * `heads`     -- both heads reached with no collision, and the heads
                   interleave, contradicting `P2` clause 2;
  * `!ok`       -- a genuine failure of the argument (must not happen).

The conclusion `SameExtension` is checked directly too.  Evidence, not proof.

Usage:  python3 scripts/verify_coalesce_induction_89.py [--bin G] [--tri G]
"""

import argparse
import itertools
import sys

from verify_crossing_coalesce_89 import (cyc, P2, is_primitive, vtx, Interleaved,
                                         pairBack, maxPairStart, maxPairLen,
                                         SameExtension, IsRepeat)


def replay(w, L, a, b, c, d, stat):
    n = len(w)
    beta = pairBack(w, a, b)
    delta = pairBack(w, c, d)
    # step 0: the two fixed endpoints of the *other* pair
    # We slide `c, d` to the head of its own chain, then slide `a, b`.
    t = 0
    while t <= delta:
        u, v = (c - t) % n, (d - t) % n
        if u in (a, b) or v in (a, b):
            # collision: {u,v} = {a,b} by the multiplicity cap
            assert {u, v} == {a, b}, (w, L, a, b, c, d, t)
            stat["collide"] += 1
            return
        if not Interleaved(w, a, b, u, v):
            stat["!ok"] += 1
            return
        t += 1
    # now u,v is the head of the (c,d) chain
    u, v = (c - delta) % n, (d - delta) % n
    s = 0
    while s <= beta:
        x, y = (a - s) % n, (b - s) % n
        if x in (u, v) or y in (u, v):
            assert {x, y} == {u, v}, (w, L, a, b, c, d, s)
            stat["collide"] += 1
            return
        if not Interleaved(w, x, y, u, v):
            stat["!ok"] += 1
            return
        s += 1
    # both heads reached, still interleaved: must be refuted by P2 clause 2
    p, q = (a - beta) % n, (b - beta) % n
    e1, e2 = maxPairLen(w, a, b), maxPairLen(w, c, d)
    if Interleaved(w, p, q, u, v):
        stat["heads"] += 1
        if not (e1 <= L - 2 or e2 <= L - 2):
            stat["!ok"] += 1
            return
    if not SameExtension(w, a, b, c, d):
        stat["!ok"] += 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bin", type=int, default=8)
    ap.add_argument("--tri", type=int, default=5)
    args = ap.parse_args()
    stat = {"collide": 0, "heads": 0, "!ok": 0}
    for alphabet, nmax in (("01", args.bin), ("012", args.tri)):
        for n in range(2, nmax + 1):
            for tup in itertools.product(alphabet, repeat=n):
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
                            if Interleaved(w, a, b, c, d):
                                replay(w, L, a, b, c, d, stat)
    for k, v in stat.items():
        print("  %-8s %d" % (k, v))
    return 1 if stat["!ok"] else 0


if __name__ == "__main__":
    sys.exit(main())
