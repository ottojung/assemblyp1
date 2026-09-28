#!/usr/bin/env python3
"""Exhaustive check of the *exact* `#89` crossing/coalescence route.

This is the search behind `docs/crossing-coalesce-89.md`.  It is **evidence,
not a proof**: the completeness of the search is not itself established in the
kernel.  What it does do is finite certification of the four statements the
Lean proof of `BBTCrossingCoalesce.CrossingPairsCoalesce` consumes, and of the
failure of the two *uncorrected* interfaces that the earlier draft used.

Transcription of `AssemblyP1/SourceFaithfulIs.lean` (`cyc`, `Agree`,
`Preceding`, `Following`, `IsRepeat`, `IsTripleRepeat`, `InOpenArc`,
`FourDistinct`, `Interleaved`), of `def:P2` in `AssemblyP1/P2.lean`, and of
`pairBack` / `pairFwd` / `maxPairStart` / `maxPairLen` in
`AssemblyP1/P2RepeatResidual.lean`.

Statements checked, for every primitive `P2` word and every `2 <= L <= G`:

  (T1) `CrossingPairsCoalesce`  -- the target itself;
  (C1) backward chord persistence *conditioned by `pairBack`*:
       `vtx a = vtx b` and `t <= pairBack a b` imply `vtx (a-t) = vtx (b-t)`;
  (C2) backward chord *maximality*: `vtx (a - pairBack a b - 1) !=
       vtx (b - pairBack a b - 1)` whenever `a != b`;
  (S1) the corrected slide interface, sliding `c, d` one step backward:
       `Interleaved a b c d` and `c,d,rot(c),rot(d)` all outside `{a,b}`
       imply `Interleaved a b (c-1) (d-1)`;
  (X1) the *uncorrected* `SlidePreservesInterleaved` of the earlier draft
       (which asserts the same conclusion from the collision hypotheses
       alone): **REFUTED**;
  (X2) the *uncorrected* `ShiftLeftPersistence` of the earlier draft
       (which quantifies over all `t <= G`, not over `t <= pairBack`):
       **REFUTED**.

Usage:  python3 scripts/verify_crossing_coalesce_89.py [--bin G] [--tri G]
"""

import argparse
import itertools
import sys

# ---------------------------------------------------------------- the source


def cyc(w, t):
    return w[t % len(w)]


def Agree(w, e, a, b):
    return all(cyc(w, a + d) == cyc(w, b + d) for d in range(e))


def Preceding(w, t):
    return cyc(w, t - 1)


def Following(w, e, t):
    return cyc(w, t + e)


def IsRepeat(w, e, a, b):
    return (1 <= e < len(w) and a != b and Agree(w, e, a, b)
            and Preceding(w, a) != Preceding(w, b)
            and Following(w, e, a) != Following(w, e, b))


def IsTripleRepeat(w, e, a, b, c):
    return (1 <= e < len(w) and len({a, b, c}) == 3
            and Agree(w, e, a, b) and Agree(w, e, a, c) and Agree(w, e, b, c)
            and not (Preceding(w, a) == Preceding(w, b) == Preceding(w, c))
            and not (Following(w, e, a) == Following(w, e, b)
                     == Following(w, e, c)))


def InOpenArc(w, a, b, p):
    n = len(w)
    return 0 < (p + n - a) % n < (b + n - a) % n


def Interleaved(w, a, b, c, d):
    if len({a, b, c, d}) != 4:
        return False
    return InOpenArc(w, a, b, c) != InOpenArc(w, a, b, d)


def P2(w, L):
    """def:P2 at read length `L` (AssemblyP1/P2.lean)."""
    n = len(w)
    for e in range(1, n):
        for a in range(n):
            for b in range(n):
                for c in range(n):
                    if IsTripleRepeat(w, e, a, b, c) and not e < L - 1:
                        return False
    R = [(e, a, b) for e in range(1, n) for a in range(n) for b in range(n)
         if IsRepeat(w, e, a, b)]
    for (e1, a1, b1) in R:
        for (e2, c1, d1) in R:
            if Interleaved(w, a1, b1, c1, d1) and not (e1 <= L - 2 or e2 <= L - 2):
                return False
    return True


def is_primitive(w):
    n = len(w)
    return all(w != w[s:] + w[:s] for s in range(1, n))


def vtx(w, x, L):
    n = len(w)
    K = L - 1
    return tuple(w[(x + i) % n] for i in range(K))


# ----------------------------------------------- P2RepeatResidual's pairBack


def backAgree(w, a, b, t):
    n = len(w)
    return all(cyc(w, a + n - t + u) == cyc(w, b + n - t + u) for u in range(t))


def pairBack(w, a, b):
    n = len(w)
    return max([t for t in range(n + 1) if backAgree(w, a, b, t)])


def pairFwd(w, a, b):
    n = len(w)
    return max([t for t in range(n + 1)
                if all(cyc(w, a + u) == cyc(w, b + u) for u in range(t))])


def maxPairStart(w, a, b):
    n = len(w)
    return (a + n - pairBack(w, a, b)) % n


def maxPairLen(w, a, b):
    n = len(w)
    beta = pairBack(w, a, b)
    return pairFwd(w, a + n - beta, b + n - beta)


def SameExtension(w, a, b, c, d):
    n = len(w)
    return (maxPairStart(w, a, b) == maxPairStart(w, c, d)
            and maxPairStart(w, b, a) == maxPairStart(w, d, c)) or (
        maxPairStart(w, a, b) == maxPairStart(w, d, c)
        and maxPairStart(w, b, a) == maxPairStart(w, c, d))


# ----------------------------------------------------------------- the search


def check_word(w, L, stat):
    n = len(w)
    K = L - 1
    chords = [(a, b) for a in range(n) for b in range(n)
              if a != b and vtx(w, a, L) == vtx(w, b, L)]
    # (T1)
    for (a, b) in chords:
        for (c, d) in chords:
            if Interleaved(w, a, b, c, d):
                stat["T1"] += 1
                if not SameExtension(w, a, b, c, d):
                    return ("T1", w, L, a, b, c, d)
    # (C1), (C2)
    for (a, b) in chords:
        beta = pairBack(w, a, b)
        for t in range(beta + 1):
            stat["C1"] += 1
            if vtx(w, (a - t) % n, L) != vtx(w, (b - t) % n, L):
                return ("C1", w, L, a, b, t)
        stat["C2"] += 1
        if vtx(w, (a - beta - 1) % n, L) == vtx(w, (b - beta - 1) % n, L):
            return ("C2", w, L, a, b, beta)
    # (S1): slide `c, d` one step backward
    for a in range(n):
        for b in range(n):
            if a == b:
                continue
            for c in range(n):
                for d in range(n):
                    if c == d or not Interleaved(w, a, b, c, d):
                        continue
                    if len({(c - 1) % n, (d - 1) % n} & {a, b}) == 0:
                        stat["S1"] += 1
                        if not Interleaved(w, a, b, (c - 1) % n, (d - 1) % n):
                            return ("S1", w, L, a, b, c, d)
    return None


def check_X1(w, L):
    """(X1): the *uncorrected* slide interface of the earlier draft.  A
    `return` here is a refutation, which is the point."""
    n = len(w)
    chords = [(a, b) for a in range(n) for b in range(n)
              if a != b and vtx(w, a, L) == vtx(w, b, L)]
    for a in range(n):
        for b in range(n):
            if a == b:
                continue
            for c in range(n):
                for d in range(n):
                    if c == d or not Interleaved(w, a, b, c, d):
                        continue
                    if (c - 1) % n in (a, b) or (d - 1) % n in (a, b):
                        continue
                    if not Interleaved(w, a, b, (c - 1) % n, (d - 1) % n):
                        return ("X1", w, L, a, b, c, d)
    return None


def check_X2(w, L):
    """(X2): the uncorrected shift-left interface, quantifier `t <= G`."""
    n = len(w)
    chords = [(a, b) for a in range(n) for b in range(n)
              if a != b and vtx(w, a, L) == vtx(w, b, L)]
    for (a, b) in chords:
        for t in range(n + 1):
            if vtx(w, (a - t) % n, L) != vtx(w, (b - t) % n, L):
                return ("X2", w, L, a, b, t)
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bin", type=int, default=10)
    ap.add_argument("--tri", type=int, default=6)
    args = ap.parse_args()
    stat = {k: 0 for k in ("T1", "C1", "C2", "S1")}
    x1 = x2 = None
    words = 0
    for n in range(2, args.bin + 1):
        for tup in itertools.product("01", repeat=n):
            w = "".join(tup)
            if not is_primitive(w):
                continue
            words += 1
            for L in range(2, n + 1):
                if not P2(w, L):
                    continue
                r = check_word(w, L, stat)
                if r is not None:
                    print("FAIL", r)
                    return 1
                if x1 is None:
                    x1 = check_X1(w, L)
    for n in range(2, args.tri + 1):
        for tup in itertools.product("012", repeat=n):
            w = "".join(tup)
            if not is_primitive(w):
                continue
            words += 1
            for L in range(2, n + 1):
                if not P2(w, L):
                    continue
                r = check_word(w, L, stat)
                if r is not None:
                    print("FAIL", r)
                    return 1
                if x2 is None:
                    x2 = check_X2(w, L)
    print("primitive words scanned:", words)
    for k, v in stat.items():
        print("  %-4s instances: %d" % (k, v))
    print("  no failure of T1 (CrossingPairsCoalesce), C1, C2, S1")
    print("X1 (uncorrected slide) refuted by", x1)
    print("X2 (uncorrected shift-left, all t <= G) refuted by", x2)
    return 0


def first_fail_x1():
    for n in range(3, 8):
        for tup in itertools.product("01", repeat=n):
            w = "".join(tup)
            if not is_primitive(w) or not P2(w, 2):
                continue
            for a in range(n):
                for b in range(n):
                    if a == b:
                        continue
                    for c in range(n):
                        for d in range(n):
                            if c == d or not Interleaved(w, a, b, c, d):
                                continue
                            if (c - 1) % n in (a, b) or (d - 1) % n in (a, b):
                                continue
                            if not Interleaved(w, a, b, (c - 1) % n, (d - 1) % n):
                                return (w, 2, a, b, c, d)
    return None


def first_fail_x2():
    for n in range(3, 8):
        for tup in itertools.product("01", repeat=n):
            w = "".join(tup)
            if not is_primitive(w):
                continue
            for L in range(2, n + 1):
                for a in range(n):
                    for b in range(n):
                        if a == b or vtx(w, a, L) != vtx(w, b, L):
                            continue
                        for t in range(n + 1):
                            if vtx(w, (a - t) % n, L) != vtx(w, (b - t) % n, L):
                                return (w, L, a, b, t)
    return None


if __name__ == "__main__":
    sys.exit(main())
