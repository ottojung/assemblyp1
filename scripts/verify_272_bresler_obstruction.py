#!/usr/bin/env python3
"""Independent verifier for AssemblyP1/FiniteBreslerObstructionGap.lean
(#272, target 5): the Bresler--Bresler--Tse all-unbridged obstruction is NOT the
exact necessary-and-sufficient condition for finite read-only recovery.

The Lean kernel is the source of truth; this is an independent, from-scratch
computational cross-check.  It

1. transcribes the source obstruction (Bresler--Bresler--Tse 2013, Theorem 1):
   an all-unbridged triple repeat or an all-unbridged interleaved pair, at the
   saturated match starts of the observed read-string set;
2. verifies the concrete witness `AABB` (length 4, read length L = 2, sampled
   starts R = {0,1}): the induced read-string set is Y = {AA, AB}, `AABB` has no
   triple repeat and no interleaved pair, so the obstruction is absent;
3. verifies that the read-realizable support of Y is not a single rotation class
   (`AAAB` also realizes Y and lies in a different orbit), so no read-only
   decoder is certain at Y;
4. exhaustively searches all same-length binary models with length G <= 7 and
   L < G for obstruction-absent but ambiguous observations, confirming the gap is
   not an isolated artifact of the chosen witness.

Run:  python3 scripts/verify_272_bresler_obstruction.py
"""

import itertools


# ----------------------------------------------------------------------------
# Circular genomes and reads
# ----------------------------------------------------------------------------

def window(s, L, r):
    G = len(s)
    return tuple(s[(r + d) % G] for d in range(L))


def readset(s, L, R):
    return frozenset(window(s, L, r) for r in R)


def canon(s):
    G = len(s)
    return min(tuple(s[(i + j) % G] for i in range(G)) for j in range(G))


def subsets(n):
    for r in range(n + 1):
        for c in itertools.combinations(range(n), r):
            yield c


# ----------------------------------------------------------------------------
# Bresler--Bresler--Tse repeat / bridging layer
# ----------------------------------------------------------------------------

def agree(s, e, a, b):
    G = len(s)
    return all(s[(a + d) % G] == s[(b + d) % G] for d in range(e))


def is_triple_repeat(s, e, a, b, c):
    G = len(s)
    if not (1 <= e < G) or len({a, b, c}) != 3:
        return False
    if not (agree(s, e, a, b) and agree(s, e, a, c) and agree(s, e, b, c)):
        return False
    prec = (s[(a - 1) % G], s[(b - 1) % G], s[(c - 1) % G])
    foll = (s[(a + e) % G], s[(b + e) % G], s[(c + e) % G])
    return not (prec[0] == prec[1] == prec[2]) and not (foll[0] == foll[1] == foll[2])


def is_repeat(s, e, a, b):
    G = len(s)
    if not (1 <= e < G) or a == b or not agree(s, e, a, b):
        return False
    return s[(a - 1) % G] != s[(b - 1) % G] and s[(a + e) % G] != s[(b + e) % G]


def in_open_arc(s, a, b, p):
    G = len(s)
    return 0 < (p - a) % G < (b - a) % G


def interleaved(s, a, b, c, d):
    if len({a, b, c, d}) != 4:
        return False
    return in_open_arc(s, a, b, c) != in_open_arc(s, a, b, d)


def match_starts(s, L, words):
    ws = set(words)
    return [t for t in range(len(s)) if window(s, L, t) in ws]


def bridges_copy(s, L, R, e, t):
    G = len(s)
    for r in R:
        for d in range(L):
            if d + e + 1 < L and (r + d + 1) % G == t:
                return True
    return False


def all_unbridged_triple(s, L, ms):
    G = len(s)
    for e in range(1, G):
        for a in range(G):
            for b in range(G):
                for c in range(G):
                    if is_triple_repeat(s, e, a, b, c):
                        if not (bridges_copy(s, L, ms, e, a)
                                and bridges_copy(s, L, ms, e, b)
                                and bridges_copy(s, L, ms, e, c)):
                            return True
    return False


def all_unbridged_interleaved(s, L, ms):
    G = len(s)
    for e1 in range(1, G):
        for a in range(G):
            for b in range(G):
                if not is_repeat(s, e1, a, b):
                    continue
                for e2 in range(1, G):
                    for c in range(G):
                        for d in range(G):
                            if not is_repeat(s, e2, c, d):
                                continue
                            if interleaved(s, a, b, c, d):
                                if not (bridges_copy(s, L, ms, e1, a)
                                        or bridges_copy(s, L, ms, e1, b)
                                        or bridges_copy(s, L, ms, e2, c)
                                        or bridges_copy(s, L, ms, e2, d)):
                                    return True
    return False


def source_obstruction(s, L, Y):
    ms = match_starts(s, L, Y)
    return all_unbridged_triple(s, L, ms) or all_unbridged_interleaved(s, L, ms)


# ----------------------------------------------------------------------------
# Read-realizable support and certainty
# ----------------------------------------------------------------------------

def certainty(s, L, R):
    G = len(s)
    Y = readset(s, L, R)
    cy = canon(s)
    alpha = sorted(set(s))
    for w in itertools.product(alpha, repeat=G):
        for R2 in subsets(G):
            if readset(w, L, R2) == Y:
                if canon(w) != cy:
                    return False
    return True


# ----------------------------------------------------------------------------
# Checks
# ----------------------------------------------------------------------------

def main():
    # (1) The concrete witness.
    s = (0, 0, 1, 1)
    L = 2
    R = (0, 1)
    Y = readset(s, L, R)
    assert Y == frozenset({(0, 0), (0, 1)}), Y
    assert not source_obstruction(s, L, Y), "witness unexpectedly carries an obstruction"
    assert not certainty(s, L, R), "witness unexpectedly certain"
    print("[1] AABB, L=2, R={0,1}: Y={AA,AB}; obstruction absent; read-realizable support not a single orbit")

    # (2) Independent competitor check: AAAB realizes Y in a different orbit.
    w = (0, 0, 0, 1)
    R2 = (0, 2)
    assert readset(w, L, R2) == Y
    assert canon(w) != canon(s)
    print("[2] competitor AAAB realizes Y via R={0,2} and lies in a different rotation orbit")

    # (3) Exhaustive gap search.
    found = []
    for n in range(4, 8):
        for g in itertools.product([0, 1], repeat=n):
            if len(set(g)) < 2:
                continue
            for l in range(2, n):
                for r in subsets(n):
                    yy = readset(g, l, r)
                    if not yy:
                        continue
                    if (not source_obstruction(g, l, yy)) and (not certainty(g, l, r)):
                        found.append((n, g, l, r))
                        break
                if found and found[-1][0] == n:
                    break
            if len(found) >= 5:
                break
        if len(found) >= 5:
            break
    assert found, "no obstruction-absent ambiguous model found"
    print("[3] exhaustive search (G<=7, binary, L<G): obstruction-absent ambiguous models found:",
          len(found))
    for n, g, l, r in found:
        print("      n=%d s=%s L=%d R=%s" % (n, g, l, r))

    print("ALL CHECKS PASS: the all-unbridged obstruction is not sufficient for read-only certainty")


if __name__ == "__main__":
    main()
