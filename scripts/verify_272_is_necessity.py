#!/usr/bin/env python3
"""Independent verifier for AssemblyP1/FiniteIsNotNecessaryCertainty.lean
(#272, subclaim 1): `I_s` is NOT necessary for read-only decoder certainty.

The Lean kernel is the source of truth; this is an independent, from-scratch
computational cross-check.  It

1. transcribes the literal historical information-feasibility predicate `I_s`
   (Shomorony--Kim--Courtade--Tse 2016, Eq. (1); Bresler--Bresler--Tse 2013
   repeat/bridging definitions) over circular genomes;
2. verifies the concrete witness `AAAB` (length 4, read length L = 3, sampled
   starts R = {0,2}): the induced read-string set is Y = {AAA, ABA}, historical
   coverage holds, the maximal triple occurrence `A` at {0,1,2} is not
   all-bridged, so `I_s` fails;
3. verifies that the read-realizable support of Y is exactly the four rotations
   of `AAAB` (a single orbit class), so a read-only decoder is certain at Y;
4. exhaustively searches all small models (alphabet size k, length G <= 7,
   L < G) for certainty-holding counterexamples and reports which clause of `I_s`
   fails.  It confirms that the triple-bridging clause and the (historical)
   coverage clause can both fail while certainty holds, and that no
   certainty-holding model fails `I_s` on the interleaved clause (evidence that
   the interleaved clause is the one tight against Bresler's necessity theorem).

Run:  python3 scripts/verify_272_is_necessity.py
"""

import itertools
import sys


# ----------------------------------------------------------------------------
# Circular genomes and reads
# ----------------------------------------------------------------------------

def window(s, L, r):
    G = len(s)
    return tuple(s[(r + d) % G] for d in range(L))


def readset(s, L, R):
    return frozenset(window(s, L, r) for r in R)


def all_windows(s, L):
    G = len(s)
    return frozenset(window(s, L, r) for r in range(G))


def canon(s):
    G = len(s)
    return min(tuple(s[(i + j) % G] for i in range(G)) for j in range(G))


def subsets(n):
    for r in range(n + 1):
        for c in itertools.combinations(range(n), r):
            yield c


# ----------------------------------------------------------------------------
# Literal historical I_s (HistoricalInformationFeasibleLiteral)
# ----------------------------------------------------------------------------

def agree(s, e, a, b):
    G = len(s)
    return all(s[(a + d) % G] == s[(b + d) % G] for d in range(e))


def is_triple_occurrence(s, e, a, b, c):
    G = len(s)
    if not (1 <= e < G) or len({a, b, c}) != 3:
        return False
    return agree(s, e, a, b) and agree(s, e, a, c) and agree(s, e, b, c)


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


def historical_covers(s, L, ms):
    G = len(s)
    return all(any((t + d) % G in ms for d in range(L - 1)) for t in range(G))


def failing_clause(s, L, R):
    """Return None if I_s holds, else the first failing clause name."""
    words = readset(s, L, R)
    ms = match_starts(s, L, words)
    if not historical_covers(s, L, ms):
        return "coverage"
    G = len(s)
    for e in range(1, G):
        for a in range(G):
            for b in range(a + 1, G):
                if not agree(s, e, a, b):
                    continue
                for c in range(b + 1, G):
                    if is_triple_occurrence(s, e, a, b, c):
                        if not all(bridges_copy(s, L, ms, e, x) for x in (a, b, c)):
                            return "triple"
    for e1 in range(1, G):
        for e2 in range(1, G):
            for a in range(G):
                for b in range(a + 1, G):
                    if not is_repeat(s, e1, a, b):
                        continue
                    for c in range(G):
                        for d in range(c + 1, G):
                            if not is_repeat(s, e2, c, d):
                                continue
                            if interleaved(s, a, b, c, d):
                                if not (bridges_copy(s, L, ms, e1, a)
                                        or bridges_copy(s, L, ms, e1, b)
                                        or bridges_copy(s, L, ms, e2, c)
                                        or bridges_copy(s, L, ms, e2, d)):
                                    return "interleaved"
    return None


# ----------------------------------------------------------------------------
# Read-only certainty at fixed length G (over alphabet range(k))
# ----------------------------------------------------------------------------

def certain(s, L, k):
    """Every length-G genome over range(k) realizing readset(s,L,all) is a
    rotation of s."""
    G = len(s)
    cs = canon(s)
    Y = readset(s, L, range(G))
    for t in itertools.product(range(k), repeat=G):
        if canon(t) != cs and Y <= all_windows(t, L):
            return False
    return True


# ----------------------------------------------------------------------------
# Checks
# ----------------------------------------------------------------------------

def main():
    ok = True

    # (2) The concrete witness.
    s = (0, 0, 0, 1)          # AAAB
    L = 3
    R = (0, 2)
    Y = readset(s, L, R)
    assert Y == frozenset({(0, 0, 0), (0, 1, 0)}), Y
    assert historical_covers(s, L, match_starts(s, L, Y)), "coverage should hold"
    assert is_triple_occurrence(s, 1, 0, 1, 2), "A at {0,1,2} is a triple occurrence"
    ms = match_starts(s, L, Y)
    assert ms == [0, 2], ms
    assert not all(bridges_copy(s, L, ms, 1, x) for x in (0, 1, 2)), "triple not all-bridged"
    assert failing_clause(s, L, R) == "triple", failing_clause(s, L, R)
    print("[1] witness AAAB, L=3, R={0,2}: Y={AAA,ABA}; coverage holds; "
          "triple clause fails -> I_s fails")

    # (3) certainty at the witness observation.
    assert certain(s, L, 2), "read-only certainty should hold at the witness"
    realizers = [t for t in itertools.product(range(2), repeat=4)
                 if Y <= all_windows(t, L)]
    assert {canon(t) for t in realizers} == {canon(s)}, realizers
    assert len(realizers) == 4, realizers
    print("[2] read-realizable support of Y = the 4 rotations of AAAB (single "
          "orbit) -> a read-only decoder is certain at Y")

    # (4) exhaustive small search.
    counts = {"coverage": 0, "triple": 0, "interleaved": 0}
    example = {}
    for G in (4, 5, 6, 7):
        for k in (2, 3):
            if k ** G > 3000:
                continue
            gs = list(itertools.product(range(k), repeat=G))
            can = {t: canon(t) for t in gs}
            wins = {}
            for t in gs:
                for L2 in range(2, G):
                    wins[(t, L2)] = all_windows(t, L2)
            for s2 in gs:
                if can[s2] != s2 or len(set(s2)) == 1:
                    continue
                for L2 in range(2, G):
                    for R2 in subsets(G):
                        if not R2:
                            continue
                        fc = failing_clause(s2, L2, R2)
                        if fc is None:
                            continue
                        Y2 = readset(s2, L2, R2)
                        cs2 = can[s2]
                        cert = all(not (can[t] != cs2 and Y2 <= wins[(t, L2)])
                                   for t in gs)
                        if cert:
                            counts[fc] += 1
                            example.setdefault(fc, (s2, L2, R2))
    print("[3] exhaustive search (G<=7, k<=3, L<G): certainty-holding I_s failures by clause:",
          counts)
    assert counts["coverage"] > 0, "expected coverage-clause counterexamples"
    assert counts["triple"] > 0, "expected triple-clause counterexamples"
    assert counts["interleaved"] == 0, (
        "no certainty-holding model should fail I_s on the interleaved clause")
    for fc, (s2, L2, R2) in sorted(example.items()):
        print("      first %-12s witness: s=%s L=%d R=%s" % (fc, s2, L2, R2))

    print()
    print("ALL CHECKS PASS: I_s is NOT necessary for read-only decoder certainty; "
          "the failure occurs on the triple-bridging clause (and on the historical "
          "coverage clause), never on the interleaved clause in the searched range.")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
