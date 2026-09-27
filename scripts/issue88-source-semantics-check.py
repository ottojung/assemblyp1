#!/usr/bin/env python3
"""Check the CORRECTED source-faithful I_s of AssemblyP1.SourceFaithfulIs.

The predicate is transcribed from AssemblyP1/SourceFaithfulIs.lean:

  InformationFeasible S L R :=
      Covers S L R
    /\\ (every triple repeat of S is all-bridged)
    /\\ (every interleaved pair of repeats of S is bridged)

  Covers S L R          := every position is covered by some read at r in R
  BridgesCopy S L R e t := exists r in R, exists d : Fin L,
                              d + e + 1 < L
                          and (r + d + 1) mod G = t

The last line is the source's strict-extension condition (Bresler et al. 2013,
Fig. 5; Shomorony et al. 2016 §3/Fig. 6): the read at r strictly straddles the
occurrence, i.e. on a suitable lift r < t' and t' + e < r + L.  See
docs/bridging-source-semantics.md.

The script reports, per read length L:

  * how many genomes of length G over an alphabet of size k are I_s-feasible at
    the maximal start set R = all starts (I_s is monotone in the start set: every
    clause is a "some r in R does ..." or a coverage condition, so feasibility at
    R = Fin G decides "some R in I_s"), and
  * how many of those carry a maximal triple repeat of length >= L - 1, which
    AssemblyP1.BridgingBridge.informationFeasible_no_long_triple_repeat says
    must be zero.

Usage:  python3 scripts/issue88-source-semantics-check.py [G] [k]
"""

import itertools
import sys


def is_feasible(S, L, R):
    G = len(S)
    assert G > 0
    cycl = lambda i: S[i % G]
    win = lambda e, r: tuple(cycl(r + d) for d in range(e))
    pre = lambda t: cycl(t + G - 1)
    fol = lambda e, t: cycl(t + e)

    def is_repeat(e, a, b):
        return (1 <= e < G and a != b and win(e, a) == win(e, b)
                and pre(a) != pre(b) and fol(e, a) != fol(e, b))

    def is_triple(e, a, b, c):
        return (1 <= e < G and len({a, b, c}) == 3
                and win(e, a) == win(e, b) == win(e, c)
                and not (pre(a) == pre(b) == pre(c))
                and not (fol(e, a) == fol(e, b) == fol(e, c)))

    def read_covers(r, p):
        return any((r + d) % G == p % G for d in range(L))

    def bridges_copy(e, t):
        # The copy's start is at offset d+1 of the read at r, and the successor
        # position t+e must still be inside that read: d + e + 1 < L.
        for r in R:
            for d in range(L):
                if d + e + 1 < L and (r + d + 1) % G == t:
                    return True
        return False

    if not all(any(read_covers(r, p) for r in R) for p in range(G)):
        return False, 'cover'

    for e in range(1, G):
        for a in range(G):
            for b in range(G):
                for c in range(G):
                    if is_triple(e, a, b, c) and not (
                            bridges_copy(e, a) and bridges_copy(e, b)
                            and bridges_copy(e, c)):
                        return False, ('clause2', e, a, b, c)

    reps = [(e, a, b) for e in range(1, G) for a in range(G) for b in range(G)
            if is_repeat(e, a, b)]

    def in_open_arc(a, b, p):
        return 0 < (p + G - a) % G < (b + G - a) % G

    for (e1, a, b) in reps:
        for (e2, c, d) in reps:
            if len({a, b, c, d}) < 4:
                continue
            if in_open_arc(a, b, c) != in_open_arc(a, b, d) and not (
                    bridges_copy(e1, a) or bridges_copy(e1, b)
                    or bridges_copy(e2, c) or bridges_copy(e2, d)):
                return False, ('clause3', e1, a, b, e2, c, d)

    return True, None


def has_long_triple(S, L):
    """A maximal triple repeat of length >= L-1, i.e. what I_s must exclude."""
    G = len(S)
    cycl = lambda i: S[i % G]
    win = lambda e, r: tuple(cycl(r + d) for d in range(e))
    pre = lambda t: cycl(t + G - 1)
    fol = lambda e, t: cycl(t + e)
    for e in range(max(1, L - 1), G):
        for a in range(G):
            for b in range(G):
                for c in range(G):
                    if len({a, b, c}) < 3:
                        continue
                    if (win(e, a) == win(e, b) == win(e, c)
                            and not (pre(a) == pre(b) == pre(c))
                            and not (fol(e, a) == fol(e, b) == fol(e, c))):
                        return (a, b, c, e)
    return None


def census(G, k):
    R = list(range(G))
    print('G = %d, alphabet size %d, R = all %d starts' % (G, k, G))
    print('  L   I_s-feasible   feasible AND has a long triple repeat')
    for L in range(2, G + 1):
        feasible = 0
        viol = 0
        for S in itertools.product(range(k), repeat=G):
            ok, _ = is_feasible(list(S), L, R)
            if ok:
                feasible += 1
                if has_long_triple(list(S), L) is not None:
                    viol += 1
        print('  %-3d %-14d %d' % (L, feasible, viol))
    print('  the last column must be 0 in every row '
          '(informationFeasible_no_long_triple_repeat)')


if __name__ == '__main__':
    G = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    k = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    census(G, k)
