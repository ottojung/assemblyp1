#!/usr/bin/env python3
"""Exhaustive evidence for issue #281: the (L-1)-window multiplicity cap.

Checks the crux of `AssemblyP1.PrimitiveP2FiniteClass.nodeWindow_count_le_two`
directly on the definitions, independently of the Lean proof: in every
primitive circular word in which three distinct starts share a length-K window
(K = L - 1), some maximal triple repeat of length >= K exists.

Definitions transcribed from AssemblyP1/SourceFaithfulIs.lean:

  cycl(i)          = S[i mod G]
  window(e, r)     = (cycl(r + d) for d < e)
  Preceding(t)     = cycl(t + G - 1)
  Following(e, t)  = cycl(t + e)
  IsTripleRepeat(e, a, b, c):
      1 <= e < G, a, b, c pairwise distinct, windows agree pairwise,
      NOT (Pred a = Pred b AND Pred b = Pred c),
      NOT (Foll e a = Foll e b AND Foll e b = Foll e c)

A word is a "power" (hence not primitive) iff it is a nontrivial repetition of
a shorter word. `IsPrimitive` is its negation, matching
AssemblyP1/PopulationReduction.IsPrimitive.

Usage:
    python3 scripts/verify_281_window_cap.py [q-max] [G-max] [K-max]

The search covers G up to the given G-max independently of the conjectured
bound, so it also searches *beyond* 2*q^K when G-max is larger: that is the
part of the evidence that would refute the bound.

The default range reproduces the evidence recorded in
docs/issue281-finite-candidate-class.md: binary exhaustive to G = 16,
ternary to G = 11, K up to 4.
"""

from __future__ import annotations

import itertools
import sys


def cycl(S, i):
    return S[i % len(S)]


def window(S, e, r):
    return tuple(cycl(S, r + d) for d in range(e))


def preceding(S, t):
    return cycl(S, t + len(S) - 1)


def following(S, e, t):
    return cycl(S, t + e)


def has_max_triple_ge(S, K):
    """Direct search for a maximal triple repeat of length >= K."""
    G = len(S)
    for e in range(K, G):
        occ = {}
        for r in range(G):
            occ.setdefault(window(S, e, r), []).append(r)
        for starts in occ.values():
            m = len(starts)
            if m < 3:
                continue
            for i in range(m):
                for j in range(i + 1, m):
                    for k in range(j + 1, m):
                        a, b, c = starts[i], starts[j], starts[k]
                        pa, pb, pc = (preceding(S, a), preceding(S, b),
                                      preceding(S, c))
                        if pa == pb and pb == pc:
                            continue
                        if following(S, e, a) == following(S, e, b) == \
                                following(S, e, c):
                            continue
                        return True
    return False


def is_primitive(S):
    G = len(S)
    for H in range(1, G):
        if G % H:
            continue
        if G // H <= 1:
            continue
        U = S[:H]
        if all(S[i] == U[i % H] for i in range(G)):
            return False
    return True


def triple_shared_start(S, K):
    """Do three distinct starts share a length-K window?"""
    occ = {}
    for r in range(len(S)):
        occ.setdefault(window(S, K, r), []).append(r)
    return any(len(v) >= 3 for v in occ.values())


def max_window_mult(S, K):
    occ = {}
    for r in range(len(S)):
        occ.setdefault(window(S, K, r), []).append(r)
    return max(len(v) for v in occ.values())


def main():
    q_max = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    g_max = int(sys.argv[2]) if len(sys.argv) > 2 else 16
    k_max = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    bad_cap = []
    bad_bound = []
    tight = []
    inadmissible_at_bound = 0
    for q in range(1, q_max + 1):
        for K in range(1, k_max + 1):
            bound = 2 * q ** K
            for G in range(1, g_max + 1):
                for tup in itertools.product(range(q), repeat=G):
                    S = list(tup)
                    if not is_primitive(S):
                        continue
                    if has_max_triple_ge(S, K):
                        # not P2-admissible: nothing to check
                        if G > bound:
                            inadmissible_at_bound += 1
                        continue
                    # admissible (primitive, no maximal triple repeat >= K).
                    if max_window_mult(S, K) > 2:
                        bad_cap.append((q, K, G, tuple(S)))
                    if G > bound:
                        bad_bound.append((q, K, G, tuple(S)))
                    if G == bound:
                        tight.append((q, K, tuple(S)))
    n = len(bad_cap) + len(bad_bound)
    print("cap failures (Primitive + P2 triple clause, but some K-window "
          "occurs 3 times):", len(bad_cap))
    for b in bad_cap[:5]:
        print("   ", b)
    print("bound failures (Primitive + P2 triple clause, but G > 2*q^K):",
          len(bad_bound))
    for b in bad_bound[:5]:
        print("   ", b)
    print("attainments (Primitive + P2 triple clause, G = 2*q^K):",
          len(tight))
    for t in tight[:8]:
        print("   ", t)
    print("non-admissible primitive words longer than 2*q^K (expected nonzero):",
          inadmissible_at_bound)
    return 1 if n else 0


if __name__ == "__main__":
    sys.exit(main())
