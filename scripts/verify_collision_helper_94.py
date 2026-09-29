#!/usr/bin/env python3
"""Falsification sweep for the board-94 COLLISION helper of front G1.

The Lean theorem proved in `AssemblyP1/Issue94HeadCollision.lean` is

    head_collision_implies_sameExtension:
      a != b, c != d, both pairs carry a common (L-1)-mer, and at least one
      of the four cross-head equalities
          A = C,  A = D,  B = C,  B = D
      holds, where A = maxPairStart a b, B = maxPairStart b a,
      C = maxPairStart c d, D = maxPairStart d c
      ==>  SameExtension a b c d.

This script is an attempt to FALSIFY it, not to support it.  Three questions:

  (V1) NON-VACUITY of the hypothesis set: is there any primitive P2 word,
       any 2 <= L <= K, and any quadruple of genuine chords for which the
       hypotheses hold?  If never, the theorem is vacuous and worthless.

  (V2) NON-TRIVIALITY of the conclusion: is `SameExtension` ever FALSE for
       two genuine chords?  If it is never false, the conclusion is a
       tautology of the setting and the theorem proves nothing.

  (V3) COUNTEREXAMPLE: is there a quadruple satisfying every hypothesis of
       the theorem for which `SameExtension` is nevertheless false?  This is
       the direct refutation attempt.  Count of violations is printed.

Note: the Lean theorem does NOT require `Interleaved`; the pointer's helper is
stated for any two chords.  So this sweep checks the stronger, unconstrained
reading.  A counterexample there is a counterexample to the Lean theorem.

Transcribes `def:P2` (AssemblyP1/P2.lean), `RepeatAdapter.IsPrimitive`,
`BBTSequenceGraph.vtx`, `P2RepeatResidual.pairBack` / `maxPairStart`, and
`BBTLadder.SameExtension`, exactly as in `verify_crossing_coalesce_89.py`.

This is EVIDENCE, not a proof: the completeness of a finite sweep is not
established in the kernel.  Its only use here is to try, and fail, to refute.

Usage:  python3 scripts/verify_collision_helper_94.py [--bin G] [--tri G]
"""

import argparse
import itertools
import sys

from verify_crossing_coalesce_89 import (P2, is_primitive, vtx, pairBack,
                                         maxPairStart, SameExtension)


def heads(w, a, b):
    return (maxPairStart(w, a, b), maxPairStart(w, b, a))


def cross_head_collision(w, a, b, c, d):
    A, B = heads(w, a, b)
    C, D = heads(w, c, d)
    return (A == C) or (A == D) or (B == C) or (B == D)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bin", type=int, default=9)
    ap.add_argument("--tri", type=int, default=0,
                    help="unused; kept for interface compatibility")
    args = ap.parse_args()

    n_words = 0
    n_regimes = 0            # (word, L) passing primitive + P2
    n_chords = 0
    n_quads = 0              # quadruples of genuine chords
    n_coll = 0               # quadruples satisfying hcoll  (V1)
    n_coll_il = 0            # ... that are also Interleaved
    n_se_false = 0           # quadruples where SameExtension is false (V2)
    n_bad = 0                # (V3) counterexamples
    n_coll_x = 0             # hcoll with the two chords genuinely different
    n_bad_x = 0              # (V3) counterexample in that genuine case
    refutation_x = None
    examples = []
    coll_examples = []
    refutation = None

    for n in range(2, args.bin + 1):
        for tup in itertools.product("01", repeat=n):
            w = "".join(tup)
            n_words += 1
            if not is_primitive(w):
                continue
            for L in range(2, n + 1):
                if not P2(w, L):
                    continue
                n_regimes += 1
                chords = [(a, b) for a in range(n) for b in range(n)
                          if a != b and vtx(w, a, L) == vtx(w, b, L)]
                n_chords += len(chords)
                for (a, b) in chords:
                    for (c, d) in chords:
                        n_quads += 1
                        se = SameExtension(w, a, b, c, d)
                        if not se:
                            n_se_false += 1
                        if cross_head_collision(w, a, b, c, d):
                            n_coll += 1
                            if {a, b} != {c, d}:
                                n_coll_x += 1
                                if not se:
                                    n_bad_x += 1
                                    if refutation_x is None:
                                        refutation_x = (w, L, a, b, c, d)
                            if len(coll_examples) < 5:
                                coll_examples.append((w, L, a, b, c, d))
                            if not se:
                                n_bad += 1
                                if refutation is None:
                                    refutation = (w, L, a, b, c, d)
        if n >= 4:
            # ternary pass, small K only
            for tup in itertools.product("012", repeat=n):
                if n > 4:
                    break
                w = "".join(tup)
                n_words += 1
                if not is_primitive(w):
                    continue
                for L in range(2, n + 1):
                    if not P2(w, L):
                        continue
                    n_regimes += 1
                    chords = [(a, b) for a in range(n) for b in range(n)
                              if a != b and vtx(w, a, L) == vtx(w, b, L)]
                    n_chords += len(chords)
                    for (a, b) in chords:
                        for (c, d) in chords:
                            n_quads += 1
                            se = SameExtension(w, a, b, c, d)
                            if not se:
                                n_se_false += 1
                            if cross_head_collision(w, a, b, c, d):
                                n_coll += 1
                                if {a, b} != {c, d}:
                                    n_coll_x += 1
                                    if not se:
                                        n_bad_x += 1
                                        if refutation_x is None:
                                            refutation_x = (w, L, a, b, c, d)
                                if len(coll_examples) < 5:
                                    coll_examples.append((w, L, a, b, c, d))
                                if not se:
                                    n_bad += 1
                                    if refutation is None:
                                        refutation = (w, L, a, b, c, d)

    print("words scanned:              %d" % n_words)
    print("primitive P2 regimes:       %d" % n_regimes)
    print("genuine chords:             %d" % n_chords)
    print("chord quadruples:           %d" % n_quads)
    print("(V1) quadruples with hcoll: %d   NON-VACUOUS: %s"
          % (n_coll, "yes" if n_coll > 0 else "NO -- VACUOUS"))
    print("(V2) quadruples, SameExt FALSE: %d   NON-TRIVIAL: %s"
          % (n_se_false, "yes" if n_se_false > 0 else "NO -- TAUTOLOGY"))
    print("(V3) hcoll AND SameExt FALSE:  %d   REFUTED: %s"
          % (n_bad, "YES" if n_bad else "no (survived this sweep)"))
    print("(V1x) GENUINE cross-chord collisions ({a,b} != {c,d}): %d" % n_coll_x)
    print("(V3x) genuine hcoll AND SameExt FALSE: %d  REFUTED: %s" % (n_bad_x, "YES" if n_bad_x else "no"))
    if refutation_x: print("COUNTEREXAMPLE (genuine):", refutation_x)
    if coll_examples:
        print("first collision examples (w, L, a, b, c, d):")
        for e in coll_examples:
            print("   ", e)
    if refutation:
        print("COUNTEREXAMPLE:", refutation)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
