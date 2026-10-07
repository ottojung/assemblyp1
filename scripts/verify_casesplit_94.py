#!/usr/bin/env python3
"""Falsification sweep for the board-94 CASE SPLIT of front G3.

The Lean theorems proved in `AssemblyP1/Issue94CaseSplit.lean` are, at
`alpha = Bin`:

    crossingPairsCoalesce_bin (equivalently `crossingPairsCoalesce`, which is
    an inhabitant of the existing `BBTCrossingCoalesce.CrossingPairsCoalesce`):

      a != b, c != d, vtx a = vtx b, vtx c = vtx d, Interleaved a b c d
      ==>  SameExtension a b c d,

    proved by splitting on whether a cross-head EQUALITY holds:

      branch 1  (A=C or A=D or B=C or B=D)   ==> front 2463a1f's helper
      branch 2  (all four cross-head inequalities) ==> front a23872a's `False`

    where A = maxPairStart a b, B = maxPairStart b a,
          C = maxPairStart c d, D = maxPairStart d c.

    crossingPairsCoalesce_of_noCollision is the same split at arbitrary alpha
    with branch 2 supplied as a hypothesis; its statement is not checkable by
    enumeration, and its content is exactly the two branches below, so this
    sweep targets the `Bin` instance.

This script is an attempt to FALSIFY the case split, not to support it.  The
questions, and why each matters for *this* front specifically (94f8 already
ran V1/V2/V3 for the collision branch alone):

  (V1) NON-VACUITY of the case split's own hypothesis set.  Unlike 94f8, the
       hypothesis set here INCLUDES `Interleaved`, which is the premise the
       whole `#89` route rests on and which the two earlier sweeps never
       exercised.  If no primitive P2 word admits two interleaving chords, the
       case split is vacuous over its actual domain and worthless.

  (V2) NON-TRIVIALITY: is `SameExtension` ever FALSE for two INTERLEAVING
       genuine chords?  If never, the conclusion is a tautology of the setting
       and the case split proves nothing.

  (V3) COUNTEREXAMPLE to the combined theorem: an interleaving chord pair
       whose head collision is GENUINE (`{a,b} != {c,d}`) and whose
       `SameExtension` is nevertheless FALSE.  This is the direct refutation
       attempt at the level of the assembled statement.

  (V4) BRANCH SEPARATION -- specific to this front and not run by 94f8.  The
       case split is only informative if BOTH branches are actually taken in
       practice.  Count how many interleaving quadruples land in branch 1 (a
       cross-head equality holds) and how many in branch 2 (all four
       inequalities hold).  If branch 2 is never taken, the case split is
       secretly a one-branch theorem and the "no-collision" front's result is
       doing no work at the `CrossingPairsCoalesce` level; that would be worth
       knowing and is exactly the kind of thing an assembly front can hide.

  (V5) BRANCH-2 REFUTATION.  Within branch 2, check the exact claim
       `no_collision_contradiction` makes: that the four inequalities are never
       simultaneously satisfiable at two interleaving chords of a primitive P2
       word.  Any instance here is a counterexample to front a23872a's theorem
       and, since branch 2 is closed by `.elim`, to this front's too.

Transcribes `def:P2` (AssemblyP1/P2.lean), `RepeatAdapter.IsPrimitive`,
`BBTSequenceGraph.vtx`, `P2RepeatResidual.pairBack` / `maxPairStart`,
`Interleaved` and `BBTLadder.SameExtension`, exactly as in
`verify_crossing_coalesce_89.py`, the module the collision sweep also uses.

This is EVIDENCE, not a proof: the completeness of a finite sweep is not
established in the kernel.  Its only use here is to try, and fail, to refute.

Usage:  python3 scripts/verify_casesplit_94.py [--bin G]
"""

import argparse
import itertools
import sys

from verify_crossing_coalesce_89 import (P2, is_primitive, vtx, pairBack,
                                         maxPairStart, SameExtension,
                                         Interleaved)


def heads(w, a, b):
    return (maxPairStart(w, a, b), maxPairStart(w, b, a))


def cross_head_collision(w, a, b, c, d):
    """Branch 1 predicate: at least one cross-head EQUALITY holds."""
    A, B = heads(w, a, b)
    C, D = heads(w, c, d)
    return (A == C) or (A == D) or (B == C) or (B == D)


def cross_head_inequalities(w, a, b, c, d):
    """Branch 2 predicate: all four cross-head INEQUALITIES hold."""
    A, B = heads(w, a, b)
    C, D = heads(w, c, d)
    return (A != C) and (A != D) and (B != C) and (B != D)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bin", type=int, default=9)
    args = ap.parse_args()

    n_words = 0
    n_regimes = 0              # (word, L) passing primitive + P2
    n_chords = 0
    n_quads = 0                # quadruples of genuine chords
    n_il = 0                   # quadruples that are Interleaved   (V1)
    n_il_genuine = 0           # ... with {a,b} != {c,d}
    n_se_false_il = 0          # interleaving quadruples, SameExt FALSE (V2)
    n_bad = 0                  # (V3) counterexamples
    n_bad_genuine = 0
    n_branch1 = 0              # (V4) cross-head equality holds
    n_branch2 = 0              # (V4) all four inequalities hold
    n_branch2_genuine = 0
    n_branch2_bad = 0          # (V5) counterexample to no_collision_contradiction
    refutation = None
    refutation_genuine = None
    b2_counterexample = None
    examples_il = []
    examples_b1 = []
    examples_b2 = []

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
                        if not Interleaved(w, a, b, c, d):
                            continue
                        n_il += 1
                        genuine = {a, b} != {c, d}
                        if genuine:
                            n_il_genuine += 1
                        se = SameExtension(w, a, b, c, d)
                        if not se:
                            n_se_false_il += 1
                        b1 = cross_head_collision(w, a, b, c, d)
                        b2 = cross_head_inequalities(w, a, b, c, d)
                        if b1:
                            n_branch1 += 1
                            if genuine and not se:
                                n_bad_genuine += 1
                                if refutation_genuine is None:
                                    refutation_genuine = (w, L, a, b, c, d)
                            if not se:
                                n_bad += 1
                                if refutation is None:
                                    refutation = (w, L, a, b, c, d)
                            if genuine and len(examples_b1) < 5:
                                examples_b1.append((w, L, a, b, c, d))
                        elif b2:
                            n_branch2 += 1
                            if genuine:
                                n_branch2_genuine += 1
                            if len(examples_b2) < 5:
                                examples_b2.append((w, L, a, b, c, d))
                            # (V5): front a23872a claims this is impossible.
                            n_branch2_bad += 1
                            if b2_counterexample is None:
                                b2_counterexample = (w, L, a, b, c, d)
                        else:
                            # b1 and b2 are exact complements by construction;
                            # reaching here would be a bug in this script.
                            raise AssertionError(
                                "b1 and b2 are not complementary at %r" % ((w, L, a, b, c, d),))
                        if genuine and len(examples_il) < 5:
                            examples_il.append((w, L, a, b, c, d))

    print("words scanned:                   %d" % n_words)
    print("primitive P2 regimes:            %d" % n_regimes)
    print("genuine chords:                  %d" % n_chords)
    print("chord quadruples:                %d" % n_quads)
    print("(V1) INTERLEAVING quadruples:    %d   NON-VACUOUS: %s"
          % (n_il, "yes" if n_il > 0 else "NO -- VACUOUS"))
    print("(V1x) ... genuinely distinct:    %d" % n_il_genuine)
    print("(V2) interleaving, SameExt FALSE:%d   NON-TRIVIAL: %s"
          % (n_se_false_il, "yes" if n_se_false_il > 0 else "NO -- TAUTOLOGY"))
    print("(V3) interleaving AND SameExt FALSE: %d   REFUTED: %s"
          % (n_bad, "YES" if n_bad else "no (survived this sweep)"))
    print("(V3x) genuine AND SameExt FALSE: %d  REFUTED: %s"
          % (n_bad_genuine, "YES" if n_bad_genuine else "no"))
    print("(V4) branch 1 (cross-head EQUALITY holds):  %d" % n_branch1)
    print("(V4) branch 2 (all four INEQUALITIES hold): %d" % n_branch2)
    print("(V4) branch 2, genuinely distinct:         %d" % n_branch2_genuine)
    print("(V5) branch-2 instances (a23872a says impossible): %d  REFUTED: %s"
          % (n_branch2_bad, "YES" if n_branch2_bad else "no (consistent)"))
    if examples_il:
        print("first genuinely-distinct interleaving examples (w, L, a, b, c, d):")
        for e in examples_il:
            print("   ", e)
    if examples_b1:
        print("first branch-1 examples:")
        for e in examples_b1:
            print("   ", e)
    if examples_b2:
        print("first branch-2 examples:")
        for e in examples_b2:
            print("   ", e)
    if b2_counterexample:
        print("COUNTEREXAMPLE to no_collision_contradiction:", b2_counterexample)
    if refutation:
        print("COUNTEREXAMPLE to the case split:", refutation)
    if refutation_genuine:
        print("COUNTEREXAMPLE (genuine):", refutation_genuine)
    return 1 if (refutation or b2_counterexample) else 0


if __name__ == "__main__":
    sys.exit(main())
