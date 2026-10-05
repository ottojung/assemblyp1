#!/usr/bin/env python3
"""Board 94, front `94real`: census behind `AssemblyP1/Issue94EulerianRealize.lean`.

Finite cross-check of the construction lemma

    window (L := L) G (traversalRead S sigma) s d = window (L := L) G S (sigma s) d

under the *exact* hypothesis the Lean proof uses: the `traverses` clause of
`BBTEulerian.EulerianCycle` alone (the `single` clause is NOT used), at
`2 <= L`, for every genome length `G >= 1` and every window length `L >= 2`,
binary alphabet, all words and all permutations.

The result is evidence only, not a completeness claim.  The proof is
`Issue94Realize.window_traversalRead_of_traverses`; this script exists to show
that the statement is not vacuous and that the hypothesis is not slack.

Usage:  python3 scripts/verify_eulerian_realize_94.py [maxG] [maxL]
"""

from itertools import product, permutations
import sys


def nodes(S, L, G):
    """The (L-1)-mer at each start: `BBTSequenceGraph.vtx`."""
    return [tuple(S[(x + d) % G] for d in range(L - 1)) for x in range(G)]


def traverses(S, L, G, sg):
    """`EulerianCycle`'s first clause: consecutive listed starts are joined."""
    N = nodes(S, L, G)
    return all(N[sg[(i + 1) % G]] == N[(sg[i] + 1) % G] for i in range(G))


def visits_all(S, L, G, sg):
    """`EulerianCycle`'s second clause: the walk is one circuit."""
    succ = {sg[i]: sg[(i + 1) % G] for i in range(G)}
    seen, x = [], 0
    for _ in range(G):
        seen.append(x)
        x = succ[x]
    return len(set(seen)) == G


def window_agrees(S, L, G, sg):
    """The window agreement the construction lemma asserts."""
    return all(S[sg[(x + d) % G]] == S[(sg[x] + d) % G] for x in range(G) for d in range(L))


def scan(maxG, maxL):
    tot = bad = tot_full = 0
    for G in range(1, maxG + 1):
        for L in range(2, maxL + 1):
            for S in product(range(2), repeat=G):
                for sg in permutations(range(G)):
                    if not traverses(S, L, G, sg):
                        continue
                    tot += 1
                    if visits_all(S, L, G, sg):
                        tot_full += 1
                    if not window_agrees(S, L, G, sg):
                        bad += 1
                        print(f"VIOLATION G={G} L={L} S={S} sigma={sg}")
    print(f"traverses-only instances: {tot} (of which Eulerian cycles: {tot_full})")
    print(f"window-agreement violations: {bad}")
    return bad == 0


if __name__ == "__main__":
    maxG = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    maxL = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    sys.exit(0 if scan(maxG, maxL) else 1)