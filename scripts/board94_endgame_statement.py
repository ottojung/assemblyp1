#!/usr/bin/env python3
"""Independent transcription of the #94 endgame definitions, for (d).

Every predicate below is transcribed from the Lean sources named in the
header comment, NOT from any existing board-94 script:

  cyc        OrientedRigidity.lean:611
  vtx        BBTCondense.lean:178 (= nodeWindow)
  fibre      BBTCondense.lean:201 (via mem_fibre: vtx r = v)
  IsRepeat / IsTripleRepeat   SourceFaithfulIs.lean:111,122
  Preceding / Following       SourceFaithfulIs.lean:100,104
  InOpenArc / Interleaved     SourceFaithfulIs.lean:355,365
  P2 / Ukkonen                P2.lean:80,91
  LongObstruction             BBTEulerian.lean:337
  Selects / SelectedTriple / SelectedInterleaved   BBTSupportInvariant.lean:158,163,176
  FibrePreserving / OneCycle / OrbitVertexEq       BBTEulerianSearch.lean:140,146,152
  VisitsAll                   BBTEulerian.lean:129
  rotAdd / nextPos / prevPos  BBTChords.lean:76,80,83

Goal: find an instance of all six hypotheses of
InterleavingObstructionNeeded with LongObstruction false (i.e. a refutation),
or establish that none exists in range.  Also record, for each P2 genome,
the counts of good/bad selected-interleaving one-cycles, and of
SelectedTriple, so the report's factual claims are census-backed.
"""

import itertools
import sys
from collections import Counter

# ---------------------------------------------------------------- primitives


def make(G):
    return dict(
        G=G,
        cyc=lambda S, i: S[i % G],
        vtx=lambda S, L, r: tuple(S[(r + d) % G] for d in range(L - 1)),
        preceding=lambda S, t: S[(t + G - 1) % G],
        following=lambda S, e, t: S[(t + e) % G],
        agree=lambda S, e, r, t: all(S[(r + d) % G] == S[(t + d) % G]
                                     for d in range(e)),
        rotAdd=lambda s, x: (x + s) % G,
        nextPos=lambda x: (x + 1) % G,
        prevPos=lambda x: (x + G - 1) % G,
        InOpenArc=lambda a, b, p: 0 < (p - a) % G < (b - a) % G,
    )


def four_distinct(a, b, c, d):
    return len({a, b, c, d}) == 4


def interleaved(E, a, b, c, d):
    return (four_distinct(a, b, c, d)
            and (E["InOpenArc"](a, b, c) != E["InOpenArc"](a, b, d)))


def is_repeat(E, S, e, a, b):
    return (1 <= e < E["G"] and a != b and E["agree"](S, e, a, b)
            and E["preceding"](S, a) != E["preceding"](S, b)
            and E["following"](S, e, a) != E["following"](S, e, b))


def is_triple_repeat(E, S, e, a, b, c):
    return (1 <= e < E["G"] and len({a, b, c}) == 3
            and E["agree"](S, e, a, b) and E["agree"](S, e, a, c)
            and E["agree"](S, e, b, c)
            and not (E["preceding"](S, a) == E["preceding"](S, b)
                     == E["preceding"](S, c))
            and not (E["following"](S, e, a) == E["following"](S, e, b)
                     == E["following"](S, e, c)))


def P2(E, S, L):
    for e in range(E["G"]):
        for a, b, c in itertools.permutations(range(E["G"]), 3):
            if is_triple_repeat(E, S, e, a, b, c) and not e < L - 1:
                return False
    for e1 in range(E["G"]):
        for e2 in range(E["G"]):
            for a, b, c, d in itertools.permutations(range(E["G"]), 4):
                if (is_repeat(E, S, e1, a, b) and is_repeat(E, S, e2, c, d)
                        and interleaved(E, a, b, c, d)):
                    if not (e1 <= L - 2 or e2 <= L - 2):
                        return False
    return True


def long_obstruction(E, S, L):
    for e in range(E["G"]):
        for a, b, c in itertools.permutations(range(E["G"]), 3):
            if is_triple_repeat(E, S, e, a, b, c) and L - 1 <= e:
                return True
    for e1 in range(E["G"]):
        for e2 in range(E["G"]):
            for a, b, c, d in itertools.permutations(range(E["G"]), 4):
                if (is_repeat(E, S, e1, a, b) and is_repeat(E, S, e2, c, d)
                        and interleaved(E, a, b, c, d)
                        and L - 1 <= e1 and L - 1 <= e2):
                    return True
    return False


def is_primitive(E, S):
    G = E["G"]
    for s in range(1, G):
        if G % s == 0 and all(S[i] == S[i % s] for i in range(G)):
            return False
    return True


# --------------------------------------------------------------- theta-level


def fibres(E, S, L):
    fib = {}
    for x in range(E["G"]):
        fib.setdefault(E["vtx"](S, L, x), []).append(x)
    return fib


def selects(E, S, L, fib, theta, v):
    return any(theta[x] != E["nextPos"](x) for x in fib[v])


def selected_triple(E, S, L, theta):
    for v, xs in fibres(E, S, L).items():
        if len(xs) >= 3 and selects(E, S, L, {v: xs}, theta, v):
            return True
    return False


def selected_interleaved(E, S, L, theta):
    fib = fibres(E, S, L)
    for a, b, c, d in itertools.permutations(range(E["G"]), 4):
        va, vc = E["vtx"](S, L, a), E["vtx"](S, L, c)
        if va != vc and not interleaved(E, a, b, c, d):
            continue
        if va != E["vtx"](S, L, b) or vc != E["vtx"](S, L, d):
            continue
        if selects(E, S, L, fib, theta, va) and selects(E, S, L, fib, theta, vc):
            return True
    return False


def fibre_preserving(E, S, L, theta):
    return all(E["vtx"](S, L, theta[x]) == E["vtx"](S, L, E["nextPos"](x))
               for x in range(E["G"]))


def one_cycle(E, theta):
    seen = [0]
    x = 0
    for _ in range(E["G"]):
        x = theta[x]
        seen.append(x)
    return len(set(seen[:E["G"]])) == E["G"] and seen[E["G"]] == 0


def orbit_vertex_eq(E, S, L, theta):
    seq = [0]
    x = 0
    for _ in range(E["G"]):
        x = theta[x]
        seq.append(x)
    truth = [E["vtx"](S, L, E["rotAdd"](k, 0)) for k in range(E["G"])]
    for k in range(E["G"]):
        rot = [E["vtx"](S, L, E["rotAdd"]((j + k) % E["G"], 0))
               for j in range(E["G"])]
        if [E["vtx"](S, L, s) for s in seq[:E["G"]]] == rot:
            return True
    return False


def cycles(G):
    """all G-cycles as tuples: a G-cycle maps 0 to something != 0, and every
    permutation with theta 0 != 0 is a G-cycle."""
    for perm in itertools.permutations(range(G)):
        yield perm


# ------------------------------------------------------------------- the sweep


def sweep(Gmax, Lmax, verbose=True):
    stats = Counter()
    refutations = []      # P2, six hypotheses, LongObstruction false
    good_selinter = []    # P2, selected interleaved, good theta
    vacuity = Counter()   # (G, L) -> [P2 words, P2 prim words, SelectedTriple count]
    for G in range(1, Gmax + 1):
        E = make(G)
        for L in range(2, Lmax + 1):
            for word in itertools.product((0, 1), repeat=G):
                S = list(word)
                stats["words"] += 1
                if not P2(E, S, L):
                    stats["notP2"] += 1
                    continue
                stats["P2"] += 1
                prim = is_primitive(E, S)
                if (G, L) not in vacuity:
                    vacuity[(G, L)] = [0, 0, 0]
                vac = vacuity[(G, L)]
                vac[0] += 1
                if prim:
                    vac[1] += 1
                LO = long_obstruction(E, S, L)
                assert LO is False, "LongObstruction must be false on P2 at 2<=L"
                for th in cycles(G):
                    if not one_cycle(E, th):
                        continue
                    if not fibre_preserving(E, S, L, th):
                        continue
                    st = selected_triple(E, S, L, th)
                    if st:
                        stats["SelTriple"] += 1
                        vac[2] += 1
                    si = selected_interleaved(E, S, L, th)
                    if not si:
                        continue
                    stats["SelInter"] += 1
                    oc = not one_cycle(E, th)
                    assert not oc
                    if orbit_vertex_eq(E, S, L, th):
                        stats["good"] += 1
                        if len(good_selinter) < 40:
                            good_selinter.append((G, L, tuple(S), th))
                    else:
                        stats["bad"] += 1
                        refutations.append((G, L, tuple(S), th))
    if verbose:
        print("stats:", dict(stats))
        print("vacuity (G,L): P2 words, P2 primitive words, P2+SelectedTriple:")
        for k in sorted(vacuity):
            print("   ", k, vacuity[k])
        print("bad selected-interleaving one-cycles on P2 genomes:",
              len(refutations))
        for r in refutations[:40]:
            print("   REFUTES InterleavingObstructionNeeded:", r)
        print("good selected-interleaving one-cycles (first 10):")
        for r in good_selinter[:10]:
            print("   ", r)
    return stats, refutations


if __name__ == "__main__":
    Gmax = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    Lmax = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    sweep(Gmax, Lmax)

# ------------------------------------------------- candidate admissible forms
#
# A  : interleaved right-maximal repeats of length >= L-1, at least one blocked
#      (this is the proposed AdmissibleObstruction)
# A2 : the same but with BOTH constituents two-sided maximal (i.e. LongObstruction's
#      second disjunct) -- expected to be refuted by P2
# A3 : as A but requiring one-sided maximality in the *Following* direction only
#      (i.e. drop the Preceding clause entirely)

def agree_len(E, S, a, b):
    n = 0
    while n < E["G"] and E["agree"](S, n + 1, a, b):
        n += 1
    return n


def right_maximal(E, S, e, a, b):
    return e >= 1 and E["agree"](S, e, a, b) and a != b and \
        E["following"](S, e, a) != E["following"](S, e, b)


def left_maximal(E, S, e, a, b):
    return e >= 1 and E["agree"](S, e, a, b) and a != b and \
        E["preceding"](S, a) != E["preceding"](S, b)


def A_obstruction(E, S, L, blocked_required=True, both_maximal=False):
    for a, b, c, d in itertools.permutations(range(E["G"]), 4):
        if not interleaved(E, a, b, c, d):
            continue
        m1, m2 = agree_len(E, S, a, b), agree_len(E, S, c, d)
        if m1 < L - 1 or m2 < L - 1:
            continue
        e1 = max(1, m1) if right_maximal(E, S, m1, a, b) else None
        e2 = max(1, m2) if right_maximal(E, S, m2, c, d) else None
        if e1 is None or e2 is None:
            continue
        if both_maximal and not (left_maximal(E, S, m1, a, b)
                                  and left_maximal(E, S, m2, c, d)):
            continue
        blk = (E["preceding"](S, a) == E["preceding"](S, b)
               or E["preceding"](S, c) == E["preceding"](S, d))
        if blocked_required and not blk:
            continue
        return (a, b, c, d, m1, m2)
    return None


def sweep_forms(Gmax, Lmax):
    cnt = Counter()
    wit = {}
    for G in range(2, Gmax + 1):
        E = make(G)
        for L in range(2, Lmax + 1):
            for word in itertools.product((0, 1), repeat=G):
                S = list(word)
                p2 = P2(E, S, L)
                a = A_obstruction(E, S, L, blocked_required=True)
                a2 = A_obstruction(E, S, L, blocked_required=True, both_maximal=True)
                a3 = A_obstruction(E, S, L, blocked_required=False)
                if p2:
                    cnt["P2"] += 1
                    if a:
                        cnt["P2_A"] += 1
                        wit.setdefault("P2_A", (G, L, tuple(S), a))
                    if a2:
                        cnt["P2_A2_BUG"] += 1
                        wit.setdefault("P2_A2_BUG", (G, L, tuple(S), a2))
                    if a3:
                        cnt["P2_A3"] += 1
                if a:
                    cnt["all_A"] += 1
                    wit.setdefault("A", (G, L, tuple(S), a))
                if a3:
                    cnt["all_A3"] += 1
    print("form census:", dict(cnt))
    for k, v in wit.items():
        print("  smallest witness", k, v)
