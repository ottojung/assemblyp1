"""94b11 falsification-first census: does "the shift between the two selected
starts of the blocked constituent is not a period" suffice, on NON-primitive
genomes?  Search for a counterexample; report census counts as evidence only.

Transcription of the Lean definitions (BBTSupportInvariant.SelectedInterleaved,
BBTChords.{FourDistinctStarts,InArc}, SourceFaithfulIs.{Preceding,Following},
RepeatAdapter.{ShiftInvariant,IsPeriod}).
"""
from itertools import product, permutations, combinations

def cyc(S, i, G):
    return S[i % G]

def vtx(S, a, L, G):
    return tuple(cyc(S, a + d, G) for d in range(L - 1))

def InArc(G, a, b, p):
    return 0 < (p + G - a) % G < (b + G - a) % G

def FourDistinct(a, b, c, d):
    return len({a, b, c, d}) == 4

def InterleavedStarts(G, a, b, c, d):
    return FourDistinct(a, b, c, d) and (InArc(G, a, b, c) != InArc(G, a, b, d))

def Preceding(S, a, G):
    return cyc(S, a + G - 1, G)

def Following(S, a, e, G):
    return cyc(S, a + e, G)

def IsRightRepeat(S, e, a, b, G):
    if not (1 <= e < G): return False
    if a == b: return False
    if any(cyc(S, a + d, G) != cyc(S, b + d, G) for d in range(e)): return False
    return Following(S, a, e, G) != Following(S, b, e, G)

def admissible(S, L, G):
    for e1 in range(1, G):
        for e2 in range(1, G):
            for a, b, c, d in permutations(range(G), 4):
                if not InterleavedStarts(G, a, b, c, d): continue
                if L - 1 > e1 or L - 1 > e2: continue
                if not IsRightRepeat(S, e1, a, b, G): continue
                if not IsRightRepeat(S, e2, c, d, G): continue
                if Preceding(S, a, G) != Preceding(S, b, G) or \
                   Preceding(S, c, G) != Preceding(S, d, G):
                    return True
    return False

def IsPeriod(S, p, G):
    return all(cyc(S, i, G) == cyc(S, i + p, G) for i in range(G))

def IsPrimitive(S, G):
    return not any(IsPeriod(S, s, G) for s in range(1, G))

def H(S, a, b, G):
    "the shift between a and b is not a period"
    s = (b + G - a) % G
    return not IsPeriod(S, s, G)

def weak_hyp(S, L, G, a, b, c, d):
    return (Preceding(S, a, G) != Preceding(S, b, G) or H(S, a, b, G)) and \
           (Preceding(S, c, G) != Preceding(S, d, G) or H(S, c, d, G))

def main():
    counterexamples = []
    stats = dict(nonprim_sel=0, sel_nonprim=0, weak_ok=0, nonprim=0, sel=0)
    for G in range(3, 9):
        for A in (1, 2):
            for S in product(range(A), repeat=G):
                for L in range(2, 5):
                    prim = IsPrimitive(S, G)
                    found = False
                    for a, b, c, d in permutations(range(G), 4):
                        if not InterleavedStarts(G, a, b, c, d): continue
                        if vtx(S, a, L, G) != vtx(S, b, L, G): continue
                        if vtx(S, c, L, G) != vtx(S, d, L, G): continue
                        found = True
                        if not prim: stats["nonprim_sel"] += 1
                        if weak_hyp(S, L, G, a, b, c, d):
                            stats["weak_ok"] += 1
                            if not admissible(S, L, G):
                                counterexamples.append((S, L, G, (a, b, c, d)))
                    if found and not prim:
                        stats["nonprim"] += 1
    print(stats)
    print("counterexamples:", len(counterexamples))
    for c in counterexamples[:10]:
        print(c)

main()