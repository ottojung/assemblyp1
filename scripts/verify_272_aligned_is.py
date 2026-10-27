#!/usr/bin/env python3
"""Exhaustively census shared literal-I_s fibres for small binary circles.

Exact model: circular spelling, fixed genome length G, fixed read length L,
orientation, distinct read-string Finset Y, and the literal historical
HistoricalInformationFeasibleLiteral predicate. A pair counts only when both
spellings have a feasible placement set inducing the same Y. This is an
exhaustive finite census, not a proof beyond the printed parameter range and
not a transfer to ordered reads/multiplicities or the historical algorithm.
"""

from itertools import combinations, product


def subsets(n):
    return [c for k in range(n + 1) for c in combinations(range(n), k)]


def win(s, L, r):
    return tuple(s[(r + d) % len(s)] for d in range(L))


def readset(s, L, R):
    return frozenset(win(s, L, r) for r in R)


def match_starts(s, L, Y):
    return {r for r in range(len(s)) if win(s, L, r) in Y}


def agree(s, e, a, b):
    return all(s[(a+d) % len(s)] == s[(b+d) % len(s)] for d in range(e))


def triple_occ(s, e, a, b, c):
    G = len(s)
    return (1 <= e < G and len({a,b,c}) == 3 and
            agree(s,e,a,b) and agree(s,e,a,c) and agree(s,e,b,c))


def repeat(s, e, a, b):
    G = len(s)
    return (1 <= e < G and a != b and agree(s,e,a,b) and
            s[(a-1)%G] != s[(b-1)%G] and s[(a+e)%G] != s[(b+e)%G])


def between(a, b, p, G):
    return 0 < (p-a) % G < (b-a) % G


def bridges(s, L, ms, e, t):
    # Source §6.4 permits a matching read start tau in
    # [t+e+1-L, t-1] (cyclic). This is exactly e+1-L <= tau-t <= -1.
    return any((t - (e+1) - j) % len(s) in ms for j in range(L-e-1))


def literal_is(s, L, R):
    G = len(s)
    Y = readset(s, L, R)
    ms = match_starts(s, L, Y)
    # Historical coverage: each cyclic interval of L-1 possible starts has
    # a matching read-string placement.
    if not all(any((t+d) % G in ms for d in range(L-1)) for t in range(G)):
        return False
    # Literal §6.4 clause quantifies over every three distinct occurrences,
    # not only maximal triple repeats.
    for e in range(1, G):
        for a, b, c in combinations(range(G), 3):
            if triple_occ(s,e,a,b,c) and not all(
                    bridges(s,L,ms,e,t) for t in (a,b,c)):
                return False
    # The stored literal predicate asks the four named copies to bridge at
    # least one of the four. Do not replace its exact source predicate here.
    for e1 in range(1,G):
      for a,b in combinations(range(G),2):
       if not repeat(s,e1,a,b): continue
       for e2 in range(1,G):
        for c,d in combinations(range(G),2):
         if not repeat(s,e2,c,d): continue
         if (len({a,b,c,d}) == 4 and
             between(a,b,c,G) != between(a,b,d,G) and
             not (bridges(s,L,ms,e1,a) or bridges(s,L,ms,e1,b) or
                  bridges(s,L,ms,e2,c) or bridges(s,L,ms,e2,d))):
             return False
    return True


def orbit(s):
    return min(s[i:]+s[:i] for i in range(len(s)))


def census(G, L):
    genomes = list(product(range(2), repeat=G))
    feasible = {}
    # Enumerate every candidate-specific placement set and exact induced Y.
    for s in genomes:
        ys = set()
        for R in subsets(G):
            if literal_is(s,L,R):
                ys.add(readset(s,L,R))
        for Y in ys:
            feasible.setdefault(Y, set()).add(orbit(s))
    collisions = [(Y, os) for Y, os in feasible.items() if len(os) > 1]
    return len(genomes), sum(map(len, feasible.values())), collisions


def main():
    # Full binary spelling space and every nontrivial proper read length up
    # through G=6. G=2 is omitted because the predicate's repeat clauses have
    # no meaningful placement range there; G=3..6 are all fully enumerated.
    for G in range(3, 7):
        for L in range(2, G):
            n, pairs, collisions = census(G,L)
            print(f"G={G} L={L} q=2: genomes={n}, feasible-(genome,Y)={pairs}, "
                  f"shared-I_s-fibres={len(collisions)}")
            if collisions:
                Y, os = collisions[0]
                print("  WITNESS:", sorted(Y), sorted(os))
                return 1
    print("NO SHARED NONROTATION I_s FIBRE in exhaustive binary census "
          "3<=G<=6, 2<=L<G")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
