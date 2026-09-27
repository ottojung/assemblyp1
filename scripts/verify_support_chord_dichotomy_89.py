#!/usr/bin/env python3
"""Exhaustive search for #89: the support/chord dichotomy for an alternative
Eulerian cycle of the condensed (L-1)-mer multigraph.

Candidate abstract statement (finite, purely combinatorial; no words):

  Let G positions carry labels W : Fin G -> lambda, and let f be a
  bijection of the positions with W (f x) = W x for all x (f is the
  label-preserving permutation of an alternative traversal) such that the
  successor theta = f . rho is a G-cycle (one circuit).  If f != id then

     (Wide)   some label occurs at three distinct positions, or
     (Cross)  there are two doubled pairs {a,b}, {c,d} of distinct
              positions with W a = W b, W c = W d, whose four endpoints
              interleave around the circle.

Equivalently the contrapositive: no wide class and no two crossing doubled
pairs forces f = id.

This script enumerates, for G = 1..Gmax, all set partitions of Fin G
restricted to classes of size <= 2 (the Wide alternative is the trivial
one, so only those partitions can falsify the statement), all label-
preserving bijections f of each such partition, and checks the cycle
condition theta = f . rho.  A counterexample is an f with f != id, theta a
G-cycle, and neither Wide nor Cross.

Usage:  python3 scripts/verify_support_chord_dichotomy_89.py [Gmax]
"""

import sys
from itertools import product


def partitions(n):
    """All set partitions of {0,...,n-1} as tuples of tuples (canonical:
    block order = order of first appearance)."""
    if n == 0:
        yield ()
        return
    for rest in partitions(n - 1):
        for i in range(len(rest)):
            yield rest[:i] + ((n - 1,) + rest[i],) + rest[i + 1:]
        yield rest + ((n - 1,),)


def nextp(x, G):
    return (x + 1) % G


def is_G_cycle(theta, G):
    """theta : list, theta^[0..G-1] from 0 are pairwise distinct."""
    seen = []
    x = 0
    for _ in range(G):
        if x in seen:
            return False
        seen.append(x)
        x = theta[x]
    return x == 0 and len(set(seen)) == G


def interleaved(a, b, c, d, G):
    """Cyclic alternation of {a,b} and {c,d} (BBTChords.InterleavedStarts)."""
    if len({a, b, c, d}) != 4:
        return False
    in_arc_ab_c = 0 < ((c - a) % G) < ((b - a) % G)
    in_arc_ab_d = 0 < ((d - a) % G) < ((b - a) % G)
    return in_arc_ab_c != in_arc_ab_d


def label_preserving_fns(blocks, G):
    """All bijections f of {0..G-1} with W (f x) = W x, where the label
    classes are `blocks`.  Blocks of size <= 2 only, so each block is
    either fixed or swapped."""
    for bits in product([0, 1], repeat=len(blocks)):
        f = list(range(G))
        for blk, bit in zip(blocks, bits):
            if bit == 1 and len(blk) == 2:
                i, j = blk
                f[i] = j
                f[j] = i
        yield f


def main():
    Gmax = int(sys.argv[1]) if len(sys.argv) > 1 else 11
    total_cex = 0
    for G in range(1, Gmax + 1):
        nparts = 0
        ncands = 0
        ncyc = 0
        nskipcross = 0
        cex = None
        for parts in partitions(G):
            if any(len(b) > 2 for b in parts):
                continue
            nparts += 1
            # label vector
            W = [0] * G
            for k, blk in enumerate(parts):
                for x in blk:
                    W[x] = k
            # `Cross` depends only on the labelling, not on f: compute it once
            # per partition, and skip the whole partition when it holds.
            pairs = [(a, b) for a in range(G) for b in range(G)
                     if a < b and W[a] == W[b]]
            cross = None
            for (a, b) in pairs:
                for (c, d) in pairs:
                    if interleaved(a, b, c, d, G):
                        cross = ((a, b), (c, d))
                        break
                if cross:
                    break
            if cross is not None:
                nskipcross += 1
                continue
            for f in label_preserving_fns(parts, G):
                if all(f[x] == x for x in range(G)):
                    continue
                ncands += 1
                theta = [f[nextp(x, G)] for x in range(G)]
                if not is_G_cycle(theta, G):
                    continue
                ncyc += 1
                cex = (G, list(parts), f, list(W))
                break
            if cex:
                break
        print("G = %2d : partitions (all classes <= 2) %7d ; already crossed %7d ;"
              " remaining nontrivial label-preserving f %8d ; of those f.rho a G-cycle %6d"
              % (G, nparts, nskipcross, ncands, ncyc))
        if cex:
            total_cex += 1
            print("  COUNTEREXAMPLE: G=%d parts=%s f=%s W=%s" % cex)
    print("counterexamples: %d" % total_cex)
    return 1 if total_cex else 0


if __name__ == "__main__":
    sys.exit(main())
