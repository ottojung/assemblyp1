#!/usr/bin/env python3
"""Mirror of the Section62FlowGenomeSeparation smallest counterexample (G=2, L=2).

S0 = 00 (windows [00,00]), S1 = 11 (windows [11,11]).
rep2 maps 11 -> 00 (RC class {00,11} -> 00).
classCount vectors are equal; exact uniform-start oriented likelihoods of
sample x0=[00] are 1 vs 0. Hence no throughput-factoring score equals it.
"""
from fractions import Fraction

def windows(genome, L):
    G = len(genome)
    return [tuple(genome[(s + k) % G] for k in range(L)) for s in range(G)]

def rep2(w):
    return (0, 0) if w == (1, 1) else w

def class_count(genome, L):
    # count over RC classes keyed by representative; only classes present shown
    from collections import Counter
    c = Counter(rep2(w) for w in windows(genome, L))
    return dict(c)

def mult(genome, L, w):
    return sum(1 for u in windows(genome, L) if u == w)

def likelihood(genome, L, sample):
    G = len(genome)
    p = Fraction(1, 1)
    for w in sample:
        p *= Fraction(mult(genome, L, w), G)
    return p

S0 = [0, 0]
S1 = [1, 1]
L = 2
x0 = [(0, 0)]
c0, c1 = class_count(S0, L), class_count(S1, L)
l0, l1 = likelihood(S0, L, x0), likelihood(S1, L, x0)
print("classCount S0:", c0)
print("classCount S1:", c1)
print("likelihood S0:", l0)
print("likelihood S1:", l1)
assert c0 == c1, "visit vectors must collide"
assert (l0, l1) == (Fraction(1, 1), Fraction(0, 1)), "must be 1 vs 0"
# conditional uniform-start window-product invariance under equal multisets:
from collections import Counter
assert Counter(windows(S0, L)) != Counter(windows(S1, L))  # oriented multisets differ
# but the spelled-word window equality DOES imply equal products (trivially):
M = Counter(windows([0, 0, 1], 2))
assert likelihood([0, 0, 1], 2, [(0, 0)]) == Fraction(M[(0, 0)], 3)
print("ML-likelihood boundary verified: equal throughput, likelihoods 1 vs 0; no throughput-factoring score equals exact oriented likelihood.")
