#!/usr/bin/env python3
"""Exact-rational check for the #265 finite-read arc figure data.

Witness: circular genomes S=AAC (truth) vs D=AAAC, read length L=2,
uniform-start error-free reads. Read laws:
  p_S: AA 1/3, AC 1/3, CA 1/3, CC 0
  p_D: AA 1/2, AC 1/4, CA 1/4, CC 0
Checks:
  - succ(1) = 2/3, succ(2) = 4/9 (strict exact-ML maximizer probability).
  - Concrete 2-read sample [AA, AA]: L_D > L_S (finite-sample reversal).
  - Concrete 1-read sample [AC]: L_S > L_D (truth wins).
All with exact Fractions; no floating point.
"""
from fractions import Fraction as Q

pS = {"AA": Q(1,3), "AC": Q(1,3), "CA": Q(1,3), "CC": Q(0)}
pD = {"AA": Q(1,2), "AC": Q(1,4), "CA": Q(1,4), "CC": Q(0)}

def lik(law, reads):
    r = Q(1)
    for x in reads:
        r *= law[x]
    return r

def succ(n):
    from itertools import product
    tot = Q(0)
    for tup in product(["AA","AC","CA","CC"], repeat=n):
        pr = lik(pS, tup)
        if pr == 0:
            continue
        if lik(pS, tup) > lik(pD, tup):
            tot += pr
    return tot

s1 = succ(1); s2 = succ(2)
assert s1 == Q(2,3), s1
assert s2 == Q(4,9), s2
assert s1 > s2

# Figure samples
assert lik(pS, ["AC"]) == Q(1,3) and lik(pD, ["AC"]) == Q(1,4)
assert lik(pS, ["AC"]) > lik(pD, ["AC"])
assert lik(pS, ["AA","AA"]) == Q(1,9) and lik(pD, ["AA","AA"]) == Q(1,4)
assert lik(pD, ["AA","AA"]) > lik(pS, ["AA","AA"])

print(f"succ(1)={s1} succ(2)={s2} reversal-2-read sample [AA,AA]: Ls=1/9 < Ld=1/4 OK")
