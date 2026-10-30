#!/usr/bin/env python3
"""Independent finite check of the P2 linear Hellinger-gap arithmetic.

For finite nonzero count profiles with multiplicities at most two, verify:
(1) distinct normalized spectra have a zero/nonzero mismatch or at least
two distinct positive integer multiplicity ratios;
(2) their Hellinger affinity gap exceeds 1/(64*max(total counts)).
The proof for any number of word types is in docs/primitive-p2-linear-rate.md.
These profiles are NOT assumed to all be realizable circular genomes.
"""
from fractions import Fraction
from itertools import product
from math import sqrt, fsum

def test_profile_pair(c, d):
    G, H = sum(c), sum(d)
    if all(c_i*H == d_i*G for c_i,d_i in zip(c,d)):
        return False
    supports_match = all((x>0) == (y>0) for x,y in zip(c,d))
    if supports_match:
        distinct_ratios = {Fraction(y,x) for x,y in zip(c,d) if x}
        assert len(distinct_ratios) >= 2, (c,d)
        assert distinct_ratios <= {Fraction(1,2),Fraction(1),Fraction(2)}
    rho = fsum(sqrt(x*y) for x,y in zip(c,d))/sqrt(G*H)
    B = max(G,H)
    gap = 1-rho
    assert gap >= 1/(64*B)-1e-12,(c,d,gap,1/(64*B))
    return True

def check(dim):
    nonzero = [c for c in product(range(3),repeat=dim) if sum(c)]
    checked = 0
    minimum = (float("inf"),None)
    for c in nonzero:
        for d in nonzero:
            if test_profile_pair(c,d):
                checked += 1
                G,H=sum(c),sum(d)
                gap = 1 - fsum(sqrt(x*y) for x,y in zip(c,d))/sqrt(G*H)
                if gap * max(G,H) < minimum[0]:
                    minimum = (gap*max(G,H),(c,d))
    return checked,minimum

if __name__ == "__main__":
    n,(val,pair)=check(5)
    print(f"{n} distinct-law profile pairs verified in dimension 5.")
    print(f"Smallest B*(1-rho): {val:.9f}; witness {pair}")
    print("P2 linear Hellinger separation: PASS")
