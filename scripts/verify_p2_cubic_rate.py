#!/usr/bin/env python3
"""Exact arithmetic checks for the primitive-P2 cubic Hellinger gap.

All integer count profiles of dimension 5 with each count 0,1,2 are
enumerated. This validates the new arithmetic bound independently
of the proof, not the existence/realizability of any particular genome.
"""
from fractions import Fraction
from itertools import product

VECTORS = [c for c in product(range(3), repeat=5) if sum(c) > 0]

def verify(c,d):
    G,H = sum(c),sum(d)
    p=tuple(Fraction(v,G) for v in c)
    q=tuple(Fraction(v,H) for v in d)
    if p==q:
        return False
    w=next(i for i in range(5) if p[i]!=q[i])
    delta=abs(p[w]-q[w])
    assert delta >= Fraction(1,G*H)
    assert 0 < p[w]+q[w] <= Fraction(2,G)+Fraction(2,H)
    # Hellinger >= coordinate gap >= this rational expression.
    rational_coordinate_lower=delta*delta/(4*(p[w]+q[w]))
    assert rational_coordinate_lower >= Fraction(1,8*G*H*(G+H))
    B=max(G,H)
    assert Fraction(1,8*G*H*(G+H)) >= Fraction(1,16*B**3)
    return True

if __name__=="__main__":
    nonidentical=0
    for c in VECTORS:
        for d in VECTORS:
            nonidentical += bool(verify(c,d))
    print(f"Validated {nonidentical} distinct-law pairs out of "
          f"{len(VECTORS)**2} ordered nonzero count-profile pairs.")
    print("Cubic Hellinger-gap arithmetic: PASS")
