#!/usr/bin/env python3
"""Independent bounded audit of physical reversal on tagged overlaps (#261).

This checks overlap-anti-morphism and finite unordered orbit counts only.
It does NOT characterize physical edge-indexed flows or genome spellings.
"""
from itertools import product

def rc(word):
    return tuple(1-b for b in reversed(word))

def pre(word, k):
    return word[:k]

def suf(word, k):
    return word[max(0,len(word)-k):]

def flip_pair(p):
    x,y = p
    return (1-y,1-x)

def orbit_pair(p):
    return frozenset([p,flip_pair(p)])

pairs = list(product((0,1),repeat=2))
orbits = {orbit_pair(p) for p in pairs}
assert len(orbits) == 3
assert frozenset(((0,0),(1,1))) in orbits
assert frozenset(((0,1),)) in orbits
assert frozenset(((1,0),)) in orbits
assert all(flip_pair(flip_pair(p))==p for p in pairs)

words = [bits for n in range(6) for bits in product((0,1), repeat=n)]
tests=0
for u in words:
    for v in words:
        for k in range(8):
            a=(suf(u,k)==pre(v,k))
            b=(suf(rc(v),k)==pre(rc(u),k))
            assert a==b, (u,v,k)
            tests+=1

# Keeping the overlap length in the identity preserves physically parallel
# overlap edges of different lengths, even with identical strand-end classes.
def edge_rev(edge):
    u,v,k=edge
    return ((v[0],1-v[1]),(u[0],1-u[1]),k)
assert all(edge_rev(edge_rev(((0,a),(1,b),k)))==((0,a),(1,b),k)
           for a,b,k in product((0,1),(0,1),range(8)))
print(f"PASS: {len(orbits)} unordered ATAT orientation orbits")
print(f"PASS: {tests} reverse-complement overlap equivalences")
print("PASS: edge reversal involutive, overlap lengths preserved")
