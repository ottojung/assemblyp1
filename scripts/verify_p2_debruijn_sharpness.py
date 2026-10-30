#!/usr/bin/env python3
"""Finite exact regressions for de Bruijn primitive-P2 sharpness construction."""
from collections import Counter
from math import sqrt

def debruijn(q,k):
    a=[0]*(q*k+1)
    seq=[]
    def db(t,p):
        if t>k:
            if k%p==0: seq.extend(a[1:p+1])
        else:
            a[t]=a[t-p]
            db(t+1,p)
            for j in range(a[t-p]+1,q):
                a[t]=j
                db(t+1,t)
    db(1,1)
    assert len(seq)==q**k
    return tuple(seq)

def spectrum(word,L):
    n=len(word)
    return Counter(tuple(word[(i+j)%n] for j in range(L))
                   for i in range(n))

def check(q,k):
    G=q**k
    L=k+1
    word=debruijn(q,k)
    start=next(i for i in range(G)
               if all(word[(i+j)%G]==0 for j in range(k)))
    S=tuple(word[(start+i)%G] for i in range(G))
    D=(0,)+S
    kS=spectrum(S,k)
    kD=spectrum(D,k)
    assert len(kS)==G and all(c==1 for c in kS.values())
    assert kD==kS+Counter({(0,)*k:1})
    assert sorted(kD.values()).count(2)==1
    lS=spectrum(S,L)
    lD=spectrum(D,L)
    assert len(lS)==G and all(c==1 for c in lS.values())
    assert (0,)*L not in lS
    assert lD==lS+Counter({(0,)*L:1})
    assert len(lD)==G+1 and all(c==1 for c in lD.values())
    # These strong multiplicity properties imply primitive P2 in both.
    assert any(c==1 for c in kD.values())
    rho=sqrt(G/(G+1))
    gap=1-rho
    B=2*G
    assert 1/(64*B)-1e-12 <= gap <= 1/B+1e-12
    return G,B*gap

if __name__=="__main__":
    for q,kmax in [(2,10),(3,6),(4,4)]:
        for k in range(1,kmax+1):
            G,r=check(q,k)
            print(f"q={q} k={k}: G={G}, B*(1-rho)={r:.8f}")
    print("Primitive-P2 de Bruijn matching-upper-family: PASS")
