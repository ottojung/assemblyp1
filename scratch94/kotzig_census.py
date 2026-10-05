"""Decisive census for the Kotzig/Ukkonen/Pevzner transposition descent.

Exact translation into repo objects (AssemblyP1/BBTEulerian.lean, BBTLadder.lean):

  Succ hG Sig x = Sig (nextPos hG (Sig.symm x))          -- BBTEulerian
  AltF hG Sig q = Succ hG Sig (prevPos hG q)             -- BBTUniqueEulerian
  ==> AltF (nextPos q) = Succ q                          -- AltF_succ
  ==> AltF = Succ . prevPos, and Succ = AltF . nextPos

A listing Sig : Fin G ~> Fin G is an alternative Eulerian traversal iff
  traverses : vtx (Sig (nextPos i)) = vtx (nextPos (Sig i))  for all i.
`single` is a tautology for EVERY Sig (Issue94TW5Single.succ_visitsAll), so the
genuine constraint is `traverses` + AltF_vtx + AltF_sq (P2 + primitive).

W := supp AltF = { q : AltF q != q }  (positions where the successor differs).
Under P2 + primitivity AltF is an involution, so W splits into t transposition
pairs, |W| = 2t: the "2-in / 2-out" pairing.  THIS IS THE OBJECTIVE DESCENT.

Kotzig/Ukkonen/Pevzner step, in this language.  Deleting one transposition pair
(a b) of AltF means AltF' = AltF . (a b) (the factor cancels, |W'| = |W| - 2),
so Succ' = AltF' . nextPos.  A listing realising Succ' exists iff Succ' is a
G-cycle, since Sig ~> Succ Sig ^-1 with Sig = a "shift-conjugation": precisely,
Succ hG Sig = Sig . nextPos . Sig.symm, so Succ is in the CONJUGACY CLASS of
nextPos, i.e. Succ must be a G-cycle.

  C1  Succ' is a G-cycle  <=>  |W'| = 0  mod 4   (parity of the sign)
  C2  |W| != 0  =>  |W| >= 4
  C3  deleting ONE factor NEVER leaves a G-cycle  ==> the classical
      "one transposition reducing |W| by 2" step is UNAVAILABLE
  C4  deleting a PAIR of factors does leave a G-cycle (t >= 4), so the real step
      reduces |W| by 4
  C5  at t = 2 (|W| = 4, the terminal case) the two chords INTERLEAVE
  C6  and is the terminal case reachable from a P2 primitive truth at all?
"""

import itertools
from collections import Counter

def cyc(S,G,i): return S[i % G]
def win(S,G,L,r): return tuple(cyc(S,G,r+d) for d in range(L))
def vtx(S,G,L,r): return win(S,G,L-1,r)
def nxt(x,G): return (x+1) % G
def prv(x,G): return (x-1) % G
def ncycles(p):
    seen,c = set(),0
    for x in range(len(p)):
        if x in seen: continue
        c+=1; y=x
        while y not in seen: seen.add(y); y=p[y]
    return c
def comp(f,g): return [f[g[x]] for x in range(len(f))]
def is_primitive(S,G):
    return not any(all(S[i]==S[(i+s)%G] for i in range(G)) for s in range(1,G))
def agree(S,G,e,a,b): return all(S[(a+d)%G]==S[(b+d)%G] for d in range(e))
def is_repeat(S,G,e,a,b):
    return (1<=e<G and a!=b and agree(S,G,e,a,b) and S[(a-1)%G]!=S[(b-1)%G]
            and S[(a+e)%G]!=S[(b+e)%G])
def is_triple(S,G,e,a,b,c):
    return (1<=e<G and len({a,b,c})==3 and agree(S,G,e,a,b) and agree(S,G,e,a,c)
            and agree(S,G,e,b,c) and len({S[(a-1)%G],S[(b-1)%G],S[(c-1)%G]})>1
            and len({S[(a+e)%G],S[(b+e)%G],S[(c+e)%G]})>1)
def in_arc(p,a,b,G): return 0<(p-a)%G<(b-a)%G
def interleaved(S,G,a,b,c,d):
    return len({a,b,c,d})==4 and (in_arc(c,a,b,G)!=in_arc(d,a,b,G))
def P2(S,G,L):
    for e in range(1,G):
        for a,b,c in itertools.permutations(range(G),3):
            if is_triple(S,G,e,a,b,c) and not e<L-1: return False
    for e1 in range(1,G):
        for a,b in itertools.permutations(range(G),2):
            if not is_repeat(S,G,e1,a,b): continue
            for e2 in range(1,G):
                for c,d in itertools.permutations(range(G),2):
                    if is_repeat(S,G,e2,c,d) and interleaved(S,G,a,b,c,d) \
                       and not (e1<=L-2 or e2<=L-2): return False
    return True
def factors(p):
    assert all(p[p[x]]==x for x in range(len(p)))
    return [(x,p[x]) for x in range(len(p)) if x<p[x]]
def swap(p,a,b):
    q=list(p); q[a],q[b]=q[b],q[a]; return q

def traversals(S,G,L):
    """All Sig with `traverses`, plus the derived AltF, W, Succ, and badness."""
    out=[]
    for p in itertools.permutations(range(G)):
        Sig=list(p); sinv=[0]*G
        for i,s in enumerate(Sig): sinv[s]=i
        if not all(vtx(S,G,L,Sig[nxt(i,G)])==vtx(S,G,L,nxt(Sig[i],G)) for i in range(G)):
            continue
        succ=[Sig[nxt(sinv[x],G)] for x in range(G)]
        altf=[succ[prv(x,G)] for x in range(G)]
        W=[x for x in range(G) if altf[x]!=x]
        # VertexCycleEq Sig (refl): vtx (Sig i) = vtx (rotAdd k (Sig i)) for some k
        vc=False
        for k in range(G):
            if all(vtx(S,G,L,Sig[i])==vtx(S,G,L,(Sig[i]+k)%G) for i in range(G)):
                vc=True; break
        out.append(dict(altf=tuple(altf),W=tuple(W),succ=tuple(succ),good=vc,
                        inv=all(altf[altf[x]]==x for x in range(G))))
    return out

def run():
    print("C1/C2/C6 : |W| distribution and t parity, over P2 primitive truths")
    print("C6       : are the |W|=4 terminal cases GOOD (same vertex cycle)?")
    dist=Counter(); tpar=Counter(); good4=Counter(); ntr=0
    for G in range(4,9):
        for L in range(2,min(G,4)+1):
            for S in itertools.product('AB',repeat=G):
                S=list(S)
                if not is_primitive(S,G) or not P2(S,G,L): continue
                ntr+=1
                for r in traversals(S,G,L):
                    dist[(G,L,len(r['W']))]+=1
                    tpar[(G,L,len(r['W'])//2)]+=1
                    if len(r['W'])==4: good4[r['good']]+=1
    bywl=Counter()
    for (G,L,k),v in dist.items(): bywl[k]+=v
    print(f"  truths: {ntr}")
    print(f"  |W| totals: {dict(sorted(bywl.items()))}")
    bad_t=[(k,v) for k,v in sorted(tpar.items()) if k[2]%2]
    print(f"  ODD t (= |W|/2) instances: {bad_t}")
    print(f"  |W|=4 cases: good={good4[True]} bad={good4[False]}")
    print()
    print("C3 : deleting ONE transposition factor of AltF never leaves a G-cycle")
    tot=0; kept=0; examples=[]
    for G in range(4,9):
        for L in range(2,min(G,4)+1):
            for S in itertools.product('AB',repeat=G):
                S=list(S)
                if not is_primitive(S,G) or not P2(S,G,L): continue
                for r in traversals(S,G,L):
                    if not r['W'] or not r['inv']: continue
                    for (a,b) in factors(list(r['altf'])):
                        tot+=1
                        a2=swap(list(r['altf']),a,b)
                        assert len(factors(a2))==len(r['W'])//2-1
                        if ncycles(comp(a2,[nxt(x,G) for x in range(G)]))==1:
                            kept+=1; examples.append((G,L,''.join(S),(a,b)))
    print(f"  (traversal, factor) deletion attempts: {tot}; still a G-cycle: {kept}")
    if examples: print(f"  counterexamples: {examples[:5]}")
    print()
    print("C4 : deleting a PAIR of factors does leave a G-cycle")
    tot=0; none_=0; bad=[]
    for G in range(4,9):
        for L in range(2,min(G,4)+1):
            for S in itertools.product('AB',repeat=G):
                S=list(S)
                if not is_primitive(S,G) or not P2(S,G,L): continue
                for r in traversals(S,G,L):
                    F=factors(list(r['altf']))
                    if len(F)<4: continue
                    tot+=1; ok=False
                    for i,j in itertools.combinations(range(len(F)),2):
                        a2=swap(swap(list(r['altf']),*F[i]),*F[j])
                        if ncycles(comp(a2,[nxt(x,G) for x in range(G)]))==1:
                            ok=True; break
                    if not ok: none_+=1; bad.append((G,L,''.join(S)))
    print(f"  traversals with t>=4: {tot}; no deletable pair: {none_} {bad[:3]}")
    print()
    print("C5 : at t=2 the two chords interleave")
    tot=0; nonil=0; wit=[]
    for G in range(4,10):
        for L in range(2,min(G,4)+1):
            for S in itertools.product('AB',repeat=G):
                S=list(S)
                if not is_primitive(S,G) or not P2(S,G,L): continue
                for r in traversals(S,G,L):
                    F=factors(list(r['altf']))
                    if len(F)!=2: continue
                    tot+=1
                    (a,b),(c,d)=F
                    if not interleaved(S,G,a,b,c,d): nonil+=1; wit.append((G,L,''.join(S),(a,b),(c,d)))
    print(f"  t=2 traversals: {tot}; chords NOT interleaving: {nonil} {wit[:3]}")

if __name__=='__main__':
    run()
