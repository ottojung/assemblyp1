from collections import Counter
from itertools import product
from math import prod
S="AAABBB"; E=("AA","AB","BB","BA")
B=((2,1,2,1),(1,1,3,1),(3,1,1,1),(1,2,1,2))
def windows(s): return [s[i]+s[(i+1)%len(s)] for i in range(len(s))]
def spectrum(s):
 c=Counter(windows(s)); return tuple(c[e] for e in E)
def score(b,x): return prod(a**n for a,n in zip(b,x))
F={(a,k,b,k) for a in range(1,7) for b in range(1,7) for k in range(1,7) if a+b+2*k==6}
W=["".join(z) for z in product("AB",repeat=6)]
assert F==set(B)=={spectrum(w) for w in W if all(spectrum(w))}
for x,starts,want,winners in [
 ((2,1,2,1),(0,1,2,3,4,5),(16,9,9,4),{0}),
 ((1,1,1,1),(0,2,4,5),(4,3,3,4),{0,3}),
 ((1,2,1,2),(0,2,2,4,5,5),(4,3,3,16),{3})]:
 assert tuple(Counter(windows(S)[i] for i in starts)[e] for e in E)==x
 assert {((i+d)%6) for i in starts for d in range(2)}==set(range(6))
 scores=tuple(score(b,x) for b in B)
 assert scores==want
 assert {i for i,s in enumerate(scores) if s==max(scores)}==winners
 assert max(score(spectrum(w),x) for w in W)==max(scores)
print("ok: 64 genomes, 4 feasible spectra, 3 complete-support covered samples")

assert score(B[2],(2,0,1,0))==9
assert score(B[0],(2,0,1,0))==8
