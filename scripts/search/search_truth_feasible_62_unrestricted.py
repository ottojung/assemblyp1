import sys
from itertools import product, combinations

def analyze(n,L,g):
    full=(1<<n)-1
    def gwin(e,r): return tuple(g[(r+i)%n] for i in range(e))
    def cyc(i): return g[i%n]
    BM={}
    for e in range(1,n):
        m=[0]*n
        for t in range(n):
            for r in range(n):
                if ((t-1-r)%n)<L and ((t+e-r)%n)<L: m[t]|=1<<r
        BM[e]=m
    def IsRepeat(e,a,b):
        if not(1<=e<n) or a==b: return False
        if gwin(e,a)!=gwin(e,b): return False
        return cyc(a+n-1)!=cyc(b+n-1) and cyc(a+e)!=cyc(b+e)
    def IsTriple(e,a,b,c):
        if not(1<=e<n) or len({a,b,c})<3: return False
        w=gwin(e,a)
        if gwin(e,b)!=w or gwin(e,c)!=w: return False
        pa=[cyc(x+n-1) for x in (a,b,c)]; fo=[cyc(x+e) for x in (a,b,c)]
        return not(pa[0]==pa[1]==pa[2]) and not(fo[0]==fo[1]==fo[2])
    def IOA(a,b,p): return 0<(p-a)%n<(b-a)%n
    def Inter(a,b,c,d):
        if len({a,b,c,d})<4: return False
        return IOA(a,b,c)==(not IOA(a,b,d))
    reps=[];trips=[]
    for e in range(1,n):
        for a,b in combinations(range(n),2):
            if IsRepeat(e,a,b): reps.append((e,a,b))
        for a,b,c in combinations(range(n),3):
            if IsTriple(e,a,b,c): trips.append((e,a,b,c))
    inter=[(e1,e2,a,b,c,d) for (e1,a,b) in reps for (e2,c,d) in reps if Inter(a,b,c,d)]
    covm=[0]*n
    for r in range(n):
        for i in range(L): covm[r]|=1<<((r+i)%n)
    def Ifeas(Rm):
        acc=0
        for r in range(n):
            if Rm>>r&1: acc|=covm[r]
        if acc!=full: return False
        for (e,a,b,c) in trips:
            for t in (a,b,c):
                if not (BM[e][t]&Rm): return False
        for (e1,e2,a,b,c,d) in inter:
            if not (BM[e1][a]&Rm or BM[e1][b]&Rm or BM[e2][c]&Rm or BM[e2][d]&Rm): return False
        return True
    d={}
    for r in range(n):
        w=gwin(L,r); d[w]=d.get(w,0)+1
    return Ifeas,d,gwin,trips

def run(NMAX,LMAX,alpha):
    for n in range(4,NMAX+1):
        genomes=[list(t) for t in product(range(alpha),repeat=n)]
        for L in range(2,min(n,LMAX)+1):
            info={}
            for g in genomes: info[tuple(g)]=analyze(n,L,g)
            for g in genomes:
                Ifeas,d,gwin,trips=info[tuple(g)]
                supp=set(d)
                # truth-feasible: exists R hitting all types and covering
                feasR=None
                for Rs in range(1,1<<n):
                    R=[i for i in range(n) if Rs>>i&1]
                    if {gwin(L,r) for r in R}!=supp: continue
                    if Ifeas(Rs): feasR=R; break
                if feasR is None: continue
                for c in genomes:
                    dc=info[tuple(c)][1]
                    if set(dc)!=supp: continue
                    # is d_c(w) > d_S(w) for some w on the support?
                    if any(dc[w]>d[w] for w in supp):
                        return ("REFUTES",n,L,''.join('AB'[x] for x in g),feasR,
                                ''.join('AB'[x] for x in c),
                                {w:d[w] for w in supp},{w:dc[w] for w in supp},
                                [(e,a,b,c2) for (e,a,b,c2) in trips if e>=L-1])
            print("done n=%d L=%d"%(n,L),flush=True)
    return None
print(run(int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3])))
