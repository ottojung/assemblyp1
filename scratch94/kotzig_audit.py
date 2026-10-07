"""Audit the classical Kotzig transposition descent in the repo's own language.

Objects mirror AssemblyP1/BBTEulerian.lean and BBTLadder.lean exactly:

  G, L, S : word of length G
  vtx(x)  = the length-(L-1) window at start x           (BBTEulerian)
  nextPos = the truth successor                           (BBTChords)
  prevPos = theta truth predecessor
  Sigma   : a candidate-to-truth start map (Fin G ~> Fin G)
  theta x = Sigma (nextPos (Sigma.symm x))   -- the traversal successor
  traverses: vtx (Sigma (nextPos i)) = vtx (nextPos (Sigma i))   for all i
  single   : (theta^[n] origin) pairwise distinct for n : Fin G
  AltF q   = theta (prevPos q)
  P2 / primitivity as in AssemblyP1/P2.lean

W := supp(AltF) = { x : theta x != nextPos x }, a set of *positions*.
rho := nextPos^-1 . theta, so supp rho = W and theta = nextPos . rho.
"""

import itertools
from math import gcd

def cyc(S, G, i):
    return S[i % G]

def win(S, G, L, r):
    return tuple(cyc(S, G, r + d) for d in range(L))

def vtx(S, G, L, r):
    return win(S, G, L - 1, r)

def rot(G, k, x):
    return (x + k) % G

def is_primitive(S, G):
    for s in range(1, G):
        if all(S[i] == S[(i + s) % G] for i in range(G)):
            return False
    return True

def agree(S, G, e, a, b):
    return all(S[(a + d) % G] == S[(b + d) % G] for d in range(e))

def preceding(S, G, a):
    return S[(a - 1) % G]

def following(S, G, e, a):
    return S[(a + e) % G]

def is_repeat(S, G, e, a, b):
    return (1 <= e < G and a != b and agree(S, G, e, a, b)
            and preceding(S, G, a) != preceding(S, G, b)
            and following(S, G, e, a) != following(S, G, e, b))

def is_triple(S, G, e, a, b, c):
    return (1 <= e < G and len({a, b, c}) == 3 and agree(S, G, e, a, b)
            and agree(S, G, e, a, c) and agree(S, G, e, b, c)
            and not (preceding(S, G, a) == preceding(S, G, b) == preceding(S, G, c))
            and not (following(S, G, e, a) == following(S, G, e, b) == following(S, G, e, c)))

def interleaved(S, G, a, b, c, d):
    # exactly one of c,d lies strictly on the open clockwise arc a->b
    def in_arc(p, a, b):
        return 0 < (p - a) % G < (b - a) % G
    return len({a, b, c, d}) == 4 and (in_arc(c, a, b) != in_arc(d, a, b))

def P2(S, G, L):
    for e in range(1, G):
        for a, b, c in itertools.permutations(range(G), 3):
            if is_triple(S, G, e, a, b, c) and not (e < L - 1):
                return False
    for e1 in range(1, G):
        for e2 in range(1, G):
            for a, b in itertools.permutations(range(G), 2):
                if not is_repeat(S, G, e1, a, b):
                    continue
                for c, d in itertools.permutations(range(G), 2):
                    if not is_repeat(S, G, e2, c, d):
                        continue
                    if interleaved(S, G, a, b, c, d):
                        if not (e1 <= L - 2 or e2 <= L - 2):
                            return False
    return True

def all_perms(G):
    return itertools.permutations(range(G))

def analyse(S, G, L):
    """Return records for every EulerianCycle Sigma (up to nothing: all of them)."""
    out = []
    nxt = lambda x: (x + 1) % G
    prv = lambda x: (x - 1) % G
    for p in all_perms(G):
        Sig = list(p)                      # Sig[i] = truth start for candidate start i
        sinv = [0] * G
        for i, s in enumerate(Sig):
            sinv[s] = i
        ok = all(vtx(S, G, L, Sig[nxt(i)]) == vtx(S, G, L, nxt(Sig[i])) for i in range(G))
        if not ok:
            continue
        theta = [Sig[nxt(sinv[x])] for x in range(G)]
        seen, x, n = set(), 0, 0
        while x not in seen:
            seen.add(x)
            x = theta[x]
            n += 1
        if n != G:                          # `single`
            continue
        altf = [theta[prv(x)] for x in range(G)]
        W = [x for x in range(G) if theta[x] != nxt(x)]
        rho = [prv(theta[x]) for x in range(G)]   # nextPos^-1 . theta
        assert sorted(x for x in range(G) if rho[x] != x) == W
        inv2 = all(altf[altf[x]] == x for x in range(G))
        # involution orbit count
        t = sum(1 for x in range(G) if altf[x] > x)
        out.append(dict(Sigma=tuple(Sig), theta=tuple(theta), W=tuple(W),
                        altf=tuple(altf), involution=inv2, t=t))
    return out

def ncycles(G, perm):
    seen, c = set(), 0
    for x in range(G):
        if x in seen:
            continue
        c += 1
        y = x
        while y not in seen:
            seen.add(y)
            y = perm[y]
    return c

def run():
    print("G  L  |W| distribution over all one-cycle Eulerian traversals (P2 + primitive truths)")
    for G in range(4, 9):
        for L in range(2, min(G, 4) + 1):
            dist, bad_inv, alt_ok = {}, 0, 0
            words = itertools.product('AB', repeat=G)
            for S in words:
                if not is_primitive(list(S), G):
                    continue
                if not P2(list(S), G, L):
                    continue
                alt_ok += 1
                for rec in analyse(list(S), G, L):
                    d = dist.setdefault(len(rec['W']), [0, 0])
                    d[0] += 1
                    if rec['W']:
                        if not rec['involution']:
                            bad_inv += 1
                        d[1] += 1
            if alt_ok == 0:
                continue
            tot = sum(v[0] for v in dist.values())
            nz = sum(v[0] for k, v in dist.items() if k != 0)
            print(f"{G} {L}  P2prim={alt_ok:5d}  traversals={tot:5d}  "
                  f"nonzero={nz:5d}  |W|dist={ {k: v[0] for k, v in sorted(dist.items())} }  "
                  f"non-involution={bad_inv}")

if __name__ == '__main__':
    run()
