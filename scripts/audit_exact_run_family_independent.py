#!/usr/bin/env python3
"""
Independent audit of the same-length run-shift family

    S(p,q) = A^p C^q ,   D(p,q) = A^(p+1) C^(q-1)      (|S| = |D| = p+q)

for the fixed-length exact Medvedev-Brudno multinomial objective together with
the source hypothesis I_s (coverage; every maximal triple repeat all-bridged;
every interleaved maximal-repeat pair bridged).

Written independently of scripts/verify_exact_run_family.py and of the
reasoning in mathematics/exact-multinomial-run-shift-family.md.  Two upgrades
over that certificate:

  * the slice likelihood ratio is checked by evaluating the full exact
    multinomial probability (n!/(prod x_i!) * prod (d_i/N)^(x_i)) under both
    candidates, not by the ratio identity, for L = 2..40;
  * the complete support search is extended to every G = p+q <= 12 (the
    in-repo certificate stops at p+q <= 9).

It also checks the corrected spectra description of the slice: D drops exactly
the L-1 S-windows A^a C^2 A^(L-2-a), a = 0..L-2.

Usage: python3 scripts/audit_exact_run_family_independent.py [Gmax]
"""
from fractions import Fraction
from itertools import combinations
from collections import defaultdict
from math import factorial
import sys


def win(seq, t, ell):
    G = len(seq)
    return tuple(seq[(t + j) % G] for j in range(ell))


def spectrum(seq, L):
    G = len(seq)
    d = defaultdict(int)
    for i in range(G):
        d[win(seq, i, L)] += 1
    return dict(d)


def covered(seq, starts, L):
    G = len(seq)
    c = set()
    for r in starts:
        c.update((r + o) % G for o in range(L))
    return c == set(range(G))


def maximal_pairs(seq):
    G = len(seq)
    out = []
    for ell in range(1, G):
        g = defaultdict(list)
        for i in range(G):
            g[win(seq, i, ell)].append(i)
        for ts in g.values():
            for a, b in combinations(ts, 2):
                if seq[(a - 1) % G] != seq[(b - 1) % G] and \
                   seq[(a + ell) % G] != seq[(b + ell) % G]:
                    out.append((ell, (a, b)))
    return out


def triple_repeats(seq):
    G = len(seq)
    out = []
    for ell in range(1, G):
        g = defaultdict(list)
        for i in range(G):
            g[win(seq, i, ell)].append(i)
        for ts in g.values():
            for tri in combinations(ts, 3):
                if len({seq[(t - 1) % G] for t in tri}) > 1 and \
                   len({seq[(t + ell) % G] for t in tri}) > 1:
                    out.append((ell, tri))
    return out


def interleaved(seq):
    reps = maximal_pairs(seq)
    out = []
    for i in range(len(reps)):
        for j in range(i + 1, len(reps)):
            e1, p1 = reps[i]
            e2, p2 = reps[j]
            four = sorted(set(p1) | set(p2))
            if len(four) != 4:
                continue
            lab = [0 if x in p1 else 1 for x in four]
            if lab in ([0, 1, 0, 1], [1, 0, 1, 0]):
                out.append((reps[i], reps[j]))
    return out


def read_windows(starts, L, G):
    return [frozenset((r + o) % G for o in range(L)) for r in starts]


def copy_bridged(wins, t, ell, G):
    left, right = (t - 1) % G, (t + ell) % G
    return any(left in x and right in x for x in wins)


def in_I_s(seq, starts, L, tris, inters, G):
    if not covered(seq, starts, L):
        return False
    wins = read_windows(starts, L, G)
    for ell, tri in tris:
        if not all(copy_bridged(wins, t, ell, G) for t in tri):
            return False
    for (e1, p1), (e2, p2) in inters:
        if not (any(copy_bridged(wins, t, e1, G) for t in p1) or
                any(copy_bridged(wins, t, e2, G) for t in p2)):
            return False
    return True


def exact_likelihood(seq, obs):
    """Full exact multinomial P[x] for candidate `seq`; obs: dict word -> count."""
    n = sum(obs.values())
    L = len(next(iter(obs)))
    d = spectrum(seq, L)
    G = len(seq)
    p = Fraction(factorial(n), 1)
    for c in obs.values():
        p /= factorial(c)
    for word, c in obs.items():
        p *= Fraction(d.get(word, 0), G) ** c
    return p


def slice_audit(hi=40):
    print(f"(A) slice S=A^L C^2, D=A^(L+1) C ; direct exact multinomial, L=2..{hi}")
    x, ok_all = 4, True
    for L in range(2, hi + 1):
        S, D, G = "A" * L + "C" * 2, "A" * (L + 1) + "C", L + 2
        starts = [0] * x + [1, G - 1]
        obs = defaultdict(int)
        for r in starts:
            obs[win(S, r, L)] += 1
        obs = dict(obs)
        dS, dD = spectrum(S, L), spectrum(D, L)
        dropped = {z for z in dS if dD.get(z, 0) == 0}
        two_c = {tuple("A" * a + "CC" + "A" * (L - 2 - a))
                 for a in range(0, L - 1)}
        ratio = exact_likelihood(D, obs) / exact_likelihood(S, obs)
        ok = (len(S) == len(D) and in_I_s(S, starts, L, triple_repeats(S),
              interleaved(S), G) and ratio == Fraction(2) ** x and dropped == two_c)
        ok_all = ok_all and ok
        if L <= 6 or not ok:
            print(f"    L={L:2d} same={len(S)==len(D)} I_s="
                  f"{in_I_s(S, starts, L, triple_repeats(S), interleaved(S), G)} "
                  f"ratio={ratio} dropped==A^aCC A^(L-2-a):{dropped == two_c} OK={ok}")
    print(f"    ALL (A) OK: {ok_all}\n")
    return ok_all


def exhaustive(Gmax=12):
    print(f"(B) complete all-subsets search, G=p+q<={Gmax}, all L, all nonempty starts")
    hits = []
    for G in range(2, Gmax + 1):
        for p in range(1, G):
            q = G - p
            S = "A" * p + "C" * q
            D = "A" * (p + 1) + "C" * (q - 1)
            tris, inters = triple_repeats(S), interleaved(S)
            for L in range(1, G + 1):
                dS, dD = spectrum(S, L), spectrum(D, L)
                missing = {z for z in dS if dD.get(z, 0) == 0}
                if not any(dS.get(z, 0) > 0 and dD.get(z, 0) > dS[z] for z in dS):
                    continue
                for mask in range(1, 1 << G):
                    starts = [i for i in range(G) if mask >> i & 1]
                    if any(win(S, r, L) in missing for r in starts):
                        continue
                    if in_I_s(S, starts, L, tris, inters, G):
                        hits.append((p, q, L, tuple(starts)))
                        break
        print(f"    ... G={G} done, hits={len(hits)}")
    print("    hits:")
    for p, q, L, st in hits:
        print(f"      p={p} q={q} L={L} starts={st}")
    outside = [h for h in hits if not (h[1] == 2 and h[0] == h[2])]
    print(f"    outside slice q=2,p=L: {outside}\n")
    return hits


if __name__ == "__main__":
    a = slice_audit()
    b = exhaustive(int(sys.argv[1]) if len(sys.argv) > 1 else 12)
    print("Summary")
    print(f"  (A) direct multinomial slice verified L=2..40: {a}")
    print(f"  (B) hits outside q=2,p=L: "
          f"{[h for h in b if not (h[1] == 2 and h[0] == h[2])]}")
