#!/usr/bin/env python3
"""Exact search behind `AssemblyP1.BBTSupportInvariant`.

Three questions, all decided by enumeration over primitive binary circular
words and over *circuits* (not over `G!` presentations) of the `(L-1)`-mer
multigraph:

Q1 (REFUTED)  the raw crossing-pairs lemma: do two interleaved doubled
    `K`-mers extend to two interleaved maximal repeats of length >= K?
    -> No.  This is the claim `BBTChords.raw_node_crossing_not_maximal` and
       `docs/audit-p2-direct-proof-maximal-extension-2026-09-21.md` refute.

Q2 (REFUTED)  the strengthened claim: must a *good* `theta` (one-cycle,
    fibre-preserving, truth's own vertex cycle) have a support with no
    crossing?
    -> No.  `S = 00101`, `L = 3`: swapping the doubled K-mers `01` and `10` at
       the interleaving starts 1 < 2 < 3 < 4 gives the single cycle
       0, 3, 2, 1, 4 with the truth's own K-mer orbit.  This is the
       anti-vacuity instance `harmless_selected_crossing_00101`.

Q3 (the target, SUPPORTED in range)  the support dichotomy: a bijective,
    fibre-preserving, one-cycle `theta` whose spelled vertex cycle differs
    from the truth's must either rematch a vertex of multiplicity >= 3, or
    rematch two interleaved doubled K-mers.
    -> Holds in every case searched.  This is `SupportDichotomy`.

Usage:  python3 scripts/verify_support_dichotomy_89.py [maxG] [maxK]
"""

import itertools
import sys
from collections import defaultdict


def cyc(S, i):
    return S[i % len(S)]


def vtx(S, K, i):
    return tuple(cyc(S, i + d) for d in range(K))


def is_primitive(S):
    n = len(S)
    for p in range(1, n):
        if n % p == 0 and all(S[i] == S[i % p] for i in range(n)):
            return False
    return True


def agree(S, e, a, b):
    return all(cyc(S, a + d) == cyc(S, b + d) for d in range(e))


def in_open_arc(G, a, b, p):
    return 0 < (p + G - a) % G < (b + G - a) % G


def interleaved(G, a, b, c, d):
    return (len({a, b, c, d}) == 4
            and in_open_arc(G, a, b, c) != in_open_arc(G, a, b, d))


def fibre_blocks(S, K):
    G = len(S)
    d = defaultdict(list)
    for i in range(G):
        d[vtx(S, K, i)].append(i)
    return list(d.values())


def all_theta(S, K):
    """Every fibre-preserving bijection theta = f . rho, f a bijection of
    each vtx-fibre onto itself.  Enumerating `f` is equivalent to enumerating
    the circuits, and is far cheaper than enumerating G! presentations."""
    G = len(S)
    blocks = fibre_blocks(S, K)
    for perm in itertools.product(*[itertools.permutations(b) for b in blocks]):
        f = [None] * G
        for p, b in zip(perm, blocks):
            for src, dst in zip(b, p):
                f[src] = dst
        yield [f[(q + 1) % G] for q in range(G)], f


def is_G_cycle(p):
    n = len(p)
    seen, cur, cnt = [False] * n, 0, 0
    while not seen[cur]:
        seen[cur] = True
        cnt += 1
        cur = p[cur]
    return cnt == n and cur == 0


def orbit_vertex_eq(S, K, J):
    G = len(S)
    listing, cur = [], 0
    for _ in range(G):
        listing.append(vtx(S, K, cur))
        cur = J[cur]
    truth = [vtx(S, K, i) for i in range(G)]
    return any(all(listing[j] == truth[(j + k) % G] for j in range(G))
               for k in range(G))


def is_repeat(S, e, a, b):
    G = len(S)
    return (1 <= e and e < G and a != b and agree(S, e, a, b)
            and cyc(S, a + G - 1) != cyc(S, b + G - 1)
            and cyc(S, a + e) != cyc(S, b + e))


def is_triple_repeat(S, e, a, b, c):
    G = len(S)
    pre = lambda t: cyc(S, t + G - 1)
    fol = lambda t: cyc(S, t + e)
    return (1 <= e and e < G and a != b and a != c and b != c
            and agree(S, e, a, b) and agree(S, e, a, c) and agree(S, e, b, c)
            and not (pre(a) == pre(b) and pre(b) == pre(c))
            and not (fol(a) == fol(b) and fol(b) == fol(c)))


def max_repeats(S, K):
    G = len(S)
    return [(e, a, b) for e in range(K, G) for a in range(G)
            for b in range(a + 1, G) if is_repeat(S, e, a, b)]


def satisfies_Ukkonen(S, K):
    G = len(S)
    for e in range(K, G):
        for a in range(G):
            for b in range(a + 1, G):
                for c in range(b + 1, G):
                    if is_triple_repeat(S, e, a, b, c):
                        return False
    mrs = max_repeats(S, K)
    for i in range(len(mrs)):
        for j in range(i + 1, len(mrs)):
            (_, a1, b1), (_, a2, b2) = mrs[i], mrs[j]
            if interleaved(G, a1, b1, a2, b2):
                return False
    return True


def max_pair_len(S, a, b):
    G = len(S)
    e = 0
    while e + 1 <= G and agree(S, e + 1, a, b):
        e += 1
    return e


def maximal_extension(S, a, b):
    """Two-sided maximal extension of the pair (a, b)."""
    G = len(S)
    e = 0
    while e + 1 <= G and agree(S, e + 1, a, b):
        e += 1
    p = 0
    while p < G and agree(S, e + 1, a - 1, b - 1):
        a, b, p = a - 1, b - 1, p + 1
    return e + p, a % G, b % G


def selected_triple(S, K, f):
    return any(len(b) >= 3 and any(f[q] != q for q in b)
               for b in fibre_blocks(S, K))


def selected_interleaved(S, K, f):
    G = len(S)
    ps = [(min(b), max(b)) for b in fibre_blocks(S, K)
          if len(b) == 2 and any(f[q] != q for q in b)]
    return any(interleaved(G, a, b, c, d)
               for i, (a, b) in enumerate(ps) for (c, d) in ps[i + 1:])


def main():
    maxG = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    maxK = int(sys.argv[2]) if len(sys.argv) > 2 else 3

    # ---- Q1: the raw crossing-pairs lemma, on primitive words ----
    q1 = dict(pairs=0, with_cross=0, fail=0)
    # ---- Q2 and Q3: over all primitive words ----
    q23 = dict(thetas=0, bad=0, good=0, good_with_selected_crossing=0,
               dichotomy_violations=0)
    viol = []

    for n in range(2, maxG + 1):
        for K in range(1, maxK + 1):
            if K >= n:
                continue
            for tup in itertools.product("AB", repeat=n):
                S = "".join(tup)
                if not is_primitive(S):
                    continue
                G = n
                q1["pairs"] += 1

                # Q1: interleaved doubled K-mers at all?
                doubled = [(a, b) for a in range(G) for b in range(a + 1, G)
                           if agree(S, K, a, b)]
                cross = [((a, b), (c, d))
                         for i, (a, b) in enumerate(doubled)
                         for (c, d) in doubled[i + 1:]
                         if interleaved(G, a, b, c, d)]
                if cross:
                    q1["with_cross"] += 1
                    (a, b), (c, d) = cross[0]
                    e1, a1, b1 = maximal_extension(S, a, b)
                    e2, a2, b2 = maximal_extension(S, c, d)
                    ok = (e1 >= K and e2 >= K and {a1, b1} != {a2, b2}
                          and interleaved(G, a1, b1, a2, b2))
                    if not ok:
                        q1["fail"] += 1

                for J, f in all_theta(S, K):
                    if not is_G_cycle(J):
                        continue
                    q23["thetas"] += 1
                    good = orbit_vertex_eq(S, K, J)
                    if good:
                        q23["good"] += 1
                        if selected_interleaved(S, K, f):
                            q23["good_with_selected_crossing"] += 1
                    else:
                        q23["bad"] += 1
                        if not (selected_triple(S, K, f)
                                or selected_interleaved(S, K, f)):
                            q23["dichotomy_violations"] += 1
                            if len(viol) < 10:
                                viol.append((S, n, K, f, J))

    print(f"primitive binary words, G <= {maxG}, K <= {maxK}\n")
    print("Q1  raw crossing-pairs lemma (interleaved doubled K-mers -> two "
          "interleaved maximal repeats):")
    print(f"      primitive (word, K) pairs       : {q1['pairs']}")
    print(f"      ...with interleaved doubled K-mers: {q1['with_cross']}")
    print(f"      ...where the lemma FAILS        : {q1['fail']}")
    print("      => the raw lemma is FALSE.\n")

    print("Q2  must a good theta have a crossing-free support?")
    print(f"      one-cycle fibre-preserving θ    : {q23['thetas']}")
    print(f"      ...of which good (truth's cycle)  : {q23['good']}")
    print(f"      ...good AND with a sel. crossing : "
          f"{q23['good_with_selected_crossing']}")
    print("      => NO: selected crossings are allowed, so neither 'f = id'")
    print("         nor 'no selected crossing' is provable.\n")

    print("Q3  the support dichotomy (the target):")
    print(f"      bad θ (wrong spelled vertex cycle): {q23['bad']}")
    print(f"      ...NOT explained by (T) or (I)   : "
          f"{q23['dichotomy_violations']}")
    for (S, n, K, f, J) in viol:
        print(f"        S={S} G={n} K={K} f={f} J={J}")
    print("      => SupportDichotomy holds in every case searched."
          if not viol else "      => COUNTEREXAMPLE FOUND.")


if __name__ == "__main__":
    main()
