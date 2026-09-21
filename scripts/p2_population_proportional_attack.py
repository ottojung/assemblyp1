#!/usr/bin/env python3
"""
Independent attack on the P2 population-identifiability question
(issue #48 / issue #45 data-regime analogue).

Question
--------
Fix a read length L >= 2.  For a circular word D let

    d_D(w) = # cyclic occurrences of the length-L word w in D

and call two spectra *proportional* if d_T = c * d_D for some rational c > 0
(equivalently the population read laws p_D = d_D/|D| agree).  Can two
*distinct* (non-rotational), primitive, P2-admissible circular genomes have
proportional L-mer spectra?

P2 (a.k.a. WEAK) means: no Bresler triple repeat of length >= L-1 and no
interleaved pair of maximal repeats whose shorter constituent has length
>= L-1 (the candidate-intrinsic shadow of Shomorony et al. I_s at the full
read set).

This script is independent of every other verifier in the repository.  It
- re-derives the definitions from scratch,
- exhaustively searches for collisions on stated finite ranges,
- cross-checks the equal-length case with the BEST theorem on the de Bruijn
  multigraph (a second, independent route), including the parallel-edge
  subtlety that makes a raw circuit count inconclusive,
- tries to build counterexamples over larger random instances.

Exact integer / Fraction arithmetic; exits non-zero on a failed assertion.

What computation can and cannot do here
---------------------------------------
The exhaustive searches below are *finite evidence*: they refute nothing
outside their ranges.  The unbounded statements are (i) Theorem P proved in
`docs/issue48/p2-population-proportional-identification-2026-09-21.md` and
(ii) the classical circular q-gram characterization (Ukkonen 1992, Pevzner
1995, Bresler-Bresler-Tse 2013 Thm 3 at K = L-1).  The script corroborates
both; it does not replace them.
"""

from __future__ import annotations

import random
from collections import defaultdict
from math import gcd, factorial
from itertools import combinations


# ---------------------------------------------------------------------------
# circular words
# ---------------------------------------------------------------------------
def rotations(w):
    return [w[i:] + w[:i] for i in range(len(w))]


def canonical(w):
    return min(rotations(w))


def is_primitive(w):
    n = len(w)
    return all(w != w[:p] * (n // p) for p in range(1, n) if n % p == 0)


def windows(w, L):
    n = len(w)
    d = defaultdict(int)
    for i in range(n):
        d[tuple(w[(i + j) % n] for j in range(L))] += 1
    return dict(d)


def normalized_spectrum(w, L):
    """Scale-free spectrum key: counts divided by their common gcd."""
    d = windows(w, L)
    g = 0
    for v in d.values():
        g = gcd(g, v)
    return tuple(sorted((k, v // g) for k, v in d.items()))


def same_length_spectrum(w, L):
    return tuple(sorted(windows(w, L).items()))


# ---------------------------------------------------------------------------
# Bresler repeat structures (re-derived)
# ---------------------------------------------------------------------------
def maximal_pairs(w):
    """All (ell, a, b) for unordered maximal repeat pairs of length ell."""
    n = len(w)
    out = []
    for ell in range(1, n):
        groups = defaultdict(list)
        for i in range(n):
            groups[tuple(w[(i + j) % n] for j in range(ell))].append(i)
        for ts in groups.values():
            if len(ts) < 2:
                continue
            for a, b in combinations(ts, 2):
                if w[(a - 1) % n] != w[(b - 1) % n] and \
                   w[(a + ell) % n] != w[(b + ell) % n]:
                    out.append((ell, a, b))
    return out


def trf(w, L):
    """No Bresler triple repeat of length >= L-1.

    Three raw occurrences of any length >= L-1 substring are equivalent to a
    maximal triple repeat of length >= L-1 (extend all three copies), so the
    raw check is the same predicate.
    """
    n = len(w)
    for ell in range(max(1, L - 1), n):
        groups = defaultdict(int)
        for i in range(n):
            groups[tuple(w[(i + j) % n] for j in range(ell))] += 1
        if any(c >= 3 for c in groups.values()):
            return False
    return True


def ilf(w, L):
    """No interleaved pair of maximal repeats both of length >= L-1."""
    reps = [(ell, (a, b)) for (ell, a, b) in maximal_pairs(w) if ell >= L - 1]
    for r1, r2 in combinations(reps, 2):
        four = sorted(set(r1[1]) | set(r2[1]))
        if len(four) != 4:
            continue
        lab = [0 if p in r1[1] else 1 for p in four]
        if lab in ([0, 1, 0, 1], [1, 0, 1, 0]):
            return False
    return True


def p2(w, L):
    return trf(w, L) and ilf(w, L)


# ---------------------------------------------------------------------------
# Lyndon words (aperiodic necklaces): one representative per rotation class
# ---------------------------------------------------------------------------
def lyndon_words(alpha, n):
    """Duval's algorithm; all Lyndon words of length exactly n over alpha."""
    k = len(alpha)
    w = [0] * (n + 1)

    def gen(t, p):
        if t > n:
            if p == n:
                yield tuple(alpha[w[i]] for i in range(1, n + 1))
        else:
            w[t] = w[t - p]
            yield from gen(t + 1, p)
            for j in range(w[t - p] + 1, k):
                w[t] = j
                yield from gen(t + 1, t)

    yield from gen(1, 1)


# ---------------------------------------------------------------------------
# de Bruijn multigraph and Eulerian circuits (BEST theorem)
# ---------------------------------------------------------------------------
def de_bruijn_graph(w, L):
    edges = defaultdict(int)
    for word, c in windows(w, L).items():
        edges[(word[:-1], word[1:])] += c
    return edges


def _det_bareiss(mat):
    n = len(mat)
    if n == 0:
        return 1
    a = [row[:] for row in mat]
    sign = 1
    prev = 1
    for k in range(n - 1):
        if a[k][k] == 0:
            swap = next((i for i in range(k + 1, n) if a[i][k] != 0), None)
            if swap is None:
                return 0
            a[k], a[swap] = a[swap], a[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                a[i][j] = (a[i][j] * a[k][k] - a[i][k] * a[k][j]) // prev
            a[i][k] = 0
        prev = a[k][k]
    return sign * a[n - 1][n - 1]


def eulerian_circuit_count(w, L):
    """# cyclic Eulerian circuits of the de Bruijn multigraph (BEST).

    WARNING: this counts parallel edge *copies* as distinct.  A count > 1 can
    therefore still correspond to a unique spelled word (see AABAB below).
    """
    edges = de_bruijn_graph(w, L)
    verts = sorted({u for u, _ in edges} | {v for _, v in edges})
    idx = {u: i for i, u in enumerate(verts)}
    m = len(verts)
    outdeg = [0] * m
    adj = [[0] * m for _ in range(m)]
    for (u, v), c in edges.items():
        adj[idx[u]][idx[v]] += c
        outdeg[idx[u]] += c
    lap = [[0] * m for _ in range(m)]
    for i in range(m):
        for j in range(m):
            if i != j:
                lap[i][i] += adj[i][j]   # self-loops cannot reach the root
                lap[i][j] -= adj[i][j]
    minor = [[lap[i][j] for j in range(1, m)] for i in range(1, m)]
    t_root = _det_bareiss(minor)
    prod = 1
    for d in outdeg:
        prod *= factorial(d - 1) if d >= 1 else 1
    return t_root * prod


def eulerian_circuits(w, L, cap=500):
    edges = de_bruijn_graph(w, L)
    out = defaultdict(list)
    for (u, v) in edges:
        out[u].append(v)
    start = sorted({u for u, _ in edges})[0]
    results = []

    def rec(cur, used, seq, remaining):
        if len(results) >= cap:
            return
        if remaining == 0 and cur == start:
            results.append(tuple(seq))
            return
        for v in out[cur]:
            key = (cur, v)
            if used[key] >= edges[key]:
                continue
            used[key] += 1
            seq.append(key)
            rec(v, used, seq, remaining - 1)
            seq.pop()
            used[key] -= 1

    rec(start, defaultdict(int), [], sum(edges.values()))
    uniq = {}
    for seq in results:
        rots = [seq[i:] + seq[:i] for i in range(len(seq))]
        uniq[min(rots)] = seq
    return list(uniq.values())


def spell(edge_seq):
    """Circular word from a cyclic sequence of (L-1)-mer edges."""
    return tuple(e[0][0] for e in edge_seq)


def spelled_partners(w, L):
    return {canonical(spell(seq)) for seq in eulerian_circuits(w, L)}


# ---------------------------------------------------------------------------
# scans
# ---------------------------------------------------------------------------
def scan(alpha, nmax, maxL, predicate, cross):
    """Group primitive Lyndon words by (normalized) spectrum; return collisions."""
    hits = []
    count = 0
    for L in range(2, maxL + 1):
        table = {}
        for n in range(L, nmax + 1):
            for w in lyndon_words(alpha, n):
                if not is_primitive(w) or not predicate(w, L):
                    continue
                count += 1
                key = normalized_spectrum(w, L) if cross else same_length_spectrum(w, L)
                if key in table:
                    n0, w0 = table[key]
                    if (n0 != n) if cross else True:
                        hits.append((L, n0, w0, n, w))
                else:
                    table[key] = (n, w)
    return count, hits


def one_sided_scan(alpha, nmax, maxL):
    """All primitive words grouped by same-length spectrum; report any group
    with a P2 member and a non-rotational other member.

    A nonempty result would refute the one-sided statement 'P2(S) alone
    determines S'; the classical circular q-gram theorem says it is empty.
    """
    hits = []
    count = 0
    for L in range(2, maxL + 1):
        for n in range(L, nmax + 1):
            groups = defaultdict(list)
            for w in lyndon_words(alpha, n):
                if is_primitive(w):
                    groups[same_length_spectrum(w, L)].append(w)
            for ws in groups.values():
                p2s = [w for w in ws if p2(w, L)]
                count += len(p2s)
                if len(ws) < 2:
                    continue
                for w in p2s:
                    hits.append((L, n, w, [x for x in ws if x != w][0]))
    return count, hits


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------
def main():
    print("independent P2 population proportional-spectrum attack")

    # -- decisive examples and the parallel-edge subtlety ------------------
    S, T = tuple("AABABB"), tuple("AABBAB")
    assert is_primitive(S) and is_primitive(T)
    assert trf(S, 3) and trf(T, 3) and not ilf(S, 3) and not ilf(T, 3)
    assert same_length_spectrum(S, 3) == same_length_spectrum(T, 3)
    assert canonical(S) != canonical(T)
    # AABAB is P2; BEST returns 2 because of two parallel ABA edges, yet the
    # only spelled word is AABAB itself.
    W = tuple("AABAB")
    assert is_primitive(W) and p2(W, 3)
    assert eulerian_circuit_count(W, 3) == 2
    assert spelled_partners(W, 3) == {canonical(W)}
    assert eulerian_circuit_count(tuple("CABABB"), 3) == 1

    # cross-length sharpness
    A, A2 = tuple("AAB"), tuple("AABAAB")            # A2 = A^2, non-primitive
    assert is_primitive(A) and p2(A, 3)
    assert not is_primitive(A2) and p2(A2, 3)
    assert normalized_spectrum(A, 3) == normalized_spectrum(A2, 3)
    assert canonical(A) != canonical(A2)
    B, B2 = tuple("AAAB"), tuple("AAAABAAB")          # B2 primitive, not TRF
    assert is_primitive(B) and p2(B, 3)
    assert is_primitive(B2) and not p2(B2, 3)
    assert normalized_spectrum(B, 3) == normalized_spectrum(B2, 3)
    assert canonical(B) != canonical(B2)
    print("  examples: TRF-only collision; P2 BEST subtlety; sharpness OK")

    # -- both-P2 equal length ---------------------------------------------
    c1, h1 = scan(("A", "B"), 20, 5, p2, cross=False)
    assert not h1, h1[:3]
    c2, h2 = scan(("A", "B", "C"), 14, 4, p2, cross=False)
    assert not h2, h2[:3]
    print(f"  equal-length both-P2: {c1}+{c2} words, 0 collisions")

    # -- Theorem P hypothesis: cross length with TRF only ------------------
    c3, h3 = scan(("A", "B"), 16, 5, trf, cross=True)
    assert not h3, h3[:3]
    c4, h4 = scan(("A", "B", "C"), 11, 4, trf, cross=True)
    assert not h4, h4[:3]
    print(f"  cross-length TRF: {c3}+{c4} words, 0 proportional collisions")

    # -- cross length with both-P2 ----------------------------------------
    c5, h5 = scan(("A", "B"), 16, 5, p2, cross=True)
    assert not h5, h5[:3]
    print(f"  cross-length both-P2: {c5} words, 0 proportional collisions")

    # -- one-sided P2 ------------------------------------------------------
    o1, oh1 = one_sided_scan(("A", "B"), 20, 5)
    o2, oh2 = one_sided_scan(("A", "B", "C"), 13, 4)
    assert not oh1 and not oh2, (oh1[:2], oh2[:2])
    print(f"  one-sided P2: {o1}+{o2} P2 words, 0 non-rotation partners")

    # -- larger random probe (both-P2, cross length) -----------------------
    rng = random.Random(20240921)
    seen = {}
    rcount = 0
    for _ in range(20000):
        q = rng.randint(2, 4)
        alpha = [chr(ord("A") + i) for i in range(q)]
        n = rng.randint(10, 40)
        w = tuple(rng.choice(alpha) for _ in range(n))
        if not is_primitive(w) or w != canonical(w):
            continue
        L = rng.randint(2, min(n, 7))
        if not p2(w, L):
            continue
        rcount += 1
        key = normalized_spectrum(w, L)
        if key in seen:
            n0, w0 = seen[key]
            assert False, ("random proportional collision", n0, w0, n, w)
        else:
            seen[key] = (n, w)
    print(f"  random: {rcount} primitive P2 Lyndon samples, 0 collisions")

    print("all independent P2 proportional-spectrum checks passed")


if __name__ == "__main__":
    main()
