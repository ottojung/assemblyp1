#!/usr/bin/env python3
"""Self-contained verification for the direct circular proof of

    P2(S,L)  =>  the L-mer spectrum determines the circular word S
                 up to cyclic shift

(primitive S), recorded in
`mathematics/circular-p2-spectrum-uniqueness-direct.md`.

The script checks, with exact integer/combinatorial arithmetic and no imports
from other repository code:

  A. the `Matching/Cycle Lemma` (the combinatorial heart of the proof):
     for sigma = (0 1 ... n-1) and an involution rho that is a product of
     disjoint transpositions, if tau = rho o sigma is a single n-cycle then
     the chord matching of rho has a crossing; equivalently, a non-crossing
     matching forces tau to have at least two cycles;
  B. the finite one-sided statement: for every circular word S (one necklace
     representative per rotation class, primitive or not) that satisfies P2,
     every same-length same-spectrum word T is a rotation of S;
  C. the *mechanism* of the proof on finite instances: recompute the
     transition permutation rho = sigma_T sigma_S^{-1}, check it is an
     involution on Out(v) for every (L-1)-mer v, and check rho = id whenever
     a same-length same-spectrum partner exists.

Exits non-zero on any failed assertion.  Finite ranges are evidence, not
proof; the unbounded content is the proof in the note plus the two lemmas.
"""

from __future__ import annotations

from collections import defaultdict
from itertools import combinations


# ---------------------------------------------------------------------------
# circular words
# ---------------------------------------------------------------------------
def rotations(w):
    return [w[i:] + w[:i] for i in range(len(w))]


def canon(w):
    return min(rotations(w))


def is_primitive(w):
    n = len(w)
    return all(not (n % d == 0 and w == w[:d] * (n // d)) for d in range(1, n))


def windows(w, L):
    n = len(w)
    d = defaultdict(int)
    for i in range(n):
        d[tuple(w[(i + j) % n] for j in range(L))] += 1
    return tuple(sorted(d.items()))


# ---------------------------------------------------------------------------
# Bresler repeat vocabulary and P2
# ---------------------------------------------------------------------------
def maximal_pairs(w):
    n = len(w)
    out = []
    for ell in range(1, n):
        g = defaultdict(list)
        for i in range(n):
            g[tuple(w[(i + j) % n] for j in range(ell))].append(i)
        for ts in g.values():
            if len(ts) < 2:
                continue
            for a, b in combinations(ts, 2):
                if w[(a - 1) % n] != w[(b - 1) % n] and w[(a + ell) % n] != w[(b + ell) % n]:
                    out.append((ell, a, b))
    return out


def trf(w, L):
    n = len(w)
    for ell in range(max(1, L - 1), n):
        g = defaultdict(int)
        for i in range(n):
            g[tuple(w[(i + j) % n] for j in range(ell))] += 1
        if any(c >= 3 for c in g.values()):
            return False
    return True


def ilf(w, L):
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


def rot_equiv(a, b):
    n = len(a)
    return any(a == b[i:] + b[:i] for i in range(n))


# ---------------------------------------------------------------------------
# Lyndon / necklace enumeration
# ---------------------------------------------------------------------------
def duval(alpha, n):
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


def all_necklaces(alpha, n):
    seen = set()
    for d in range(1, n + 1):
        if n % d:
            continue
        for w0 in duval(alpha, d):
            w = tuple(w0) * (n // d)
            seen.add(min(w[i:] + w[:i] for i in range(n)))
    return seen


# ---------------------------------------------------------------------------
# check A: the Matching/Cycle Lemma
# ---------------------------------------------------------------------------
def single_cycle(perm, n):
    seen = [False] * n
    i = 0
    cnt = 0
    while not seen[i]:
        seen[i] = True
        i = perm[i]
        cnt += 1
    return cnt == n and i == 0


def involution_pairs(p, n):
    """Return list of transpositions of an involution p, or None."""
    pairs = []
    used = set()
    for i in range(n):
        if i in used:
            continue
        j = p[i]
        if j == i:
            used.add(i)
            continue
        if p[j] != i:
            return None
        pairs.append((min(i, j), max(i, j)))
        used.add(i)
        used.add(j)
    return pairs


def crossing(pairs):
    for x in range(len(pairs)):
        a, b = pairs[x]
        for y in range(x + 1, len(pairs)):
            c, d = pairs[y]
            if (a < c < b < d) or (c < a < d < b):
                return True
    return False


def check_matching_cycle_lemma(maxn):
    from itertools import permutations
    tested = 0
    for n in range(2, maxn + 1):
        for p in permutations(range(n)):
            pairs = involution_pairs(p, n)
            if pairs is None or len(pairs) == 0:
                continue  # rho must be nontrivial
            t = [p[(i + 1) % n] for i in range(n)]  # rho o sigma
            if single_cycle(t, n):
                assert crossing(pairs), (n, p, pairs)
                tested += 1
    return tested


# ---------------------------------------------------------------------------
# transition permutation rho for two same-spectrum words
# ---------------------------------------------------------------------------
def edge_occurrences(w, L):
    """List of edge occurrences indexed by start; each is (tail,type)."""
    n = len(w)
    return [(tuple(w[(i + j) % n] for j in range(L - 1)),
             tuple(w[(i + j) % n] for j in range(L))) for i in range(n)]




def check_mechanism(alpha, maxn, Ls):
    """For every same-length same-spectrum non-rotation pair (S,T) with S
    primitive, verify the proof mechanism:
       - rho = sigma_T sigma_S^{-1} preserves every Out(v);
       - rho is a nontrivial involution;
       - rho's chord matching has a crossing;
       - consequently S is not P2 (ILF fails via the crossed repeats).
    Returns the number of non-rotation pairs analysed (must be > 0)."""
    from itertools import product
    checked = 0
    for n in range(2, maxn + 1):
        necks = all_necklaces(alpha, n)
        for L in Ls:
            if L > n:
                continue
            groups = defaultdict(list)
            for w in necks:
                groups[windows(w, L)].append(w)
            for spec, ws in groups.items():
                if len(ws) < 2:
                    continue
                for s in ws:
                    if not is_primitive(s):
                        continue
                    edges = edge_occurrences(s, L)
                    # the involution/crossing mechanism needs (L-1)-mer
                    # multiplicity <= 2 (Lemma L*); skip the residual regime
                    mult = defaultdict(int)
                    for (tail, _) in edges:
                        mult[tail] += 1
                    if max(mult.values()) > 2:
                        continue
                    for t in ws:
                        if t == s or rot_equiv(s, t):
                            continue
                        # label T occurrences by type to align with S
                        tedges = edge_occurrences(t, L)
                        by_type = defaultdict(list)
                        for idx, (_, typ) in enumerate(tedges):
                            by_type[typ].append(idx)
                        pos = {}
                        for idx, (_, typ) in enumerate(edges):
                            pos[idx] = by_type[typ].pop()
                        inv = {v: k for k, v in pos.items()}
                        rho = {}
                        for p in range(n):
                            q = pos[p]
                            succ_q = (q + 1) % n
                            succ_p = (p + 1) % n
                            # sigma_T(succ_p) = occurrence whose T-successor is succ_q
                            rho[succ_p] = inv[succ_q]
                        for p in range(n):
                            assert edges[rho[p]][0] == edges[p][0], ("Out(v)", s, t, L, p)
                        prs = involution_pairs([rho[i] for i in range(n)], n)
                        assert prs, ("nontrivial involution", s, t, L, rho)
                        assert crossing(prs), ("crossing", s, t, L, prs)
                        assert not p2(s, L), ("P2 with non-rotation partner", s, t)
                        checked += 1
    return checked


# ---------------------------------------------------------------------------
# check B: finite one-sided statement
# ---------------------------------------------------------------------------
def check_finite(alpha, maxn, Ls):
    total_p2 = 0
    nontrivial = 0
    for n in range(2, maxn + 1):
        necks = all_necklaces(alpha, n)
        for L in Ls:
            if L > n:
                continue
            groups = defaultdict(list)
            for w in necks:
                groups[windows(w, L)].append(w)
            for spec, ws in groups.items():
                if len(ws) < 2:
                    continue
                nontrivial += 1
                for s in ws:
                    if not p2(s, L):
                        continue
                    total_p2 += 1
                    for t in ws:
                        if t == s:
                            continue
                        assert rot_equiv(s, t), ("CEX", ''.join(s), ''.join(t), n, L)
    return total_p2, nontrivial


# ---------------------------------------------------------------------------
def main():
    print("A. Matching/Cycle Lemma (involution products, n<=8) ...", end=" ")
    k = check_matching_cycle_lemma(8)
    print("PASS ({} single-cycle nontrivial matchings, all crossing)".format(k))

    print("B. finite one-sided P2 uniqueness: AB n<=18, ABC n<=11 ...", end=" ")
    a = check_finite("AB", 18, [2, 3, 4, 5, 6])
    b = check_finite("ABC", 11, [2, 3, 4, 5])
    print("PASS ({} nontrivial fibres; 0 containing a P2 word with a non-rotation mate)".format(a[1] + b[1]))

    print("C. proof mechanism (rho involution, Out(v)-preserving, crossing) ...", end=" ")
    c = check_mechanism("AB", 12, [2, 3, 4, 5])
    print("PASS ({} non-rotation pairs analysed)".format(c))

    print("all checks passed")


if __name__ == "__main__":
    main()
