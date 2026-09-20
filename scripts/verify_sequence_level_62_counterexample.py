#!/usr/bin/env python3
"""
Sequence-level Medvedev-Brudno section 6.2 counterexample with a flow-feasible
truth, and the exact scope defect that hid it.

Result
------
The well-posed statement

    I_s  and  S in F_flow(R)  =>  S is a maximum-likelihood maximizer
                                  over the sequence-level flow-feasible set

is FALSE.  Explicit witness (single strand, read length L = 4, binary alphabet):

    truth        S = AAAAAB                (G = 6)
    realized     starts = (0, 2, 3, 4, 5)  (N = 5 reads)
    observed     x = {AAAA:1, AAAB:1, AABA:1, ABAA:1, BAAA:1}
    competitor   D = AAABA                 (read-tiled: spec_4(D) = x)

Both S and D are sequence-level section 6.2 feasible (Observation-7 criterion:
support equality of the length-L window spectra plus per-occurrence lower
bounds d >= x), the source I_s hypothesis holds for (S, reads), and D strictly
beats S under both the exact multinomial objective and the literal section 6.1
binomial objective:

    exact multinomial ratio  L(D)/L(S) = 3888/3125  > 1
    section 6.1 binomial     L(D)/L(S) = 625/512    > 1

Why the repository's earlier search missed it
---------------------------------------------
docs/section62-bidirected-flow-feasibility.md section 5 and
scripts/se62_bidirected_feasibility_search.py enumerate instances with the
number of reads n fixed equal to the truth length G.  With n = G, truth
feasibility `d_S(w) >= x_w` combined with `sum x_w = n = G = sum d_S(w)`
forces x = d_S exactly, so no strictly better read-tiled competitor can exist
in that scope.  The witness above has n = 5 < G = 6, i.e. it lies outside the
searched scope.  The claim in that note that "when the observed spectrum is
complete the truth is a maximizer ... in every tested range" therefore only
tests the degenerate n = G, x = d_S corner.

This file: exact rational arithmetic only; deterministic; exits non-zero on any
failed assertion.  Computational evidence + finite exact proof of the listed
instance; the general negative mechanism is the repository's own read-tiled
dominance theorem.
"""
from itertools import combinations, product as iproduct
from fractions import Fraction
from collections import Counter, defaultdict


# ---------------------------------------------------------------------------
# Source predicates (transcribed from docs/bridging-source-semantics.md)
# ---------------------------------------------------------------------------
def win(S, L, i):
    G = len(S)
    return tuple(S[(i + j) % G] for j in range(L))


def spec(S, L):
    G = len(S)
    return Counter(win(S, L, i) for i in range(G))


def covers_all(S, T, L):
    G = len(S)
    cov = set()
    for r in T:
        for o in range(L):
            cov.add((r + o) % G)
    return len(cov) == G


def maximal_repeat_pairs(S):
    """Pairs of equal length-ell windows maximal on both sides (both differ)."""
    G = len(S)
    out = []
    for ell in range(1, G):
        groups = defaultdict(list)
        for i in range(G):
            groups[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for pos in groups.values():
            for p in combinations(pos, 2):
                a, b = p
                if (S[(a - 1) % G] != S[(b - 1) % G]
                        and S[(a + ell) % G] != S[(b + ell) % G]):
                    out.append((ell, p))
    return out


def triple_repeats(S):
    """Three equal length-ell windows, three-copy maximality (not all equal)."""
    G = len(S)
    out = []
    for ell in range(1, G):
        groups = defaultdict(list)
        for i in range(G):
            groups[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for pos in groups.values():
            for t in combinations(pos, 3):
                if (len({S[(a - 1) % G] for a in t}) > 1
                        and len({S[(a + ell) % G] for a in t}) > 1):
                    out.append((ell, t))
    return out


def interleaved_pairs(S):
    reps = maximal_repeat_pairs(S)
    out = []
    for i in range(len(reps)):
        for j in range(i + 1, len(reps)):
            e1, p1 = reps[i]
            e2, p2 = reps[j]
            four = sorted(set(p1) | set(p2))
            if len(four) != 4:
                continue
            lab = {x: 0 for x in p1}
            lab.update({x: 1 for x in p2})
            if [lab[x] for x in four] in ([0, 1, 0, 1], [1, 0, 1, 0]):
                out.append(((e1, p1), (e2, p2)))
    return out


def copy_bridged(S, t, ell, T, L):
    G = len(S)
    for r in T:
        pos = {(r + o) % G for o in range(L)}
        if (t - 1) % G in pos and (t + ell) % G in pos:
            return True
    return False


def information_feasible(S, T, L):
    """I_s: coverage + all triple repeats all-bridged + interleaved pairs bridged."""
    if not covers_all(S, T, L):
        return False
    for ell, t in triple_repeats(S):
        if not all(copy_bridged(S, x, ell, T, L) for x in t):
            return False
    for (e1, p1), (e2, p2) in interleaved_pairs(S):
        if not (any(copy_bridged(S, x, e1, T, L) for x in p1)
                or any(copy_bridged(S, x, e2, T, L) for x in p2)):
            return False
    return True


# ---------------------------------------------------------------------------
# Eulerian realizability of a spectrum as a single circular genome
# ---------------------------------------------------------------------------
def eulerian_realizable(x, L):
    adj = defaultdict(list)
    und = defaultdict(set)
    outd, ind = defaultdict(int), defaultdict(int)
    verts = set()
    for w, c in x.items():
        a, b = w[:L - 1], w[1:]
        outd[a] += c
        ind[b] += c
        verts.update((a, b))
        for _ in range(c):
            adj[a].append(b)
            und[a].add(b)
            und[b].add(a)
    if any(outd[v] != ind[v] for v in verts):
        return False
    start = next(v for v in verts if outd[v] > 0)
    seen = {start}
    stack = [start]
    while stack:
        v = stack.pop()
        for b in und[v]:
            if b not in seen:
                seen.add(b)
                stack.append(b)
    return all(v in seen for v in verts if outd[v] > 0 or ind[v] > 0)


def eulerian_genome(x, L):
    """Return one circular genome whose length-L spectrum is x, or None."""
    if not eulerian_realizable(x, L):
        return None
    local = defaultdict(list)
    for w, c in x.items():
        for _ in range(c):
            local[w[:L - 1]].append(w[1:])
    start = next(iter(local))
    stack, path = [start], []
    while stack:
        v = stack[-1]
        if local.get(v):
            stack.append(local[v].pop())
        else:
            path.append(stack.pop())
    path.reverse()
    seq = list(path[0])
    for v in path[1:]:
        seq.append(v[-1])
    return tuple(seq[:len(seq) - (L - 1)])


# ---------------------------------------------------------------------------
# Likelihood ratios
# ---------------------------------------------------------------------------
def exact_ratio(x, dS, dD, G, M):
    """Exact multinomial ratio L_exact(D|x) / L_exact(S|x) (observation-only
    multinomial coefficient cancels)."""
    r = Fraction(1)
    for w, xw in x.items():
        r *= Fraction(dD.get(w, 0), M) ** xw / Fraction(dS.get(w, 0), G) ** xw
    return r


def binomial_ratio(x, dS, dD, G, N):
    """Literal section 6.1 ratio with external genome-length N; observation-only
    coefficient cancels and the N^n normalisers cancel in the ratio."""
    n = sum(x.values())
    r = Fraction(1)
    for w, xw in x.items():
        dd, ds = dD.get(w, 0), dS.get(w, 0)
        if dd > N or ds > N:
            return None
        r *= (Fraction(dd ** xw * (N - dd) ** (n - xw))
              / Fraction(ds ** xw * (N - ds) ** (n - xw)))
    return r


# ---------------------------------------------------------------------------
# The witness
# ---------------------------------------------------------------------------
def verify_witness():
    S = tuple("AAAAAB")
    D = tuple("AAABA")
    L = 4
    T = (0, 2, 3, 4, 5)
    x = Counter({win(S, L, t): 1 for t in T})
    dS, dD = spec(S, L), spec(D, L)
    print("=== witness S=AAAAAB, L=4, starts=(0,2,3,4,5), D=AAABA ===")
    print("  S windows :", [ "".join(win(S, L, i)) for i in range(len(S))])
    print("  spec(S)   :", { "".join(w): c for w, c in dS.items()})
    print("  realized x:", { "".join(w): c for w, c in x.items()})

    assert covers_all(S, T, L)
    assert information_feasible(S, T, L)
    assert set(spec(S, L)) == set(x) and all(dS[w] >= c for w, c in x.items())
    assert set(spec(D, L)) == set(x) and all(dD[w] >= c for w, c in x.items())
    assert spec(D, L) == x, "D is read-tiled"
    assert len(set(maximal_repeat_pairs(S))) == 4
    assert interleaved_pairs(S) == []

    G, M = len(S), len(D)
    r_exact = exact_ratio(x, dS, dD, G, M)
    r_binom = binomial_ratio(x, dS, dD, G, G)
    r_binom_n = binomial_ratio(x, dS, dD, G, sum(x.values()))
    print("  I_s holds, S in F_flow, D in F_flow: True")
    print("  exact multinomial ratio :", r_exact)
    print("  section 6.1 binom (N=G):", r_binom)
    print("  section 6.1 binom (N=n):", r_binom_n)
    assert r_exact == Fraction(3888, 3125) and r_exact > 1
    assert r_binom == Fraction(625, 512) and r_binom > 1
    assert r_binom_n is not None and r_binom_n > 1
    assert eulerian_genome(x, L) is not None
    return S, D, L, T


# ---------------------------------------------------------------------------
# The scope defect: with n = G no counterexample can exist
# ---------------------------------------------------------------------------
def ng_scope_is_degenerate(G, L):
    """With exactly G reads, truth feasibility forces x = d_S."""
    return True  # sum x = G = sum d_S and x <= d_S coordinatewise


def bounded_search(maxG=7):
    """Search binary truths with n <= G-1, via start-support + Eulerian
    realizability.  Returns the smallest-gap witnesses found."""
    found = []

    def mults(T, maxN):
        T = list(T)
        k = len(T)
        def rec(i, rem, cur):
            if i == k:
                if cur:
                    yield tuple(cur)
                return
            for v in range(1, rem + 1):
                cur.append(v)
                yield from rec(i + 1, rem - v, cur)
                cur.pop()
        yield from rec(0, maxN, [])

    for G in range(4, maxG + 1):
        for L in (2, 3, 4):
            if L >= G:
                continue
            for S in iproduct((0, 1), repeat=G):
                dS = spec(S, L)
                supp = frozenset(dS)
                ws = [win(S, L, i) for i in range(G)]
                for k in range(1, G + 1):
                    for T in combinations(range(G), k):
                        if not information_feasible(S, T, L):
                            continue
                        for mult in mults(T, G - 1):
                            x = Counter()
                            for t, m in zip(T, mult):
                                x[ws[t]] += m
                            if frozenset(x) != supp:
                                continue
                            if any(dS[w] < c for w, c in x.items()):
                                continue
                            if dict(x) == dict(dS):
                                continue
                            if not eulerian_realizable(x, L):
                                continue
                            D = eulerian_genome(x, L)
                            assert D is not None and spec(D, L) == x
                            r = exact_ratio(x, dS, spec(D, L), G, len(D))
                            if r > 1:
                                found.append((G, L, S, T, mult, x, D, r))
    return found


def main():
    verify_witness()
    print()
    print("=== bounded binary search over n <= G-1 (smallest witness) ===")
    found = bounded_search(maxG=7)
    found.sort(key=lambda z: (z[0], z[1]))
    assert found, "expected to recover the witness"
    G, L, S, T, mult, x, D, r = found[0]
    print("  earliest witness: G=%d L=%d S=%s T=%s D=%s exact_ratio=%s"
          % (G, L, "".join("AB"[c] for c in S), T,
             "".join("AB"[c] for c in D), r))
    print("  total witnesses with G<=7:", len(found))
    print()
    print("ALL ASSERTIONS PASS")


if __name__ == "__main__":
    raise SystemExit(main())
