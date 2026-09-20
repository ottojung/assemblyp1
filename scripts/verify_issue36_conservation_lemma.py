#!/usr/bin/env python3
"""
Independent verification of the "conditional conservation lemma" around issue #36.

The lemma (from the issue #36 status comments):

    Under the per-occurrence section 6.2 reading, if the experiment has
    n = N = |S| = G reads, with N the externally known genome size and with
    per-occurrence feasibility of the truth, then
        sum_w d_S(w) = G = sum_w x_w  and  d_S(w) >= x_w
    force d_S = x.  Consequently every same-length feasible competitor also has
    d_D = x = d_S, so no same-length likelihood improvement is possible.

This script does three independent things, all in exact rational arithmetic:

  [A] Proves/verifies the arithmetic core (per-coordinate section 6.1 binomial
      maximisation).  For the d-dependent factor
          phi_{x,n,N}(d) = (d/N)^x (1 - d/N)^(n-x),   0 <= d <= N,
      the real maximiser is d = N x / n; when n = N it is the integer d = x.
      Because the section 6.1 objective is separable, this extends *coordinate-
      wise* to arbitrary integer vertex-throughput vectors, i.e. to the whole
      section 6.2 bidirected-flow class, spellable or not.

  [B] Refutes the *flow-level* reading of the lemma's premise: the actual
      section 6.2 flow constraints do not contain any total-count identity
      sum_w d_w = N (or = n).  Explicit circulation certificates are given:
        * S = ACGT, L = 2, n = N = G = 4: the observed-read overlap graph is a
          4-cycle; the circulation of value 2 is feasible and has
          sum_w d_w = 8 != N = 4, yet is strictly worse than the truth.
        * S = AAATAT (reverse-complement reading, per-type lower bound):
          a feasible flow has sum_w d_w = 5 != N = 6 and beats the truth.
      So the conservation identity is a property of length-N *molecules*, not a
      flow conservation law.

  [C] Exhibits a generic-regime, per-occurrence, I_s, truth-feasible
      counterexample with n != N that strictly beats the truth under the
        section 6.1 binomial:
          G = 5, L = 3, n = 3, N = 5, S = AAATT, D = AAAATT, ratio 9/8.

Run:  python3 scripts/verify_issue36_conservation_lemma.py
Exits non-zero on any assertion failure.
"""
import sys
from fractions import Fraction
from itertools import combinations
from collections import defaultdict, Counter


# ---------------------------------------------------------------------------
# section 6.1 separable binomial factor
# ---------------------------------------------------------------------------
def phi(x, n, N, d):
    """d-dependent part of one section 6.1 binomial factor: (d/N)^x (1-d/N)^(n-x)."""
    return Fraction(d, N) ** x * Fraction(N - d, N) ** (n - x)


def binom_product(x, n, N, d):
    """Product of the section 6.1 factors over the support of x."""
    r = Fraction(1)
    for w, xw in x.items():
        r *= phi(xw, n, N, d.get(w, 0))
    return r


# ---------------------------------------------------------------------------
# molecule / spectrum machinery (single-strand and reverse-complement readings)
# ---------------------------------------------------------------------------
def make_comp(sigma):
    """Reverse-complement involution on alphabet {0,...,sigma-1}."""
    c = {}
    for i in range(0, sigma - 1, 2):
        c[i] = i + 1
        c[i + 1] = i
    if sigma % 2:
        c[sigma - 1] = sigma - 1
    return c


def mol(s, comp):
    """Molecule class of a symbol sequence (unordered reverse-complement pair)."""
    if comp is None:
        return tuple(s)
    r = tuple(comp[c] for c in reversed(s))
    return min(tuple(s), r)


def spec(seq, L, comp):
    """Multiset of length-L molecule-class windows of a circular sequence."""
    G = len(seq)
    return Counter(mol(tuple(seq[(i + j) % G] for j in range(L)), comp)
                   for i in range(G))


def observed(S, starts, L, comp):
    x = Counter()
    for r in starts:
        x[mol(tuple(S[(r + j) % len(S)] for j in range(L)), comp)] += 1
    return x


# ---------------------------------------------------------------------------
# I_s machinery (coverage + all triple repeats bridged + interleaved pairs
# bridged), re-derived from the Bresler / Shomorony definitions.
# ---------------------------------------------------------------------------
def covers_all(S, starts, L):
    G = len(S)
    cov = set()
    for r in starts:
        for o in range(L):
            cov.add((r + o) % G)
    return len(cov) == G


def maximal_repeat_pairs(S):
    G = len(S)
    out, seen = [], set()
    for ell in range(1, G):
        groups = defaultdict(list)
        for i in range(G):
            groups[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for _, pos in groups.items():
            if len(pos) < 2:
                continue
            for t1, t2 in combinations(pos, 2):
                if (S[(t1 - 1) % G] != S[(t2 - 1) % G]
                        and S[(t1 + ell) % G] != S[(t2 + ell) % G]):
                    pair = (t1, t2)
                    if pair not in seen:
                        seen.add(pair)
                        out.append((ell, pair))
    return out


def triple_repeats(S):
    G = len(S)
    out, seen = [], set()
    for ell in range(1, G):
        groups = defaultdict(list)
        for i in range(G):
            groups[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for _, pos in groups.items():
            if len(pos) < 3:
                continue
            for tri in combinations(pos, 3):
                pre = {S[(t - 1) % G] for t in tri}
                post = {S[(t + ell) % G] for t in tri}
                if len(pre) > 1 and len(post) > 1:
                    key = tuple(sorted(tri))
                    if key not in seen:
                        seen.add(key)
                        out.append((ell, key))
    return out


def interleaved_pairs(S):
    reps = maximal_repeat_pairs(S)
    out, seen = [], set()
    for i in range(len(reps)):
        e1, p1 = reps[i]
        for j in range(i + 1, len(reps)):
            e2, p2 = reps[j]
            four = sorted(set(p1) | set(p2))
            if len(four) != 4:
                continue
            lab = {p: 0 for p in p1}
            lab.update({p: 1 for p in p2})
            seq = [lab[p] for p in four]
            if seq in ([0, 1, 0, 1], [1, 0, 1, 0]):
                key = (e1, tuple(sorted(p1)), e2, tuple(sorted(p2)))
                if key not in seen:
                    seen.add(key)
                    out.append(((e1, tuple(sorted(p1))), (e2, tuple(sorted(p2)))))
    return out


def copy_bridged(S, t, ell, starts, L):
    G = len(S)
    for r in starts:
        rp = {(r + o) % G for o in range(L)}
        if (t - 1) % G in rp and (t + ell) % G in rp:
            return True
    return False


def check_I_s(S, starts, L):
    if not covers_all(S, starts, L):
        return False
    for ell, pos in triple_repeats(S):
        for t in pos:
            if not copy_bridged(S, t, ell, starts, L):
                return False
    for (e1, p1), (e2, p2) in interleaved_pairs(S):
        b1 = any(copy_bridged(S, t, e1, starts, L) for t in p1)
        b2 = any(copy_bridged(S, t, e2, starts, L) for t in p2)
        if not (b1 or b2):
            return False
    return True


# ---------------------------------------------------------------------------
# [A] per-coordinate section 6.1 maximum
# ---------------------------------------------------------------------------
def check_per_coordinate():
    checks = 0
    for N in range(2, 10):
        for n in range(1, N + 1):
            for x in range(0, n + 1):
                vals = [(phi(x, n, N, d), d) for d in range(0, N + 1)]
                if n == N and 0 < x < n:
                    best = max(vals)
                    assert best[1] == x, (N, n, x)
                    assert all(phi(x, n, N, d) < phi(x, n, N, x)
                               for d in range(0, N + 1) if d != x), (N, n, x)
                # real stationary point d = N x / n is the unique maximum
                dstar = Fraction(N * x, n)
                if dstar.denominator == 1 and 0 <= dstar <= N:
                    ds = int(dstar)
                    assert all(phi(x, n, N, d) <= phi(x, n, N, ds)
                               for d in range(0, N + 1)), (N, n, x)
                if 0 < x < n:
                    d = Fraction(N * x, n)
                    deriv = Fraction(x) / d - Fraction(n - x) / (N - d)
                    assert deriv == 0, (N, n, x)
                checks += 1
    print(f"  [A] per-coordinate maximum verified on {checks} (N,n,x) cases; "
          f"stationary point d = N x / n exact; d = x when n = N")
    return True


# ---------------------------------------------------------------------------
# [B] flow-level refutation of the total-count identity
# ---------------------------------------------------------------------------
def vertex_throughput_of_closed_walk(walk, L):
    """Throughput vector of a closed walk of read-molecule vertices.

    A closed walk r_0 -> r_1 -> ... -> r_k = r_0 through reads with proper
    overlaps (length L-1) is a section 6.2 circulation; its vertex throughput is
    the number of occurrences of each vertex type (Observation 7).
    """
    tp = Counter()
    for v in walk:
        tp[v] += 1
    return tp


def check_flow_total_identity_refutation():
    # (B1) S = ACGT, L = 2, single-strand reading: the four observed reads are
    # distinct and the overlap graph on them is a 4-cycle.  The circulation of
    # value 2 has vertex throughput 2 at each vertex, total 8 != N = 4, and is a
    # valid section 6.2 bidirected flow (lower bounds 1 satisfied, conservation
    # exact, ub = infinity).
    comp = None
    S = (0, 1, 2, 3)
    L = 2
    spS = spec(S, L, comp)
    starts = [0, 1, 2, 3]
    x = observed(S, starts, L, comp)
    assert set(spS) == set(x) and dict(spS) == dict(x), (spS, x)
    n = sum(x.values())
    N = len(S)
    assert n == N == 4
    # graph cycle: each observed read overlaps the next by L-1 = 1
    reads = [mol(tuple(S[(i + j) % len(S)] for j in range(L)), comp)
             for i in range(len(S))]
    k = 2
    tp = Counter()
    for _ in range(k):
        for v in reads:
            tp[v] += 1
    assert sum(tp.values()) == k * N == 8 != N
    # it is feasible: throughput >= 1 at every vertex and balanced on a cycle.
    assert all(tp[v] >= 1 for v in reads)
    # yet it is strictly worse than the truth under section 6.1 (n = N)
    prod_truth = binom_product(x, n, N, dict(x))
    prod_flow = binom_product(x, n, N, tp)
    assert prod_flow < prod_truth, (prod_flow, prod_truth)
    print(f"  [B1] S=ACGT L=2: feasible circulation with sum d = {sum(tp.values())}"
          f" != N = {N}; section 6.1 value {prod_flow} < truth {prod_truth}")

    # (B2) S = AAATAT, L = 3, reverse-complement A<->T, per-type lower bound.
    # The flow d* = spec(AAATA) = x is feasible, total 5 != N = 6, and beats the
    # per-type-feasible truth.
    A, T = 0, 1
    comp = {A: T, T: A}
    S = (A, A, A, T, A, T)
    L = 3
    starts = [0, 0, 1, 3, 5]
    x = observed(S, starts, L, comp)
    spS = spec(S, L, comp)
    N = len(S)
    n = sum(x.values())
    assert n == 5 and N == 6
    # truth is feasible under the per-type lower bound (d >= 1 on the support)
    assert set(spS) == set(x)
    assert all(spS[w] >= 1 for w in x)
    # the winning flow is the read-tiled genome AAATA
    D = (A, A, A, T, A)
    spD = spec(D, L, comp)
    assert dict(spD) == dict(x), (spD, x)
    assert sum(spD.values()) == len(D) == 5 != N
    # per-type feasible: every observed molecule appears at least once in D
    assert all(spD[w] >= 1 for w in x)
    prod_truth = binom_product(x, n, N, dict(spS))
    prod_flow = binom_product(x, n, N, dict(spD))
    assert prod_flow > prod_truth, (prod_flow, prod_truth)
    assert prod_flow / prod_truth == Fraction(1280, 243)
    print(f"  [B2] S=AAATAT L=3: feasible flow D=AAATA has sum d = 5 != N = 6;"
          f" beats truth by {prod_flow / prod_truth}")
    return True


# ---------------------------------------------------------------------------
# [C] generic-regime per-occurrence counterexample (n != N) with I_s
# ---------------------------------------------------------------------------
def check_generic_counterexample():
    comp = {0: 1, 1: 0}   # A <-> T/B involution on a two-symbol alphabet
    S = (0, 0, 0, 1, 1)   # AAATT
    D = (0, 0, 0, 0, 1, 1)  # AAAATT
    starts = [0, 1, 4]
    L, N = 3, 5
    x = observed(S, starts, L, comp)
    spS = spec(S, L, comp)
    spD = spec(D, L, comp)
    n = sum(x.values())
    assert n == 3
    assert check_I_s(S, starts, L), "I_s must hold"
    assert set(spS) == set(x), (spS, x)
    assert set(spD) == set(x), (spD, x)
    # per-occurrence feasibility of both truth and competitor
    assert all(spS[w] >= c for w, c in x.items()), (spS, x)
    assert all(spD[w] >= c for w, c in x.items()), (spD, x)
    prod_truth = binom_product(x, n, N, dict(spS))
    prod_cand = binom_product(x, n, N, dict(spD))
    assert prod_cand / prod_truth == Fraction(9, 8)
    print(f"  [C] S=AAATT L=3 n=3 N=5: I_s holds, truth and D=AAAATT are both"
          f" per-occurrence feasible; ratio {prod_cand / prod_truth} > 1")
    return True


# ---------------------------------------------------------------------------
# [D] slice sanity: n = N = G forces d_S = x for a feasible truth
# ---------------------------------------------------------------------------
def check_slice_collapse():
    # Exhaustive over all small circular truths and all read multisets of size
    # n = G; independence of I_s (it is not used).
    import itertools
    checked = 0
    for G in range(2, 7):
        for comp in (None, make_comp(2)):
            sigma = 2
            for S in itertools.product(range(sigma), repeat=G):
                spS = spec(S, L := 2, comp)
                for starts in itertools.combinations_with_replacement(range(G), G):
                    x = observed(S, starts, L, comp)
                    if set(spS) != set(x):
                        continue
                    if not all(spS[w] >= c for w, c in x.items()):
                        continue
                    # n = N = G
                    assert sum(x.values()) == G == len(S)
                    assert dict(spS) == dict(x), (S, starts, spS, x)
                    checked += 1
    print(f"  [D] n=N=G slice: {checked} feasible-truth instances, "
          f"all collapse to d_S = x")
    return True


def main():
    print("=" * 78)
    print("Issue #36: conditional conservation lemma, independent verification")
    print("=" * 78)
    ok = True
    ok &= check_per_coordinate()
    ok &= check_flow_total_identity_refutation()
    ok &= check_generic_counterexample()
    ok &= check_slice_collapse()
    print("\nALL ASSERTIONS PASS" if ok else "\nFAILURE")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
