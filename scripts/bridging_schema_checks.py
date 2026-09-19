#!/usr/bin/env python3
"""
Reproducible checks for docs/bridging-schemas-and-flow-feasibility-gaps.md.

Checks, in order:
  A. Tandem-repetition invariance of the exact multinomial likelihood.
  B. Witness that I_s does not bound maximal repeat length (S = ABCABD, L = 3).
  C. Falsification of the "singleton theorem" for Variant F as stated
     (S = ACGTG, L = 3, reads ACG/CGT/TGA: coverage + distinct reads, but no
     single closed walk through the overlap graph).
  D. Repeat-free per-occurrence flow model: for S = AABB, L = 2 with the full
     spectrum observed, the truth is an exact maximizer and the tie class is
     exactly the spectra k * d_S.

All arithmetic uses exact rationals (fractions.Fraction).  Run from anywhere:
    python3 scripts/bridging_schema_checks.py
"""
import os
import sys
from collections import Counter
from fractions import Fraction
from itertools import product as iterproduct

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from fixed_length_bridging_search_v2 import (  # noqa: E402
    check_I_s,
    find_all_interleaved_pairs,
    find_all_maximal_repeat_pairs,
    find_all_triple_repeats,
)


def windows(seq, L):
    """Counter of length-L circular windows of seq."""
    n = len(seq)
    return Counter(tuple(seq[(i + j) % n] for j in range(L)) for i in range(n))


def exact_ll(cand, obs, L):
    """Exact multinomial likelihood ordering product (coefficient dropped)."""
    d = windows(cand, L)
    M = len(cand)
    val = Fraction(1)
    for w, x in obs.items():
        c = d.get(w, 0)
        if c == 0:
            return Fraction(0)
        val *= Fraction(c, M) ** x
    return val


def check_A():
    print("=== A. Tandem-repetition invariance ===")
    ok = True
    trials = [
        (tuple("ACGT"), 2, Counter({("A", "C"): 2, ("G", "T"): 1})),
        (tuple("ABC"), 2, Counter({("A", "B"): 1, ("B", "C"): 1, ("C", "A"): 1})),
        (("A",), 3, Counter({("A", "A", "A"): 5})),
        (tuple("ACGT"), 3, Counter({("A", "C", "G"): 1, ("C", "G", "T"): 1})),
    ]
    for base, L, obs in trials:
        vals = [exact_ll(base * k, obs, L) for k in range(1, 7)]
        same = len(set(vals)) == 1
        ok &= same
        print(f"  base={''.join(base):>4} L={L}: k=1..6 equal -> {same}")
    print(f"  RESULT: {'PASS' if ok else 'FAIL'}\n")
    return ok


def check_B():
    print("=== B. I_s does not bound maximal repeat length ===")
    S = tuple("ABCABD")
    G, L = len(S), 3
    starts = list(range(G))
    reps = find_all_maximal_repeat_pairs(S)
    triples = find_all_triple_repeats(S)
    inter = find_all_interleaved_pairs(S)
    maxlen = max(e for e, _, _ in reps)
    ok = (check_I_s(S, starts, L) and not triples and not inter
          and maxlen >= L - 1)
    print(f"  S=ABCABD G=6 L=3, R = all six windows")
    print(f"  I_s holds: {check_I_s(S, starts, L)}")
    print(f"  maximal repeats (len,(t1,t2)): {[(e, p) for e, p, _ in reps]}")
    print(f"  triple repeats: {len(triples)}, interleaved pairs: {len(inter)}")
    print(f"  max repeat length = {maxlen} >= L-1 = {L - 1}")
    print(f"  RESULT: {'PASS' if ok else 'FAIL'}\n")
    return ok


def overlap_adj(reads):
    n = len(reads)
    return [[j for j in range(n) if i != j and reads[i][1:] == reads[j][:-1]]
            for i in range(n)]


def closed_walk_covers_all(reads):
    n = len(reads)
    adj = overlap_adj(reads)
    full = (1 << n) - 1

    def dfs(start, cur, mask, length):
        if length > 2 * n:
            return False
        if cur == start and mask == full and length > 0:
            return True
        for nxt in adj[cur]:
            if dfs(start, nxt, mask | (1 << nxt), length + 1):
                return True
        return False

    return any(dfs(s, s, 1 << s, 0) for s in range(n))


def check_C():
    print("=== C. Variant F singleton theorem fails as stated ===")
    S = tuple("ACGTG")
    G, L = len(S), 3
    starts = [0, 1, 3]
    reads = [tuple(S[(r + d) % G] for d in range(L)) for r in starts]
    rep_free = len(windows(S, L)) == G
    coverage = (set((r + d) % G for r in starts for d in range(L))
                == set(range(G)))
    adj = overlap_adj(reads)
    closed = closed_walk_covers_all(reads)
    ok = rep_free and coverage and not closed
    print(f"  S=ACGTG L=3 starts={starts} reads={[''.join(r) for r in reads]}")
    print(f"  repeat-free: {rep_free}, coverage: {coverage}")
    print(f"  overlap adjacency: {adj}")
    print(f"  single closed walk covering all reads exists: {closed}")
    print(f"  RESULT: {'PASS' if ok else 'FAIL'}\n")
    return ok


def check_D():
    print("=== D. Repeat-free per-occurrence flow: truth is an exact maximizer ===")
    S = tuple("AABB")
    L, maxlen = 2, 12
    dS = windows(S, L)
    assert all(v == 1 for v in dS.values())
    suppS = set(dS)
    G = len(S)
    obs = {w: 1 for w in suppS}
    llS = exact_ll(S, obs, L)
    best = Fraction(0)
    maximizers = set()
    for M in range(1, maxlen + 1):
        for D in iterproduct("AB", repeat=M):
            dD = windows(D, L)
            if not set(dD) <= suppS:
                continue
            if any(dD.get(w, 0) < 1 for w in suppS):
                continue
            ll = exact_ll(D, obs, L)
            can = min(D[i:] + D[:i] for i in range(len(D)))
            if ll > best:
                best, maximizers = ll, {can}
            elif ll == best:
                maximizers.add(can)
    tie_ok = all(
        set(windows(m, L)) == suppS and len(set(windows(m, L).values())) == 1
        for m in maximizers
    )
    ok = (best == llS) and tie_ok
    print(f"  S=AABB L=2, obs = one copy of each window, |maximizers|={len(maximizers)}")
    print(f"  ll(S)={llS}, max ll(D)={best}, equal: {best == llS}")
    print(f"  every maximizer has spectrum k*d_S: {tie_ok}")
    print(f"  tandem S, S^2, S^3 are maximizers: "
          f"{all(tuple(S * k) in maximizers for k in (1, 2, 3))}")
    print(f"  RESULT: {'PASS' if ok else 'FAIL'}\n")
    return ok


def main():
    results = [check_A(), check_B(), check_C(), check_D()]
    print("OVERALL:", "ALL PASS" if all(results) else "FAILURES PRESENT")
    return 0 if all(results) else 1


if __name__ == "__main__":
    sys.exit(main())
