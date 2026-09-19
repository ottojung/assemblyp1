#!/usr/bin/env python3
"""
Audit of the "Section 6.2 flow feasibility of the AAACC/AAAAC witness" claim.

Question.  Does the repository's fixed-length binomial witness
(truth S = AAACC, reads AAA/AAC/CAA, competitor D = AAAAC) correspond to a
feasible Medvedev-Brudno Section 6.2 flow solution?

The claim on branch `agent/flow-model-0919b`
(`docs/flow-feasibility-aaacc-witness.md`) checks *copy-vector* feasibility:
a candidate is accepted when its observed-read copy vector d_D can be realized
by *some* integer circulation in the read overlap graph.  Section 6.2, however,
interprets a flow through Observation 7 as the *set of walks* it decomposes
into, and a single circular genome D is realized only when one closed walk in
the (transitively reduced) overlap graph *spells* D.  A flow that decomposes
into several walks is explicitly a "non-contiguous assembly" (Medvedev-Brudno
Section 6.2, last sentence), not a sequence.

This script separates the two readings with exact arithmetic:

  (weak,  copy vector)  d_D is a feasible circulation copy vector;
  (strong, walk spelling) some closed walk spells D.

Main findings (see docs/flow-feasibility-aaacc-witness-audit.md):

  * The competitor D = AAAAC is feasible even in the strong reading: the closed
    walk AAA -2-> AAA -2-> AAC -1-> CAA -2-> AAA spells D.
  * The truth S = AAACC is feasible only in the weak reading.  It is NOT
    walk-spellable: the only edge out of AAC places CAA two positions later,
    while in S the CAA window sits three positions after the AAC window, and
    the intermediate windows ACC/CCA are not observed read types.  Hence
    S is not in the sequence-level Section 6.2 candidate set, and the witness
    does not exhibit a sequence-level counterexample.
  * The same defect holds for the relabelled AAABB/AAAAB witness and for the
    smallest fixed-length flow-feasible instance S = AACC, D = ACAC.
  * Under the strong reading, no I_s-satisfying source-faithful counterexample
    exists for binary G <= 8 (and ternary G <= 5): every instance whose truth is
    flow-feasible has the truth as a maximizer under the literal Section 6.2
    vertex cost.  Dropping the repeat-bridging clauses of I_s immediately
    produces many, so the bridging hypothesis is load-bearing here too.

All arithmetic uses fractions.Fraction.  Run:
    python3 scripts/flow_feasibility_aaacc_audit.py
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations, product as iproduct
import sys


# --------------------------------------------------------------------------
# finite circular-string helpers
# --------------------------------------------------------------------------
def windows(seq, L):
    n = len(seq)
    return Counter(tuple(seq[(i + j) % n] for j in range(L)) for i in range(n))


def overlaps(u, v):
    L = len(u)
    return [l for l in range(1, L) if u[L - l:] == v[:l]]


def build_edges(reads, loops=True):
    return [(i, j, l)
            for i, u in enumerate(reads)
            for j, v in enumerate(reads)
            if (loops or i != j)
            for l in overlaps(u, v)]


def rotations(seq):
    return [seq[i:] + seq[:i] for i in range(len(seq))]


def canon(seq):
    return min(rotations(seq))


def spelled_genomes(reads, edges, G, max_edges):
    """Canonical circular genomes of length G spelled by a closed walk in the
    directed overlap graph on `reads`.  Shift of an edge u->v of overlap l is
    len(u) - l; a closed walk spells a circular string of length equal to the
    sum of its edge shifts."""
    adj = {}
    for e in edges:
        adj.setdefault(e[0], []).append(e)
    found = set()

    def dfs(start, cur, seq, shift, arr):
        if cur == start and seq and shift == G:
            if all(x is not None for x in arr):
                found.add(canon(tuple(arr)))
        if len(seq) >= max_edges or shift >= G:
            return
        for (i, j, l) in adj.get(cur, []):
            ns = shift + len(reads[i]) - l
            if ns > G:
                continue
            newarr = arr[:]
            ok = True
            for k, ch in enumerate(reads[i]):
                p = (shift + k) % G
                if newarr[p] is not None and newarr[p] != ch:
                    ok = False
                    break
                newarr[p] = ch
            if not ok:
                continue
            dfs(start, j, seq + [(i, j, l)], ns, newarr)

    for st in range(len(reads)):
        dfs(st, st, [], 0, [None] * G)
    return found


# --------------------------------------------------------------------------
# Medvedev-Brudno Section 6.1/6.2 objective (exact, fixed external length N)
# --------------------------------------------------------------------------
def mb_vertex_likelihood(d, x, n, N):
    """Literal Section 6.1 binomial approximation restricted to the Section 6.2
    read vertices, up to the d-independent binomial coefficients:
        prod_v (d_v/N)^{x_v} (1 - d_v/N)^{n - x_v}.
    This is exp(-sum_v c_v(d_v)) for c_v(d) = -x_v log d - (n - x_v) log(N-d)
    plus a d-independent constant (Medvedev-Brudno 2009, equation for c_i)."""
    val = Fraction(1)
    for dv, xv in zip(d, x):
        if xv == 0:
            continue
        val *= Fraction(dv, N) ** xv
        e = n - xv
        if e > 0:
            if N - dv <= 0:
                return Fraction(0)
            val *= Fraction(N - dv, N) ** e
    return val


def full_binom_likelihood(D, L, x, n, N, alphabet):
    """Full product over every length-L type in `alphabet` (includes unobserved
    types, which contribute (1 - d/N)^n)."""
    dD = windows(D, L)
    val = Fraction(1)
    for t in iproduct(alphabet, repeat=L):
        xv = x.get(t, 0)
        dv = dD.get(t, 0)
        if xv > 0:
            val *= Fraction(dv, N) ** xv
        e = n - xv
        if e > 0:
            if N - dv <= 0:
                return Fraction(0)
            val *= Fraction(N - dv, N) ** e
    return val


# --------------------------------------------------------------------------
# I_s (Shomorony Eq. (1); Bresler repeat semantics)
# --------------------------------------------------------------------------
def bridged_copy(S, t, ell, starts, L):
    G = len(S)
    for r in starts:
        for tt in (t, t + G, t - G):
            if r < tt and tt + ell < r + L:
                return True
    return False


def maximal_repeat_pairs(S):
    G = len(S)
    out = []
    for ell in range(1, G):
        seen = {}
        for t in range(G):
            w = tuple(S[(t + j) % G] for j in range(ell))
            seen.setdefault(w, []).append(t)
        for w, ts in seen.items():
            for t1, t2 in combinations(ts, 2):
                if (S[(t1 - 1) % G] != S[(t2 - 1) % G] and
                        S[(t1 + ell) % G] != S[(t2 + ell) % G]):
                    out.append((ell, t1, t2))
    return out


def triple_repeats(S):
    G = len(S)
    out = []
    for ell in range(1, G):
        seen = {}
        for t in range(G):
            w = tuple(S[(t + j) % G] for j in range(ell))
            seen.setdefault(w, []).append(t)
        for w, ts in seen.items():
            for t1, t2, t3 in combinations(ts, 3):
                pre = [S[(t - 1) % G] for t in (t1, t2, t3)]
                post = [S[(t + ell) % G] for t in (t1, t2, t3)]
                if len(set(pre)) > 1 and len(set(post)) > 1:
                    out.append((ell, (t1, t2, t3)))
    return out


def interleaved_pairs(S):
    reps = maximal_repeat_pairs(S)
    out = []
    for (l1, a1, a3), (l2, a2, a4) in combinations(reps, 2):
        labels = [lab for _, lab in sorted(
            [(a1, "r1"), (a2, "r2"), (a3, "r1"), (a4, "r2")])]
        if labels == ["r1", "r2", "r1", "r2"]:
            out.append(((l1, a1, a3), (l2, a2, a4)))
    return out


def covers(S, starts, L):
    G = len(S)
    return set((r + j) % G for r in starts for j in range(L)) == set(range(G))


def satisfies_Is(S, starts, L):
    if not covers(S, starts, L):
        return False
    for ell, (t1, t2, t3) in triple_repeats(S):
        for t in (t1, t2, t3):
            if not bridged_copy(S, t, ell, starts, L):
                return False
    for (l1, a1, a3), (l2, a2, a4) in interleaved_pairs(S):
        if not (bridged_copy(S, a1, l1, starts, L) or
                bridged_copy(S, a3, l1, starts, L) or
                bridged_copy(S, a2, l2, starts, L) or
                bridged_copy(S, a4, l2, starts, L)):
            return False
    return True


def instance(S, starts, L):
    reads = sorted({tuple(S[(r + j) % len(S)] for j in range(L))
                    for r in starts})
    counts = Counter(tuple(S[(r + j) % len(S)] for j in range(L))
                     for r in starts)
    x = tuple(counts[r] for r in reads)
    dS = tuple(windows(S, L).get(r, 0) for r in reads)
    return reads, x, dS


# --------------------------------------------------------------------------
# checks
# --------------------------------------------------------------------------
def check_source_objective():
    """The certificate's exact objective reproduces the two ratios it reports."""
    S, starts, L = tuple("AAACC"), [0, 1, 4], 3
    D = tuple("AAAAC")
    reads, x, dS = instance(S, starts, L)
    dD = tuple(windows(D, L).get(r, 0) for r in reads)
    n, N = sum(x), len(S)
    assert reads == [("A", "A", "A"), ("A", "A", "C"), ("C", "A", "A")]
    assert dS == (1, 1, 1) and dD == (2, 1, 1)
    vS = mb_vertex_likelihood(dS, x, n, N)
    vD = mb_vertex_likelihood(dD, x, n, N)
    assert vS == Fraction(4096, 1953125) and vD == Fraction(4608, 1953125)
    assert vD / vS == Fraction(9, 8)
    fS = full_binom_likelihood(S, L, Counter({tuple(S[(r + j) % len(S)]
                                                   for j in range(L)): 1
                                              for r in starts}), n, N,
                               ("A", "C"))
    fD = full_binom_likelihood(D, L, Counter({tuple(S[(r + j) % len(S)]
                                                    for j in range(L)): 1
                                               for r in starts}), n, N,
                                ("A", "C"))
    assert fS == Fraction(16777216, 30517578125)
    assert fD == Fraction(294912, 244140625)
    assert fD / fS == Fraction(1125, 512)
    print("[source] MB Section 6.1 binomial approx and c_i formula reproduced; "
          "vertex ratios 9/8, full ratios 1125/512 match the certificate.")
    return S, starts, L, D, reads, x, dS, dD


def check_witness_spelling(S, starts, L, D, reads, x, dS, dD):
    G = len(S)
    edges = build_edges(reads, loops=True)
    spelled = spelled_genomes(reads, edges, G, max_edges=G)
    print("[witness] I_s =", satisfies_Is(S, starts, L))
    print("[witness] overlap edges:", [''.join(reads[i]) + '->' +
          ''.join(reads[j]) + f'({l})' for (i, j, l) in edges])
    print("[witness] length-5 genomes spelled by closed walks:",
          sorted(''.join(t) for t in spelled))
    assert satisfies_Is(S, starts, L)
    # weak reading: both copy vectors are feasible circulations
    assert canon(S) not in spelled, "truth unexpectedly walk-spellable"
    assert canon(D) in spelled, "competitor unexpectedly not walk-spellable"
    # exact obstruction: the only edge out of AAC goes to CAA with shift 2
    aac = reads.index(("A", "A", "C"))
    out_edges = [(reads[j], l) for (i, j, l) in edges if i == aac]
    print("[witness] outgoing edges of AAC:", out_edges)
    assert out_edges == [(("C", "A", "A"), 1)]
    # weak reading: d_S = (1,1,1) is realized by the cycle AAA->AAC->CAA->AAA
    cyc = [(reads.index(("A", "A", "A")), reads.index(("A", "A", "C")), 1),
           (reads.index(("A", "A", "C")), reads.index(("C", "A", "A")), 1),
           (reads.index(("C", "A", "A")), reads.index(("A", "A", "A")), 1)]
    for e in cyc:
        assert e in edges, e
    inn = [0] * len(reads)
    for (i, j, l) in cyc:
        inn[j] += 1
    assert tuple(inn) == dS == (1, 1, 1)
    print("[witness] weak reading: d_S = (1,1,1) is a feasible circulation "
          "(cycle AAA->AAC->CAA->AAA) but it spells a length-6 genome, not S.")
    shift = L - out_edges[0][1]
    # in S, AAC occurs only at start 1 and CAA only at start 4 (shift 3)
    assert [t for t, w in ((t, tuple(S[(t + j) % G] for j in range(L)))
                           for t in range(G)) if w == ("A", "A", "C")] == [1]
    assert [t for t, w in ((t, tuple(S[(t + j) % G] for j in range(L)))
                           for t in range(G)) if w == ("C", "A", "A")] == [4]
    assert 1 + shift == 3 != 4
    print("[witness] obstruction: AAC forces CAA at shift", shift,
          "(position 3), but S places CAA at position 4; windows ACC/CCA "
          "are unobserved.")
    print("[witness] D = AAAAC is spelled by AAA -2-> AAA -2-> AAC -1-> CAA "
          "-2-> AAA.")
    return spelled


def check_nearby():
    cases = [
        ("AAACC/AAAAC", tuple("AAACC"), [0, 1, 4], 3, tuple("AAAAC")),
        ("AAABB/AAAAB", tuple("AAABB"), [0, 1, 4], 3, tuple("AAAAB")),
        ("AACC/ACAC", tuple("AACC"), [1, 3], 2, tuple("ACAC")),
    ]
    for name, S, starts, L, D in cases:
        reads, x, dS = instance(S, starts, L)
        edges = build_edges(reads, loops=True)
        spelled = spelled_genomes(reads, edges, len(S), max_edges=len(S))
        assert satisfies_Is(S, starts, L)
        assert canon(S) not in spelled
        assert canon(D) in spelled
        print(f"[nearby] {name}: truth spellable=False, competitor "
              f"spellable=True, spelled={sorted(''.join(t) for t in spelled)}")


def run_search(Gmax, alphabet, require_Is, label):
    """Return (#truth-flow-feasible instances, [counterexamples]).  A
    counterexample is a same-length competitor that is itself walk-spellable
    and strictly beats the truth under the Section 6.2 vertex cost."""
    hits = []
    tally = 0
    for G in range(3, Gmax + 1):
        for S in iproduct(alphabet, repeat=G):
            if S != canon(S) or len(set(S)) < 2:
                continue
            for L in range(2, G):
                for k in range(1, G + 1):
                    for st in combinations(range(G), k):
                        if require_Is and not satisfies_Is(S, st, L):
                            continue
                        if not require_Is and not covers(S, st, L):
                            continue
                        reads, x, dS = instance(S, st, L)
                        if len(reads) < 2:
                            continue
                        edges = build_edges(reads, loops=True)
                        spelled = spelled_genomes(reads, edges, G,
                                                  max_edges=G)
                        if canon(S) not in spelled:
                            continue
                        n, N = sum(x), G
                        vS = mb_vertex_likelihood(dS, x, n, N)
                        tally += 1
                        for D in sorted(spelled):
                            if D == canon(S):
                                continue
                            dD = tuple(windows(D, L).get(r, 0) for r in reads)
                            if any(v < 1 for v in dD):
                                continue
                            vD = mb_vertex_likelihood(dD, x, n, N)
                            if vD > vS:
                                hits.append((G, L, "".join(S), "".join(D),
                                             st, x, vD / vS))
                                break
        print(f"[{label}] G={G}: truth-flow-feasible instances={tally}, "
              f"counterexamples={len(hits)}")
    return tally, hits


def check_search():
    tally, hits = run_search(8, ("A", "C"), True, "I_s")
    assert hits == [], hits
    print(f"[search] binary G<=8 with I_s and truth flow-feasible: "
          f"{tally} instances, 0 sequence-level counterexamples.")
    _, ctrl = run_search(7, ("A", "C"), False, "control(no repeat clauses)")
    assert ctrl, "control unexpectedly empty"
    ctrl_min = min(ctrl, key=lambda r: (r[0], r[1]))
    G, L, Sc, Dc, stc, xc, ratio = ctrl_min
    assert (G, L, Sc, Dc) == (5, 2, "AAAAC", "AACAC"), ctrl_min
    assert not satisfies_Is(tuple(Sc), list(stc), L), ctrl_min
    print(f"[control] coverage + truth flow-feasible but no repeat-bridging "
          f"clauses: {len(ctrl)} counterexamples; smallest {ctrl_min} "
          f"(I_s = {satisfies_Is(tuple(Sc), list(stc), L)}).")
    t3, hits3 = run_search(5, ("A", "B", "C"), True, "I_s ternary")
    assert hits3 == [], hits3
    print(f"[search] ternary G<=5 with I_s and truth flow-feasible: "
          f"{t3} instances, 0 sequence-level counterexamples.")


def main():
    print("=" * 74)
    print("AUDIT: Section 6.2 flow feasibility of the AAACC/AAAAC witness")
    print("=" * 74)
    S, starts, L, D, reads, x, dS, dD = check_source_objective()
    check_witness_spelling(S, starts, L, D, reads, x, dS, dD)
    check_nearby()
    print("=" * 74)
    check_search()
    print("=" * 74)
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
