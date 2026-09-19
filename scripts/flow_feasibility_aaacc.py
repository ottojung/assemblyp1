#!/usr/bin/env python3
"""
Reproducible certificate: the AAACC/AAAAC (and AAABB/AAAAB) fixed-length
binomial witness is feasible for the Medvedev-Brudno Section 6.2
overlap-graph bidirected/flow candidate set, and strictly beats the truth.

Model used (Medvedev & Brudno 2009, "Maximum Likelihood Genome Assembly",
Sections 6.1-6.2), single-strand specialization:

  * vertices of the overlap graph are the distinct observed reads;
  * edges are all overlaps of length 1..L-1, including self-overlaps (loops),
    which Section 3.2 of the paper explicitly allows in its multigraph;
  * a flow is a nonnegative integer circulation with (flow through v) >= 1
    for every read vertex v; d_v := flow through v is the predicted copy count;
  * by Observation 7, for the transitively reduced graph the number of visits
    to a read equals the number of times it occurs as a submolecule, so a flow
    realizes a circular assembly D exactly when its copy vector equals d_D on
    the observed read types;
  * Section 6.2 minimizes the vertex costs c_v(d_v) of the Section 6.1
    separable/binomial approximation with fixed external length N.  As an
    exact rational likelihood this is

        L_flow(d) = prod_v (d_v/N)^{x_v} * (1 - d_v/N)^{n - x_v},

    which is maximized (equivalently cost minimized).

  The full Section 6.1 product-of-binomials over *all* k-mers is also checked;
  the witness beats the truth under both objectives.

Run:
    python3 scripts/flow_feasibility_aaacc.py
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations, product as iproduct
import sys


# --------------------------------------------------------------------------
# basic helpers
# --------------------------------------------------------------------------
def windows(seq, L):
    n = len(seq)
    return Counter(tuple(seq[(i + j) % n] for j in range(L)) for i in range(n))


def overlap_lengths(u, v):
    """All overlap lengths l in 1..L-1 with u[-l:] == v[:l]."""
    L = len(u)
    return [l for l in range(1, L) if u[L - l:] == v[:l]]


def build_overlap_graph(reads, loops=True):
    """All directed overlap edges (i, j, l), including self-loops."""
    edges = []
    for i, u in enumerate(reads):
        for j, v in enumerate(reads):
            if i == j and not loops:
                continue
            for l in overlap_lengths(u, v):
                edges.append((i, j, l))
    return edges


def feasible_copy_vectors(nv, edges, cap):
    """Enumerate integer circulations with edge flows <= cap and every vertex
    visited at least once.  Returns the set of copy vectors d (inflow per
    vertex)."""
    out = set()
    for f in iproduct(range(cap + 1), repeat=len(edges)):
        inn = [0] * nv
        outflow = [0] * nv
        for val, (i, j, _l) in zip(f, edges):
            outflow[i] += val
            inn[j] += val
        if inn == outflow and all(v >= 1 for v in inn):
            out.add(tuple(inn))
    return out


def witness_flow_for_vector(nv, edges, target, cap):
    """Return an edge-flow vector realizing the target copy vector, or None."""
    for f in iproduct(range(cap + 1), repeat=len(edges)):
        inn = [0] * nv
        outflow = [0] * nv
        for val, (i, j, _l) in zip(f, edges):
            outflow[i] += val
            inn[j] += val
        if inn == outflow and tuple(inn) == target:
            return f
    return None


def flow_likelihood(d, x, n, N):
    """Section 6.2 vertex-cost likelihood, exact rational."""
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
    """Full Section 6.1 product of binomial marginals over every length-L type
    in `alphabet`; exact rational."""
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


def rotations(seq):
    return [seq[i:] + seq[:i] for i in range(len(seq))]


def canonical(seq):
    return min(rotations(seq))


# --------------------------------------------------------------------------
# I_s checks (Bresler/Shomorony semantics)
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
                if S[(t1 - 1) % G] != S[(t2 - 1) % G] and \
                   S[(t1 + ell) % G] != S[(t2 + ell) % G]:
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
        return False, "no coverage"
    for ell, (t1, t2, t3) in triple_repeats(S):
        for t in (t1, t2, t3):
            if not bridged_copy(S, t, ell, starts, L):
                return False, "unbridged triple copy"
    for (l1, a1, a3), (l2, a2, a4) in interleaved_pairs(S):
        if not (bridged_copy(S, a1, l1, starts, L) or
                bridged_copy(S, a3, l1, starts, L) or
                bridged_copy(S, a2, l2, starts, L) or
                bridged_copy(S, a4, l2, starts, L)):
            return False, "unbridged interleaved pair"
    return True, "ok"


# --------------------------------------------------------------------------
# checks
# --------------------------------------------------------------------------
def analyse_instance(name, S, starts, L, D, alphabet=("A", "C", "T", "G"),
                     cap=6):
    """Print and return a certificate dict for one witness instance."""
    print("-" * 72)
    print(f"{name}: truth S={''.join(S)} (G={len(S)}), L={L}, "
          f"starts={starts}, competitor D={''.join(D)}")
    reads = [tuple(S[(r + j) % len(S)] for j in range(L)) for r in starts]
    rd = sorted(set(reads))
    ok, why = satisfies_Is(S, starts, L)
    print(f"  reads = {[''.join(r) for r in reads]}; distinct = "
          f"{[''.join(r) for r in rd]}")
    print(f"  I_s (coverage + all-bridged triples + bridged interleaved): "
          f"{ok} ({why})")
    assert ok, "hypothesis I_s fails"

    # the graph must include loops; check that the competitor uses one
    edges = build_overlap_graph(rd, loops=True)
    loops = [( ''.join(rd[i]), l) for i, j, l in edges if i == j]
    print(f"  self-overlaps (loops): {loops}")

    xcount = Counter(reads)
    x = tuple(xcount[r] for r in rd)
    n, N = len(reads), len(S)
    dS = tuple(windows(S, L).get(r, 0) for r in rd)
    dD = tuple(windows(D, L).get(r, 0) for r in rd)

    dvs = feasible_copy_vectors(len(rd), edges, cap)
    print(f"  feasible copy vectors (cap={cap}), first few: "
          f"{sorted(dvs)[:8]} ...")
    print(f"  d_truth|reads = {dS}  feasible: {dS in dvs}")
    print(f"  d_D|reads     = {dD}  feasible: {dD in dvs}")
    assert dS in dvs and dD in dvs, "witness copy vector not flow-feasible"

    f = witness_flow_for_vector(len(rd), edges, dD, cap)
    used = [( ''.join(rd[i]), ''.join(rd[j]), l, v)
            for (i, j, l), v in zip(edges, f) if v > 0]
    print(f"  witnessing flow for d_D (u -> v, overlap, value): {used}")

    # Observation 7: visits equal submolecule occurrences of D
    print(f"  D windows = {dict(windows(D, L))}")
    print(f"  observed visits equal D-window occurrences for observed "
          f"types: {dD == tuple(windows(D, L).get(r, 0) for r in rd)}")

    # objective ratios
    vS = flow_likelihood(dS, x, n, N)
    vD = flow_likelihood(dD, x, n, N)
    print(f"  Section 6.2 vertex-cost L_flow: truth={vS}, D={vD}, "
          f"D/truth={vD / vS}")
    fS = full_binom_likelihood(S, L, xcount, n, N, alphabet)
    fD = full_binom_likelihood(D, L, xcount, n, N, alphabet)
    print(f"  Full Section 6.1 binomial (all types): truth={fS}, D={fD}, "
          f"D/truth={fD / fS}")
    assert vD > vS and fD > fS, "competitor does not strictly beat truth"

    # Section 6.2 optimum over all feasible copy vectors
    best = max(dvs, key=lambda d: flow_likelihood(d, x, n, N))
    print(f"  Section 6.2 argmax over feasible flows: {best} "
          f"(ratio vs truth {flow_likelihood(best, x, n, N) / vS})")
    return {"S": S, "D": D, "dS": dS, "dD": dD, "ratio_flow": vD / vS,
            "ratio_full": fD / fS, "argmax": best,
            "argmax_ratio": flow_likelihood(best, x, n, N) / vS}


def check_witnesses():
    print("=" * 72)
    print("WITNESS CERTIFICATES")
    print("=" * 72)
    # The AAACC / AAAAC witness (relabelled B -> C of the AAABB / AAAAB one)
    a = analyse_instance("AAACC witness", tuple("AAACC"), [0, 1, 4], 3,
                         tuple("AAAAC"), alphabet=("A", "C"), cap=5)
    # The original repo witness (isomorphic relabelling B <-> C)
    b = analyse_instance("AAABB witness", tuple("AAABB"), [0, 1, 4], 3,
                         tuple("AAAAB"), alphabet=("A", "B"), cap=5)
    return a, b


def omin_sensitivity(S=("A", "A", "A", "C", "C"), starts=(0, 1, 4), L=3,
                     D=("A", "A", "A", "A", "C")):
    """The witness needs overlap threshold omin = 1.  With omin = 2 the truth
    itself is not flow-feasible, so the model is ill-posed there."""
    print("=" * 72)
    print("OVERLAP-THRESHOLD (omin) SENSITIVITY")
    print("=" * 72)
    reads = [tuple(S[(r + j) % len(S)] for j in range(L)) for r in starts]
    rd = sorted(set(reads))
    dS = tuple(windows(S, L).get(r, 0) for r in rd)
    dD = tuple(windows(D, L).get(r, 0) for r in rd)
    all_edges = build_overlap_graph(rd, loops=True)
    result = {}
    for omin in (1, 2):
        edges = [e for e in all_edges if e[2] >= omin]
        dvs = feasible_copy_vectors(len(rd), edges, 5)
        result[omin] = (dS in dvs, dD in dvs)
        print(f"  omin={omin}: |E|={len(edges)}, truth feasible={dS in dvs}, "
              f"D feasible={dD in dvs}, #feasible copy vectors={len(dvs)}")
    assert result[1] == (True, True) and result[2] == (False, False)
    return result


def smallest_counterexample(maxG=4, cap=4, alphabet=("A", "C")):
    """Search for the smallest same-length flow-feasible counterexample under
    the full Section 6.1 binomial objective.  G=3 has none; G=4 first hit is
    S=AACC with D=ACAC."""
    print("=" * 72)
    print("SMALLEST SAME-LENGTH FLOW-FEASIBLE COUNTEREXAMPLE SEARCH")
    print(f"alphabet={alphabet}, G <= {maxG}, edge cap={cap}")
    print("=" * 72)
    hits = []
    for G in range(3, maxG + 1):
        nS = 0
        for S in iproduct(alphabet, repeat=G):
            if S != canonical(S) or len(set(S)) < 2:
                continue
            for L in range(2, G):
                for k in range(1, G + 1):
                    for st in combinations(range(G), k):
                        ok, _ = satisfies_Is(S, st, L)
                        if not ok:
                            continue
                        reads = [tuple(S[(r + j) % G] for j in range(L))
                                 for r in st]
                        rd = sorted(set(reads))
                        if len(rd) < 2:
                            continue
                        edges = build_overlap_graph(rd, loops=True)
                        if len(edges) > 9:
                            continue
                        x = Counter(reads)
                        n, N = len(reads), G
                        dvs = feasible_copy_vectors(len(rd), edges, cap)
                        dS = tuple(windows(S, L).get(r, 0) for r in rd)
                        if dS not in dvs:
                            continue
                        fS = full_binom_likelihood(
                            S, L, x, n, N, alphabet)
                        for D in iproduct(alphabet, repeat=G):
                            if D != canonical(D) or D == canonical(S):
                                continue
                            dD = windows(D, L)
                            if any(dD.get(r, 0) < 1 for r in rd):
                                continue
                            if tuple(dD.get(r, 0) for r in rd) not in dvs:
                                continue
                            fD = full_binom_likelihood(
                                D, L, x, n, N, alphabet)
                            if fD > fS:
                                hits.append((G, L, "".join(S),
                                             "".join(D), fS, fD))
            nS += 1
        print(f"  scanned G={G}: hits so far {len(hits)}")
    hits.sort(key=lambda t: (t[0], t[1]))
    for h in hits:
        print(f"  G={h[0]} L={h[1]} S={h[2]} D={h[3]} "
              f"ratio={h[5] / h[4]}")
    assert not any(h[0] == 3 for h in hits), "unexpected G=3 counterexample"
    assert hits and hits[0][:4] == (4, 2, "AACC", "ACAC"), \
        "smallest counterexample changed"
    print("  smallest: G=4, L=2, S=AACC, D=ACAC (full-objective ratio 4096/729)")
    return hits


if __name__ == "__main__":
    check_witnesses()
    omin_sensitivity()
    smallest_counterexample()
    print()
    print("ALL CHECKS PASSED")
