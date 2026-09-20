#!/usr/bin/env python3
"""
Why does the recorded section 6.2 sequence-level search find no counterexample?

This script verifies, with exact rational arithmetic, the structural explanation:

  (Lemma 2 / Theorem 3 of mathematics/section62-peroccurrence-search-degeneracy.md)
  In the slice "number of reads n = external N = true genome length G", the
  per-occurrence feasibility of the truth forces d_S = x (the truth is
  *read-tiled*).  The literal section 6.1 separable binomial is, coordinatewise,
  maximized at d_w = N x_w / n = x_w, so no support-equal, lower-bounded candidate
  (of any length) can strictly beat the truth.  The recorded zero is therefore a
  theorem about that slice, and the bridging hypothesis I_s plays no role in it.

  Section 6.2 as stated in the source has n (number of reads) independent of N
  (true genome length), and the recorded search fixes n = N = G.  Outside that
  slice the explanation fails and sequence-level section 6.2 per-occurrence
  counterexamples exist (with I_s and a feasible truth).

Exits non-zero on any assertion failure.  Computational checks are exact
(fractions.Fraction); the analytic lemmas are checked symbolically/exhaustively
over the relevant finite integer ranges.

Run:  python3 scripts/verify_se62_peroccurrence_slice.py
"""
import sys
import time
from fractions import Fraction
from itertools import product as iproduct, combinations_with_replacement
from collections import defaultdict

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import se62_bidirected_feasibility_search as m  # noqa: E402


# ---------------------------------------------------------------------------
# Lemma 1: the per-coordinate section 6.1 binomial factor is maximized at
# d = N x / n, and at d = x when n = N.
# ---------------------------------------------------------------------------
def phi(x, n, N, d):
    """The d-dependent part of the section 6.1 marginal: (d/N)^x (1-d/N)^(n-x)."""
    return Fraction(d, N) ** x * Fraction(N - d, N) ** (n - x)


def check_per_coordinate_max():
    """Exhaustively verify the per-coordinate maximum for small n, N."""
    checks = 0
    for N in range(2, 9):
        for n in range(1, N + 1):
            for x in range(0, n + 1):
                vals = [(phi(x, n, N, d), d) for d in range(0, N + 1)]
                if n == N and 0 < x < n:
                    # unique maximizer at d = x
                    best = max(vals)
                    assert best[1] == x and phi(x, n, N, x) > 0
                    assert all(phi(x, n, N, d) < phi(x, n, N, x)
                               for d in range(0, N + 1) if d != x)
                # general: no value exceeds the candidate real maximizer's value
                dstar = Fraction(N * x, n)
                if dstar.denominator == 1 and 0 <= dstar <= N:
                    dstar = int(dstar)
                    assert all(phi(x, n, N, d) <= phi(x, n, N, dstar)
                               for d in range(0, N + 1))
                checks += 1
    # exact rational certificate of the stationary point d = N x / n:
    # d/dd log phi = x/d - (n-x)/(N-d); substituting d = N x / n gives zero.
    for N in range(2, 9):
        for n in range(1, N + 1):
            for x in range(1, n):
                d = Fraction(N * x, n)
                deriv = Fraction(x, 1) / d - Fraction(n - x, 1) / (N - d)
                assert deriv == 0, (N, n, x, deriv)
    print(f"  [A] per-coordinate maximum verified ({checks} (N,n,x) cases; "
          f"exact stationary point d = N x / n)")
    return True


# ---------------------------------------------------------------------------
# Lemma 2 / Theorem 3: exhaustive verification of the slice collapse and of
# "no candidate beats the truth" in the recorded search slice (n = N = G).
# ---------------------------------------------------------------------------
def collapse_and_no_cex(G, L, sigma, comp):
    """Return (instances, collapse_violations, cex) over the n=N=G slice."""
    inst = collapse_viol = cex = 0
    by_support = defaultdict(dict)
    for mm in range(1, 2 * G + 1):
        for D in iproduct(range(sigma), repeat=mm):
            sp = m.spec_mol(D, L, comp)
            key = tuple(sorted(sp.items()))
            by_support[frozenset(sp)].setdefault(key, sp)
    for S in iproduct(range(sigma), repeat=G):
        trips = m.triple_repeats(S)
        inter = m.interleaved_pairs(S)
        spS = m.spec_mol(S, L, comp)
        suppS = frozenset(spS)
        for starts in combinations_with_replacement(range(G), G):
            if not m.check_I_s(S, starts, L, trips, inter):
                continue
            x = m.observed(S, starts, L, comp)
            if frozenset(x) != suppS:
                continue
            if any(spS.get(w, 0) < c for w, c in x.items()):
                continue
            inst += 1
            # Lemma 2: truth feasibility forces d_S = x.
            if dict(spS) != dict(x):
                collapse_viol += 1
            for key, spD in by_support.get(suppS, {}).items():
                if key == tuple(sorted(spS.items())):
                    continue
                if any(spD.get(w, 0) < c for w, c in x.items()):
                    continue
                if any(spD.get(w, 0) > G for w in x):  # outside binomial domain
                    continue
                r = Fraction(1)
                for w, xw in x.items():
                    r *= phi(xw, G, G, spD.get(w, 0)) / phi(xw, G, G, spS[w])
                if r > 1:
                    cex += 1
    return inst, collapse_viol, cex


def check_collapse_and_no_cex():
    total = 0
    for G, L, sigma in [(4, 3, 2), (5, 3, 2), (5, 3, 3), (6, 3, 2),
                        (6, 3, 3), (5, 4, 2)]:
        for cname, comp in [("ss", None), ("rc", m.make_comp(sigma))]:
            t0 = time.time()
            inst, viol, cex = collapse_and_no_cex(G, L, sigma, comp)
            total += inst
            assert viol == 0, f"collapse Lemma 2 failed G={G} L={L} {cname}"
            assert cex == 0, f"candidate beat truth in slice G={G} L={L} {cname}"
            print(f"  [B] G={G} L={L} sigma={sigma} {cname}: "
                  f"instances={inst} collapse-violations={viol} cex={cex} "
                  f"({time.time()-t0:.1f}s)")
    print(f"  [B] total n=N=G instances checked: {total}")
    return True


# ---------------------------------------------------------------------------
# Outside the slice: explicit sequence-level section 6.2 counterexamples with
# per-occurrence lower bounds, I_s, and a feasible truth.
# ---------------------------------------------------------------------------
def ratio_binomial(spD, spS, x, N0):
    n = sum(x.values())
    r = Fraction(1)
    for w, xw in x.items():
        r *= phi(xw, n, N0, spD.get(w, 0)) / phi(xw, n, N0, spS[w])
    return r


def check_explicit_counterexample(G, L, S, starts, D, N0, comp, expected):
    alphabet = "AT" if len({c for c in S} | {c for c in D}) <= 2 else "ABC"
    spS = m.spec_mol(S, L, comp)
    spD = m.spec_mol(D, L, comp)
    x = m.observed(S, starts, L, comp)
    suppx = frozenset(x)
    trips = m.triple_repeats(S)
    inter = m.interleaved_pairs(S)
    assert m.check_I_s(S, starts, L, trips, inter), "I_s failed"
    assert frozenset(spS) == suppx, "truth support != observed support"
    assert all(spS.get(w, 0) >= c for w, c in x.items()), "truth not per-occ feasible"
    assert frozenset(spD) == suppx, "candidate support != observed support"
    assert all(spD.get(w, 0) >= c for w, c in x.items()), "candidate not per-occ feasible"
    r = ratio_binomial(spD, spS, x, N0)
    lit = lambda t: m.literal(t, alphabet)
    print(f"  [C] G={G} L={L} n={sum(x.values())} N={N0} reading={comp is not None}")
    print(f"      truth S={lit(S)}  windows={ {lit(k): v for k, v in spS.items()} }")
    print(f"      observed x={ {lit(k): v for k, v in x.items()} }")
    print(f"      competitor D={lit(D)}  spectrum={ {lit(k): v for k, v in spD.items()} }")
    print(f"      I_s=True, both per-occurrence feasible, binomial ratio={r}")
    assert r == expected, f"ratio {r} != {expected}"
    assert r > 1
    return True


def check_generic_regime_cex():
    comp = m.make_comp(2)  # A<->B involution on the two-symbol alphabet
    # G = 5, L = 3, n = 3 reads: the observed multiset x is NOT the truth spectrum.
    check_explicit_counterexample(5, 3, (0, 0, 0, 1, 1), (0, 1, 4),
                                  (0, 0, 0, 0, 1, 1), 5, comp, Fraction(9, 8))
    # G = 6, L = 3, n = 4 reads: the winner is the read-tiled genome AAAB,
    # d_D = x, length n = 4 < G.
    check_explicit_counterexample(6, 3, (0, 0, 0, 1, 0, 1), (0, 1, 3, 5),
                                  (0, 0, 0, 1), 6, comp, Fraction(125, 81))
    return True


# ---------------------------------------------------------------------------
# The slice is non-generic: the source fixes the external N to the true genome
# length G, but the number of reads n is an independent model parameter.
# ---------------------------------------------------------------------------
def main():
    print("=" * 78)
    print("Section 6.2 per-occurrence search: slice collapse and generic cex")
    print("=" * 78)
    ok = True
    ok &= check_per_coordinate_max()
    ok &= check_collapse_and_no_cex()
    ok &= check_generic_regime_cex()
    print("\nALL ASSERTIONS PASS" if ok else "\nFAILURE")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
