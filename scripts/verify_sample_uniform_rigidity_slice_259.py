#!/usr/bin/env python3
"""Sample-uniform rigidity slice for board issue #259 (axis B, minimal cell).

Independent exact-integer verification (no Lean import).  Unlike the
covered-sample iff of `ProductBinomialRigidityNecessity` (same-support
candidates, merged PR #293), this slice allows NEW-SUPPORT same-length
realizable candidates and quantifies over every REALIZABLE COMPLETE-SUPPORT
observation at the same sample size:

  * alphabet {0,1}, read length L=2 (universe U = 4 two-mers);
  * genome length G in {3,4,5,6}; fixed external normalizer N = G;
  * candidate class = all distinct realizable same-G circular spectra
    (binary necklaces; includes new-support competitors);
  * observation class X(A) = realizable same-G spectra x with x_e >= 1 for
    every e in supp(A) (complete support), sample size n = G = N;
  * exact score F_C(x) = prod_e C_e^x_e (N-C_e)^(n-x_e) with 0^0 = 1:
    a zero-count type observed positively kills the score (0^k=0, k>0);
    a zero-count type unobserved contributes one even at boundary C_e = N.
  * rigidity = uniqueness of the positive balanced circulation of total G
    on the truth support (de Bruijn graph of U restricted to supp(A)).

The extra (N-C_e)^(n-x_e) factors over ALL types (including zero-count
ones) are what separate this MB09 section 6.1 product-binomial surrogate
from the exact multinomial (#256); nothing about the exact multinomial is
imported here.  General bidirected flows (#260/#261) are untouched.

Findings (exact integers, re-derived below):
  * necessity holds in this slice: 0 nonrigid-but-maximal truths;
    cells G=3,4 hold it NON-VACUOUSLY (maximal truths exist and are rigid);
    cells G=5,6 hold it vacuously (every truth is beaten at some
    realizable complete-support x, so maximality is empty there).
  * sufficiency fails already at the smallest cell: the rigid truth
    A=(3,0,0,0) (word 000) is beaten at the realizable complete-support
    observation x=(1,1,1,0) (word 001) by B=x, with F_A=0 vs F_B=1728.

Exit code 0 means every check passed.
"""

from __future__ import annotations

import itertools
import sys
from collections import defaultdict

ALPHA = (0, 1)
L = 2
G_RANGE = (3, 4, 5, 6)
U = list(itertools.product(ALPHA, repeat=L))


def spectrum_of(word) -> tuple:
    G = len(word)
    counts = defaultdict(int)
    for i in range(G):
        counts[tuple(word[(i + t) % G] for t in range(L))] += 1
    return tuple(counts.get(w, 0) for w in U)


def realizable_spectra(G: int) -> dict:
    """Distinct spectra of binary circular genomes of length G."""
    seen = set()
    out: dict = {}
    for word in itertools.product(ALPHA, repeat=G):
        if word in seen:
            continue
        for k in range(G):
            seen.add(word[k:] + word[:k])
        out.setdefault(spectrum_of(word), word)
    return out


def positive_circulations(A: list[int], G: int) -> list[tuple]:
    """Positive balanced flows of total G on the truth-support subgraph."""
    edges = [w for w, a in zip(U, A) if a > 0]
    nodes: dict = {}
    for w in edges:
        nodes.setdefault(w[:-1], len(nodes))
        nodes.setdefault(w[1:], len(nodes))
    inc = [(nodes[w[:-1]], nodes[w[1:]]) for w in edges]
    m, n = len(edges), len(nodes)
    vals = [1] * m
    out: list[tuple] = []

    def rec(i: int, remaining: int) -> None:
        if i == m:
            if remaining != 0:
                return
            bal = [0] * n
            for e in range(m):
                u, v = inc[e]
                bal[u] += vals[e]
                bal[v] -= vals[e]
            if all(b == 0 for b in bal):
                out.append(tuple(vals))
            return
        for val in range(1, remaining - (m - i - 1) + 1):
            vals[i] = val
            rec(i + 1, remaining - val)
        vals[i] = 1

    rec(0, G)
    return out


def pow01(base: int, exp: int) -> int:
    """Exact 0^0=1 convention for the polynomial score."""
    if exp == 0:
        return 1
    if base == 0:
        return 0
    return base ** exp


def score(C: tuple, x: tuple, N: int) -> int:
    n = sum(x)
    total = 1
    for c, xe in zip(C, x):
        total *= pow01(c, xe) * pow01(N - c, n - xe)
    return total


def main() -> int:
    grand = {"rigid_max": 0, "rigid_beaten": 0,
             "nonrigid_max": 0, "nonrigid_beaten": 0}
    witness = None
    vacuous_cells = []
    for G in G_RANGE:
        N = G
        table = realizable_spectra(G)
        live = list(table)
        maximal_found = 0
        for A in live:
            supp = [i for i, a in enumerate(A) if a > 0]
            rigid = len(positive_circulations(list(A), G)) == 1
            xs = [x for x in live if all(x[i] >= 1 for i in supp)]
            assert xs, f"empty observation class for {A} at G={G}"
            beaten = [(x, B) for x in xs for B in live
                      if B != A and score(B, x, N) > score(A, x, N)]
            maximal = not beaten
            maximal_found += maximal
            key = ("rigid" if rigid else "nonrigid",
                   "max" if maximal else "beaten")
            grand[{"rigid_max": "rigid_max", "rigid_beaten": "rigid_beaten",
                   "nonrigid_max": "nonrigid_max",
                   "nonrigid_beaten": "nonrigid_beaten"}
                  [key[0] + ("_max" if key[1] == "max" else "_beaten")]] += 1
            if not maximal and witness is None and rigid:
                witness = (G, A, beaten[0][0], beaten[0][1])
        if maximal_found == 0:
            vacuous_cells.append(G)
        print(f"  G={G}: spectra={len(live)} maximal-truths={maximal_found}")
    print("verify_sample_uniform_rigidity_slice_259.py (binary L=2, G=3..6)")
    print(f"  rigid&maximal={grand['rigid_max']} "
          f"rigid&beaten={grand['rigid_beaten']} "
          f"nonrigid&maximal={grand['nonrigid_max']} "
          f"nonrigid&beaten={grand['nonrigid_beaten']}")
    print(f"  vacuous cells (no maximal truth): {vacuous_cells}")
    assert witness is not None, "expected a rigid-but-beaten witness"
    G, A, x, B = witness
    fa, fb = score(A, x, G), score(B, x, G)
    print(f"  smallest rigid-but-beaten: G=N=n={G} A={A} x={x} B={B}")
    print(f"  F_A(x)={fa} F_B(x)={fb} (exact integers, 0^0=1)")
    assert fa < fb, "witness must strictly lose"
    # Pin the smallest cell's exact values (G=3 must be the witness cell).
    assert G == 3 and A == (3, 0, 0, 0) and x == (1, 1, 1, 0), witness
    assert (fa, fb) == (0, 1728), (fa, fb)
    if grand["nonrigid_max"] != 0:
        raise AssertionError(
            f"necessity fails: {grand['nonrigid_max']} nonrigid maximal")
    print("OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
