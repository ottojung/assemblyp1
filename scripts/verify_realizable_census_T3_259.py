#!/usr/bin/env python3
"""Realizable-support census for #259, ternary read length 3 (bounded extension).

Independent exact-integer verification (no Lean import) toward the L6/Q4 goal:
enumerates all ternary-necklace (circular-genome) spectra for read length L=3
and genome lengths G in 3..7, decides rigidity (uniqueness of the positive
balanced circulation of total G on the truth support) and covered-sample
maximality over the same-length realizable class via the merged #259
covered-sample iff (zero-weight / pointwise-domination branches), all with
exact ``int`` arithmetic.

Model: MB09 section 6.1 fixed-external-N product-binomial surrogate with
``N = G``.  Candidate length is fixed (L=3, universe = 27 ternary 3-mers);
normalization N is the circular genome length; support is the set of 3-mers
with positive count; sample size n = sum(x) is free above the covered-sample
bound; the extra ``(1-d(w)/N)^(n-x(w))`` factors (including zero-count
coordinates) are exactly what ``effectiveWeight`` encodes, separating this
from the exact multinomial (#256, not imported).  General bidirected flows
(#260/#261) are untouched.

Exit code 0 means every check passed, including:
  * 0 nonrigid-but-maximal spectra (necessity holds on this class), and
  * at least one explicit rigid-but-beaten exact witness (sufficiency fails
    via a new-support candidate), printed with exact integer weights.
"""

from __future__ import annotations

import itertools
import sys
from collections import defaultdict

ALPHA = (0, 1, 2)
L = 3
G_RANGE = range(3, 8)


def eff_weight(N: int, B: list[int], i: int) -> int:
    w = B[i]
    for j in range(len(B)):
        if j != i:
            w *= N - B[j]
    return w


def support(B: list[int]) -> list[int]:
    return [i for i in range(len(B)) if B[i] > 0]


def dominates_pointwise(N: int, A: list[int], B: list[int]) -> bool:
    return all(eff_weight(N, B, i) <= eff_weight(N, A, i) for i in support(A))


def zero_on_support(N: int, A: list[int], B: list[int]) -> bool:
    return any(eff_weight(N, B, i) == 0 for i in support(A))


def spectrum_vec(s, U, index) -> list[int]:
    G = len(s)
    c = defaultdict(int)
    for i in range(G):
        c[tuple(s[(i + t) % G] for t in range(L))] += 1
    return [c.get(w, 0) for w in U]


def necklaces(G: int):
    seen = set()
    for words in itertools.product(ALPHA, repeat=G):
        if words in seen:
            continue
        for k in range(G):
            seen.add(words[k:] + words[:k])
        yield words


def positive_circulations(A: list[int], U, G: int) -> list[tuple]:
    edges = [w for w, a in zip(U, A) if a > 0]
    nodes: dict = {}
    for w in edges:
        nodes.setdefault(w[:-1], len(nodes))
        nodes.setdefault(w[1:], len(nodes))
    inc = [(nodes[w[:-1]], nodes[w[1:]]) for w in edges]
    m, n = len(edges), len(nodes)
    if m == 0:
        return []
    out: list[tuple] = []
    vals = [1] * m

    def rec(i: int, remaining: int):
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


def main() -> int:
    U = list(itertools.product(ALPHA, repeat=L))
    total = 0
    rigid_max = rigid_notmax = nonrigid_max = nonrigid_notmax = 0
    witness = None
    for G in G_RANGE:
        items: dict = {}
        for s in necklaces(G):
            key = tuple(spectrum_vec(s, U, None))
            items.setdefault(key, s)
        specs = list(items.items())
        # skip truths with a zero effective weight on their own support
        # (boundary-degenerate; outside the positive-weight theorem scope)
        live = []
        for keyA, _ in specs:
            A = list(keyA)
            if all(eff_weight(G, A, i) != 0 for i in support(A)):
                live.append(A)
        for A in live:
            rigid = len(positive_circulations(A, U, G)) == 1
            beaten_by = None
            for B in live:
                if B == A:
                    continue
                if not zero_on_support(G, A, B) and not dominates_pointwise(G, A, B):
                    beaten_by = B
                    break
            maximal = beaten_by is None
            total += 1
            if rigid and maximal:
                rigid_max += 1
            elif rigid and not maximal:
                rigid_notmax += 1
                if witness is None:
                    witness = (G, A, beaten_by)
            elif (not rigid) and maximal:
                nonrigid_max += 1
            else:
                nonrigid_notmax += 1
    print("verify_realizable_census_T3_259.py (ternary L=3, G=3..7)")
    print(f"  distinct realizable truth spectra: {total}")
    print(f"  rigid&maximal={rigid_max} rigid&NOT-maximal={rigid_notmax} "
          f"nonrigid&maximal={nonrigid_max} nonrigid&NOT-maximal={nonrigid_notmax}")
    if witness is not None:
        G, A, B = witness
        eA = [eff_weight(G, A, i) for i in support(A)]
        eB = [eff_weight(G, B, i) for i in support(A)]
        gap = [i for i in support(A) if eB[support(A).index(i)] > eA[support(A).index(i)]]
        print(f"  witness G={G} A={A} B={B}")
        print(f"  effA(supp)={eA} effB(supp)={eB} strict-gain-coords={gap}")
    if nonrigid_max != 0:
        raise AssertionError(f"necessity counterexample: {nonrigid_max} nonrigid maximal")
    if rigid_notmax < 1:
        raise AssertionError("expected at least one rigid-but-beaten witness")
    print("OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
