#!/usr/bin/env python3
"""Independent numerical evidence for board issue #256.

For every small circular word ``S`` (alphabet size ``k``, length ``G``) and read
length ``L`` with ``2 <= L <= G``, this script:

1. builds the length-``L`` spectrum ``A`` of ``S``, the edge set ``E = supp(A)``,
   and the de Bruijn support graph ``X_S`` (nodes are length-``(L-1)`` windows);
2. enumerates ``F``, the set of *all* positive integer balanced circulations of
   total ``G`` on ``E`` (exhaustively, by a sum-pruned DFS over positive
   compositions of ``G``);
3. checks that ``A`` is itself a positive balanced circulation of total ``G``
   (so ``A in F``);
4. checks the constructive beating witness: for every ``B in F`` with ``B != A``
   it builds ``x`` (``x[w] = M+1``, ``x[e] = 1`` for ``e != w``, ``w`` chosen with
   ``A[w] < B[w]``) and verifies ``Lik(A;x) < Lik(B;x)`` with exact
   ``fractions.Fraction`` arithmetic.

Because the beating witness is constructive, checking it for every ``B != A``
establishes the ``=>`` direction of the iff on every scanned instance, while
``A in F`` and ``F == {A}`` establish the ``<=`` direction. The script therefore
verifies the iff on the whole scanned scope, not merely samples it. This is
independent evidence (the Lean proof is the authority); it is exhaustive in
scope, not a proof of the general statement.

Reproduce:

    python3 scripts/verify_robust_same_length_iff_256.py
    python3 scripts/verify_robust_same_length_iff_256.py --full

Exits non-zero on any failed assertion.
"""

from __future__ import annotations

import argparse
import itertools
import sys
from fractions import Fraction


def windows(word, L):
    G = len(word)
    return [tuple(word[(i + d) % G] for d in range(L)) for i in range(G)]


def spectrum(word, L):
    spec = {}
    for w in windows(word, L):
        spec[w] = spec.get(w, 0) + 1
    return spec


def balanced(E, val):
    """Balance of the weight vector ``val`` on the de Bruijn support graph."""
    out, inn = {}, {}
    for w in E:
        p, s = w[:-1], w[1:]
        out[p] = out.get(p, 0) + val[w]
        inn[s] = inn.get(s, 0) + val[w]
    nodes = set(out) | set(inn)
    return all(out.get(v, 0) == inn.get(v, 0) for v in nodes)


def circulations(E, G):
    """All positive integer balanced circulations of total ``G`` on ``E``.

    Sum-pruned DFS over positive compositions of ``G`` into ``len(E)`` parts.
    """
    result = []
    n = len(E)
    val = {}

    def rec(i, remaining):
        if i == n:
            if remaining == 0 and balanced(E, val):
                result.append(dict(val))
            return
        # every remaining edge needs at least 1, so cap the current value
        for v in range(1, remaining - (n - i - 1) + 1):
            val[E[i]] = v
            rec(i + 1, remaining - v)
        val.pop(E[i], None)

    rec(0, G)
    return result


def likelihood(B, x, G):
    prod = Fraction(1)
    for e in B:
        prod *= Fraction(B[e], G) ** x[e]
    return prod


def beating_sample(A, B):
    """Return the constructive sample x with Lik(A;x) < Lik(B;x), or None."""
    w = next((e for e in A if A[e] < B[e]), None)
    if w is None:
        return None
    r = Fraction(B[w], A[w])
    C = Fraction(1)
    for e in A:
        if e != w:
            C *= Fraction(B[e], A[e])
    M = 0
    while r ** M * C <= 1:
        M += 1
        if M > 10_000:
            raise AssertionError("amplification did not converge")
    x = {e: 1 for e in A}
    x[w] = M + 1
    return x


def scan(alphabets, Ls, Gmax, verbose=False):
    checked_words = rigid = nonrigid = witnesses = 0
    for k in alphabets:
        for G in range(max(Ls), Gmax + 1):
            for L in Ls:
                if L > G:
                    continue
                for word in itertools.product(range(k), repeat=G):
                    spec = spectrum(list(word), L)
                    E = sorted(spec)
                    A = {e: spec[e] for e in E}
                    F = circulations(E, G)
                    checked_words += 1
                    assert A in F, f"A not a circulation for {word} L={L}"
                    if len(F) == 1:
                        assert F[0] == A, f"F not {{A}} but |F|=1 for {word}"
                        rigid += 1
                        continue
                    nonrigid += 1
                    for B in F:
                        if B == A:
                            continue
                        x = beating_sample(A, B)
                        assert x is not None, f"no edge to amplify {word}"
                        assert all(v > 0 for v in x.values()), "x not positive"
                        la = likelihood(A, x, G)
                        lb = likelihood(B, x, G)
                        assert la < lb, (
                            f"witness failed: word={word} L={L} B={B} "
                            f"Lik(A)={la} Lik(B)={lb}"
                        )
                        witnesses += 1
                    if verbose:
                        print(f"non-rigid: S={word} L={L} |F|={len(F)}")
    return checked_words, rigid, nonrigid, witnesses


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--full", action="store_true")
    args = ap.parse_args()

    if args.full:
        alphabets, Ls, Gmax = [2, 3], [2, 3, 4], 11
    else:
        alphabets, Ls, Gmax = [2], [2, 3], 10

    checked, rigid, nonrigid, witnesses = scan(alphabets, Ls, Gmax, verbose=False)
    print(
        f"words checked : {checked}\n"
        f"  rigid (F={{A}}) : {rigid}\n"
        f"  non-rigid      : {nonrigid}\n"
        f"  beating witnesses verified : {witnesses}"
    )
    print("all assertions passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
