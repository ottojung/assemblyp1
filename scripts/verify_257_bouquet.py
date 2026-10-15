#!/usr/bin/env python3
"""Exhaustive small-case cross-check for the BOUQUET rigidity criterion of
Antonina board issue #257 (AssemblyP1, ``github.com/ottojung/assemblyp1``),
scope §8.1.

Claim (now proved and kernel-checked in
``AssemblyP1/RigidityBouquet.lean``, theorem ``bouquet_nonrigid_iff``):

    For a bouquet of ``k`` directed cycles through a common vertex, with cycle
    lengths ``len_i`` and constant multiplicity ``mult_i >= 1`` on cycle ``i``,
    the circulation ``A`` is NOT rigid iff there is a nonzero integer vector
    ``x`` with ``sum_i len_i x_i = 0`` (zero-sum) and ``x_i >= 1 - mult_i``
    (box).

The script is self-contained (no repository import), uses exact integer
arithmetic, and is deterministic. It has three independent parts:

* ``bruteforce``: for every bouquet in a small exhaustive scope, compute
  rigidity from scratch by enumerating *all* positive integer circulations of
  total ``G`` on the actual support graph (balance-guided backtracking), and
  compare with the Diophantine criterion. Exit non-zero on any mismatch.
* ``gap``: confirm the real/integer gap witness of the Lean theorem
  ``len233_mult211_real_integer_gap`` (a rational nonzero solution exists, but
  no integer one does).
* ``instances``: re-derive the kernel-checked worked instances
  ``len24_mult21_rigid`` (rigid despite a repeated cycle),
  ``len23_mult41_nonrigid`` (explicit witness ``x = (-3, 2)``).

Exit code is non-zero if any check fails.
"""
from __future__ import annotations

import sys
from fractions import Fraction
from itertools import product


# --------------------------------------------------------------------------
# bouquet construction
# --------------------------------------------------------------------------
def bouquet(lengths):
    """Return (n, arcs, cycle_edges) for the bouquet of the given cycle lengths.

    Vertices: 0 is the common vertex; cycle i has internal vertices. Edge j of
    cycle i (0 <= j < len_i) runs from the previous vertex to the next one.
    """
    n = 1
    arcs = []
    cyc = []
    for i, L in enumerate(lengths):
        idx = []
        if L == 1:
            idx.append(len(arcs))
            arcs.append((0, 0))
        else:
            prev = 0
            for _ in range(L - 1):
                v = n
                n += 1
                idx.append(len(arcs))
                arcs.append((prev, v))
                prev = v
            idx.append(len(arcs))
            arcs.append((prev, 0))
        cyc.append(idx)
    return n, arcs, cyc


def A_from(lengths, mults):
    _, _, cyc = bouquet(lengths)
    A = [0] * sum(lengths)
    for i in range(len(lengths)):
        for e in cyc[i]:
            A[e] = mults[i]
    return A


# --------------------------------------------------------------------------
# from-scratch brute force: enumerate ALL positive circulations of total G
# --------------------------------------------------------------------------
def enum_positive_circulations(n, arcs, G, cap):
    out = [[] for _ in range(n)]
    inn = [[] for _ in range(n)]
    for i, (u, v) in enumerate(arcs):
        out[u].append(i)
        inn[v].append(i)
    m = len(arcs)
    B = [0] * m

    def rec(i, remaining):
        if i == m:
            for v in range(n):
                if sum(B[e] for e in out[v]) != sum(B[e] for e in inn[v]):
                    return
            if remaining == 0:
                yield tuple(B)
            return
        lo = 1
        hi = remaining - (m - i - 1)
        if hi < lo:
            return
        hi = min(hi, cap)
        for val in range(lo, hi + 1):
            B[i] = val
            yield from rec(i + 1, remaining - val)
        B[i] = 0

    yield from rec(0, G)


def is_rigid_bruteforce(n, arcs, A):
    G = sum(A)
    count = 0
    for B in enum_positive_circulations(n, arcs, G, G):
        if tuple(A) != B:
            return False
    return True


# --------------------------------------------------------------------------
# Diophantine criterion (the claim under test)
# --------------------------------------------------------------------------
def diophantine_nonrigid(lengths, mults, bound=None):
    """Brute-force the criterion: nonzero integer x with sum len_i x_i = 0 and
    x_i >= -(mult_i - 1). Returns a witness or None."""
    k = len(lengths)
    s = [m - 1 for m in mults]
    if bound is None:
        bound = max(lengths) * max(max(s), 1) + max(lengths) + 2
    lo = [-s[i] for i in range(k)]
    for x in product(*[range(lo[i], bound + 1) for i in range(k)]):
        if all(v == 0 for v in x):
            continue
        if sum(lengths[i] * x[i] for i in range(k)) == 0:
            return x
    return None


def real_nonrigid(lengths, mults):
    """Exact rational check: is there a nonzero rational x with the constraints?
    The polytope {x : l.x = 0, x_i >= -s_i} is bounded; real non-rigidity holds
    iff one of its vertices (k-1 active bounds) is nonzero."""
    k = len(lengths)
    s = [m - 1 for m in mults]
    from itertools import combinations
    for I in combinations(range(k), k - 1):
        rem = [j for j in range(k) if j not in I]
        if not rem:
            continue
        j = rem[0]
        val = Fraction(-sum(lengths[i] * (-s[i]) for i in I), lengths[j])
        if val >= -s[j]:
            x = [Fraction(0)] * k
            for i in I:
                x[i] = Fraction(-s[i])
            x[j] = val
            if any(v != 0 for v in x):
                return x
    return None


# --------------------------------------------------------------------------
# checks
# --------------------------------------------------------------------------
def check_bruteforce(kmax=4, lmax=4, mmax=3):
    tested = 0
    bad = 0
    for k in range(2, kmax + 1):
        for lengths in product(range(1, lmax + 1), repeat=k):
            for mults in product(range(1, mmax + 1), repeat=k):
                n, arcs, _ = bouquet(list(lengths))
                A = A_from(list(lengths), list(mults))
                G = sum(A)
                if G > 12:
                    continue
                rigid_bf = is_rigid_bruteforce(n, arcs, A)
                witness = diophantine_nonrigid(list(lengths), list(mults))
                nonrigid_dio = witness is not None
                tested += 1
                if rigid_bf != (not nonrigid_dio):
                    bad += 1
                    print(f"MISMATCH lengths={lengths} mults={mults} "
                          f"rigid_bf={rigid_bf} dio_nonrigid={nonrigid_dio} x={witness}")
    print(f"[bruteforce] tested {tested} bouquets, mismatches {bad}")
    return bad == 0


def check_gap():
    """len233/mult211: rational witness (-1, 0, 2/3) exists, integer does not."""
    lengths = (2, 3, 3)
    mults = (2, 1, 1)
    rx = real_nonrigid(lengths, mults)
    ix = diophantine_nonrigid(lengths, mults)
    ok = rx is not None and ix is None
    print(f"[gap] lengths={lengths} mults={mults} rational_witness={rx} "
          f"integer_witness={ix} ok={ok}")
    return ok


def check_instances():
    ok = True
    # len24/mult21 : rigid despite the 2-cycle traversed twice
    lengths, mults = (2, 4), (2, 1)
    ix = diophantine_nonrigid(lengths, mults)
    n, arcs, _ = bouquet(list(lengths))
    A = A_from(list(lengths), list(mults))
    rb = is_rigid_bruteforce(n, arcs, A)
    this = (ix is None) and rb
    print(f"[instance] len24/mult21 rigid (criterion {ix is None}, brute {rb}) ok={this}")
    ok = ok and this
    # len23/mult41 : non-rigid witness x = (-3, 2)
    lengths, mults = (2, 3), (4, 1)
    ix = diophantine_nonrigid(lengths, mults)
    n, arcs, _ = bouquet(list(lengths))
    A = A_from(list(lengths), list(mults))
    rb = not is_rigid_bruteforce(n, arcs, A)
    this = (ix is not None) and rb
    print(f"[instance] len23/mult41 non-rigid (criterion witness {ix}, brute non-rigid {rb}) ok={this}")
    ok = ok and this
    return ok


def main():
    results = [check_bruteforce(), check_gap(), check_instances()]
    if all(results):
        print("ALL CHECKS PASSED")
        return 0
    print("FAILURES DETECTED")
    return 1


if __name__ == "__main__":
    sys.exit(main())
