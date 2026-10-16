#!/usr/bin/env python3
"""Cross-check for the TARGET-CYCLE / numerical-semigroup reduction of Antonina
board issue #257 (AssemblyP1, ``github.com/ottojung/assemblyp1``), scope
§8.1/§8.2.

Claim (now proved and kernel-checked in
``AssemblyP1/RigidityTargetCycle.lean``, theorem
``targetCycle_nonrigid_iff_coin``):

    The target-cycle bouquet — coin cycles of lengths ``a_i >= 1`` each
    traversed once, plus one target cycle of length ``t >= 1`` traversed twice,
    all through a common vertex — is NOT rigid iff ``t`` is a nonnegative
    integer combination of the coin lengths ``a_i``.

Equivalently: the bouquet is rigid iff ``t`` is *not* in the numerical
semigroup ``<a_0, ..., a_{n-1}>``. This makes the family exactly the unbounded
coin / change-making problem.

The script is self-contained (no repository import), uses exact integer
arithmetic, and is deterministic. It has four independent parts:

* ``bruteforce``: for every target-cycle bouquet in a small exhaustive scope,
  compute rigidity from scratch by enumerating *all* positive integer
  circulations of total ``G`` on the actual support graph (balance-guided
  backtracking), and compare with coin representability. Exit non-zero on any
  mismatch.
* ``apery``: cross-check the polynomial-time Apéry-set / residue-graph
  shortest-path representability algorithm against a bounded brute force on
  small cases, then demonstrate it on large targets (binary-sized) where the
  brute force is infeasible. This is the §8.2 upper-bound witness: because an
  explicit support graph encodes the coin lengths in *unary* (one edge per unit
  of length), representability — hence bouquet rigidity — is decidable in
  polynomial time, so the naive "NP-hardness via the coin problem" reading is
  refuted.
* ``instances``: re-derive the kernel-checked worked instances
  (``coin_nonrigid_23_5``, ``coin_rigid_23_1``, ``coin_rigid_33_2``).
* ``gap``: the length ``(2,3,3)``, multiplicity ``(2,1,1)`` real/integer-gap
  bouquet re-read with the length-``2`` cycle as the target; rigid, matching
  ``coin_rigid_33_2``.

Exit code is non-zero if any check fails.
"""
from __future__ import annotations

import heapq
import sys
from itertools import product


# --------------------------------------------------------------------------
# target-cycle bouquet construction (reused from verify_257_bouquet.py shape)
# --------------------------------------------------------------------------
def bouquet(lengths):
    """Return (n, arcs, cycle_edges) for the bouquet of the given cycle lengths."""
    n = 1
    arcs = []
    cyc = []
    for L in lengths:
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


def target_cycle(coeffs, t):
    """lengths/mults of the target-cycle bouquet: coins once, target twice."""
    lengths = list(coeffs) + [t]
    mults = [1] * len(coeffs) + [2]
    return lengths, mults


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
    for B in enum_positive_circulations(n, arcs, G, G):
        if tuple(A) != B:
            return False
    return True


# --------------------------------------------------------------------------
# coin / numerical-semigroup representability
# --------------------------------------------------------------------------
def coin_representable_bruteforce(coeffs, t, cap=None):
    """Bounded exact check: is t = sum_i coeffs_i * y_i for some y_i >= 0?"""
    coeffs = list(coeffs)
    if t < 0:
        return False
    if t == 0:
        return True
    if cap is None:
        cap = t
    # DFS over coordinates with a running total.
    coeffs = sorted(set(coeffs))
    if not coeffs:
        return t == 0

    def rec(i, rem):
        if rem == 0:
            return True
        if i == len(coeffs):
            return False
        c = coeffs[i]
        k = rem // c
        # try from the largest multiple downward (finds solutions fast)
        for mult in range(k, -1, -1):
            if rec(i + 1, rem - mult * c):
                return True
        return False

    return rec(0, t)


def coin_representable_apery(coeffs, t):
    """Exact polynomial-time representability via the Apéry set.

    Let m = min(coeffs). In the residue graph on Z/m, an edge r -> (r+d) % m of
    weight d for every denomination d; dist[r] is the smallest representable
    number congruent to r (mod m). Then t is representable iff t >= dist[t % m].
    Cost O(m * |coeffs|) arithmetic ops: polynomial in the unary graph size.
    """
    coeffs = sorted(set(int(c) for c in coeffs))
    if t < 0:
        return False
    if t == 0:
        return True
    if not coeffs:
        return False
    m = coeffs[0]
    INF = None
    dist = [INF] * m
    dist[0] = 0
    pq = [(0, 0)]
    while pq:
        d, r = heapq.heappop(pq)
        if dist[r] != d:
            continue
        for c in coeffs:
            nr = (r + c) % m
            nd = d + c
            if dist[nr] is None or nd < dist[nr]:
                dist[nr] = nd
                heapq.heappush(pq, (nd, nr))
    r = t % m
    return dist[r] is not None and t >= dist[r]


# --------------------------------------------------------------------------
# checks
# --------------------------------------------------------------------------
def check_bruteforce(kmax=3, lmax=4, tmax=8, Gmax=20):
    tested = 0
    bad = 0
    for k in range(0, kmax + 1):
        for coeffs in product(range(1, lmax + 1), repeat=k):
            for t in range(1, tmax + 1):
                lengths, mults = target_cycle(list(coeffs), t)
                if sum(lengths) > 12:
                    continue
                A = A_from(lengths, mults)
                G = sum(A)
                if G > Gmax:
                    continue
                n, arcs, _ = bouquet(lengths)
                rigid_bf = is_rigid_bruteforce(n, arcs, A)
                representable = coin_representable_bruteforce(list(coeffs), t)
                tested += 1
                # reduction: non-rigid <=> representable
                if rigid_bf == representable:
                    bad += 1
                    print(f"MISMATCH coeffs={coeffs} t={t} rigid_bf={rigid_bf} "
                          f"representable={representable}")
    print(f"[bruteforce] tested {tested} target-cycle bouquets, mismatches {bad}")
    return bad == 0


def check_apery():
    """Small-case agreement with brute force, then a large-target demonstration."""
    bad = 0
    tested = 0
    for k in range(1, 4):
        for coeffs in product(range(1, 7), repeat=k):
            for t in range(0, 40):
                a = coin_representable_apery(list(coeffs), t)
                b = coin_representable_bruteforce(list(coeffs), t)
                tested += 1
                if a != b:
                    bad += 1
                    print(f"APERY MISMATCH coeffs={coeffs} t={t} apery={a} bf={b}")
    # Large targets (binary-sized, brute force infeasible): consistency checks.
    # (2,3): representable iff t != 1; (6,9,20): Frobenius number 43.
    big_ok = True
    for t in [10**9, 10**9 + 1, 12345678901234567890]:
        if not coin_representable_apery([2, 3], t):
            big_ok = False
    if coin_representable_apery([2, 3], 1):
        big_ok = False
    # Frobenius number of (6,9,20) is 43: 43 not representable, 44.. representable.
    if coin_representable_apery([6, 9, 20], 43):
        big_ok = False
    for t in range(44, 120):
        if not coin_representable_apery([6, 9, 20], t):
            big_ok = False
    print(f"[apery] tested {tested} small cases, mismatches {bad}; "
          f"large-target checks ok={big_ok}")
    return bad == 0 and big_ok


def check_instances():
    ok = True
    cases = [
        ((2, 3), 5, False),  # representable -> non-rigid
        ((2, 3), 1, True),   # not representable -> rigid
        ((3, 3), 2, True),   # not representable -> rigid
    ]
    for coeffs, t, expect_rigid in cases:
        lengths, mults = target_cycle(list(coeffs), t)
        A = A_from(lengths, mults)
        n, arcs, _ = bouquet(lengths)
        rigid_bf = is_rigid_bruteforce(n, arcs, A)
        representable = coin_representable_bruteforce(list(coeffs), t)
        this = (rigid_bf == expect_rigid) and (rigid_bf == (not representable))
        print(f"[instance] coeffs={coeffs} t={t} rigid_bf={rigid_bf} "
              f"representable={representable} expect_rigid={expect_rigid} ok={this}")
        ok = ok and this
    return ok


def check_gap():
    """(2,3,3)/(2,1,1) bouquet re-read: target length 2, coins (3,3) -> rigid."""
    # original bouquet: lengths (2,3,3), mults (2,1,1), rigid (real/integer gap)
    lengths, mults = (2, 3, 3), (2, 1, 1)
    A = A_from(list(lengths), list(mults))
    n, arcs, _ = bouquet(list(lengths))
    rigid_bf = is_rigid_bruteforce(n, arcs, A)
    # re-read with the length-2 cycle as target: coins (3,3), t = 2
    representable = coin_representable_bruteforce([3, 3], 2)
    ok = rigid_bf and (not representable)
    print(f"[gap] bouquet lengths={lengths} mults={mults} rigid_bf={rigid_bf}; "
          f"target-cycle coins=(3,3) t=2 representable={representable} ok={ok}")
    return ok


def main():
    results = [check_bruteforce(), check_apery(), check_instances(), check_gap()]
    if all(results):
        print("ALL CHECKS PASSED")
        return 0
    print("FAILURES DETECTED")
    return 1


if __name__ == "__main__":
    sys.exit(main())
