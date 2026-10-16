#!/usr/bin/env python3
"""Exhaustive small-case cross-check for the LP-RELAXATION no-go of Antonina
board issue #257 (AssemblyP1, ``github.com/ottojung/assemblyp1``), scope
§8.1/§8.2.

Headline claim (proved and kernel-checked in ``AssemblyP1/RigidityNoGo.lean``,
theorem ``coin_bouquet_real_nonrigid``): the **direct rational/LP relaxation**
of the bouquet criterion is satisfied by the *coin bouquet* (one target
``t``-cycle of multiplicity ``2``, ``k >= 1`` coin cycles of lengths
``coins i`` of multiplicity ``1``) for **every** instance, including the rigid
ones. Hence no decision procedure based only on that fractional relaxation can
decide rigidity.

The exact integer classification of this same family is proved in PR #283
(``AssemblyP1.RigidityTargetCycle.targetCycle_nonrigid_iff_coin``); the Lean
theorem ``coin_bouquet_nonrigid_iff`` cross-checked here is an *independent*
kernel-checked restatement of it with the opposite index convention (target
cycle first), not a competing claim:

    the coin bouquet is NOT rigid iff ``t`` is a nonnegative integer combination
    of the ``coins i`` (numerical-semigroup membership).

This script is self-contained (no repository import), uses exact arithmetic, and
is deterministic. It has three parts:

* ``bruteforce``: for every coin system in a small exhaustive scope, compute
  rigidity from scratch by enumerating *all* positive integer circulations of
  total ``G`` on the actual support graph (balance-guided backtracking), and
  compare with semigroup membership. Exit non-zero on any mismatch. This
  cross-checks the PR #283 / ``coin_bouquet_nonrigid_iff`` classification.
* ``lp``: confirm the LP no-go ``coin_bouquet_real_nonrigid``: the direct
  rational relaxation has a nonzero witness for every coin bouquet with
  ``k >= 1`` -- in particular for the rigid instances, so no criterion based
  only on the direct rational relaxation can certify rigidity.
* ``instances``: re-derive the crosscheck instances ``coins23_target1_rigid``
  (rigid) and ``coins23_target5_nonrigid`` (witness ``y = (1, 1)``).

Exit code is non-zero if any check fails.
"""
from __future__ import annotations

import sys
from fractions import Fraction
from itertools import product


# --------------------------------------------------------------------------
# bouquet construction (matches the Lean ``coinLen`` / ``coinMult``)
# --------------------------------------------------------------------------
def bouquet(lengths):
    """Return (n, arcs, cycle_edges) for the bouquet of the given cycle lengths.

    Vertices: 0 is the common vertex; cycle i has internal vertices. Edge j of
    cycle i (0 <= j < len_i) runs from the previous vertex to the next one.
    """
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


def coin_lengths(coins, t):
    """Cycle lengths of the coin bouquet: [t] ++ coins."""
    return [t] + list(coins)


def coin_mults(coins, t):
    """Multiplicities: target cycle 2, each coin cycle 1."""
    return [2] + [1] * len(coins)


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
# semigroup membership (the criterion under test)
# --------------------------------------------------------------------------
def semigroup_member(coins, t):
    """DP over the target: is t a nonnegative integer combination of coins?"""
    reach = [False] * (t + 1)
    reach[0] = True
    for x in range(1, t + 1):
        for c in coins:
            if c <= x and reach[x - c]:
                reach[x] = True
                break
    return reach[t]


def semigroup_witness(coins, t):
    """Return a nonnegative combination or None (small targets only)."""
    k = len(coins)
    if k == 0:
        return () if t == 0 else None
    bound = t // min(coins) + 1
    for y in product(range(bound + 1), repeat=k):
        if sum(coins[i] * y[i] for i in range(k)) == t:
            return y
    return None


def real_witness(coins, t):
    """Direct fractional relaxation witness x_0 = -1, x_1 = t / coins[0].

    Returns True when the rational point is a valid nonzero witness of the
    *relaxed* system (zero weighted length sum and the box), which always holds
    for k >= 1 and t >= 1.
    """
    if not coins:
        return False
    lens = coin_lengths(coins, t)
    mults = coin_mults(coins, t)
    x = [Fraction(0)] * len(lens)
    x[0] = Fraction(-1)
    x[1] = Fraction(t, coins[0])
    if all(v == 0 for v in x):
        return False
    if sum(lens[i] * x[i] for i in range(len(lens))) != 0:
        return False
    for i in range(len(lens)):
        if x[i] < 1 - mults[i]:
            return False
    return True


# --------------------------------------------------------------------------
# checks
# --------------------------------------------------------------------------
def check_bruteforce(kmax=3, cmax=4, tmax=12, gmax=26):
    tested = 0
    rigid = 0
    nonrigid = 0
    bad = 0
    for k in range(1, kmax + 1):
        for coins in product(range(1, cmax + 1), repeat=k):
            for t in range(1, tmax + 1):
                lengths = coin_lengths(coins, t)
                mults = coin_mults(coins, t)
                G = sum(lengths[i] * mults[i] for i in range(len(lengths)))
                if G > gmax:
                    continue
                n, arcs, _ = bouquet(lengths)
                A = A_from(lengths, mults)
                rigid_bf = is_rigid_bruteforce(n, arcs, A)
                member = semigroup_member(coins, t)
                tested += 1
                if rigid_bf:
                    rigid += 1
                else:
                    nonrigid += 1
                if rigid_bf != (not member):
                    bad += 1
                    print(f"MISMATCH coins={coins} t={t} rigid_bf={rigid_bf} "
                          f"semigroup_member={member} witness={semigroup_witness(coins, t)}")
    print(f"[bruteforce] tested {tested} coin bouquets "
          f"({rigid} rigid / {nonrigid} non-rigid), mismatches {bad}")
    return bad == 0


def check_lp(kmax=3, cmax=4, tmax=12, gmax=26):
    """The direct rational relaxation always has a witness (LP no-go)."""
    tested = 0
    bad = 0
    rigid_with_lp_witness = 0
    for k in range(1, kmax + 1):
        for coins in product(range(1, cmax + 1), repeat=k):
            for t in range(1, tmax + 1):
                lengths = coin_lengths(coins, t)
                mults = coin_mults(coins, t)
                G = sum(lengths[i] * mults[i] for i in range(len(lengths)))
                if G > gmax:
                    continue
                tested += 1
                rw = real_witness(coins, t)
                if not rw:
                    bad += 1
                    print(f"LP NO-GO FAILURE: no rational witness coins={coins} t={t}")
                member = semigroup_member(coins, t)
                if rw and not member:
                    # rigid integer instance whose direct LP relaxation reports
                    # non-rigidity -- the core of the no-go
                    rigid_with_lp_witness += 1
    print(f"[lp] tested {tested} coin bouquets, LP witness always present: "
          f"{tested - bad}/{tested}; rigid-but-LP-nonrigid instances {rigid_with_lp_witness}")
    return bad == 0 and rigid_with_lp_witness > 0


def check_instances():
    ok = True
    # coins {2, 3}, target 1: not representable -> rigid
    coins, t = (2, 3), 1
    member = semigroup_member(coins, t)
    n, arcs, _ = bouquet(coin_lengths(coins, t))
    A = A_from(coin_lengths(coins, t), coin_mults(coins, t))
    rb = is_rigid_bruteforce(n, arcs, A)
    this = (not member) and rb
    print(f"[instance] coins={coins} t={t} rigid (member {member}, brute {rb}) ok={this}")
    ok = ok and this
    # coins {2, 3}, target 5 = 2 + 3: representable -> non-rigid
    coins, t = (2, 3), 5
    member = semigroup_member(coins, t)
    wit = semigroup_witness(coins, t)
    n, arcs, _ = bouquet(coin_lengths(coins, t))
    A = A_from(coin_lengths(coins, t), coin_mults(coins, t))
    rb = not is_rigid_bruteforce(n, arcs, A)
    this = member and rb and (wit == (1, 1))
    print(f"[instance] coins={coins} t={t} non-rigid (member {member}, witness {wit}, "
          f"brute non-rigid {rb}) ok={this}")
    ok = ok and this
    return ok


def main():
    results = [check_bruteforce(), check_lp(), check_instances()]
    if all(results):
        print("ALL CHECKS PASSED")
        return 0
    print("FAILURES DETECTED")
    return 1


if __name__ == "__main__":
    sys.exit(main())
