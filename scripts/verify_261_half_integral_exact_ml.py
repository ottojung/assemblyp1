#!/usr/bin/env python3
"""Independent exact-rational verifier for board #261's integer-vs-half-integral
exact-likelihood claim.

Kernel-checked companion: ``AssemblyP1/Section62HalfIntegralExactML.lean``
(``exactLik_smul``, ``half_integral_doubling``).

The claim under test: for the **exact multinomial** read likelihood with the
candidate's own length ``N = sum_v d_v`` (the MB09 §6.1 first display), the
half-integral relaxation of the §6.2 bidirected overlap flow polytope cannot
strictly beat the integer optimum, because the exact likelihood is
scale-invariant and the §6.2 clauses are homogeneous (doubling a half-integral
feasible flow gives an integer feasible flow with the same normalized
throughput).

This script re-derives the arithmetic in exact ``Fraction`` arithmetic and
fails (non-zero exit) if any check is violated.

Checks
------
W1  exactLik(k * d) == exactLik(d) for many rational d and many k > 0.
W2  The AAATT half-integral throughput (5/2, 1, 1) and its integer double
    (5, 2, 2) have the same normalized spectrum and the same exact likelihood
    on the observed sample x = (AAA:2, AAT:1, TAA:1).
W3  The §6.1 separable-binomial objective is NOT scale-invariant, so the
    binomial ``half_integral_gap`` does not transfer to the exact objective.
W4  Doubling a half-integral circulation on a tiny bidirected overlap graph
    yields an integer circulation with doubled throughput and the same
    normalized throughput.
"""

from fractions import Fraction
from itertools import product


def exact_lik(d, x):
    """Exact multinomial likelihood of the normalized throughput d at sample x.

    ``d`` and ``x`` are dicts on the same finite class set.  The candidate
    length is ``N = sum_v d_v``.
    """
    N = sum(d.values())
    assert N > 0, "candidate length must be positive"
    out = Fraction(1)
    for v in d:
        p = d[v] / N
        out *= p ** x.get(v, 0)
    return out


def scale(d, k):
    return {v: k * d[v] for v in d}


def check_w1():
    cases = [
        ({0: Fraction(5, 2), 1: Fraction(1), 2: Fraction(1)}, (2, 1, 1)),
        ({0: Fraction(3, 2), 1: Fraction(3, 2)}, (1, 3)),
        ({0: Fraction(1), 1: Fraction(2), 2: Fraction(3)}, (0, 1, 2)),
        ({0: Fraction(7, 2), 1: Fraction(1, 2), 2: Fraction(2)}, (2, 0, 3)),
    ]
    ks = [Fraction(2), Fraction(3), Fraction(5, 2), Fraction(1, 2),
          Fraction(10), Fraction(7, 3)]
    n = 0
    for d, xv in cases:
        x = {i: xv[i] for i in range(len(xv))}
        base = exact_lik(d, x)
        for k in ks:
            assert exact_lik(scale(d, k), x) == base, (d, x, k)
            n += 1
    return n


def check_w2():
    # Observed sample: AAA:2, AAT:1, TAA:1 over classes (0,1,4).
    x = {0: 2, 1: 1, 4: 1}
    half = {0: Fraction(5, 2), 1: Fraction(1), 4: Fraction(1)}
    integer = {0: Fraction(5), 1: Fraction(2), 4: Fraction(2)}  # = 2 * half
    assert integer == scale(half, 2)
    # normalized spectra agree
    Nh, Ni = sum(half.values()), sum(integer.values())
    for v in half:
        assert half[v] / Nh == integer[v] / Ni, v
    assert exact_lik(half, x) == exact_lik(integer, x)
    # the *unnormalized* exact factor at d=5/2 on length 5 equals d=5 on length 10
    assert (Fraction(5, 2) / 5) == (Fraction(5) / 10)
    return 1


def binom_core(d, x, N):
    """§6.1 separable-binomial comparison core with external N (as in the Lean
    module GeneralBidirectedFlowML.binomCore)."""
    n = sum(x.values())
    out = Fraction(1)
    for v in d:
        out *= d[v] ** x.get(v, 0) * (N - d[v]) ** (n - x.get(v, 0))
    return out


def check_w3():
    # The §6.1 AAA marginal with external N = 5, n = 4 reads and x_0 = 2 is
    # C(4,2) * (d/5)^2 (1 - d/5)^2, proportional to d^2 (5-d)^2, which is
    # strictly maximized at the half-integral d = 5/2 and ties at the integer
    # maximizers d = 2, 3.  That is the binomial gap.
    def aaa(d):
        return d ** 2 * (5 - d) ** 2
    half_d = Fraction(5, 2)
    assert aaa(half_d) > aaa(Fraction(2))
    assert aaa(half_d) > aaa(Fraction(3))
    assert aaa(Fraction(2)) == aaa(Fraction(3))
    # The exact objective has no such gap: the half-integral throughput and its
    # integer double have the same normalized spectrum and the same likelihood.
    half = {0: Fraction(5, 2), 1: Fraction(1)}
    integer = {0: Fraction(5), 1: Fraction(2)}
    x = {0: 2, 1: 1}
    assert exact_lik(half, x) == exact_lik(integer, x)
    return 1


def check_w4():
    """A tiny §6.2-style bidirected overlap graph.

    Two molecule classes {a, b}; four edges with signed incidences:
      e0: a -> a  (+1 at a, -1 at a)   (self-loop, flow variable f0)
      e1: a -> b  (+1 at a, -1 at b)
      e2: b -> a  (+1 at b, -1 at a)
      e3: b -> b  (+1 at b, -1 at b)   (self-loop)
    Balance at a: +f0 + f1 - f2 - f0 = f1 - f2 = 0  => f1 = f2.
    Balance at b: -f1 + f2 + f3 - f3 = -f1 + f2 = 0  => f1 = f2.
    Throughput a = f0 + f1 ; throughput b = f2 + f3.
    A half-integral feasible circulation: f = (0, 1/2, 1/2, 0), throughput
    (1/2, 1/2) has total 1; the vertex lower bound is 1 so this is *not*
    feasible, but (f0, f1, f2, f3) = (1/2, 1/2, 1/2, 1/2) gives throughput
    (1, 1) with total 2 >= 1 per vertex: feasible.  Its double
    (1, 1, 1, 1) is integer feasible with throughput (2, 2).
    """
    edges = [
        # (tail_class, head_class, sgn_tail, sgn_head)
        ("a", "a", 1, -1),
        ("a", "b", 1, -1),
        ("b", "a", 1, -1),
        ("b", "b", 1, -1),
    ]
    classes = ["a", "b"]

    def bal(f):
        out = {c: Fraction(0) for c in classes}
        for (sx, sy, gx, gy), fe in zip(edges, f):
            out[sx] += gx * fe
            out[sy] += gy * fe
        return out

    def thr(f):
        out = {c: Fraction(0) for c in classes}
        for (sx, sy, gx, gy), fe in zip(edges, f):
            out[sx] += fe
        return out

    def feasible(f):
        if any(fe < 0 for fe in f):
            return False
        if any(bal(f)[c] != 0 for c in classes):
            return False
        if any(thr(f)[c] < 1 for c in classes):
            return False
        return True

    half = [Fraction(1, 2)] * 4
    integer = [Fraction(1)] * 4
    assert feasible(half)
    assert feasible(integer)
    assert [2 * fe for fe in half] == integer
    th, ti = thr(half), thr(integer)
    assert {c: 2 * th[c] for c in classes} == ti
    # normalized throughputs agree
    Nh, Ni = sum(th.values()), sum(ti.values())
    for c in classes:
        assert th[c] / Nh == ti[c] / Ni
    # exact likelihood agrees on an arbitrary sample
    x = {"a": 1, "b": 2}
    assert exact_lik(th, x) == exact_lik(ti, x)
    return 1


def main():
    n1 = check_w1()
    n2 = check_w2()
    n3 = check_w3()
    n4 = check_w4()
    print(f"W1 exactLik scale-invariance: {n1} assertions PASS")
    print(f"W2 AAATT half vs integer double: {n2} PASS")
    print(f"W3 binomial is not scale-invariant: {n3} PASS")
    print(f"W4 tiny §6.2 circulation doubling: {n4} PASS")
    print("ALL CHECKS PASS")


if __name__ == "__main__":
    main()
