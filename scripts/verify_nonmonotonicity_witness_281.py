#!/usr/bin/env python3
"""Exact verification of the #281 non-monotonicity witness.

Witness (issue #281, part A):
  truth     S = AAC   (circular genome, length 3)
  candidate D = AAAC  (circular genome, length 4)
  oriented error-free reads of fixed length L = 2, uniform random start.

The read law of a circular genome is the uniform distribution over its
`len(genome)` cyclic length-L windows.  With this law the two read
distributions are
    p_S : AA = 1/3, AC = 1/3, CA = 1/3, CC = 0
    p_D : AA = 1/2, AC = 1/4, CA = 1/4, CC = 0
so they are distinct (identifiable) and the Hellinger affinity is < 1.

The exact finite-sample maximum-likelihood success probability
    succ(n) = P_S( L_S(R_1..R_n) > L_D(R_1..R_n) )
is computed in exact rational arithmetic for small n, both by exhaustive
enumeration of read tuples and, independently, by the binomial reduction.
The result is NOT monotone in n: succ(1) = 2/3 > succ(2) = 4/9.
"""
from fractions import Fraction
from itertools import product
from math import comb

S = "AAC"
D = "AAAC"
L = 2


def windows(genome, ell):
    m = len(genome)
    return ["".join(genome[(i + j) % m] for j in range(ell)) for i in range(m)]


def read_law(genome, ell):
    """Uniform-start oriented read law as {word: Fraction}."""
    ws = windows(genome, ell)
    m = len(ws)
    law = {}
    for w in ws:
        law[w] = law.get(w, Fraction(0)) + Fraction(1, m)
    return law


def read_universe(p, q):
    return sorted(set(p) | set(q))


def tuple_weight(law, tup):
    w = Fraction(1)
    for r in tup:
        w *= law.get(r, Fraction(0))
    return w


def succ_by_enumeration(p, q, n):
    """P_p(L_p > L_q) over all n-tuples, exact enumeration."""
    total = Fraction(0)
    for tup in product(read_universe(p, q), repeat=n):
        lp = tuple_weight(p, tup)
        lq = tuple_weight(q, tup)
        if lp > lq:              # truth strictly beats the competitor
            total += lp
    return total


def succ_by_binomial(p, q, n):
    """Independent derivation for this witness via the #AA count.

    On tuples without CC, L_D / L_S = 3^n / 2^(2n - a) where a = #AA,
    so L_D >= L_S  <=>  a >= n*log2(4/3); because log2(4/3) is irrational
    there are no ties and the threshold is a > n*log2(4/3).
    Under p_S each read is AA w.p. 1/3 and non-AA w.p. 2/3.
    """
    from math import log2
    thr = n * log2(Fraction(4, 3))
    total = Fraction(0)
    for a in range(n + 1):
        if a < thr:              # truth strictly beats competitor: L_S > L_D
            # C(n,a) (1/3)^a (2/3)^(n-a)
            total += Fraction(comb(n, a) * 2 ** (n - a), 3 ** n)
    return total


def main():
    p = read_law(S, L)
    q = read_law(D, L)
    print("read law p_S:", {k: str(v) for k, v in sorted(p.items())})
    print("read law p_D:", {k: str(v) for k, v in sorted(q.items())})

    # Hellinger affinity < 1  <=>  distinct laws (identifiability).
    aff = sum((p.get(w, Fraction(0)) * q.get(w, Fraction(0))) ** Fraction(1, 2)
              for w in read_universe(p, q))
    print("affinity rho(p_S,p_D) =", float(aff))
    assert aff < 1, "laws must be distinct for the exponential bound"

    succ = {}
    for n in range(0, 7):
        e = succ_by_enumeration(p, q, n)
        b = succ_by_binomial(p, q, n)
        assert e == b, (n, e, b)
        succ[n] = e
        print(f"n={n}: succ(enum) = {e} = {float(e):.6f}   (binom cross-check ok)")

    # The claim: success probability is not monotone in n.
    assert succ[1] > succ[2], (succ[1], succ[2])
    assert succ[3] > succ[4], (succ[3], succ[4])
    assert succ[5] > succ[6], (succ[5], succ[6])
    print("non-monotone: succ(1)=%s > succ(2)=%s ; succ(3)=%s > succ(4)=%s ; "
          "succ(5)=%s > succ(6)=%s"
          % (succ[1], succ[2], succ[3], succ[4], succ[5], succ[6]))

    # No ties anywhere: strict and non-strict success events coincide.
    from math import log2
    for n in range(1, 40):
        assert abs(n * log2(Fraction(4, 3)) - round(n * log2(Fraction(4, 3)))) > 1e-9
    print("no ties for 1<=n<40 (threshold n*log2(4/3) is never an integer)")

    # Sanity: consistency, succ(n) -> 1 (law of large numbers).
    for n in (20, 40, 80):
        print(f"n={n}: succ = {float(succ_by_binomial(p, q, n)):.6f}")
    print("OK: #281 non-monotonicity witness verified")


if __name__ == "__main__":
    main()
