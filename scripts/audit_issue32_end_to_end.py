#!/usr/bin/env python3
"""End-to-end independent audit of issue #32 (2026-09-19).

This script is independent of scripts/audit_binomial_marginals_issue32.py.  It
was written from the primary-source formula read directly from the PMC equation
image M31.gif:

    L[d_1,...,d_{4^k} | x_1,...,x_{4^k}]
        ~= prod_i P[X_i = x_i]
         = prod_i C(n,x_i) (d_i/N)^{x_i} (1 - d_i/N)^{n-x_i},

with the source convex cost (M33.gif)

    c_i(d_i) = -(x_i log d_i) - (n - x_i) log(N - d_i).

Witness (DNA relabeling B->C of the issue #31 AAABB / AAAAB instance):

    truth       S = AAACC, |S| = 5
    competitor  D = AAAAC, |D| = 5
    reads       k = 3, n = 3, realized starts 0,1,4 -> AAA, AAC, CAA once each
    fixed external N = 5

Run:  python3 scripts/audit_issue32_end_to_end.py
"""

from fractions import Fraction as F
from itertools import product
from math import comb

ALPHABET = "ACGT"
K = 3
NREADS = 3
N = 5
TYPES = ["".join(t) for t in product(ALPHABET, repeat=K)]


def spectrum(genome):
    n = len(genome)
    counts = {}
    for i in range(n):
        word = "".join(genome[(i + j) % n] for j in range(K))
        counts[word] = counts.get(word, 0) + 1
    return counts


def observed(genome, starts):
    n = len(genome)
    counts = {}
    for r in starts:
        word = "".join(genome[(r + j) % n] for j in range(K))
        counts[word] = counts.get(word, 0) + 1
    return counts


def literal_product(genome, obs, with_coefficients=True, denominator=N):
    spec = spectrum(genome)
    total = F(1)
    for t in TYPES:
        d = spec.get(t, 0)
        x = obs.get(t, 0)
        if d > denominator:
            raise ValueError(f"{t}: d={d} > N={denominator} (binomial domain)")
        if d == 0 and x > 0:
            return F(0)
        p = F(d, denominator)
        coeff = comb(NREADS, x) if with_coefficients else 1
        total *= coeff * p ** x * (1 - p) ** (NREADS - x)
    return total


def zero_count_dropped(genome, obs, denominator=N):
    spec = spectrum(genome)
    total = F(1)
    for t in TYPES:
        d = spec.get(t, 0)
        x = obs.get(t, 0)
        if d == 0 and x > 0:
            return F(0)
        total *= F(d, denominator) ** x
    return total


def fixed_length_exact_multinomial(genome, obs, denominator=N):
    spec = spectrum(genome)
    total = F(1)
    for t in TYPES:
        d = spec.get(t, 0)
        x = obs.get(t, 0)
        if d == 0 and x > 0:
            return F(0)
        total *= comb(NREADS, x) * F(d, denominator) ** x
    return total


def convex_cost_identity(genome, obs, denominator=N):
    """Check L = K * prod_i d_i^{x_i} (N - d_i)^{n - x_i}."""
    spec = spectrum(genome)
    lhs = literal_product(genome, obs)
    constant = F(1)
    body = F(1)
    for t in TYPES:
        d = spec.get(t, 0)
        x = obs.get(t, 0)
        constant *= comb(NREADS, x)
        if d == 0 and x > 0:
            return lhs == 0
        body *= F(d) ** x * F(denominator - d) ** (NREADS - x)
    rhs = constant / F(denominator) ** (NREADS * len(TYPES)) * body
    return lhs == rhs


def main():
    S, D = "AAACC", "AAAAC"
    obs = observed(S, [0, 1, 4])

    assert spectrum(S) == {"AAA": 1, "AAC": 1, "ACC": 1, "CCA": 1, "CAA": 1}
    assert spectrum(D) == {"AAA": 2, "AAC": 1, "ACA": 1, "CAA": 1}
    assert obs == {"AAA": 1, "AAC": 1, "CAA": 1}

    L_S = literal_product(S, obs)
    L_D = literal_product(D, obs)
    ratio = L_D / L_S
    assert L_S == F(452984832, 30517578125)
    assert L_D == F(7962624, 244140625)
    assert ratio == F(1125, 512)
    assert ratio > 1

    assert literal_product(D, obs, with_coefficients=False) / \
        literal_product(S, obs, with_coefficients=False) == ratio
    assert zero_count_dropped(D, obs) / zero_count_dropped(S, obs) == 2
    assert fixed_length_exact_multinomial(D, obs) / \
        fixed_length_exact_multinomial(S, obs) == 2

    assert convex_cost_identity(S, obs)
    assert convex_cost_identity(D, obs)

    print("L_A(S) =", L_S)
    print("L_A(D) =", L_D)
    print("L_A(D)/L_A(S) =", ratio, "=", float(ratio))
    print("zero-count-dropped ratio =", zero_count_dropped(D, obs) / zero_count_dropped(S, obs))
    print("fixed-length exact multinomial ratio =",
          fixed_length_exact_multinomial(D, obs) / fixed_length_exact_multinomial(S, obs))
    print("convex-cost identity holds for both candidates")
    print()

    print("candidate length / copy-count check (N = %d):" % N)
    for g in ("AAACC", "AAAAC", "AAAAAC", "AAAAAAC", "AAAAAA"):
        spec = spectrum(g)
        total = sum(spec.values())
        dmax = max(spec.values())
        domain = "domain-valid d_i<=N" if dmax <= N else "OUT OF DOMAIN d_i>N"
        length_fixed = "Sigma d_i = N" if total == N else "Sigma d_i = %d != N" % total
        print("  %-8s len=%d  Sigma d_i=%d  max d_i=%d  %s; %s"
              % (g, len(g), total, dmax, domain, length_fixed))
    print()
    print("Note: the binomial approximation's derivation fixes the candidate length")
    print("to the known true length N, i.e. Sigma_i d_i = N. Under that reading the")
    print("witness S and D both lie in the approximation's candidate universe.")
    print()
    print("all assertions passed")


if __name__ == "__main__":
    main()
