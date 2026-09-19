#!/usr/bin/env python3
"""Independent exact-rational audit of issue #32.

Literal Medvedev--Brudno (2009) Section 6.1 product-of-binomial-marginals
approximation:

    L[d_1,...,d_{4^k} | x_1,...,x_{4^k}]
        ~= prod_i P[X_i = x_i]
        = prod_i C(n, x_i) (d_i / N)^{x_i} (1 - d_i / N)^{n - x_i},

with a single fixed external N (the known true genome length).  The product
ranges over all 4^k read types and retains the (1 - d_i/N) factors as well as
the observation-only binomial coefficients C(n, x_i).

Witness (DNA relabeling of the #31 AAABB / AAAAB instance):
    truth       S = AAACC, |S| = 5
    competitor  D = AAAAC, |D| = 5
    read length k = 3, n = 3 reads
    realized starts 0, 1, 4  ->  observed types AAA, AAC, CAA once each
    fixed external N = 5

This script recomputes the scores over the full 4^3 = 64-type space with exact
Fraction arithmetic and separates the contributions of the binomial
coefficients and the zero-count factors.

Run:  python3 scripts/audit_binomial_marginals_issue32.py
"""
from fractions import Fraction
from math import comb, log
from itertools import product

ALPHABET = "ACGT"
L = 3
N = 5   # fixed external genome length
NR = 3  # n: number of sampled reads


def spectrum(genome):
    """Circular k-mer occurrence counts of a string (k = L)."""
    g = len(genome)
    spec = {}
    for i in range(g):
        kmer = "".join(genome[(i + j) % g] for j in range(L))
        spec[kmer] = spec.get(kmer, 0) + 1
    return spec


def all_types():
    return ["".join(t) for t in product(ALPHABET, repeat=L)]


def literal_binomial(genome, obs, n=NR, fixed_N=N, keep_coeff=True):
    """Exact value of the literal Section 6.1 product over all read types."""
    spec = spectrum(genome)
    total = Fraction(1)
    for t in all_types():
        d = spec.get(t, 0)
        x = obs.get(t, 0)
        if d > fixed_N:
            raise ValueError(f"{t}: d={d} > N={fixed_N}, outside approximation domain")
        p = Fraction(d, fixed_N)
        coeff = comb(n, x) if keep_coeff else 1
        if d == 0 and x > 0:
            return Fraction(0)
        total *= coeff * (p ** x) * ((1 - p) ** (n - x))
    return total


def drop_onesided(genome, obs, n=NR, fixed_N=N):
    """The misreading that deletes the (1 - d_i/N)^{n - x_i} factors."""
    spec = spectrum(genome)
    total = Fraction(1)
    for t in all_types():
        d = spec.get(t, 0)
        x = obs.get(t, 0)
        if d == 0 and x > 0:
            return Fraction(0)
        total *= Fraction(d, fixed_N) ** x
    return total


def exact_fixed_length_multinomial(genome, obs, n=NR, fixed_N=N):
    """The *exact* multinomial at common candidate length fixed_N (Variant E)."""
    spec = spectrum(genome)
    total = Fraction(1)
    for t in all_types():
        d = spec.get(t, 0)
        x = obs.get(t, 0)
        if d == 0 and x > 0:
            return Fraction(0)
        total *= comb(n, x) * (Fraction(d, fixed_N) ** x)
    return total


def log_cost_identity_check(genome, obs, n=NR, fixed_N=N):
    """Check  L = K * prod_i d_i^{x_i} (N - d_i)^{n - x_i}  with K = prod_i C(n,x_i) / N^{n*4^k}."""
    spec = spectrum(genome)
    lhs = literal_binomial(genome, obs, n, fixed_N)
    K = Fraction(1)
    body = Fraction(1)
    for t in all_types():
        d = spec.get(t, 0)
        x = obs.get(t, 0)
        K *= comb(n, x)
        if d == 0 and x > 0:
            return lhs == 0
        body *= Fraction(d, 1) ** x * Fraction(fixed_N - d, 1) ** (n - x)
    rhs = K / Fraction(fixed_N, 1) ** (n * len(all_types())) * body
    return lhs == rhs


def main():
    S = "AAACC"
    D = "AAAAC"
    starts = [0, 1, 4]
    obs = {}
    for s in starts:
        kmer = "".join(S[(s + j) % len(S)] for j in range(L))
        obs[kmer] = obs.get(kmer, 0) + 1

    print("spectrum(S=AAACC):", spectrum(S))
    print("spectrum(D=AAAAC):", spectrum(D))
    print("observed reads   :", obs)
    print("n =", sum(obs.values()), " fixed external N =", N, " k =", L)
    print()

    L_S = literal_binomial(S, obs)
    L_D = literal_binomial(D, obs)
    ratio = L_D / L_S

    print("literal full PMF (with binomial coefficients and zero-count factors):")
    print("  L_A(S) =", L_S, "=", float(L_S))
    print("  L_A(D) =", L_D, "=", float(L_D))
    print("  L_A(D)/L_A(S) =", ratio, "=", float(ratio))
    print()

    ratio_nocoef = literal_binomial(D, obs, keep_coeff=False) / literal_binomial(S, obs, keep_coeff=False)
    print("drop observation-only binomial coefficients:", ratio_nocoef, "==", ratio)

    ratio_drop = drop_onesided(D, obs) / drop_onesided(S, obs)
    print("drop (1-d_i/N)^{n-x_i} factors            :", ratio_drop, "=", float(ratio_drop))

    ratio_e = exact_fixed_length_multinomial(D, obs) / exact_fixed_length_multinomial(S, obs)
    print("exact fixed-length multinomial (Variant E):", ratio_e, "=", float(ratio_e))

    print()
    print("source convex-cost identity L = K prod d_i^{x_i}(N-d_i)^{n-x_i}:")
    for name, g in (("S", S), ("D", D)):
        print(f"  {name}: identity holds =", log_cost_identity_check(g, obs))

    assert L_S == Fraction(452984832, 30517578125), L_S
    assert L_D == Fraction(7962624, 244140625), L_D
    assert ratio == Fraction(1125, 512), ratio
    assert ratio_nocoef == Fraction(1125, 512)
    assert ratio_drop == 2
    assert ratio_e == 2
    assert log_cost_identity_check(S, obs) and log_cost_identity_check(D, obs)
    assert ratio > 1 and ratio_e > 1

    print()
    print("candidate-universe / domain check (fixed external N does not fix length):")
    for g in ("AAAAA", "AAAAAC", "AAAAAA"):
        spec = spectrum(g)
        dmax = max(spec.values())
        in_domain = dmax <= N
        status = "in domain" if in_domain else "OUT OF DOMAIN (some d_i > N)"
        print(f"  candidate {g:>7} (len {len(g)}): max d_i = {dmax} -> {status}")
        try:
            literal_binomial(g, obs)
        except ValueError as exc:
            print(f"      literal_binomial raised: {exc}")
    print("  => candidates of length != N are admissible for the literal objective")
    print("     whenever d_i <= N for every type; the external N is a probability")
    print("     denominator, not a length constraint on D.")

    print()
    print("all assertions passed; competitor D beats truth S for")
    print("  - the literal full binomial-marginal objective (1125/512 > 1), and")
    print("  - the simplified objective that drops the (1-d_i/N) factors (2 > 1).")


if __name__ == "__main__":
    main()
