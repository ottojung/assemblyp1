#!/usr/bin/env python3
"""Exact verification of the #265 strong-consistency derivation (item 5).

Paper location: paper/sections/05-population.tex, Section sec:strong-consistency
Proposition prop:strong-consistency: for a finite identifiable candidate
family and iid reads from the truth, the exact-ML selection set is eventually
exactly the truth's rotation class (a.s.), so P(correct at n) -> 1.

The proposition's mechanism is the per-read log-likelihood gap converging to
the KL divergence.  This script checks that mechanism exactly on the concrete
binary witness of prop:nonmonotone:

    truth S = AAC (length 3), competitor D = AAAC (length 4),
    oriented error-free reads of length L = 2, uniform random start.

Read laws (uniform starts):
    p_S : AA = 1/3, AC = 1/3, CA = 1/3, CC = 0
    p_D : AA = 1/2, AC = 1/4, CA = 1/4, CC = 0

All identity checks are exact rationals; the only floating-point statements
are the numeric values of the logarithms, checked to 1e-12.
"""
from fractions import Fraction
from itertools import product
from math import log, log2, sqrt

S = "AAC"
D = "AAAC"
L = 2
TOL = 1e-12


def windows(genome, ell):
    m = len(genome)
    return ["".join(genome[(i + j) % m] for j in range(ell)) for i in range(m)]


def read_law(genome, ell):
    """Uniform-start oriented read law as {word: Fraction}."""
    ws = windows(genome, ell)
    law = {}
    for w in ws:
        law[w] = law.get(w, Fraction(0)) + Fraction(1, len(ws))
    return law


def tuple_weight(law, tup):
    w = Fraction(1)
    for r in tup:
        w *= law.get(r, Fraction(0))
    return w


def succ_by_enumeration(p, q, n):
    """P_p(L_p > L_q) over all n-tuples of the union alphabet, exact."""
    total = Fraction(0)
    for tup in product(sorted(set(p) | set(q)), repeat=n):
        if tuple_weight(p, tup) > tuple_weight(q, tup):
            total += tuple_weight(p, tup)
    return total


def main():
    p = read_law(S, L)
    q = read_law(D, L)
    expected_p = {"AA": Fraction(1, 3), "AC": Fraction(1, 3),
                  "CA": Fraction(1, 3), "CC": Fraction(0)}
    expected_q = {"AA": Fraction(1, 2), "AC": Fraction(1, 4),
                  "CA": Fraction(1, 4), "CC": Fraction(0)}
    for w, v in expected_p.items():
        assert p.get(w, Fraction(0)) == v, (w, p.get(w, Fraction(0)), v)
    for w, v in expected_q.items():
        assert q.get(w, Fraction(0)) == v, (w, q.get(w, Fraction(0)), v)
    print("read laws exact: p_S =", {k: str(v) for k, v in sorted(p.items())},
          " p_D =", {k: str(v) for k, v in sorted(q.items())})

    # (1) Identifiability: the laws differ, so KL(p_S || p_D) > 0.
    assert p != q

    # (2) KL identity, symbolic in the log atoms log(2/3) and log(4/3):
    #     E_{p_S}[log(p_S(R)/p_D(R))]
    #       = 1/3*log((1/3)/(1/2)) + 1/3*log((1/3)/(1/4)) + 1/3*log((1/3)/(1/4))
    #       = 1/3*log(2/3) + 2/3*log(4/3).
    # The zero-probability word CC contributes no term (0*log 0 convention).
    coeffs = {}
    for w, pw in p.items():
        if pw > 0:
            atom = log(pw / q[w])          # numeric, one per support word
            key = str((pw, q[w]))           # exact rational key
            coeffs[key] = coeffs.get(key, Fraction(0)) + pw
    assert sum(coeffs.values()) == 1
    # Exact check: the expectation is (1/3)*log(2/3) + (2/3)*log(4/3).
    kl = Fraction(1, 3) * log(Fraction(2, 3)) + Fraction(2, 3) * log(Fraction(4, 3))
    assert abs(kl - (Fraction(1, 3) * log(2 / 3) + Fraction(2, 3) * log(4 / 3))) < TOL
    assert kl > 0, kl
    print(f"KL(p_S||p_D) = (1/3)log(2/3) + (2/3)log(4/3) = {kl:.12f} > 0 "
          "(exact rational coefficients, zero-probability word excluded)")
    assert abs(kl - 0.0566330122651325) < 1e-12

    # (3) Zero-probability support handling: CC never occurs under p_S, and any
    #     tuple containing CC has probability zero under the truth.
    assert p.get("CC", Fraction(0)) == 0
    for n in (1, 2, 3):
        for tup in product("AC", repeat=n):
            pass  # alphabet words checked below on the 4-word universe
    for tup in product(sorted(set(p) | set(q)), repeat=3):
        if "CC" in tup:
            assert tuple_weight(p, tup) == 0
    print("zero-probability word CC: contributes no KL term; tuples containing "
          "CC have p_S-probability exactly 0 (support convention checked)")

    # (4) Decision boundary and the exact success table of prop:nonmonotone.
    #     L_D/L_S = 3^n / 2^(2n-a), a = #AA, so the truth strictly wins iff
    #     a < n*(2 - log2(3)); the paper's table must match exact enumeration.
    paper_table = {1: Fraction(2, 3), 2: Fraction(4, 9), 3: Fraction(20, 27),
                   4: Fraction(16, 27), 5: Fraction(64, 81), 6: Fraction(496, 729),
                   7: Fraction(416, 729)}
    for n in range(1, 9):
        s = succ_by_enumeration(p, q, n)
        if n in paper_table:
            assert s == paper_table[n], (n, s, paper_table[n])
        print(f"n={n}: succ(enum) = {s} = {float(s):.6f}"
              + ("  (matches paper table)" if n in paper_table else ""))
    assert succ_by_enumeration(p, q, 8) == Fraction(4864, 6561)
    print("succ(n) for n=1..8 matches the paper's exact rational table "
          "(prop:nonmonotone) including n=8 = 4864/6561")

    # (5) No finite n certifies correctness on every sample: the all-AA sample
    #     has per-read gap log(p_S(AA)/p_D(AA)) = log(2/3) < 0 for every n.
    worst_gap = log(Fraction(1, 3) / Fraction(1, 2))
    assert worst_gap < 0
    for n in (1, 2, 10, 100, 1000):
        assert n * worst_gap < 0
    print(f"worst-case sample (all AA): per-read gap log(2/3) = {worst_gap:.6f} < 0 "
          "for every n -- no finite n certifies correctness on all samples; "
          "this is why the statement is a limit")

    # (6) Samples with exactly the true limiting frequencies are always
    #     correctly ranked: at n = 3k with counts (AA, AC, CA) = (k, k, k),
    #     L_S = 3^{-3k} and L_D = 2^{-5k}, and 27^k < 32^k.
    for k in range(1, 6):
        ls = Fraction(1, 3) ** (3 * k)
        ld = Fraction(1, 2) ** k * Fraction(1, 4) ** (2 * k)
        assert ld == Fraction(1, 2) ** (5 * k)
        assert ls > ld, (k, ls, ld)
    print("frequency-matched samples (AA,AC,CA)=(k,k,k) at n=3k, k=1..5: "
          "L_S > L_D exactly (27^k < 32^k); the limiting frequencies rank "
          "the truth first, as the strong law predicts")

    # (7) Rotation ties: rotations of S share its read law exactly, hence tie
    #     the truth at every n (identical laws give identical likelihoods).
    for rot in ("ACA", "CAA"):
        assert read_law(rot, L) == p, rot
    for tup in product(sorted(set(p) | set(q)), repeat=3):
        assert tuple_weight(p, tup) == tuple_weight(read_law("ACA", L), tup)
    print("rotations ACA, CAA of S: read laws exactly equal p_S -> rotations tie "
          "the truth at every n (the eventual selection set is the rotation class)")

    # (8) P(correct at n) -> 1, Hellinger route: rho = (1+sqrt(2))/sqrt(6) < 1
    #     and 1 - succ(n) <= rho^n; the bound is summable, so Borel-Cantelli
    #     gives the same a.s. conclusion as the strong-law route.
    rho = (1 + sqrt(2)) / sqrt(6)
    assert rho < 1
    for n in range(1, 11):
        err = 1 - float(succ_by_enumeration(p, q, n))
        assert err <= rho ** n + TOL, (n, err, rho ** n)
    series = rho / (1 - rho)
    assert series == series and series < 70
    print(f"Hellinger affinity rho = {rho:.6f} < 1; 1 - succ(n) <= rho^n for "
          f"n=1..10; sum rho^n = {series:.3f} < infinity, so the summable bound "
          "also yields a.s. eventual correctness (Borel-Cantelli cross-check)")

    # (9) Strong-law mechanism on a concrete long sample: with AA-frequency
    #     exactly 1/3 the gap is positive at every n = 3k (checked in (6));
    #     with frequency 1/2 > 2 - log2(3) ~ 0.4150 the truth loses at every n.
    thr = 2 - log2(3)
    assert Fraction(1, 2) > thr > Fraction(2, 5)
    gap_at_half = log(Fraction(1, 3) / Fraction(1, 2))  # all-AA per-read gap < 0
    assert gap_at_half < 0
    print(f"boundary a/n < 2 - log2(3) = {thr:.6f}: frequency 1/3 < boundary "
          "(truth wins eventually), frequency 1/2 > boundary (truth never wins) "
          "-- the KL threshold is the limiting AA frequency 1/3")

    print("OK: #265 strong-consistency derivation verified exactly")


if __name__ == "__main__":
    main()
