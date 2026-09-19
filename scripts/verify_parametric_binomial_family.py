#!/usr/bin/env python3
"""Exact-rational verification of the parametric product-of-binomial family.

Objective (Medvedev-Brudno 2009, section 6.1 literal product of binomial
marginals, "Variant A"), fixed external length N:

    L_A(C) = prod_tau C(n, x_tau) (d_C(tau)/N)^{x_tau}
                                  (1 - d_C(tau)/N)^{n - x_tau}.

Because the observation-only factors cancel between two candidates, the
ordering ratio for length-N candidates S, D is exactly

    R(D,S) = prod_{tau: d_D != d_S}
                 (d_D/d_S)^{x_tau} ((N-d_D)/(N-d_S))^{n-x_tau},   0^0 := 1.

The family studied here is

    S(L) = A^L C^2,   D(L) = A^{L+1} C,   read length k = L,   N = L+2,

with observed read multiset

    { A^L : x,  A^{L-1} C : 1,  C A^{L-1} : 1 },   n = x + 2,

realized by the true starts 0 (x times), 1 and N-1.

The script (1) checks the exact factorization against a full-type-space
product, (2) checks the closed-form ratio, (3) checks the count-spectrum
change, and (4) checks the I_s bridging/coverage certificate used to keep the
instance source-faithful.  Only standard-library exact arithmetic is used.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from fractions import Fraction
from itertools import product

ALPHABET = "ACGT"


def kmers(word: str, k: int) -> Counter:
    n = len(word)
    return Counter(tuple(word[(i + j) % n] for j in range(k)) for i in range(n))


def marginal_power(d: int, x: int, N: int, n: int) -> Fraction:
    """d^x (N-d)^(n-x) with the convention 0^0 = 1."""
    base = Fraction(1) if (d == 0 and x == 0) else Fraction(d) ** x
    return base * Fraction(N - d) ** (n - x)


def ratio_full_type_space(S: str, D: str, obs: dict, k: int, N: int, n: int) -> Fraction:
    """Literal product over all |ALPHABET|^k read types."""
    all_types = set(product(ALPHABET, repeat=k)) | set(obs)
    dS, dD = kmers(S, k), kmers(D, k)
    R = Fraction(1)
    for tau in all_types:
        a, b, x = dS.get(tau, 0), dD.get(tau, 0), obs.get(tau, 0)
        if a == b:
            continue
        R *= marginal_power(b, x, N, n) / marginal_power(a, x, N, n)
    return R


def ratio_factorized(S: str, D: str, obs: dict, k: int, N: int, n: int) -> Fraction:
    """The changed-type product of the factorized lemma."""
    dS, dD = kmers(S, k), kmers(D, k)
    R = Fraction(1)
    for tau in set(dS) | set(dD):
        a, b, x = dS.get(tau, 0), dD.get(tau, 0), obs.get(tau, 0)
        if a == b:
            continue
        R *= marginal_power(b, x, N, n) / marginal_power(a, x, N, n)
    return R


def family_instance(L: int, x: int):
    S = "A" * L + "CC"
    D = "A" * (L + 1) + "C"
    k = L
    N = L + 2
    starts = [0] * x + [1, N - 1]
    obs: dict = {}
    for s in starts:
        tau = tuple(S[(s + j) % N] for j in range(k))
        obs[tau] = obs.get(tau, 0) + 1
    n = sum(obs.values())
    return S, D, k, N, starts, obs, n


def closed_form(L: int, x: int) -> Fraction:
    N = L + 2
    return (
        Fraction(2) ** x
        * Fraction(N - 2, N - 1) ** 2
        * Fraction(N, N - 1) ** (x + 2)
    )


def spectrum_change(L: int):
    S, D, k, N, _, _, _ = family_instance(L, 1)
    dS, dD = kmers(S, k), kmers(D, k)
    removed = sorted("".join(t) for t in set(dS) - set(dD))
    added = sorted("".join(t) for t in set(dD) - set(dS))
    return removed, added


# --- I_s bridging/coverage certificate ---------------------------------------


def window(word: str, t: int, ell: int) -> tuple:
    n = len(word)
    return tuple(word[(t + j) % n] for j in range(ell))


def copy_bridged(read_starts, L: int, N: int, t: int, ell: int) -> bool:
    """A length-ell copy at t is bridged by a read covering t-1 and t+ell."""
    for r in read_starts:
        arc = {(r + j) % N for j in range(L)}
        if (t - 1) % N in arc and (t + ell) % N in arc:
            return True
    return False


def check_source_certificate(S: str, L: int, read_starts) -> tuple[bool, str]:
    """Check coverage, all-bridged maximal triple repeats, no unbridged
    interleaved repeat pair, matching the repository's source semantics."""
    N = len(S)

    covered = set()
    for r in read_starts:
        covered |= {(r + j) % N for j in range(L)}
    if covered != set(range(N)):
        return False, "coverage fails"

    groups_by_ell = {}
    for ell in range(1, N):
        groups = defaultdict(list)
        for t in range(N):
            groups[window(S, t, ell)].append(t)
        groups_by_ell[ell] = groups

    for ell, groups in groups_by_ell.items():
        for w, starts in groups.items():
            if len(starts) < 3:
                continue
            prec = {S[(t - 1) % N] for t in starts}
            foll = {S[(t + ell) % N] for t in starts}
            if len(prec) > 1 and len(foll) > 1:
                for t in starts:
                    if not copy_bridged(read_starts, L, N, t, ell):
                        return False, f"unbridged triple copy ell={ell} at {t}"

    # Maximal repeat pairs: every 2-subset of copies that is maximal on both
    # sides (the repository/Lean convention, cf. AAABB where {0,2} is listed
    # for the length-1 A copies even though three copies exist).
    pairs = []
    for ell, groups in groups_by_ell.items():
        for w, starts in groups.items():
            if len(starts) < 2:
                continue
            for i in range(len(starts)):
                for j in range(i + 1, len(starts)):
                    t1, t2 = starts[i], starts[j]
                    if S[(t1 - 1) % N] != S[(t2 - 1) % N] and S[(t1 + ell) % N] != S[(t2 + ell) % N]:
                        pairs.append((ell, (t1, t2)))

    for i in range(len(pairs)):
        for j in range(i + 1, len(pairs)):
            ell1, (a, b) = pairs[i]
            ell2, (c, d) = pairs[j]
            if len({a, b, c, d}) < 4:
                continue
            def between(x, y, z):
                return (x < y < z) or (z < x < y) or (y < z < x)

            # Chords {a,b} and {c,d} interleave iff exactly one of c, d lies
            # on the clockwise arc from a to b.
            alternating = between(a, c, b) != between(a, d, b)
            if alternating:
                ok = any(copy_bridged(read_starts, L, N, t, ell1) for t in (a, b))
                ok = ok or any(copy_bridged(read_starts, L, N, t, ell2) for t in (c, d))
                if not ok:
                    return False, f"unbridged interleaved pair {pairs[i]} {pairs[j]}"
    return True, "coverage + all-bridged triples + no unbridged interleaving"


def main() -> int:
    # 1. Base witness (AAACC / AAAAC): 1125/512, and factorization agreement.
    S0, D0 = "AAACC", "AAAAC"
    obs0 = {tuple("AAA"): 1, tuple("AAC"): 1, tuple("CAA"): 1}
    r_full = ratio_full_type_space(S0, D0, obs0, 3, 5, 3)
    r_fact = ratio_factorized(S0, D0, obs0, 3, 5, 3)
    assert r_full == r_fact == Fraction(1125, 512), (r_full, r_fact)
    print("base witness AAACC/AAAAC ratio =", r_full)

    # 2. Family: full-type-space == factorized == closed form; R > 2^x.
    for L in range(3, 9):
        for x in range(1, 6):
            S, D, k, N, starts, obs, n = family_instance(L, x)
            rf = ratio_full_type_space(S, D, obs, k, N, n)
            rp = ratio_factorized(S, D, obs, k, N, n)
            cf = closed_form(L, x)
            assert rf == rp == cf, (L, x, rf, rp, cf)
            assert rf > Fraction(2) ** x
    print("family ratios: full == factorized == closed form, and R > 2^x")

    # 3. Count-spectrum change: exactly L-1 zero-count deletions and L-2
    #    zero-count creations (net -1 zero-count unit).
    for L in range(3, 12):
        removed, added = spectrum_change(L)
        assert len(removed) == L - 1, (L, removed)
        assert len(added) == L - 2, (L, added)
    print("spectrum change: (L-1) deletions, (L-2) creations, all 1<->0")

    # 4. Source certificate for the L-family with starts {0,1,N-1}, and the
    #    kernel-checked witness realization starts {0,1,4} for L=3.
    ok, msg = check_source_certificate("AAACC", 3, [0, 1, 4])
    assert ok, msg
    for L in range(3, 13):
        S = "A" * L + "CC"
        N = L + 2
        ok, msg = check_source_certificate(S, L, [0, 1, N - 1])
        assert ok, (L, msg)
    print("source certificate: coverage + all-bridged triples + no interleaving")

    print("all parametric binomial family checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
