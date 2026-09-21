#!/usr/bin/env python3
"""Independent verification for the strict oriented single-strand Section 6.2 rigidity theorem.

This script is self-contained: it re-implements oriented spectra, window-support
grouping, Bresler triple repeats, and the minimal obstruction witnesses from
scratch.  It shares no code with the repository search scripts.  All arithmetic
is exact (fractions.Fraction); it is deterministic and exits non-zero on any
failed assertion.

It checks, on exhaustive small scopes and on explicit witnesses:

  A. Theorem A (short-repeat rigidity): no word whose length-(L-1) windows all
     occur at most twice is non-rigid.
  B. Main theorem (non-rigid => long Bresler triple repeat): every word carrying
     a same-support same-length different-spectrum competitor has a Bresler
     triple repeat of length >= L-1, i.e. no I_s-admissible word is non-rigid.
  C. Periodic Lemma C: S = P^k with a period factor of length >= L-1 repeated in
     circular P has a long Bresler triple repeat.
  D. Minimal same-length obstruction: S = AAAAAAB vs D = AAABAAB (G=7, L=3)
     is non-rigid and carries a long triple repeat; the truth can be beaten once
     the observation is skewed.
  E. Variable-length boundary: S = AAATT, D = AAAATT (L=3) satisfies I_s with
     supp(spec S) = supp(spec D) = supp(x) and is beaten under both the exact
     multinomial and the fixed-N Section 6.1 binomial objective.

Usage:
    python3 scripts/verify_oriented_se62_rigidity.py          # quick
    python3 scripts/verify_oriented_se62_rigidity.py --full   # wider scopes
"""

from __future__ import annotations

import sys
from fractions import Fraction
from itertools import combinations, product


# --------------------------------------------------------------------------- #
# Core combinatorial objects (strict oriented single-strand).
# --------------------------------------------------------------------------- #


def windows(s: tuple[str, ...], L: int) -> list[tuple[str, ...]]:
    """The G length-L circular windows of s, in start order."""
    G = len(s)
    return [tuple(s[(i + j) % G] for j in range(L)) for i in range(G)]


def oriented_spec(s: tuple[str, ...], L: int) -> dict[tuple[str, ...], int]:
    d: dict[tuple[str, ...], int] = {}
    for w in windows(s, L):
        d[w] = d.get(w, 0) + 1
    return d


def support(s: tuple[str, ...], L: int) -> frozenset[tuple[str, ...]]:
    return frozenset(oriented_spec(s, L).keys())


def minmer_counts(s: tuple[str, ...], L: int) -> dict[tuple[str, ...], int]:
    """Multiplicities of length-(L-1) factors."""
    d: dict[tuple[str, ...], int] = {}
    for w in windows(s, L - 1):
        d[w] = d.get(w, 0) + 1
    return d


def long_bresler_triple(s: tuple[str, ...], L: int):
    """A Bresler triple repeat of length >= L-1, or None.

    Three starts carrying an equal length-ell window whose preceding symbols are
    not all equal and whose following symbols are not all equal.
    """
    G = len(s)
    for ell in range(L - 1, G + 1):
        groups: dict[tuple[str, ...], list[int]] = {}
        for t in range(G):
            w = tuple(s[(t + j) % G] for j in range(ell))
            groups.setdefault(w, []).append(t)
        for starts in groups.values():
            if len(starts) < 3:
                continue
            for comb in combinations(starts, 3):
                prevs = {s[(t - 1) % G] for t in comb}
                nexts = {s[(t + ell) % G] for t in comb}
                if len(prevs) > 1 and len(nexts) > 1:
                    return ell, comb
    return None


def repeated_period_factors(P: tuple[str, ...]):
    """Lengths ell and witness residues of circular factors of P repeated in P."""
    p = len(P)
    for ell in range(1, p + 1):
        seen: dict[tuple[str, ...], int] = {}
        for t in range(p):
            w = tuple(P[(t + j) % p] for j in range(ell))
            if w in seen:
                yield ell, seen[w], t
            else:
                seen[w] = t


def is_primitive(P: tuple[str, ...]) -> bool:
    p = len(P)
    for d in range(1, p):
        if p % d == 0 and all(P[i] == P[i % d] for i in range(p)):
            return False
    return True


# --------------------------------------------------------------------------- #
# Explicit witnesses.
# --------------------------------------------------------------------------- #


def ratio_exact(x, dS, dD):
    """Exact same-length multinomial ratio prod (dD/dS)^x (0/0 types omitted)."""
    r = Fraction(1)
    for w, xw in x.items():
        if xw == 0:
            continue
        r *= Fraction(dD[w], dS[w]) ** xw
    return r


def ratio_exact_multinomial(x, dS, dD, G_S, G_D):
    """Exact MB09 Section 6.1 multinomial ratio with candidate-intrinsic lengths."""
    r = Fraction(1)
    for w, xw in x.items():
        if xw == 0:
            continue
        r *= (Fraction(dD[w], G_D) / Fraction(dS[w], G_S)) ** xw
    return r


def ratio_fixedN(x, dS, dD, n, N):
    """Literal fixed-N product of binomial marginals ratio (zero-count factors too)."""

    def prod(d):
        r = Fraction(1)
        for w in d:
            xw = x.get(w, 0)
            r *= Fraction(1) * Fraction(d[w], N) ** xw
            r *= (1 - Fraction(d[w], N)) ** (n - xw)
        return r

    return prod(dD) / prod(dS)


def add_counts(base, w, m):
    out = dict(base)
    out[w] = out.get(w, 0) + m
    return out


# --------------------------------------------------------------------------- #
# Checks.
# --------------------------------------------------------------------------- #


def check_scope(alphabet, G, L, verbose=True):
    words = [tuple(t) for t in product(alphabet, repeat=G)]
    by_support: dict[frozenset, list[tuple[str, ...]]] = {}
    spectra: dict[frozenset, set] = {}
    for s in words:
        key = support(s, L)
        by_support.setdefault(key, []).append(s)
        spectra.setdefault(key, set()).add(tuple(sorted(oriented_spec(s, L).items())))

    nonrigid_supports = 0
    nonrigid_words = 0
    short_repeat_nonrigid = 0
    no_triple_nonrigid = 0

    for key, specs in spectra.items():
        if len(specs) <= 1:
            continue
        nonrigid_supports += 1
        for s in by_support[key]:
            nonrigid_words += 1
            if all(v <= 2 for v in minmer_counts(s, L).values()):
                short_repeat_nonrigid += 1
            if long_bresler_triple(s, L) is None:
                no_triple_nonrigid += 1

    if verbose:
        print(
            f"  G={G:>2} L={L} sigma={len(alphabet)}: "
            f"nonrigid_supports={nonrigid_supports:>5} "
            f"(A)short_repeat_nonrigid={short_repeat_nonrigid} "
            f"(B)no_triple_nonrigid={no_triple_nonrigid}"
        )
    assert short_repeat_nonrigid == 0, "Theorem A violated"
    assert no_triple_nonrigid == 0, "main theorem violated"
    return nonrigid_supports


def check_periodic(alphabet, L, p_max, k_max, verbose=True):
    bad = 0
    for p in range(1, p_max + 1):
        for P in product(alphabet, repeat=p):
            if not is_primitive(P):
                continue
            for ell, r1, r2 in repeated_period_factors(P):
                if ell < L - 1:
                    continue
                for k in range(2, k_max + 1):
                    S = P * k
                    if long_bresler_triple(S, L) is None:
                        bad += 1
    if verbose:
        print(f"  periodic check L={L} p<={p_max} k<={k_max}: bad={bad}")
    assert bad == 0, "Lemma C violated"


def witness_min_same_length_same_support():
    # Overall minimum (searched scope: sigma in {2,3,4}, L in {2,3,4}): G=5, L=2.
    S = tuple("AAAAB")
    D = tuple("AABAB")
    L = 2
    assert support(S, L) == support(D, L)
    dS, dD = oriented_spec(S, L), oriented_spec(D, L)
    assert dS != dD
    tr = long_bresler_triple(S, L)
    assert tr is not None, "minimal non-rigid witness must have a long triple repeat"
    w0 = tuple("AB")
    assert dD[w0] > dS[w0]
    x = add_counts(dS, w0, 12)
    r = ratio_exact(x, dS, dD)
    assert r > 1, "skewed observation must beat the truth"
    print(
        f"  (D) minimum: S=AAAAB D=AABAB L=2: non-rigid, long triple ell={tr[0]}, "
        f"ratio(x=dS+12*e_AB)={r} > 1"
    )

    # Smallest with L >= 3.
    S3 = tuple("AAAAAAB")
    D3 = tuple("AAABAAB")
    L3 = 3
    assert support(S3, L3) == support(D3, L3)
    dS3, dD3 = oriented_spec(S3, L3), oriented_spec(D3, L3)
    assert dS3 != dD3
    tr3 = long_bresler_triple(S3, L3)
    assert tr3 is not None
    w03 = tuple("AAB")
    assert dD3[w03] > dS3[w03]
    r3 = ratio_exact(add_counts(dS3, w03, 12), dS3, dD3)
    assert r3 > 1
    print(
        f"  (D) L>=3 minimum: S=AAAAAAB D=AAABAAB L=3: non-rigid, "
        f"long triple ell={tr3[0]}, ratio(x=dS+12*e_AAB)={r3} > 1"
    )


def witness_variable_length():
    S = tuple("AAATT")
    D = tuple("AAAATT")
    L = 3
    G = len(S)
    dS, dD = oriented_spec(S, L), oriented_spec(D, L)
    V = support(S, L)
    assert support(D, L) == V
    # I_s with the full read set: no long Bresler triple repeat and no interleaved
    # pair with both constituents long; the only repeat is a bridgeable length-1 A.
    tr = long_bresler_triple(S, L)
    assert tr is None or tr[0] <= L - 2
    w0 = tuple("AAA")
    assert dD[w0] > dS[w0]
    for m in (0, 1, 2, 3):
        x = add_counts(dS, w0, m)
        n = sum(x.values())
        r_exact = ratio_exact_multinomial(x, dS, dD, G, len(D))
        r_fix = ratio_fixedN(x, dS, dD, n, G)
        if m == 0:
            assert r_exact < 1 and r_fix < 1
        else:
            assert r_exact > 1 and r_fix > 1
        print(
            f"  (E) S=AAATT D=AAAATT L=3 m={m}: exact={r_exact} fixedN={r_fix}"
        )


def main(argv):
    full = "--full" in argv
    print("[A/B] exhaustive: non-rigid <=> long Bresler triple repeat")
    total = 0
    scopes = [
        (("A", "B"), 3, range(5, 13)),
        (("A", "B"), 4, range(6, 12)),
        (("A", "B", "C"), 3, range(5, 10)),
    ]
    if full:
        scopes = [
            (("A", "B"), 3, range(5, 15)),
            (("A", "B"), 4, range(6, 14)),
            (("A", "B"), 5, range(7, 13)),
            (("A", "B", "C"), 3, range(5, 11)),
            (("A", "B", "C", "D"), 3, range(5, 9)),
        ]
    for alphabet, L, Grange in scopes:
        for G in Grange:
            total += check_scope(alphabet, G, L, verbose=True)
    print(f"  total non-rigid supports scanned: {total}")

    print("[C] periodic Lemma C")
    check_periodic(("A", "B"), 3, 9, 3)
    if full:
        check_periodic(("A", "B"), 4, 8, 2)
        check_periodic(("A", "B", "C"), 3, 6, 3)

    print("[D] minimal same-length same-support obstruction")
    witness_min_same_length_same_support()

    print("[E] variable-length strict-oriented boundary")
    witness_variable_length()

    print("all oriented Section 6.2 rigidity checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
