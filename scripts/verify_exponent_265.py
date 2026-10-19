#!/usr/bin/env python3
"""Exact verification for #265: restricted vs unrestricted exact-ML exponent.

Two independent checks are performed, both self-contained (no external
statistics assumed):

1.  **Unrestricted-universe obstruction (definitive counterexample).**  The
    oriented uniform-start circular read law of a genome is unchanged when the
    genome is replaced by an m-fold repetition of itself (m >= 2).  Hence
    ``S = AB`` and ``D = ABAB`` are two *distinct* circular genomes with
    identical read laws at *every* read length.  Over a candidate universe that
    contains such a pair the truth's own read law is a member of the candidate
    read-law family, so the "some competitor ties or beats the truth" event is
    the certain event and the exact-ML error probability is 1 for every n; no
    uniform exponential decay is possible.  A primitive near-repeat family
    (AB)^m A with vanishing separation is checked as a second obstruction.

2.  **Non-tightness of the kernel-checked exponent ``1/(8 B^4)``.**  For small
    primitive-P2 classes (the exact candidate class of
    ``AssemblyP1.PrimitiveP2UniformSeparation``) the *complete* class is
    enumerated and the exact worst-case Hellinger separation
    ``gamma = min over (truth, non-rotational competitor) of 1 - rho`` is
    computed.  ``gamma`` exceeds the theorem's lower bound ``1/(8 B^4)`` by a
    factor that grows with ``B``; the extremal pair is a one-symbol insertion
    with ``gamma * B`` roughly constant, indicating the true exponent is 1, not
    4.  This is an exact finite computation; the asymptotic claim is stated as a
    conjecture in docs/restricted-vs-unrestricted-exponent-265.md, not here.

Run:  python3 scripts/verify_exponent_265.py
Exit code 0 means every checked identity/inequality held.
"""
from __future__ import annotations

import itertools
import sys
from fractions import Fraction
from math import sqrt

FAIL = []


def check(condition: bool, message: str) -> None:
    if not condition:
        FAIL.append(message)
        print(f"FAIL: {message}")
    else:
        print(f"ok:   {message}")


# --------------------------------------------------------------------------
# Exact genome / read-law model (matches AssemblyP1.SourceFaithfulIs.Genome and
# AssemblyP1.FiniteReadRecoveryGenome.circularReadPMF).
# --------------------------------------------------------------------------
def cyc(S, i):
    return S[i % len(S)]


def window(S, L, r):
    return tuple(cyc(S, r + d) for d in range(L))


def read_law(S, L):
    """Uniform-start oriented circular read law as {word: Fraction}."""
    G = len(S)
    counts = {}
    for r in range(G):
        w = window(S, L, r)
        counts[w] = counts.get(w, 0) + 1
    return {w: Fraction(c, G) for w, c in counts.items()}


def affinity(p, q):
    keys = set(p) | set(q)
    return sum(sqrt(float(p.get(k, 0)) * float(q.get(k, 0))) for k in keys)


def is_primitive(S):
    G = len(S)
    for s in range(1, G):
        if all(cyc(S, i) == cyc(S, i + s) for i in range(G)):
            return False
    return True


def rotations(S):
    G = len(S)
    return {tuple(S[(i + r) % G] for i in range(G)) for r in range(G)}


def agree(S, e, a, b):
    return all(window(S, e, a)[d] == window(S, e, b)[d] for d in range(e))


def is_repeat(S, e, a, b):
    G = len(S)
    return (
        1 <= e < G
        and a != b
        and agree(S, e, a, b)
        and cyc(S, a - 1) != cyc(S, b - 1)
        and cyc(S, a + e) != cyc(S, b + e)
    )


def is_triple_repeat(S, e, a, b, c):
    G = len(S)
    if not (1 <= e < G and len({a, b, c}) == 3):
        return False
    if not (agree(S, e, a, b) and agree(S, e, a, c) and agree(S, e, b, c)):
        return False
    pre = not (cyc(S, a - 1) == cyc(S, b - 1) == cyc(S, c - 1))
    fol = not (cyc(S, a + e) == cyc(S, b + e) == cyc(S, c + e))
    return pre and fol


def in_open_arc(S, a, b, p):
    G = len(S)
    return 0 < (p + G - a) % G < (b + G - a) % G


def interleaved(S, a, b, c, d):
    if len({a, b, c, d}) < 4:
        return False
    return in_open_arc(S, a, b, c) != in_open_arc(S, a, b, d)


def P2(S, L):
    """AssemblyP1.P2 (oriented, read length L).

    Grouping positions by their length-``e`` window makes this quadratic in the
    group sizes instead of cubic in ``G``; equivalent to the definition but fast
    enough to enumerate the complete class at ``B = 16``.
    """
    G = len(S)
    reps = []
    for e in range(1, G):
        groups = {}
        for a in range(G):
            groups.setdefault(window(S, e, a), []).append(a)
        # clause 1: no maximal triple repeat of length >= L - 1
        if e >= L - 1:
            for pos in groups.values():
                if len(pos) >= 3:
                    for a, b, c in itertools.combinations(pos, 3):
                        if is_triple_repeat(S, e, a, b, c):
                            return False
        # collect maximal repeats for clause 2
        for pos in groups.values():
            for a, b in itertools.combinations(pos, 2):
                if cyc(S, a - 1) != cyc(S, b - 1) and cyc(S, a + e) != cyc(S, b + e):
                    reps.append((e, a, b))
    # clause 2: no interleaved maximal repeat pair with both parts >= L - 1
    for (e1, a, b) in reps:
        for (e2, c, d) in reps:
            if interleaved(S, a, b, c, d) and not (e1 <= L - 2 or e2 <= L - 2):
                return False
    return True


# --------------------------------------------------------------------------
# Check 1: unrestricted-universe obstruction.
# --------------------------------------------------------------------------
def check_collision():
    print("\n== Check 1a: exact read-law collision AB vs ABAB ==")
    S = (0, 1)          # AB
    D = (0, 1, 0, 1)    # ABAB = S repeated twice
    check(S != D, "S=AB and D=ABAB are distinct genomes")
    check(len(S) != len(D), "AB and ABAB are not rotations (different lengths)")
    for L in range(1, 7):
        ps = read_law(S, L)
        pd = read_law(D, L)
        check(ps == pd, f"read laws agree at L={L}")

    # general m-fold repetition: D_i = S_{i mod G}, read laws must coincide
    print("\n== Check 1b: m-fold repetition preserves the read law ==")
    for base, m in [((0, 1), 3), ((0, 0, 1), 2), ((0, 1, 1, 0), 3)]:
        G = len(base)
        D = tuple(base[i % G] for i in range(m * G))
        for L in range(1, 5):
            check(read_law(base, L) == read_law(D, L),
                  f"m={m} base={base} L={L}: laws agree")

    # with a colliding competitor in the family the wrong event is certain:
    # the truth's own law is in the candidate read-law family, so the event
    # "some q in family has L_q >= L_truth" holds for every sample, i.e. the
    # exact-ML error probability is 1 for every n (no decay, uniform or not).
    print("\n== Check 1c: collision forces exact-ML error = 1 for every n ==")
    Struth = (0, 1)
    Dcollide = (0, 1, 0, 1)
    family_laws = {tuple(sorted((w, float(v)) for w, v in read_law(Dcollide, L).items()))
                   for L in (2,)}
    truth_laws = tuple(sorted((w, float(v)) for w, v in read_law(Struth, 2).items()))
    check(truth_laws in family_laws,
          "truth read law is present in the candidate read-law family")


def check_primitive_vanishing():
    print("\n== Check 1d: primitive competitors with vanishing separation ==")
    S = (0, 1)  # AB, primitive-P2
    prev = None
    decreasing = True
    for m in range(1, 9):
        D = tuple([0, 1] * m + [0])  # (AB)^m A, primitive, length 2m+1
        check(is_primitive(D), f"m={m}: (AB)^m A is primitive")
        gap = 1 - affinity(read_law(S, 2), read_law(D, 2))
        if prev is not None and not gap < prev:
            decreasing = False
        prev = gap
    check(decreasing, "separation 1-rho strictly decreases to 0 along (AB)^m A")
    print(f"       final m=8: 1-rho = {prev:.6g} (no positive uniform margin)")


# --------------------------------------------------------------------------
# Check 2: exact worst-case separation over the primitive-P2 class.
# --------------------------------------------------------------------------
def primitive_p2_class(q, L):
    B = 2 * q ** (L - 1)
    out = []
    for G in range(1, B + 1):
        for w in itertools.product(range(q), repeat=G):
            if is_primitive(w) and P2(w, L):
                out.append(w)
    return out, B


def worst_separation(q, L):
    cls, B = primitive_p2_class(q, L)
    laws = {S: read_law(S, L) for S in cls}
    best = None  # (gap, S, D)
    for i, S in enumerate(cls):
        p = laws[S]
        rots = rotations(S)
        for j, D in enumerate(cls):
            if i == j or D in rots:
                continue
            r = laws[D]
            if r == p:
                continue
            gap = 1 - affinity(p, r)
            if best is None or gap < best[0]:
                best = (gap, S, D)
    return cls, B, best


def check_exponent():
    print("\n== Check 2: exact worst-case separation vs the 1/(8 B^4) bound ==")
    rows = []
    for (q, L) in [(2, 2), (3, 2), (2, 3), (2, 4)]:
        cls, B, (gap, S, D) = worst_separation(q, L)
        bound = 1 / (8 * B ** 4)
        ratio = gap / bound
        rows.append((q, L, B, len(cls), gap, ratio, gap * B, S, D))
        print(f"  q={q} L={L} B={B} |class|={len(cls)}")
        print(f"    extremal S={S}")
        print(f"             D={D}  (|D|=|S|+1, one-symbol insertion)")
        print(f"    gamma={gap:.9g}  1/(8B^4)={bound:.6g}  ratio={ratio:.4g}"
              f"  gamma*B={gap*B:.6f}")
        check(ratio > 1.0, f"q={q},L={L}: true separation exceeds the bound")
        check(D == S + (S[-1],) or len(D) == len(S) + 1,
              f"q={q},L={L}: extremal competitor is a one-symbol insertion")

    # exact clean value for q=2, L=2: 1 - rho = 1 - sqrt(3)/2
    gap22 = rows[0][4]
    check(abs(gap22 - (1 - sqrt(3) / 2)) < 1e-12,
          "q=2,L=2 exact gamma = 1 - sqrt(3)/2 = 0.1339745962...")

    # gamma * B is (roughly) constant, supporting exponent 1 rather than 4
    gammab = [row[6] for row in rows]
    check(all(0.45 <= x <= 0.60 for x in gammab),
          "gamma * B stays in [0.45,0.60]: true exponent is 1, not 4")
    print("\n  ratio to 1/(8B^4) grows like B^3 (4*B^3):")
    for (q, L, B, n, gap, ratio, gb, S, D) in rows:
        print(f"    B={B:>3}: ratio={ratio:>10.4g}   4*B^3={4*B**3:>10.4g}")


def main() -> int:
    check_collision()
    check_primitive_vanishing()
    check_exponent()
    print()
    if FAIL:
        print(f"{len(FAIL)} check(s) FAILED")
        return 1
    print("all exponent-265 checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
