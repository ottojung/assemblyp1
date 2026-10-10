#!/usr/bin/env python3
"""
Independent exact verification of the PARAMETRIC STRENGTHENING of the
same-length Medvedev-Brudno (2009) Section 6.2 counterexample recorded in

    AssemblyP1/SameLengthSection62Parametric.lean

and, at ``k = 0``, in ``AssemblyP1/SameLengthSection62Counterexample.lean``.

Base witness (kernel-checked, ``k = 0``):

    alphabet          {A, T}, reverse-complement involution A <-> T
    truth             S = AAATAT   (G = 6)
    competitor        D = AAAAAT   (|D| = G = 6, SAME LENGTH)
    read length       L = 3
    external size     N = 6
    realized starts   (0, 0, 1, 3, 5)          (n = 5 reads; start 0 twice)
    observed          x = { AAA:2, AAT:1, ATA:1, TAA:1 }
    truth spectrum    d_S = { AAA:1, AAT:1, ATA:3, TAA:1 }
    competitor spec   d_D = { AAA:3, AAT:1, ATA:1, TAA:1 }

Parametric family.  For arbitrary ``k : Nat`` add ``k`` extra *actual* AAA
reads at start 0, so the sampling is

    starts(k) = (0 repeated 2+k times, 1, 3, 5)      n = 5 + k
    x(k)      = { AAA:2+k, AAT:1, ATA:1, TAA:1 }

The set of realized *placements* (distinct sampled starts) is still
{0,1,3,5} and the observed read types are unchanged, so the inputs of the
historical I_s coverage/bridging hypothesis (which consumes only the distinct
start set) and the full MB09 Section 6.2 spelled-flow feasibility of both S and
D are literally unchanged; the canonical literal Section 6.4 historical I_s
transfers to every k from the k = 0 certificate (see the Lean module).

Claims checked here, exactly and deterministically with ``fractions.Fraction``
(exits non-zero on any failed assertion):

  (1) For every k in 0..KMAX the observed counts are as above, n = 5 + k, and
      the observed support {AAA, AAT, ATA, TAA} is independent of k.

  (2) The candidate-intrinsic exact multinomial ratio, computed directly as
      prod_c d_D(c)^{x_c} / prod_c d_S(c)^{x_c} over ALL eight molecule-class
      codes (zero-count factors included), equals 3 ** (k + 1).

  (3) The literal Section 6.1 product-of-binomial-marginals ratio, computed
      directly as prod_c [ C(n, x_c) (d_D(c)/N)^{x_c} (1 - d_D(c)/N)^{n-x_c} ]
      / prod_c [ C(n, x_c) (d_S(c)/N)^{x_c} (1 - d_S(c)/N)^{n-x_c} ] over ALL
      eight molecule-class codes, equals 5 ** (k + 1).

  (4) Both ratios are strictly greater than 1 for every k, and at k = 0 they
      are the already-published 3 and 5.

The exact algebra is the one stated in the module: the increment x_AAA + 1
multiplies the exact ratio by 3 (since d_D(AAA)/d_S(AAA) = 3), while the
binomial ratio increment additionally shifts n in every complement exponent,
giving a constant factor 3 * (5/3) = 5 per step.
"""

from __future__ import annotations

import sys
from collections import Counter
from fractions import Fraction

A, T = 0, 1
COMP = {A: T, T: A}

# The eight molecule-class labels of the Lean `Fin 8` code, in code order.
CLASS_CODES = list(range(8))

KMAX = 40


def rc(s):
    return tuple(COMP[c] for c in reversed(s))


def mol(s):
    return min(tuple(s), rc(tuple(s)))


def word(s):
    return "".join("AT"[c] for c in s)


def windows(seq, L):
    G = len(seq)
    return [tuple(seq[(i + j) % G] for j in range(L)) for i in range(G)]


def code(w):
    """The Lean `Fin 8` molecule-class code: min(own code, rc code)."""
    def bit(c):
        return c
    own = bit(w[0]) * 4 + bit(w[1]) * 2 + bit(w[2])
    r = rc(w)
    other = bit(r[0]) * 4 + bit(r[1]) * 2 + bit(r[2])
    return min(own, other)


def observed_counts(S, starts, L):
    x = Counter()
    for r in starts:
        x[code(tuple(S[(r + j) % len(S)] for j in range(L)))] += 1
    return x


def spectrum(seq, L):
    return Counter(code(w) for w in windows(seq, L))


def exact_product(sp, x):
    """prod_c d_c^{x_c} over ALL eight class codes (0^0 = 1)."""
    r = Fraction(1)
    for c in CLASS_CODES:
        r *= Fraction(sp.get(c, 0)) ** x.get(c, 0)
    return r


def binom_product(x, n, N, d):
    """prod_c C(n, x_c) (d_c/N)^{x_c} (1 - d_c/N)^{n - x_c} over ALL eight
    class codes, zero-count factors included."""
    r = Fraction(1)
    for c in CLASS_CODES:
        xc = x.get(c, 0)
        dc = d.get(c, 0)
        r *= (Fraction(1) if xc == 0 else Fraction(_choose(n, xc))) \
            * Fraction(dc, N) ** xc \
            * (Fraction(N - dc, N)) ** (n - xc)
    return r


def _choose(n, k):
    from math import comb
    return comb(n, k)


def starts_for(k):
    return tuple([0] * (2 + k) + [1, 3, 5])


def main():
    L = 3
    S = (A, A, A, T, A, T)   # AAATAT
    D = (A, A, A, A, A, T)   # AAAAAT
    N = len(S)

    dS = spectrum(S, L)
    dD = spectrum(D, L)

    checks = []

    def chk(name, cond):
        checks.append((name, bool(cond)))

    base_support = None

    for k in range(KMAX + 1):
        starts = starts_for(k)
        n = len(starts)
        x = observed_counts(S, starts, L)

        # (1) counts, n, and unchanged support
        chk(f"k={k}: n = 5 + k", n == 5 + k)
        chk(f"k={k}: x = {{AAA:2+k, AAT:1, ATA:1, TAA:1}}",
            dict(x) == {0: 2 + k, 1: 1, 2: 1, 4: 1})
        support = frozenset(c for c in CLASS_CODES if x.get(c, 0) > 0)
        if base_support is None:
            base_support = support
        chk(f"k={k}: observed support unchanged",
            support == base_support == frozenset({0, 1, 2, 4}))

        # (2) exact multinomial ratio
        r_exact = exact_product(dD, x) / exact_product(dS, x)
        chk(f"k={k}: exact multinomial ratio = 3^(k+1)",
            r_exact == Fraction(3) ** (k + 1))
        chk(f"k={k}: exact ratio > 1", r_exact > 1)

        # (3) Section 6.1 binomial ratio (all zero-count factors retained)
        r_binom = binom_product(x, n, N, dict(dD)) / binom_product(x, n, N, dict(dS))
        chk(f"k={k}: Section 6.1 binomial ratio = 5^(k+1)",
            r_binom == Fraction(5) ** (k + 1))
        chk(f"k={k}: binomial ratio > 1", r_binom > 1)

    # (4) k = 0 reduces to the already-published witness
    chk("k=0: exact ratio is 3", exact_product(dD, observed_counts(S, starts_for(0), L))
        / exact_product(dS, observed_counts(S, starts_for(0), L)) == 3)
    chk("k=0: binomial ratio is 5",
        binom_product(observed_counts(S, starts_for(0), L), 5, N, dict(dD))
        / binom_product(observed_counts(S, starts_for(0), L), 5, N, dict(dS)) == 5)

    failed = [name for name, ok in checks if not ok]
    print(f"checked k = 0..{KMAX} ({len(checks)} assertions)")
    print(f"truth S = {word(S)} (G={len(S)}), competitor D = {word(D)} (G={len(D)})")
    print(f"d_S = {fmt(dS)}")
    print(f"d_D = {fmt(dD)}")
    if failed:
        print("\nFAILED:")
        for name in failed:
            print(f"  [FAIL] {name}")
        print("\nSOME CHECKS FAILED")
        return 1
    print("\nALL CHECKS PASS")
    return 0


def fmt(c):
    parts = []
    for code_val, v in sorted(c.items()):
        bits = ((code_val >> 2) & 1, (code_val >> 1) & 1, code_val & 1)
        parts.append(f"{word(bits)}:{v}")
    return "{" + ", ".join(parts) + "}"


if __name__ == "__main__":
    sys.exit(main())
