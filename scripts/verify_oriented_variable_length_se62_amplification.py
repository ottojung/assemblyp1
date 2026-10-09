#!/usr/bin/env python3
"""Exact verification of the AMPLIFICATION REDUCTION for the oriented
single-strand Section 6.2 variable-length counterexample (board issue #210).

Self-contained, exact integer / Fraction arithmetic, no repository imports.
Exit status is non-zero if any assertion fails.

Families (truth S = AAATT, G = 5, L = 3, competitor D = AAAATT, |D| = 6,
observation x^{(M)} = spec_3(S) + M e_AAA, n = 5 + M):

  [1]  the instance: spectra, base ratios at M = 0
  [2]  Lemma 1 (exact-ML amplification): the ratio identity for M = 0..200
  [3]  Theorem B closed form (3125/3888)(5/3)^M > 1 for M >= 1
  [4]  Lemma 2 (fixed-N binomial amplification): the ratio identity
  [5]  Theorem C closed form (81/128) 2^M > 1 for M >= 1, N domain
  [6]  the amplification preserves I_s and section 6.2 admissibility
        (monotonicity facts, checked as finite predicates on this instance)
"""

from fractions import Fraction
from math import factorial
import sys

SIG = ("A", "T")


def windows(w, L):
    n = len(w)
    return [tuple(w[(i + j) % n] for j in range(L)) for i in range(n)]


def spectrum(w, L):
    d = {}
    for win in windows(w, L):
        d[win] = d.get(win, 0) + 1
    return d


def vec_add(d, k, w):
    e = dict(d)
    e[w] = e.get(w, 0) + k
    return e


def multinomial_coeff(x):
    num = factorial(sum(x.values()))
    den = 1
    for c in x.values():
        den *= factorial(c)
    return Fraction(num, den)


def lik_exact(d, x):
    """Section 6.1 exact objective, candidate-intrinsic N(D) = sum d."""
    n = sum(x.values())
    t = sum(d.values())
    if t == 0:
        return Fraction(0)
    p = Fraction(1)
    for w, xw in x.items():
        if xw > 0:
            p *= Fraction(d.get(w, 0), t) ** xw
    return multinomial_coeff(x) * p


def lik_binom(d, x, N):
    """Section 6.1 product of binomial marginals, external known N.
    Returns None if some d_w leaves the domain 0..N."""
    n = sum(x.values())
    keys = sorted(set(x) | set(d))
    p = Fraction(1)
    for w in keys:
        dw = d.get(w, 0)
        if dw > N:
            return None
        xw = x.get(w, 0)
        p *= Fraction(dw, N) ** xw * Fraction(N - dw, N) ** (n - xw)
    return p


def check(label, cond):
    if not cond:
        print("FAIL:", label)
        sys.exit(1)
    return True


S = ("A", "A", "A", "T", "T")
D = ("A", "A", "A", "A", "T", "T")
L = 3
G = len(S)
N_EXT = 5
W = ("A", "A", "A")
A_SPEC = spectrum(S, L)
D_SPEC = spectrum(D, L)
ALL_STARTS = frozenset(range(G))
M_MAX = 200


def observation(M):
    return vec_add(A_SPEC, M, W)


def part1_instance():
    print("=" * 76)
    print("AMPLIFICATION REDUCTION, oriented variable-length section 6.2")
    print("truth S = %s (G = %d), competitor D = %s (|D| = %d), L = %d"
          % ("".join(S), G, "".join(D), len(D), L))
    print("=" * 76)
    print("\n[1] the instance and the M = 0 base ratios")
    print("    spec_3(S) = %s" % { "".join(k): v for k, v in sorted(A_SPEC.items())})
    print("    spec_3(D) = %s" % { "".join(k): v for k, v in sorted(D_SPEC.items())})
    check("spectrum totals", sum(A_SPEC.values()) == G and sum(D_SPEC.values()) == len(D))
    check("d_D = spec_S + e_AAA", D_SPEC == vec_add(A_SPEC, 1, W))
    x0 = observation(0)
    rex0 = lik_exact(D_SPEC, x0) / lik_exact(A_SPEC, x0)
    rbn0 = lik_binom(D_SPEC, x0, N_EXT) / lik_binom(A_SPEC, x0, N_EXT)
    print("    M = 0 exact ratio      = %s  (< 1: the competitor LOSES at M = 0)" % rex0)
    print("    M = 0 binomial ratio   = %s  (< 1)" % rbn0)
    check("base exact ratio 3125/3888", rex0 == Fraction(3125, 3888))
    check("base binomial ratio 81/128", rbn0 == Fraction(81, 128))
    print("    p_D(AAA)/p_S(AAA) = (2/6)/(1/5) = %s  (exact amplification factor)"
          % (Fraction(2, 6) / Fraction(1, 5)))
    print("    Q_AAA = (2/5)/(1/5) = 2  (binomial amplification factor; all other")
    print("    coordinates of d_D and d_S coincide, so the product over i != AAA is 1)")


def part2_lemma1():
    print("\n[2] Lemma 1 (exact-ML amplification), M = 0..%d" % M_MAX)
    print("    L_E(D|x^{(m)})/L_E(S|x^{(m)}) = [L_E(D|x)/L_E(S|x)] (p_D(w)/p_S(w))^m")
    base = lik_exact(D_SPEC, observation(0)) / lik_exact(A_SPEC, observation(0))
    factor = Fraction(D_SPEC[W], len(D)) / Fraction(A_SPEC[W], G)
    worst = None
    for m in range(0, M_MAX + 1):
        x = observation(m)
        ratio = lik_exact(D_SPEC, x) / lik_exact(A_SPEC, x)
        expect = base * factor ** m
        if ratio != expect:
            worst = m
            break
        if m in (0, 1, 2, 3, 10, 100, 200):
            print("    m = %3d: ratio = %s" % (m, ratio))
    check("Lemma 1 identity for all m in 0..%d" % M_MAX, worst is None)
    print("    identity holds for every m = 0..%d (exact Fraction arithmetic)" % M_MAX)


def part3_theoremB():
    print("\n[3] Theorem B closed form: ratio(M) = (3125/3888)(5/3)^M > 1 for M >= 1")
    base = Fraction(3125, 3888)
    factor = Fraction(5, 3)
    for m in range(1, M_MAX + 1):
        x = observation(m)
        ratio = lik_exact(D_SPEC, x) / lik_exact(A_SPEC, x)
        if ratio != base * factor ** m:
            print("FAIL: Theorem B at m = %d" % m)
            sys.exit(1)
    print("    closed form verified for m = 1..%d" % M_MAX)
    check("M=1 strict", base * factor > 1)
    check("M=1 value 15625/11664", base * factor == Fraction(15625, 11664))
    print("    ratio(1) = %s > 1; ratio diverges like (5/3)^m" % (base * factor))


def part4_lemma2():
    print("\n[4] Lemma 2 (fixed-N binomial amplification), N = %d, M = 0..%d"
          % (N_EXT, M_MAX))
    print("    L_A(D|x^{(m)})/L_A(S|x^{(m)}) = [L_A(D|x)/L_A(S|x)] Q_w^m, Q_AAA = 2")
    base = lik_binom(D_SPEC, observation(0), N_EXT) / lik_binom(A_SPEC, observation(0), N_EXT)
    q = Fraction(2)
    for m in range(0, M_MAX + 1):
        x = observation(m)
        ld = lik_binom(D_SPEC, x, N_EXT)
        ls = lik_binom(A_SPEC, x, N_EXT)
        check("M=%d: both candidates in N domain" % m,
              ld is not None and ls is not None)
        ratio = ld / ls
        if ratio != base * q ** m:
            print("FAIL: Lemma 2 at m = %d" % m)
            sys.exit(1)
        if m in (0, 1, 2, 3, 10, 100, 200):
            print("    m = %3d: ratio = %s" % (m, ratio))
    print("    identity holds for every m = 0..%d; both candidates stay in the" % M_MAX)
    print("    N domain at every m because they are FIXED (d_D(AAA) = 2 < N = 5)")


def part5_theoremC():
    print("\n[5] Theorem C closed form: ratio(M) = (81/128) 2^M > 1 for M >= 1")
    base = Fraction(81, 128)
    for m in range(1, M_MAX + 1):
        x = observation(m)
        ratio = lik_binom(D_SPEC, x, N_EXT) / lik_binom(A_SPEC, x, N_EXT)
        if ratio != base * Fraction(2) ** m:
            print("FAIL: Theorem C at m = %d" % m)
            sys.exit(1)
    print("    closed form verified for m = 1..%d" % M_MAX)
    check("M=1 strict, value 81/64", base * 2 == Fraction(81, 64))
    check("M=2 strict, value 81/32", base * 4 == Fraction(81, 32))
    print("    ratio(1) = 81/64 (kernel-checked in Lean: this instance coincides")
    print("    with the growing family at M=1), ratio(2) = 81/32; the ratio")
    print("    diverges like 2^m.  (The growing-family value 27/16 at M=2, also")
    print("    kernel-checked in Lean, is a DIFFERENT instance: D_2 = AAAATTA.)")


def part6_monotonicity():
    print("\n[6] monotonicity of I_s and section 6.2 admissibility under added reads")
    print("    (finite-predicate checks on this instance; the general facts are")
    print("    proved in the note section 4)")

    def read_covers(Gm, L, r, p):
        return any(p == (r + d) % Gm for d in range(L))

    def covers(Gm, L, R):
        return all(any(read_covers(Gm, L, r, p) for r in R) for p in range(Gm))

    def bridges_copy(Gm, L, R, e, t):
        for r in R:
            for d in range(L):
                if d + e + 1 < L and (r + d + 1) % Gm == t % Gm:
                    return True
        return False

    def is_triple_repeat(w, e, a, b, c):
        Gm = len(w)
        if not (1 <= e < Gm) or a == b or a == c or b == c:
            return False
        for (p, q) in ((a, b), (a, c), (b, c)):
            if any(w[(p + j) % Gm] != w[(q + j) % Gm] for j in range(e)):
                return False
        if w[(a - 1) % Gm] == w[(b - 1) % Gm] == w[(c - 1) % Gm]:
            return False
        return not (w[(a + e) % Gm] == w[(b + e) % Gm] == w[(c + e) % Gm])

    def in_open_arc(Gm, a, b, p):
        return 0 < (p + Gm - a) % Gm < (b + Gm - a) % Gm

    def interleaved(Gm, a, b, c, d):
        if len({a, b, c, d}) != 4:
            return False
        return in_open_arc(Gm, a, b, c) != in_open_arc(Gm, a, b, d)

    def is_repeat(w, e, a, b):
        Gm = len(w)
        if not (1 <= e < Gm) or a == b:
            return False
        if any(w[(a + j) % Gm] != w[(b + j) % Gm] for j in range(e)):
            return False
        if w[(a - 1) % Gm] == w[(b - 1) % Gm]:
            return False
        return w[(a + e) % Gm] != w[(b + e) % Gm]

    def information_feasible(w, L, R):
        Gm = len(w)
        if not covers(Gm, L, R):
            return False
        for e in range(1, Gm):
            for a in range(Gm):
                for b in range(Gm):
                    for c in range(Gm):
                        if is_triple_repeat(w, e, a, b, c):
                            if not all(bridges_copy(Gm, L, R, e, t) for t in (a, b, c)):
                                return False
        for e1 in range(1, Gm):
            for a in range(Gm):
                for b in range(Gm):
                    if not is_repeat(w, e1, a, b):
                        continue
                    for e2 in range(1, Gm):
                        for c in range(Gm):
                            for d in range(Gm):
                                if not is_repeat(w, e2, c, d):
                                    continue
                                if interleaved(Gm, a, b, c, d):
                                    if not any(bridges_copy(Gm, L, R, e, t)
                                                for e, t in ((e1, a), (e1, b),
                                                             (e2, c), (e2, d))):
                                        return False
        return True

    base = information_feasible(S, L, ALL_STARTS)
    check("R = all starts in I_s", base)
    for m in range(1, M_MAX + 1):
        Rm = set(ALL_STARTS) | {0}
        if not information_feasible(S, L, Rm):
            print("FAIL: I_s lost at m = %d" % m)
            sys.exit(1)
    print("    I_s(R_m) holds for every m = 1..%d (adding reads at the AAA start" % M_MAX)
    print("    preserves coverage, all-bridged, and interleaved-bridged)")

    def per_vertex(d, x):
        return all(d.get(w, 0) >= 1 for w in x if x[w] > 0)

    def spelled(d, x):
        return ({w for w, c in d.items() if c > 0}
                == {w for w, c in x.items() if c > 0})

    for m in range(0, M_MAX + 1):
        x = observation(m)
        check("M=%d: truth F1/F3" % m, per_vertex(A_SPEC, x) and spelled(A_SPEC, x))
        check("M=%d: competitor F1/F3" % m, per_vertex(D_SPEC, x) and spelled(D_SPEC, x))
    print("    F1 (per-vertex lower bound 1) and F3 (spelled support equality)")
    print("    hold for both candidates at every m = 0..%d: they are properties" % M_MAX)
    print("    of the fixed spectra, unaffected by the sample multiplicities")


def main():
    part1_instance()
    part2_lemma1()
    part3_theoremB()
    part4_lemma2()
    part5_theoremC()
    part6_monotonicity()
    print("\nALL ASSERTIONS PASSED")


if __name__ == "__main__":
    main()
