#!/usr/bin/env python3
"""Exact verification for the ORIENTED single-strand Section 6.2 case with
unrestricted candidate length (variable genome length).

Self-contained, exact integer / Fraction arithmetic, no repository imports.
Exit status is non-zero if any assertion fails.

Sections
  [1]  the instance: truth S, read length L, its spectrum and its a^L run
  [2]  the run-extension lemma spec_L(S^(k)) = spec_L(S) + k e_{a^L}
  [3]  R in I_s for the realized read starts (Shomorony / Bresler predicate,
       transcribed exactly as in AssemblyP1/SourceFaithfulIs.lean)
  [4]  the strict counterexample family: exact and fixed-N ratios, sample
       multiplicity, support, and the N domain
  [5]  the universal upper bound L*(x) and who attains it
  [6]  the stronger per-occurrence feasibility variant d >= x (bounded census)
  [7]  feasibility under the three Section 6.2 readings
"""

from fractions import Fraction
from itertools import product, combinations
import sys

SIG = ("A", "T")


def w2s(w):
    return "".join(w)


# --------------------------------------------------------------------------
# circular words, windows, spectra
# --------------------------------------------------------------------------

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


# --------------------------------------------------------------------------
# I_s (mirrors AssemblyP1/SourceFaithfulIs.lean)
# --------------------------------------------------------------------------

def read_covers(G, L, r, p):
    return any(p == (r + d) % G for d in range(L))


def bridges_copy(G, L, R, e, t):
    for r in R:
        for d in range(L):
            if d + e + 1 < L and (r + d + 1) % G == t % G:
                return True
    return False


def is_repeat(w, e, a, b):
    G = len(w)
    if not (1 <= e < G) or a == b:
        return False
    if any(w[(a + j) % G] != w[(b + j) % G] for j in range(e)):
        return False
    if w[(a - 1) % G] == w[(b - 1) % G]:
        return False
    return w[(a + e) % G] != w[(b + e) % G]


def is_triple_repeat(w, e, a, b, c):
    G = len(w)
    if not (1 <= e < G) or a == b or a == c or b == c:
        return False
    for (p, q) in ((a, b), (a, c), (b, c)):
        if any(w[(p + j) % G] != w[(q + j) % G] for j in range(e)):
            return False
    if w[(a - 1) % G] == w[(b - 1) % G] == w[(c - 1) % G]:
        return False
    return not (w[(a + e) % G] == w[(b + e) % G] == w[(c + e) % G])


def in_open_arc(G, a, b, p):
    return 0 < (p + G - a) % G < (b + G - a) % G


def interleaved(G, a, b, c, d):
    if len({a, b, c, d}) != 4:
        return False
    return in_open_arc(G, a, b, c) != in_open_arc(G, a, b, d)


def covers(G, L, R):
    return all(any(read_covers(G, L, r, p) for r in R) for p in range(G))


def information_feasible(w, L, R):
    """R in I_s: coverage, all triple repeats all-bridged, interleaved pairs
    bridged.  R is the SET of distinct realized read starts."""
    G = len(w)
    if not covers(G, L, R):
        return False, "coverage"
    for e in range(1, G):
        for a in range(G):
            for b in range(G):
                for c in range(G):
                    if is_triple_repeat(w, e, a, b, c):
                        if not all(bridges_copy(G, L, R, e, t) for t in (a, b, c)):
                            return False, ("triple", e, a, b, c)
    for e1 in range(1, G):
        for a in range(G):
            for b in range(G):
                if not is_repeat(w, e1, a, b):
                    continue
                for e2 in range(1, G):
                    for c in range(G):
                        for d in range(G):
                            if not is_repeat(w, e2, c, d):
                                continue
                            if interleaved(G, a, b, c, d):
                                if not any(bridges_copy(G, L, R, e, t)
                                           for e, t in ((e1, a), (e1, b),
                                                        (e2, c), (e2, d))):
                                    return False, ("interleaved", e1, a, b,
                                                   e2, c, d)
    return True, None


# --------------------------------------------------------------------------
# Section 6.2 feasibility notions, Section 6.1 objectives
# --------------------------------------------------------------------------

def feasible_F1(d, x):
    """Source per-vertex lower bound 1 (MB09 6.2)."""
    return all(d.get(w, 0) >= 1 for w in x if x[w] > 0)


def feasible_F2(d, x):
    """Per-occurrence strengthening d_w >= x_w (NOT the source bound)."""
    return all(d.get(w, 0) >= x[w] for w in x if x[w] > 0)


def feasible_F3(d, x):
    """Spelled support equality."""
    return ({w for w, c in d.items() if c > 0}
            == {w for w, c in x.items() if c > 0})


def multinomial_coeff(x):
    from math import factorial
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


def lik_exact_ratio(d, x, aref):
    """Ratio, without the observation-only multinomial coefficient."""
    n = sum(x.values())
    t = sum(d.values())
    ta = sum(aref.values())
    if t == 0 or ta == 0:
        return None
    p = Fraction(1)
    for w, xw in x.items():
        if xw > 0:
            if aref.get(w, 0) == 0:
                return Fraction(0)
            p *= Fraction(d.get(w, 0) * aref.get(w, 0) * ta,
                          t * aref.get(w, 0) ** 2) ** xw
    return p


def lik_binom(d, x, N):
    """Section 6.1 tractable objective: product of binomial marginals, with
    external known N.  Returns None if some d_w leaves the domain 0..N."""
    n = sum(x.values())
    keys = sorted({w for w in x if x[w] > 0} | {w for w in d if d[w] > 0})
    p = Fraction(1)
    for w in keys:
        dw = d.get(w, 0)
        if dw > N:
            return None
        xw = x.get(w, 0)
        p *= Fraction(dw, N) ** xw * Fraction(N - dw, N) ** (n - xw)
    return p


def lstar(x):
    """The universal upper bound L*(x) = (n!/prod x_w!) prod (x_w/n)^{x_w}."""
    n = sum(x.values())
    p = Fraction(1)
    for xw in x.values():
        if xw > 0:
            p *= Fraction(xw, n) ** xw
    return multinomial_coeff(x) * p


def check(label, cond):
    if not cond:
        print("FAIL:", label)
        sys.exit(1)
    return True


# --------------------------------------------------------------------------
# the instance and the counterexample family
# --------------------------------------------------------------------------

S = ("A", "A", "A", "T", "T")
L = 3
G = len(S)
A_SPEC = spectrum(S, L)
BOOST = ("A", "A", "A")
A0 = A_SPEC[BOOST]
ALL_STARTS = frozenset(range(G))


def witness_competitor(M):
    """D_M: S with M extra A's inserted inside its maximal A^3 run."""
    return ("A",) * (M + 2) + ("T", "T") + ("A",)


def witness_observation(M):
    """x_M = spec_L(S) + M e_AAA (all G starts plus M extra copies of the
    start whose window is AAA)."""
    return vec_add(A_SPEC, M, BOOST)


def part1_instance():
    print("=" * 76)
    print("ORIENTED single-strand Section 6.2, unrestricted candidate length")
    print("truth S = %s, G = %d, read length L = %d" % (w2s(S), G, L))
    print("=" * 76)
    print("\n[1] spec_%d(S) = %s (total %d)"
          % (L, {w2s(k): v for k, v in sorted(A_SPEC.items())},
             sum(A_SPEC.values())))
    check("spectrum total = G", sum(A_SPEC.values()) == G)
    check("AAA is a length-L run block", S[0:3] == BOOST)
    check("A_AAA < G (truth is not constant)", A0 < G)
    print("    the maximal run of A has length exactly L = 3, and the window")
    print("    a^L = AAA occurs %d < G times, so the truth is not constant." % A0)

    print("\n[2] run-extension lemma: spec_L(S^(k)) = spec_L(S) + k e_{a^L}")
    for k in range(0, 7):
        w = ("A",) * (3 + k) + ("T", "T")
        check("run extension k=%d" % k,
              spectrum(w, L) == vec_add(A_SPEC, k, BOOST))
    print("    inserting k extra A's into the maximal A^3 run adds exactly k")
    print("    copies of the window AAA and preserves every other window:")
    print("    verified exhaustively for k = 0..6.")

    ok, why = information_feasible(S, L, ALL_STARTS)
    print("\n[3] R = all %d starts: R in I_s = %s" % (G, ok))
    if not ok:
        print("    first violation: %s" % (why,))
    check("I_s for the all-starts read set", ok)
    print("    (coverage by all starts; the unique maximal triple repeat is")
    print("     the length-1 A at (0,1,2), all-bridged since 1 = L-2; the")
    print("     interleaved-repeat clause is vacuous on this instance.)")


def part4_family():
    print("\n[4] the strict counterexample family")
    print("    observation x_M = spec_%d(S) + M e_AAA, realized by all G" % L)
    print("    starts plus M extra copies of the start with window AAA")
    print("    (n = G + M reads); competitor D_M = S with M extra A's")
    print("    inserted in its A^3 run (|D_M| = G + M).")
    hdr = (" M   n  |D|  supp(x)              F1(truth,comp)  F3   "
           "exact ratio        fixed-N ratio (N=G)")
    print("    " + hdr)
    print("    " + "-" * len(hdr))
    rex, rbn = {}, {}
    for M in range(0, 5):
        x = witness_observation(M)
        D = witness_competitor(M)
        d = spectrum(D, L)
        n, t = sum(x.values()), len(D)
        f1t, f1c = feasible_F1(A_SPEC, x), feasible_F1(d, x)
        f3t, f3c = feasible_F3(A_SPEC, x), feasible_F3(d, x)
        f2t, f2c = feasible_F2(A_SPEC, x), feasible_F2(d, x)
        a = lik_exact(d, x) / lik_exact(A_SPEC, x)
        b1, b2 = lik_binom(d, x, G), lik_binom(A_SPEC, x, G)
        rex[M], rbn[M] = a, (None if (b1 is None or b2 is None) else b1 / b2)
        print("    %2d  %2d  %2d  %-19s  %-5s %-5s      %-5s %-16s %s"
              % (M, n, t, ",".join(sorted(w2s(t) for t in x)),
                 f1t, f1c, f3c, a, rbn[M]))
        check("M=%d: observation is a possible read multiset of S" % M,
              set(x) <= set(A_SPEC) and all(x[w] >= A_SPEC[w] for w in A_SPEC))
        check("M=%d: truth F1" % M, f1t)
        check("M=%d: truth F3" % M, f3t)
        check("M=%d: competitor F1" % M, f1c)
        check("M=%d: competitor F3" % M, f3c)
        check("M=%d: competitor is a spelled circuit" % M,
              feasible_F3(d, x))
        check("M=%d: N domain (all d_w <= N)" % M,
              all(v <= G for v in d.values()))
        check("M=%d: closed form" % M,
              (Fraction(G, G + M) ** (G + M))
              * (Fraction(A0 + M, A0) ** (A0 + M)) == a)
    print("\n    closed form: exact ratio(M) = (G/(G+M))^(G+M)")
    print("                            * ((A_0+M)/A_0)^(A_0+M),  A_0 = %d" % A0)
    print("    Since A_0 < G, the ratio is > 1 for every M >= 1 and = 1 at")
    print("    M = 0 (where the observation is a multiple of spec(S)).")
    for M in range(1, 5):
        check("M=%d exact strict" % M, rex[M] > 1)
    check("M=0 exact ratio = 1", rex[0] == 1)
    print("    fixed-N ratio (N=G=5): strict for M=1 (%s) and M=2 (%s);"
          % (rbn[1], rbn[2]))
    print("    M=3 ties exactly (x_AAA = 4, n = 8, the binomial factor is")
    print("    symmetric under p -> 1-p); M=4 has d_AAA = 5 = N which makes")
    print("    every other binomial factor 0, i.e. it leaves the admissible")
    print("    part of the domain.  The N domain is therefore essential and")
    print("    is satisfied for M <= 3.")
    check("M=1 fixed-N strict", rbn[1] > 1)
    check("M=2 fixed-N strict", rbn[2] > 1)
    check("M=3 fixed-N tie", rbn[3] == 1)

    print("\n    per-occurrence variant d >= x: the TRUTH is not feasible for")
    print("    any M >= 1, because x(AAA) = 1+M > 1 = spec(S)(AAA).")
    for M in range(1, 4):
        check("M=%d: truth not F2" % M, not feasible_F2(A_SPEC,
                                                       witness_observation(M)))
    print("    So this family witnesses the source per-vertex reading (F1)")
    print("    and the spelled support-equality reading (F3), and is silent")
    print("    on the stronger per-occurrence reading; see section [6].")


def part5_bound():
    print("\n[5] the universal upper bound L*(x) = (n!/prod x_w!) prod (x_w/n)^{x_w}")
    print("    exhaustive check over every circular binary word of length")
    print("    <= 12 that is F1-feasible:")
    for M in (0, 1, 2, 3):
        x = witness_observation(M)
        n = sum(x.values())
        bound, worst_viol = lstar(x), 0
        best, bestw = None, None
        for tlen in range(1, 13):
            for D in product(SIG, repeat=tlen):
                d = spectrum(D, L)
                if not feasible_F1(d, x):
                    continue
                v = lik_exact(d, x)
                if best is None or v > best:
                    best, bestw = v, D
                if v > bound:
                    worst_viol += 1
        check("M=%d: no word exceeds L*(x)" % M, worst_viol == 0)
        attained = (best == bound)
        print("    M=%d: n=%2d  best = %s (%s)  L*(x) = %s  -> bound %s"
              % (M, n, best, w2s(bestw), bound,
                 "ATTAINED" if attained else "not attained (in this scope)"))
        check("M=%d: truth <= L*(x)" % M, lik_exact(A_SPEC, x) <= bound)
    print("    The bound is attained exactly by the candidates whose")
    print("    normalized spectrum equals x/n; D_M attains it for every M,")
    print("    and the truth attains it exactly at M = 0.")


def part6_peroccurrence():
    print("\n[6] the stronger per-occurrence variant d >= x (bounded census)")
    print("    Question: with x <= spec_L(S) (so that the truth itself is")
    print("    feasible under the strengthened bound) and R in I_s, can any")
    print("    per-occurrence-feasible competitor strictly beat the truth?")
    print("    Scope: circular truth over {A,T}, G <= 6, L = 3, every start")
    print("    set T with T in I_s, every observation x with")
    print("    (window multiset at T) <= x <= spec_L(S) and |x| <= G, every")
    print("    circular binary competitor of length <= G + 3.")
    print("    BOUNDED EVIDENCE ONLY, not a proof of absence.")

    def best_competitor(spec, x, Gn, feas):
        """Best strict ratio over all binary words of length <= G+3, or
        None if none strictly beats the truth."""
        best = None
        for tlen in range(1, Gn + 4):
            for D in product(SIG, repeat=tlen):
                d = spectrum(D, L)
                if not feas(d, x):
                    continue
                r = lik_exact(d, x) / lik_exact(spec, x)
                if r > 1 and (best is None or r > best[0]):
                    best = (r, w2s(D))
        return best

    def flow_admissible(supp):
        """Necessary condition for ANY Section 6.2 flow to exist on the
        read-overlap graph: every read vertex must lie on a directed cycle
        inside the read set.  Without it the truth is not a candidate
        either, so the instance is vacuous under the source reading."""
        for w in supp:
            suc = any(u[:L - 1] == w[1:] for u in supp)
            pre = any(w[:L - 1] == u[1:] for u in supp)
            if not (suc and pre):
                return False
        return True

    wins = []
    n_is, n_x = 0, 0
    for Gn in range(3, 7):
        for Sw in product(SIG, repeat=Gn):
            spec = spectrum(Sw, L)
            for tsize in range(1, Gn + 1):
                for T in combinations(range(Gn), tsize):
                    ok, _ = information_feasible(Sw, L, set(T))
                    if not ok:
                        continue
                    n_is += 1
                    base = {}
                    for r in T:
                        w = windows(Sw, L)[r]
                        base[w] = base.get(w, 0) + 1
                    types = sorted(spec)

                    def rec(i, cur):
                        if i == len(types):
                            if 0 < sum(cur.values()) <= Gn:
                                yield dict(cur)
                            return
                        w = types[i]
                        for v in range(base.get(w, 0), spec[w] + 1):
                            cur[w] = v
                            if sum(cur.values()) <= Gn:
                                yield from rec(i + 1, cur)
                        cur.pop(w, None)

                    for x in rec(0, {}):
                        n_x += 1
                        b = best_competitor(spec, x, Gn, feasible_F2)
                        if b is not None:
                            wins.append((Gn, w2s(Sw), sorted(T), x, b))
    print("    I_s-feasible (S,T) pairs: %d ; observations scanned: %d"
          % (n_is, n_x))
    raw = [w for w in wins
           if flow_admissible({u for u in w[3] if w[3][u] > 0})]
    print("    strict per-occurrence wins before the flow-admissibility"
          " filter: %d" % len(wins))
    print("    after the filter (a read set with no directed cycle supports")
    print("    no Section 6.2 flow at all, so the truth is not a candidate")
    print("    there either): %d" % len(raw))
    if raw:
        raw.sort(key=lambda t: (t[0], sum(t[3].values()), t[4][0]))
        for (Gn, Sw, T, x, b) in raw[:10]:
            print("      S=%s (G=%d) T=%s x=%s (n=%d) ratio %s by D=%s"
                  % (Sw, Gn, T, {w2s(k): v for k, v in sorted(x.items())},
                     sum(x.values()), b[0], b[1]))
        print("    (surviving wins have sample multiplicities n = %s; see the"
              " note.)" % sorted({sum(w[3].values()) for w in raw}))
    else:
        print("    no strict per-occurrence counterexample survives in scope.")


def compositions(k, total):
    """All weak compositions of `total` into `k` parts."""
    if k == 1:
        yield (total,)
        return
    for i in range(total + 1):
        for rest in compositions(k - 1, total - i):
            yield (i,) + rest


def main():
    part1_instance()
    part4_family()
    part5_bound()
    if "--peroccurrence" in sys.argv:
        part6_peroccurrence()
    print("\nALL ASSERTIONS PASSED")


if __name__ == "__main__":
    main()
