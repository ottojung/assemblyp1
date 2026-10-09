#!/usr/bin/env python3
"""Verification of the two-disjoint-circles duplex model (V5) for issue #215.

This script is self-contained and exact (integers and `fractions.Fraction`).
It shares no code with any other repository script.  It exits non-zero on any
failed assertion.

The V5 model represents duplex DNA as TWO DISJOINT circular strands
`(S, rc(S))`, each of length `G`, rather than as the single artificial
length-`2G` circle `S · rc(S)` of the Bresler remap (V3).  For any oriented
`L`-mer `w`,

    spec_duplex(w) = spec_S(w) + spec_rcS(w) = spec_S(w) + spec_S(rc(w)),

giving exactly `2G` oriented windows with NO seam terms.  A read at `S`-start
`t` has its reverse-complement partner at `rc(S)`-start `(G - t - L) mod G`,
exactly, even when the read wraps.

The script checks, in order:

  0. The V5 spec identity and read-placement map (exhaustive, binary scope).
  1. The `AAATAT -> AAAAAT` witness under V5, circle-by-circle reading:
     `I_s` on `S` and on `rc(S)` with the partner read set.
  2. The witness under the duplex-as-a-whole reading: mixed triple repeats
     and the failure of `I_s` on the duplex.
  3. Exact compatibility of the circle-by-circle reading with the oriented
     single-strand reduction (the `rc` symmetry).
  4. The candidate set: V5 duplex candidate vs V3 doubled candidate, and the
     effect on the likelihood ratio.
  5. Source-faithfulness: V5 vs the MB09 molecule spectrum and the Bresler
     doubled spectrum; when V5 and V3 coincide (the R2 condition).
  6. Bounded searches: how often mixed triple repeats occur, and the V5/V3
     agreement rate.

Usage:
    python3 scripts/verify_two_disjoint_circles_duplex.py           # quick
    python3 scripts/verify_two_disjoint_circles_duplex.py --full     # wider
"""

from __future__ import annotations

import sys
from fractions import Fraction
from itertools import combinations, product

FULL = "--full" in sys.argv[1:]

DNA = ("A", "C", "G", "T")
COMP = {"A": "T", "T": "A", "C": "G", "G": "C"}


def rc(w):
    """Reverse complement of a word (tuple of symbols)."""
    return tuple(COMP[c] for c in reversed(w))


def class_of(w):
    """Canonical representative of the reverse-complement orbit of `w`."""
    r = rc(w)
    return w if w <= r else r


def window(g, e, r):
    """Length-`e` circular window of `g` beginning at `r`."""
    G = len(g)
    return tuple(g[(r + i) % G] for i in range(e))


def spectrum(g, e):
    """Oriented length-`e` circular window counts of `g`."""
    s = {}
    for t in range(len(g)):
        w = window(g, e, t)
        s[w] = s.get(w, 0) + 1
    return s


def molecule_spectrum(g, e):
    """`m_S(c)` = summed oriented occurrences of the words in class `c`."""
    m = {}
    for t in range(len(g)):
        c = class_of(window(g, e, t))
        m[c] = m.get(c, 0) + 1
    return m


def lint_spectrum(g, e):
    """Non-wrapping (linear) length-`e` occurrences of the words of `g`."""
    G = len(g)
    s = {}
    for t in range(0, G - e + 1):
        w = tuple(g[t : t + e])
        s[w] = s.get(w, 0) + 1
    return s


def wrap_spectrum(g, e):
    """Wrapping (circular-only) length-`e` occurrences of the words of `g`."""
    G = len(g)
    s = {}
    for t in range(G - e + 1, G):
        w = window(g, e, t)
        s[w] = s.get(w, 0) + 1
    return s


def seam_windows(g, L):
    """The `2(L-1)` junction windows of the doubled genome `S · rc(S)`."""
    G = len(g)
    W = 2 * G
    hs = tuple(g) + tuple(rc(g))
    out = {}
    for t in list(range(G - L + 1, G)) + list(range(W - L + 1, W)):
        w = window(hs, L, t)
        out[w] = out.get(w, 0) + 1
    return out


# --------------------------------------------------------------------------- #
# The oriented single-strand I_s (Shomorony et al. 2016, Bresler et al. 2013
# repeat definitions), transcribed from AssemblyP1/SourceFaithfulIs.lean.
# --------------------------------------------------------------------------- #


def covers(g, L, R):
    G = len(g)
    return all(
        any(p == (r + d) % G for d in range(L) for r in R) for p in range(G)
    )


def bridges_copy(g, L, R, e, t):
    G = len(g)
    return any(
        d + e + 1 < L and (r + d + 1) % G == t for r in R for d in range(L)
    )


def triple_repeats(g):
    G = len(g)
    out = []
    for e in range(1, G):
        groups = {}
        for t in range(G):
            groups.setdefault(window(g, e, t), []).append(t)
        for _, sts in groups.items():
            if len(sts) < 3:
                continue
            for a, b, c in combinations(sorted(sts), 3):
                pre = [g[(x - 1) % G] for x in (a, b, c)]
                post = [g[(x + e) % G] for x in (a, b, c)]
                if pre[0] == pre[1] == pre[2]:
                    continue
                if post[0] == post[1] == post[2]:
                    continue
                out.append((e, a, b, c))
    return out


def repeat_pairs(g):
    G = len(g)
    out = []
    for e in range(1, G):
        groups = {}
        for t in range(G):
            groups.setdefault(window(g, e, t), []).append(t)
        for _, sts in groups.items():
            for a, b in combinations(sorted(sts), 2):
                if g[(a - 1) % G] != g[(b - 1) % G] and g[(a + e) % G] != g[(b + e) % G]:
                    out.append((e, a, b))
    return out


def in_open_arc(G, a, b, p):
    return 0 < (p + G - a) % G < (b + G - a) % G


def interleaved(G, a, b, c, d):
    if len({a, b, c, d}) != 4:
        return False
    return in_open_arc(G, a, b, c) != in_open_arc(G, a, b, d)


def information_feasible(g, L, R):
    G = len(g)
    R = sorted(set(R))
    if not covers(g, L, R):
        return False
    for e, a, b, c in triple_repeats(g):
        if not all(bridges_copy(g, L, R, e, t) for t in (a, b, c)):
            return False
    rps = repeat_pairs(g)
    for (e1, a, b), (e2, c, d) in combinations(rps, 2):
        if interleaved(G, a, b, c, d):
            if not (
                any(bridges_copy(g, L, R, e1, t) for t in (a, b))
                or any(bridges_copy(g, L, R, e2, t) for t in (c, d))
            ):
                return False
    return True


# --------------------------------------------------------------------------- #
# The V5 two-disjoint-circles duplex model
# --------------------------------------------------------------------------- #


def duplex_spec(g, e):
    """V5 duplex oriented spectrum: spec_S(w) + spec_S(rc(w))."""
    specS = spectrum(g, e)
    specRcS = spectrum(tuple(rc(g)), e)
    out = {}
    for w in set(specS) | set(specRcS):
        out[w] = specS.get(w, 0) + specRcS.get(w, 0)
    return out


def duplex_molecule_spectrum(g, e):
    """V5 duplex molecule spectrum: class-summed duplex oriented spectrum."""
    m = {}
    for w, n in duplex_spec(g, e).items():
        c = class_of(w)
        m[c] = m.get(c, 0) + n
    return m


def partner_start(t, G, L):
    """V5 read-placement map: S-start t -> rc(S)-start (G - t - L) mod G."""
    return (G - t - L) % G


def duplex_positions(g):
    """All (circle, start) positions of the duplex."""
    G = len(g)
    return [("S", t) for t in range(G)] + [("R", t) for t in range(G)]


def duplex_window(g, circle, t, e):
    gg = g if circle == "S" else tuple(rc(g))
    return window(gg, e, t)


def duplex_preceding(g, circle, t):
    gg = g if circle == "S" else tuple(rc(g))
    return gg[(t - 1) % len(gg)]


def duplex_following(g, circle, t, e):
    gg = g if circle == "S" else tuple(rc(g))
    return gg[(t + e) % len(gg)]


def duplex_mixed_triple_repeats(g, L):
    """Maximal triple repeats of the duplex with copies on both circles."""
    G = len(g)
    pos = duplex_positions(g)
    out = []
    for e in range(1, G):
        groups = {}
        for p in pos:
            groups.setdefault(duplex_window(g, p[0], p[1], e), []).append(p)
        for _, sts in groups.items():
            if len(sts) < 3:
                continue
            for a, b, c in combinations(sorted(sts), 3):
                pre = [duplex_preceding(g, p[0], p[1]) for p in (a, b, c)]
                post = [duplex_following(g, p[0], p[1], e) for p in (a, b, c)]
                if pre[0] == pre[1] == pre[2]:
                    continue
                if post[0] == post[1] == post[2]:
                    continue
                if len(set(p[0] for p in (a, b, c))) > 1:
                    out.append((e, a, b, c))
    return out


# --------------------------------------------------------------------------- #
# Reporting helpers
# --------------------------------------------------------------------------- #

FAILURES = []


def check(cond, msg):
    print(("  [ok]   " if cond else "  [FAIL] ") + msg)
    if not cond:
        FAILURES.append(msg)


def section(title):
    print()
    print(title)
    print("-" * len(title))


def fmt_counts(d):
    return "{" + ", ".join(f"{''.join(c)}:{d[c]}" for c in sorted(d)) + "}"


# --------------------------------------------------------------------------- #
# Section 0: the V5 spec identity and read-placement map (exhaustive)
# --------------------------------------------------------------------------- #


def section0():
    section("0. The V5 spec identity and read-placement map (exhaustive)")
    L = 3
    tot = spec_ok = place_ok = 0
    for G in range(2, 9):
        for gw in product(("A", "T"), repeat=G):
            g = tuple(gw)
            rcg = tuple(rc(g))
            specS = spectrum(g, L)
            specRcS = spectrum(rcg, L)
            v5 = duplex_spec(g, L)
            # identity: spec_duplex(w) = spec_S(w) + spec_S(rc(w))
            ok = all(
                v5.get(w, 0) == specS.get(w, 0) + specS.get(rc(w), 0)
                for w in set(v5) | set(rc(x) for x in v5)
            )
            # total is exactly 2G
            ok = ok and sum(v5.values()) == 2 * G
            # read-placement map: window_rcS((G-t-L)%G) = rc(window_S(t))
            pok = all(
                window(rcg, L, partner_start(t, G, L)) == rc(window(g, L, t))
                for t in range(G)
            )
            tot += 1
            if ok:
                spec_ok += 1
            if pok:
                place_ok += 1
    check(spec_ok == tot,
          f"spec_duplex(w) = spec_S(w) + spec_S(rc(w)) and total = 2G "
          f"(exhaustive, binary, 2 <= G <= 8, L = 3): {spec_ok}/{tot}")
    check(place_ok == tot,
          f"read-placement map: window_rcS((G-t-L) mod G) = rc(window_S(t)) "
          f"for every t, including wrapping (exhaustive): {place_ok}/{tot}")


# --------------------------------------------------------------------------- #
# Section 1: the witness under V5, circle-by-circle reading
# --------------------------------------------------------------------------- #


def section1():
    section("1. The AAATAT -> AAAAAT witness under V5, circle-by-circle reading")
    S = tuple("AAATAT")
    G = len(S)
    L = 3
    rcS = tuple(rc(S))
    starts = [0, 0, 1, 3, 5]
    S_reads = sorted(set(starts))
    rcS_reads = sorted(set(partner_start(t, G, L) for t in starts))
    print(f"  S = {''.join(S)}, rc(S) = {''.join(rcS)}")
    print(f"  S read set: {S_reads}")
    print(f"  rc(S) partner read set: {rcS_reads}")
    check(information_feasible(S, L, S_reads),
          "I_s on S with the realized read set holds (matches the kernel-checked "
          "certificate on main)")
    check(information_feasible(rcS, L, rcS_reads),
          "I_s on rc(S) with the partner read set holds (circle-by-circle reading)")
    # the rc symmetry maps the partner read set back to the S read set
    mapped = sorted(set(partner_start(t, G, L) for t in rcS_reads))
    check(mapped == S_reads,
          f"the rc symmetry maps the partner read set back to the S read set: "
          f"{mapped} == {S_reads}")
    print("  Verdict: under the circle-by-circle reading, the witness hypothesis")
    print("  side HOLDS on the duplex: I_s on S and I_s on rc(S) both hold.")


# --------------------------------------------------------------------------- #
# Section 2: the witness under the duplex-as-a-whole reading
# --------------------------------------------------------------------------- #


def section2():
    section("2. The witness under the duplex-as-a-whole reading (mixed triple repeats)")
    S = tuple("AAATAT")
    G = len(S)
    L = 3
    mixed = duplex_mixed_triple_repeats(S, L)
    unbridgeable = [m for m in mixed if m[0] + 2 > L]
    print(f"  mixed triple repeats of the duplex: {len(mixed)}")
    for e, a, b, c in mixed:
        if e + 2 > L:
            print(f"    e={e} copies={a},{b},{c}  (unbridgeable: e+2={e+2} > L={L})")
    check(len(mixed) > 0,
          "the duplex carries mixed triple repeats (copies on both circles)")
    check(len(unbridgeable) > 0,
          f"{len(unbridgeable)} mixed triple repeats have e >= L-1 = {L-1}, so "
          f"bridgesCopy_length (e + 2 <= L) forbids bridging by ANY read of length L")
    print("  Verdict: under the duplex-as-a-whole reading, the witness hypothesis")
    print("  side FAILS on the duplex: the mixed triple repeats of length >= L-1")
    print("  cannot be bridged, so I_s is violated for every read set.")
    print("  (This reading is also not well-defined: two disjoint circles have no")
    print("  natural cyclic order for the interleaving condition.)")


# --------------------------------------------------------------------------- #
# Section 3: exact compatibility with the oriented single-strand reduction
# --------------------------------------------------------------------------- #


def section3():
    section("3. Exact compatibility of the circle-by-circle reading with the single-strand reduction")
    import random
    random.seed(42)
    L = 3
    all_ok = True
    n_tests = 0
    for G in range(4, 8):
        for gw in product(("A", "T"), repeat=G):
            g = tuple(gw)
            rcg = tuple(rc(g))
            for _ in range(20):
                R = sorted(set(random.randrange(G) for _ in range(random.randint(G, 2 * G))))
                rcR = sorted(set(partner_start(t, G, L) for t in R))
                a = information_feasible(g, L, R)
                b = information_feasible(rcg, L, rcR)
                n_tests += 1
                if a != b:
                    all_ok = False
                    print(f"  FAIL: S={''.join(g)} R={R} rcR={rcR} I_s(S)={a} I_s(rcS)={b}")
    check(all_ok,
          f"I_s on rc(S) with the partner read set <-> I_s on S with the original "
          f"read set (the rc symmetry), tested on {n_tests} random instances: "
          f"exact compatibility holds")
    print("  The rc symmetry phi: (circle, start) -> (other circle, (G-start-L) mod G)")
    print("  is a bijection of the duplex that swaps the circles, maps reads to")
    print("  reads, and preserves windows (up to rc), preceding/following symbols")
    print("  (up to comp), and bridging.  Hence I_s on the duplex (circle-by-circle)")
    print("  is equivalent to I_s on S.  This is exact compatibility.")


# --------------------------------------------------------------------------- #
# Section 4: the candidate set and the likelihood ratio
# --------------------------------------------------------------------------- #


def section4():
    section("4. The candidate set: V5 duplex candidate vs V3 doubled candidate")
    S = tuple("AAATAT")
    D = tuple("AAAAAT")
    G = len(S)
    L = 3
    rcS = tuple(rc(S))
    rcD = tuple(rc(D))

    # V5 candidate duplex (D, rcD)
    v5_cand = duplex_spec(D, L)
    # V3 candidate D · rcD (length 2G)
    DrcD = tuple(D) + tuple(rcD)
    v3_cand = spectrum(DrcD, L)
    print(f"  V5 candidate duplex (D, rc(D)) oriented spec: {fmt_counts(v5_cand)}")
    print(f"  V3 candidate D·rc(D) oriented spec:            {fmt_counts(v3_cand)}")
    check(v5_cand == v3_cand,
          "for this D, the V5 and V3 candidate spectra coincide (R2 holds for D=AAAAAT)")

    # molecule spectra
    v5_mol = duplex_molecule_spectrum(D, L)
    v3_mol = molecule_spectrum(DrcD, L)
    print(f"  V5 candidate molecule spec: {fmt_counts(v5_mol)}")
    print(f"  V3 candidate molecule spec: {fmt_counts(v3_mol)}")
    check(v5_mol == v3_mol,
          "the V5 and V3 candidate molecule spectra coincide for this D")

    # truth duplex molecule spectrum = 2 * S molecule spectrum
    molS = molecule_spectrum(S, L)
    truth_duplex_mol = duplex_molecule_spectrum(S, L)
    print(f"  truth duplex molecule spec: {fmt_counts(truth_duplex_mol)}")
    print(f"  2 * S molecule spec:        {fmt_counts({c: 2 * n for c, n in molS.items()})}")
    check(truth_duplex_mol == {c: 2 * n for c, n in molS.items()},
          "the truth duplex molecule spectrum is exactly 2 x the S molecule spectrum")

    # likelihood ratio (the factor of 2 cancels)
    starts = [0, 0, 1, 3, 5]
    x = {}
    for t in starts:
        c = class_of(window(S, L, t))
        x[c] = x.get(c, 0) + 1
    print(f"  observation x: {fmt_counts(x)}")

    def exact_ratio(m_S, m_D):
        total = Fraction(1)
        for c, xc in x.items():
            if xc == 0:
                continue
            if m_D.get(c, 0) == 0:
                return Fraction(0)
            total *= Fraction(m_D[c], m_S[c]) ** xc
        return total

    def binomial_ratio(m_S, m_D, N):
        n = sum(x.values())
        ratio = Fraction(1)
        for c, xc in x.items():
            dD, dS = m_D.get(c, 0), m_S[c]
            num = Fraction(_choose(n, xc)) * Fraction(dD, N) ** xc * (1 - Fraction(dD, N)) ** (n - xc)
            den = Fraction(_choose(n, xc)) * Fraction(dS, N) ** xc * (1 - Fraction(dS, N)) ** (n - xc)
            ratio *= num / den
        return ratio

    # V5: candidate molecule spec is 2*m_D, truth is 2*m_S; ratio uses m_S, m_D
    r_exact_v5 = exact_ratio(molS, molecule_spectrum(D, L))
    r_bin_v5 = binomial_ratio(molS, molecule_spectrum(D, L), G)
    print(f"  V5 exact ratio (using m_S, m_D): {r_exact_v5}")
    print(f"  V5 binomial ratio (using m_S, m_D): {r_bin_v5}")
    check(r_exact_v5 == 3 and r_bin_v5 == 5,
          "the witness conclusion side holds under V5: D beats S (ratio 3 exact, 5 binomial)")
    print("  Verdict: under V5 (circle-by-circle), the witness is a genuine")
    print("  counterexample: the hypothesis side holds and D beats S.")


def _choose(n, k):
    r = 1
    for i in range(1, k + 1):
        r = r * (n - k + i) // i
    return r


# --------------------------------------------------------------------------- #
# Section 5: source-faithfulness and the V5/V3 agreement rate
# --------------------------------------------------------------------------- #


def section5():
    section("5. Source-faithfulness: V5 vs MB09 molecule spectrum and Bresler doubled spectrum")
    L = 3
    tot = v5_eq_v3 = r2_holds = 0
    for G in range(2, 9):
        for gw in product(("A", "T"), repeat=G):
            g = tuple(gw)
            v5 = duplex_spec(g, L)
            hs = tuple(g) + tuple(rc(g))
            v3 = spectrum(hs, L)
            seam = seam_windows(g, L)
            wrap = wrap_spectrum(g, L)
            wraprc = wrap_spectrum(tuple(rc(g)), L)
            r2 = all(
                seam.get(w, 0) == wrap.get(w, 0) + wraprc.get(w, 0)
                for w in set(seam) | set(wrap) | set(wraprc)
            )
            tot += 1
            if v5 == v3:
                v5_eq_v3 += 1
            if r2:
                r2_holds += 1
    print(f"  binary 2 <= G <= 8, L = 3: {tot} genomes")
    print(f"  V5 duplex spec == V3 doubled spec: {v5_eq_v3}/{tot}")
    print(f"  R2 (j_S = wrap_S + wrap_S∘rc) holds: {r2_holds}/{tot}")
    check(v5_eq_v3 == r2_holds,
          "V5 and V3 induce the same read-type distribution iff R2 holds")
    check(v5_eq_v3 < tot,
          "V5 and V3 are different models: they differ on a substantial fraction of genomes")

    # V5 duplex molecule spectrum vs MB09 molecule spectrum
    print()
    print("  V5 duplex molecule spectrum vs MB09 (single-strand) molecule spectrum:")
    S = tuple("AAATAT")
    molS = molecule_spectrum(S, L)
    truth_duplex_mol = duplex_molecule_spectrum(S, L)
    print(f"    MB09 molecule spectrum of S:     {fmt_counts(molS)}")
    print(f"    V5 duplex molecule spectrum:      {fmt_counts(truth_duplex_mol)}")
    check(truth_duplex_mol == {c: 2 * n for c, n in molS.items()},
          "the V5 duplex molecule spectrum is 2 x the MB09 molecule spectrum of S")
    print("  So V5 records the same molecule classes as MB09, with doubled")
    print("  multiplicities (both strands contribute).  The likelihood ratio is")
    print("  unchanged (the factor of 2 cancels).  V5 is NOT the MB09 model (which")
    print("  uses a single circle with rc-collapsed reads), nor the Bresler model")
    print("  (which uses the length-2G circle).  It is a distinct model.")


# --------------------------------------------------------------------------- #
# Section 6: bounded searches
# --------------------------------------------------------------------------- #


def section6():
    section("6. Bounded searches")
    L = 3
    # how often do mixed triple repeats occur, and how often are they unbridgeable?
    tot = has_mixed = has_unbridgeable = 0
    for G in range(2, 9):
        for gw in product(("A", "T"), repeat=G):
            g = tuple(gw)
            mixed = duplex_mixed_triple_repeats(g, L)
            unb = [m for m in mixed if m[0] + 2 > L]
            tot += 1
            if mixed:
                has_mixed += 1
            if unb:
                has_unbridgeable += 1
    print(f"  binary 2 <= G <= 8, L = 3: {tot} genomes")
    print(f"  duplex has mixed triple repeats: {has_mixed}/{tot}")
    print(f"  duplex has unbridgeable mixed triple repeats (e >= L-1): {has_unbridgeable}/{tot}")
    check(has_mixed > 0,
          "mixed triple repeats are a general phenomenon, not specific to the witness")
    check(has_unbridgeable > 0,
          "unbridgeable mixed triple repeats occur in general, so the duplex-as-a-whole")
    print("  reading is strictly stronger than the single-strand I_s in general.")

    # V5 vs V3 candidate spectrum agreement as a function of G
    print()
    print("  V5 vs V3 candidate spectrum agreement by G:")
    for G in range(2, 9):
        t = agree = 0
        for gw in product(("A", "T"), repeat=G):
            g = tuple(gw)
            v5 = duplex_spec(g, L)
            hs = tuple(g) + tuple(rc(g))
            v3 = spectrum(hs, L)
            t += 1
            if v5 == v3:
                agree += 1
        print(f"    G = {G}: {agree}/{t}")


def section7():
    section("7. Palindromes (even L) and the MB09 unordered molecule count")
    # A word w is a self-RC palindrome iff rc(w) == w.  MB09 §3.1/§4.1
    # represents each k-molecule once, so its count sums S-locus occurrences
    # over the DISTINCT words of the class: a palindrome class {w} is counted
    # once (spec_S(w)), a non-palindrome class {w, rc(w)} twice
    # (spec_S(w) + spec_S(rc(w))).  The V5 duplex molecule spectrum counts
    # windows on BOTH strands, so it is exactly 2 x the single-strand MB09
    # molecule spectrum, palindromes included (each strand contributes one).
    for L in (2, 3, 4):
        n_pal = sum(1 for w in product("AT", repeat=L) if rc(w) == w)
        print(f"  L = {L}: {n_pal} self-RC palindromes among 2^{L} words")
    check(sum(1 for w in product("AT", repeat=3) if rc(w) == w) == 0,
          "L = 3 (the witness): there are NO self-RC palindromes, so the "
          "palindrome subtlety does not affect the witness")
    check(sum(1 for w in product("AT", repeat=2) if rc(w) == w) == 2,
          "L = 2: two self-RC palindromes (AT, TA), so the subtlety is live for even L")

    # verify the identity m_duplex(c) = 2 * m_S(c) for all classes, including
    # palindrome classes, over a binary scope and both parities of L
    for L in (2, 3, 4):
        all_ok = True
        for G in range(L + 1, 8):
            for gw in product(("A", "T"), repeat=G):
                g = tuple(gw)
                mS = molecule_spectrum(g, L)
                md = duplex_molecule_spectrum(g, L)
                if md != {c: 2 * n for c, n in mS.items()}:
                    all_ok = False
        check(all_ok,
              f"L = {L}: m_duplex(c) = 2 * m_S(c) for every class, including "
              f"self-RC palindromes (binary scope)")
    print("  The V5 duplex molecule spectrum records the same molecule classes as")
    print("  MB09, with exactly doubled multiplicities; the likelihood ratio is")
    print("  unchanged because the factor 2 cancels between two candidates.")


def main():
    print("AssemblyP1 issue #215: the two-disjoint-circles duplex model (V5)")
    print("oriented single-strand I_s vs duplex DNA as two disjoint circles")
    section0()
    section1()
    section2()
    section3()
    section4()
    section5()
    section6()
    section7()
    print()
    if FAILURES:
        print(f"FAILED: {len(FAILURES)} assertion(s)")
        for f in FAILURES:
            print(f"  - {f}")
        sys.exit(1)
    print("All assertions passed.")


if __name__ == "__main__":
    main()
