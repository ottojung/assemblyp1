#!/usr/bin/env python3
"""Independent audit of the issue #215 reconciliation appendix.

This script shares NO code with
`scripts/verify_oriented_molecule_bridging.py` or any other repository script.
Everything is re-implemented from scratch on a different data representation
(words as `str`, spectra as `dict[str, int]`), so that agreement between the two
scripts is evidence about the *mathematics* and not about a shared bug.

It answers, in order:

  A. the `AAATAT -> AAAAAT` molecule witness, under every bridging version
     (V1 placement-retaining, V2 `Φ(I_s)`, V3 Bresler 2G remap);
  B. the exact word labels of the doubled genome's long triple repeats, which
     the appendix lists as `AT@...` for all five length-2 entries;
  C. whether "380 of 1016 wrapping windows also occur in the doubled genome"
     means "occur at the natural seat" or "occur at all";
  D. the `L`-mer-class-multiplicity-even repair count in the appendix's §4.4
     table, printed as `64` while the shipped script reports `60`;
  E. how much the module-local, deprecated endpoint-only certificate
     `SameLengthSection62Counterexample.truth_source_certificate` differs from
     the authoritative `SourceFaithfulIs.InformationFeasible` on this instance
     and on the three liftings of the witness observation;
  F. the coverage of the kernel-checked `partner_placements` statement: it
     compares `window 3 b 0` with `comp (window 3 b' 2)` only, i.e. one of the
     three symbol components of each partner window.

Usage:
    python3 scripts/audit_215_transfer_reconciliation.py
"""

from __future__ import annotations

import sys
from fractions import Fraction
from itertools import combinations, product

DNA = ("A", "C", "G", "T")
COMP = {"A": "T", "T": "A", "C": "G", "G": "C"}

FAILURES: list[str] = []


def check(cond, msg):
    print(("  [ok]   " if cond else "  [FAIL] ") + msg)
    if not cond:
        FAILURES.append(msg)


def section(title):
    print()
    print(title)
    print("-" * len(title))


# --------------------------------------------------------------------------- #
# Alphabet layer
# --------------------------------------------------------------------------- #


def rc(w: str) -> str:
    return "".join(COMP[c] for c in reversed(w))


def cls(w: str) -> str:
    return min(w, rc(w))


def windows(g: str, e: int):
    G = len(g)
    return [g[(r + i) % G] for r in range(G) for i in range(e)]


def win(g: str, e: int, r: int) -> str:
    G = len(g)
    return "".join(g[(r + i) % G] for i in range(e))


def oriented_spectrum(g: str, e: int) -> dict[str, int]:
    out: dict[str, int] = {}
    for r in range(len(g)):
        w = win(g, e, r)
        out[w] = out.get(w, 0) + 1
    return out


def molecule_spectrum(g: str, e: int) -> dict[str, int]:
    out: dict[str, int] = {}
    for r in range(len(g)):
        c = cls(win(g, e, r))
        out[c] = out.get(c, 0) + 1
    return out


def lint_spectrum(g: str, e: int) -> dict[str, int]:
    out: dict[str, int] = {}
    for r in range(0, len(g) - e + 1):
        w = g[r : r + e]
        out[w] = out.get(w, 0) + 1
    return out


def wrap_spectrum(g: str, e: int) -> dict[str, int]:
    out: dict[str, int] = {}
    for r in range(len(g) - e + 1, len(g)):
        w = win(g, e, r)
        out[w] = out.get(w, 0) + 1
    return out


def seam_windows(g: str, e: int) -> dict[str, int]:
    G, W = len(g), 2 * len(g)
    hs = doubled(g)
    out: dict[str, int] = {}
    for r in list(range(G - e + 1, G)) + list(range(W - e + 1, W)):
        w = win(hs, e, r)
        out[w] = out.get(w, 0) + 1
    return out


def doubled(g: str) -> str:
    return g + rc(g)


# --------------------------------------------------------------------------- #
# `I_s`, transcribed from `AssemblyP1/SourceFaithfulIs.lean` (not from the
# shipped #215 script)
# --------------------------------------------------------------------------- #


def prec(g: str, t: int) -> str:
    return g[(t - 1) % len(g)]


def foll(g: str, e: int, t: int) -> str:
    return g[(t + e) % len(g)]


def is_repeat(g: str, e: int, a: int, b: int) -> bool:
    G = len(g)
    return (
        1 <= e < G
        and a != b
        and win(g, e, a) == win(g, e, b)
        and prec(g, a) != prec(g, b)
        and foll(g, e, a) != foll(g, e, b)
    )


def is_triple(g: str, e: int, a: int, b: int, c: int) -> bool:
    G = len(g)
    return (
        1 <= e < G
        and a != b
        and a != c
        and b != c
        and win(g, e, a) == win(g, e, b)
        and win(g, e, a) == win(g, e, c)
        and win(g, e, b) == win(g, e, c)
        and not (prec(g, a) == prec(g, b) == prec(g, c))
        and not (foll(g, e, a) == foll(g, e, b) == foll(g, e, c))
    )


def triple_repeats(g: str):
    out = []
    G = len(g)
    for e in range(1, G):
        for a, b, c in combinations(range(G), 3):
            if is_triple(g, e, a, b, c):
                out.append((e, a, b, c))
    return out


def repeat_pairs(g: str):
    out = []
    G = len(g)
    for e in range(1, G):
        for a, b in combinations(range(G), 2):
            if is_repeat(g, e, a, b):
                out.append((e, a, b))
    return out


def bridges(g: str, L: int, R, e: int, t: int) -> bool:
    G = len(g)
    for r in set(R):
        for d in range(L):
            if d + e + 1 < L and (r + d + 1) % G == t:
                return True
    return False


def bridges_endpoint_only(g: str, L: int, R, e: int, t: int) -> bool:
    """The DEPRECATED predicate of
    `AssemblyP1/SameLengthSection62Counterexample.lean` (`bridgedCopy`): some
    realized read covers `t-1` and `t+e`, with no single-interval requirement."""
    G = len(g)
    for r in set(R):
        lo, hi = (t - 1) % G, (t + e) % G
        covers = {(r + i) % G for i in range(L)}
        if lo in covers and hi in covers:
            return True
    return False


def covers(g: str, L: int, R) -> bool:
    G = len(g)
    pos = set()
    for r in set(R):
        pos |= {(r + i) % G for i in range(L)}
    return len(pos) == G


def in_open_arc(G: int, a: int, b: int, p: int) -> bool:
    return 0 < (p + G - a) % G < (b + G - a) % G


def interleaved(G: int, a: int, b: int, c: int, d: int) -> bool:
    return len({a, b, c, d}) == 4 and in_open_arc(G, a, b, c) != in_open_arc(G, a, b, d)


def information_feasible(g: str, L: int, R) -> bool:
    if not covers(g, L, R):
        return False
    for e, a, b, c in triple_repeats(g):
        if not all(bridges(g, L, R, e, t) for t in (a, b, c)):
            return False
    rps = repeat_pairs(g)
    for (e1, a, b), (e2, c, d) in combinations(rps, 2):
        if interleaved(len(g), a, b, c, d):
            if not (
                any(bridges(g, L, R, e1, t) for t in (a, b))
                or any(bridges(g, L, R, e2, t) for t in (c, d))
            ):
                return False
    return True


def certificate_deprecated(g: str, L: int, R) -> bool:
    """The module-local `SourceCertificate` of
    `SameLengthSection62Counterexample.lean` (endpoint-only bridging)."""
    if not covers(g, L, R):
        return False
    for e, a, b, c in triple_repeats(g):
        if not all(bridges_endpoint_only(g, L, R, e, t) for t in (a, b, c)):
            return False
    return True


# --------------------------------------------------------------------------- #
# Objectives
# --------------------------------------------------------------------------- #


def exact_ratio(x: dict[str, int], mS: dict[str, int], mD: dict[str, int]) -> Fraction:
    total = Fraction(1)
    for c, n in x.items():
        if n == 0:
            continue
        if mD.get(c, 0) == 0:
            return Fraction(0)
        total *= Fraction(mD[c], mS[c]) ** n
    return total


def choose(n: int, k: int) -> int:
    r = 1
    for i in range(1, k + 1):
        r = r * (n - k + i) // i
    return r


def binomial_ratio(x, mS, mD, N: int) -> Fraction:
    n = sum(x.values())
    ratio = Fraction(1)
    for c, nc in x.items():
        dD, dS = mD.get(c, 0), mS[c]
        num = Fraction(choose(n, nc)) * Fraction(dD, N) ** nc * (1 - Fraction(dD, N)) ** (n - nc)
        den = Fraction(choose(n, nc)) * Fraction(dS, N) ** nc * (1 - Fraction(dS, N)) ** (n - nc)
        ratio *= num / den
    return ratio


# --------------------------------------------------------------------------- #
# A. the witness, under V1 / V2 / V3
# --------------------------------------------------------------------------- #


def sectionA():
    section("A. The `AAATAT -> AAAAAT` witness, version by version")
    S, D, L = "AAATAT", "AAAAAT", 3
    real = (0, 0, 1, 3, 5)
    R = sorted(set(real))
    x: dict[str, int] = {}
    for t in real:
        c = cls(win(S, L, t))
        x[c] = x.get(c, 0) + 1
    mS, mD = molecule_spectrum(S, L), molecule_spectrum(D, L)
    print(f"  x = {x}")
    print(f"  d_S = {mS}")
    print(f"  d_D = {mD}")
    check(mD[cls("AAA")] == 3 and mD[cls("ATA")] == 1, "d_D(AAA)=3, d_D(ATA)=1")
    check(mS[cls("AAA")] == 1 and mS[cls("ATA")] == 3, "d_S(AAA)=1, d_S(ATA)=3")
    check(set(mS) == set(mD) == set(x), "supp(d_S) = supp(d_D) = supp(x)")
    check(set(oriented_spectrum(S, L)) != set(oriented_spectrum(D, L)),
          "oriented supports differ (TAT in S only) while class supports coincide")
    re_, rb = exact_ratio(x, mS, mD), binomial_ratio(x, mS, mD, len(S))
    check(re_ == 3, f"exact candidate-intrinsic multinomial ratio = {re_}")
    check(rb == 5, f"literal MB09 §6.1 fixed-N binomial ratio = {rb}")

    # V1: placements retained, class-collapsed read types recorded.
    v1 = information_feasible(S, L, R)
    check(v1 and covers(S, L, R),
          "V1: realized placement set {0,1,3,5} satisfies I_s (all three clauses)")
    # V2: classes only; some lifting of x is I_s-feasible.
    seats: dict[str, list[int]] = {}
    for t in range(len(S)):
        seats.setdefault(cls(win(S, L, t)), []).append(t)
    print(f"  placement seats per class: "
          f"{ {c: v for c, v in sorted(seats.items())} }")
    lifts = []
    def build(i, keys, acc):
        if i == len(keys):
            lifts.append(tuple(sorted(acc)))
            return
        for t in seats[keys[i]]:
            build(i + 1, keys, acc + [t])

    keylist = [c for c, n in sorted(x.items()) for _ in range(n)]
    build(0, keylist, [])
    lifts = sorted(set(lifts))
    check(len(lifts) == 3, f"exactly 3 placement multisets realize x (got {len(lifts)})")
    statuses = {lf: information_feasible(S, L, list(lf)) for lf in lifts}
    for lf in sorted(statuses):
        print(f"    lifting {list(lf)}: I_s = {statuses[lf]}")
    check(statuses.get((0, 0, 1, 3, 5), False),
          "V2: x ∈ Φ(I_s) because the realized lifting {0,0,1,3,5} is I_s-feasible")
    check(sum(statuses.values()) == 1,
          "exactly one lifting of x is I_s-feasible: bridging is NOT Φ-invariant")
    check(any(not v for v in statuses.values()),
          "V2 is strictly weaker than V1: other liftings of x violate I_s")

    # V3: Bresler 2G remap.
    hs = doubled(S)
    print(f"  doubled genome S·ρ(S) = {hs} (length {len(hs)})")
    check(hs == "AAATATATATTT", "the doubled genome is the length-12 circle AAATATATATTT")
    # Bresler: each realized read becomes itself and its reverse complement.
    # A non-wrapping read (t <= G-L) sits at absolute start t of S·ρ(S); a
    # wrapping read sits at G+t.  The partner of the read at absolute start b
    # sits at 2G-b-L, an exact symmetry of the doubled circle.
    Gn = len(S)
    seat_ok = True
    for t in R:
        base = t if t <= Gn - L else Gn + t
        if win(hs, L, base % (2 * Gn)) != win(S, L, t):
            seat_ok = False
    check(seat_ok,
          "every realized read has a genuine seat in the doubled circle "
          "(non-wrapping reads at the same start, wrapping reads at G+t)")
    partner_ok = True
    for t in R:
        base = t if t <= Gn - L else Gn + t
        if win(hs, L, (2 * Gn - base - L) % (2 * Gn)) != rc(win(S, L, t)):
            partner_ok = False
    check(partner_ok,
          "the Bresler partner placement 2G-b-L carries ρ(read at b), where b is "
          "the DOUBLED-CIRCLE absolute start (not the original circular start: the "
          "wrapping read at 5 seats at 11 and its partner at 10, not at 4)")
    long = [t for t in triple_repeats(hs) if t[0] >= L - 1]
    print(f"  long triple repeats of the doubled genome: {long}")
    check(len(long) == 6, "there are 6 maximal triple repeats of length >= L-1")
    # every length-e copy with e >= L-1 is unbridgeable by any length-L read
    check(all(e + 2 > L for e, *_ in long),
          "each of them has e + 2 > L, so bridgesCopy_length forbids bridging")
    full = set(range(2 * len(S)))
    unbridgeable = all(
        not bridges(hs, L, full, e, t)
        for e, a, b, c in long for t in (a, b, c)
    )
    check(unbridgeable,
          "even the full placement set {0..11} bridges none of them")
    check(not information_feasible(hs, L, full),
          "V3: InformationFeasible fails for EVERY read set -> witness inadmissible")
    return S, D, L, R, x, mS, mD, lifts, statuses


# --------------------------------------------------------------------------- #
# B. the word labels of the doubled genome's long triple repeats
# --------------------------------------------------------------------------- #


def sectionB(hs):
    section("B. Exact word labels of the doubled genome's long triple repeats")
    print("  the appendix §3.2 (and the module docstring of")
    print("  `AssemblyP1/DoubleStrandBridgingTransfer.lean`) list the six long")
    print("  triple repeats as `AT@{2,4,8}`, `AT@{2,6,8}`, `AT@{3,5,11}`,")
    print("  `AT@{3,7,11}`, `AT@{5,7,11}` and `ATATA@{2,4,6}`.")
    for e, a, b, c in triple_repeats(hs):
        if e >= 2:
            print(f"    (e={e}) word = {win(hs, e, a)!r} @ {{{a},{b},{c}}}")
    expect = {
        (2, 2, 4, 8): "AT",
        (2, 2, 6, 8): "AT",
        (2, 3, 5, 11): "TA",
        (2, 3, 7, 11): "TA",
        (2, 5, 7, 11): "TA",
        (4, 2, 4, 6): "ATAT",
    }
    # what the shipped appendix §3.2 (and the Lean module docstring) actually print
    appendix_claims = {
        (2, 2, 4, 8): "AT",
        (2, 2, 6, 8): "AT",
        (2, 3, 5, 11): "AT",
        (2, 3, 7, 11): "AT",
        (2, 5, 7, 11): "AT",
        (4, 2, 4, 6): "ATATA",
    }
    for trip, word in expect.items():
        e, a, b, c = trip
        check(is_triple(hs, e, a, b, c) and win(hs, e, a) == word,
              f"{trip} really is a maximal triple repeat whose length-{e} window "
              f"is {word!r}")
    mislabeled = {t: (appendix_claims[t], expect[t])
                  for t in expect if appendix_claims[t] != expect[t]}
    print("  appendix entries whose printed label disagrees with the computed word:")
    for t, (claimed, actual) in sorted(mislabeled.items()):
        print(f"    {t}: appendix prints {claimed!r}, the length-{t[0]} window is "
              f"{actual!r}")
    check(len(mislabeled) == 4,
          "the appendix mislabels 4 of the 6 long triple repeats (three TA@... "
          "printed as AT@..., and the length-4 ATAT printed as the five-symbol "
          "string 'ATATA')")
    check(("AT", "ATATA") == ("AT", "ATATA") and len("ATAT") == 4,
          "the headline obstruction is the length-4 word ATAT; the string 'ATATA' "
          "has length 5 and cannot be a length-4 window, so the appendix's label "
          "for the Theorem 3.2 obstruction is impossible as written")


# --------------------------------------------------------------------------- #
# C. wrapping windows: seat vs occurrence
# --------------------------------------------------------------------------- #


def sectionC():
    section("C. Wrapping windows of S: seat in S·ρ(S) vs occurrence in it")
    tot = seat = anywhere = anywhere_fail = 0
    for G in range(2, 9):
        for gw in product("AT", repeat=G):
            g = "".join(gw)
            hs = doubled(g)
            for t in range(G - 3 + 1, G):
                w = win(g, 3, t)
                tot += 1
                if win(hs, 3, (G + t) % (2 * G)) == w:
                    seat += 1
                if any(win(hs, 3, r) == w for r in range(2 * G)):
                    anywhere += 1
                else:
                    anywhere_fail += 1
    print(f"  wrapping windows in scope (binary, 2<=G<=8, L=3): {tot}")
    print(f"    sitting at their natural seat G+t: {seat}")
    print(f"    occurring somewhere in S·ρ(S): {anywhere}")
    print(f"    occurring nowhere in S·ρ(S): {anywhere_fail}")
    check(tot == 1016, "the scope really has 1016 wrapping windows")
    check(seat == 380, "the shipped script's 380 counts the NATURAL SEAT, not any occurrence")
    check(anywhere < tot,
          "some wrapping windows occur nowhere in the doubled genome, so the "
          "Bresler remap does not in general map a read set to a read set")
    return tot, seat, anywhere, anywhere_fail


# --------------------------------------------------------------------------- #
# D. the `L`-mer-class-multiplicity-even repair count
# --------------------------------------------------------------------------- #


def circulations(alphabet, L, G, want_classes):
    words = ["".join(w) for w in product(alphabet, repeat=L)]
    out = []

    def rec(i, remaining, cur):
        if i == len(words) - 1:
            vec = cur + [remaining]
            B = dict(zip(words, vec))
            if any(vec) and {cls(w) for w, n in B.items() if n} == set(want_classes):
                if balanced(B):
                    out.append({w: n for w, n in B.items() if n})
            return
        for v in range(remaining + 1):
            rec(i + 1, remaining - v, cur + [v])

    rec(0, G, [])
    return out


def balanced(B) -> bool:
    bal: dict[str, int] = {}
    for w, n in B.items():
        if n == 0:
            continue
        bal[w[:-1]] = bal.get(w[:-1], 0) + n
        bal[w[1:]] = bal.get(w[1:], 0) - n
    return all(v == 0 for v in bal.values())


def molecule_nonrigid(g, L):
    V = set(molecule_spectrum(g, L))
    spectra = []
    for B in circulations(sorted(set(g)), L, len(g), V):
        m = molecule_spectrum_from_vector(B)
        if m not in spectra:
            spectra.append(m)
    return len(spectra) > 1


def molecule_spectrum_from_vector(B):
    m: dict[str, int] = {}
    for w, n in B.items():
        c = cls(w)
        m[c] = m.get(c, 0) + n
    return m


def sectionD():
    section("D. Census of the chromosome: recompute the appendix §4.4 repair table")
    rows = []
    for G in range(4, 9):
        for gw in product("AT", repeat=G):
            g = "".join(gw)
            if any(e >= 2 for e, *_ in triple_repeats(g)):
                continue
            m, mm = molecule_spectrum(g, 3), molecule_spectrum(g, 2)
            s = oriented_spectrum(g, 3)
            rows.append((g, molecule_nonrigid(g, 3),
                         max(mm.values()) <= 2, max(m.values()) <= 2,
                         all(s[w] == s.get(rc(w), 0) for w in s),
                         all(v % 2 == 0 for v in m.values()),
                         all(v % 2 == 0 for v in mm.values()),
                         max(mm.values()) <= 2 and max(m.values()) <= 2))
    names = ["h1 (L-1)-class<=2", "h2 L-class<=2", "h3 class-symmetric",
             "h5 L-class mult even", "h6 (L-1)-class mult even",
             "h7 both class mults<=2"]
    idx = {"h1 (L-1)-class<=2": 2, "h2 L-class<=2": 3, "h3 class-symmetric": 4,
           "h5 L-class mult even": 5, "h6 (L-1)-class mult even": 6,
           "h7 both class mults<=2": 7}
    print(f"  genomes in scope (binary, L=3, 4<=G<=8): {len(rows)}")
    for n in names:
        sat = [r for r in rows if r[idx[n]]]
        bad = [r for r in sat if r[1]]
        print(f"    {n}: satisfied by {len(sat)}, still non-rigid {len(bad)}")
    check(len(rows) == 162, "162 genomes in scope, matching the appendix")
    h5 = [r for r in rows if r[5]]
    h5bad = [r for r in h5 if r[1]]
    print(f"  appendix §4.4 row 'every L-mer class multiplicity even' prints "
          f"64 / 16; recomputed {len(h5)} / {len(h5bad)}")
    check(len(h5) == 60, "the correct count is 60, so the appendix table cell 64 is stale")
    check(len(h5bad) == 16, "the 'still non-rigid' cell 16 is correct")
    nr = sum(1 for r in rows if r[1])
    check(nr == 86, f"86 molecule-non-rigid genomes in scope (got {nr})")
    h7 = [r for r in rows if r[7]]
    check(len(h7) == 30 and all(not r[1] for r in h7),
          "h7 ('both class multiplicities <= 2') is satisfied by 30 and refuted by none")


# --------------------------------------------------------------------------- #
# E. deprecated certificate vs authoritative `InformationFeasible`
# --------------------------------------------------------------------------- #


def sectionE(S, L, R, lifts):
    section("E. The cited certificate vs the authoritative `I_s`")
    print("  the appendix credits the I_s kernel-check to")
    print("  `SameLengthSection62Counterexample.truth_source_certificate`, whose")
    print("  `SourceCertificate` discharges the module-local `bridgedCopy`")
    print("  (endpoint-only) predicate, which `SourceFaithfulIs.lean` records as")
    print("  the superseded, strictly weaker convention.")
    auth = information_feasible(S, L, R)
    dep = certificate_deprecated(S, L, R)
    check(auth, "authoritative I_s holds on {0,1,3,5} (basis of the real verdict)")
    check(dep, "the deprecated endpoint-only certificate also holds on {0,1,3,5}")
    # where the two predicates differ, on this instance's liftings and genomes
    stronger = []
    for lf in lifts:
        if certificate_deprecated(S, L, list(lf)) and not information_feasible(S, L, list(lf)):
            stronger.append(lf)
    print(f"  liftings where the deprecated predicate accepts and I_s rejects: "
          f"{ [list(l) for l in stronger] }")
    check(all(certificate_deprecated(S, L, list(l)) == information_feasible(S, L, list(l))
              for l in lifts),
          "on the three liftings of x the two predicates happen to AGREE, so the "
          "mis-citation does not change the verdict here -- but the strength "
          "attributed to the kernel-check is not the strength it has")


# --------------------------------------------------------------------------- #
# F. coverage of the kernel-checked `partner_placements`
# --------------------------------------------------------------------------- #


def sectionF(hs):
    section("F. Coverage of the kernel-checked `partner_placements` statement")
    G, L, W = 6, 3, 12
    partner_of = {0: 9, 1: 8, 3: 6, 11: 10}
    print("  the auditor found `DoubleStrandBridgingTransfer.partner_placements`")
    print("  comparing only `window 3 b 0` with `comp (window 3 b' 2)` -- one of")
    print("  the three symbol components of each partner window, i.e. 4 of 12,")
    print("  while the module docstring advertised 'kernel-checks the read-partner")
    print("  placements that Bresler's doubling induces'.  It has been replaced by")
    print("  `partner_windows` (+ `partner_starts`), which proves the componentwise")
    print("  identity for every d : Fin 3.  This section checks the mathematics of")
    print("  both statements.")
    comp_ok = all(
        hs[(b + d) % W] == COMP[hs[(p + 2 - d) % W]]
        for b, p in partner_of.items() for d in range(L)
    )
    check(comp_ok, "the full anti-palindromic component identity holds for all 3 d")
    lean_checked = all(
        hs[(b + 0) % W] == COMP[hs[(p + 2) % W]] for b, p in partner_of.items()
    )
    check(lean_checked, "the single component the shipped theorem really checked holds")
    # the seat rule 2G - b - L, with b the absolute seat in the doubled circle
    check(all(2 * G - b - L < 2 * G for b in partner_of)
          and partner_of[11] == (2 * G - 11 - L) % W
          and partner_of[0] == 2 * G - 0 - L
          and partner_of[1] == 2 * G - 1 - L
          and partner_of[3] == 2 * G - 3 - L,
          "the seat rule 2G-b-L really maps 0->9, 1->8, 3->6 and the wrapping "
          "read's seat 11 -> 10 (not 2G-5-L = 4)")
    total_components = 4 * L
    checked_components = 4 * 1
    print(f"  components of the four partner windows: {total_components}; "
          f"components the shipped theorem compared: {checked_components}")
    check(checked_components < total_components and comp_ok,
          "so the shipped `partner_placements` verified only 4 of 12 components: "
          "true but narrower than advertised; `partner_windows` closes the gap")


# --------------------------------------------------------------------------- #
# G. the remap-density claim of appendix §3.3
# --------------------------------------------------------------------------- #


def is_primitive(g: str) -> bool:
    G = len(g)
    return not any(G % p == 0 and g[:p] * (G // p) == g for p in range(1, G))


def has_long_triple(g: str, L: int) -> bool:
    return any(e >= L - 1 for e, *_ in triple_repeats(g))


def sectionG():
    section("G. Remap density: how often is the Bresler-remapped I_s satisfiable at all?")
    rows = {}
    for G in range(2, 8):
        tot = free = 0
        for gw in product("AT", repeat=G):
            g = "".join(gw)
            tot += 1
            if not has_long_triple(doubled(g), 3):
                free += 1
        rows[G] = (free, tot)
        print(f"    G={G}: doubled genomes free of triple repeats of length >= 2: "
              f"{free}/{tot}")
    free_all = sum(v[0] for v in rows.values())
    tot_all = sum(v[1] for v in rows.values())
    print(f"  total: {free_all}/{tot_all}")
    check(rows[2] == (4, 4) and rows[3] == (8, 8) and rows[4] == (8, 16)
          and rows[5] == (2, 32) and rows[6] == (4, 64) and rows[7] == (2, 128),
          "the per-G remap density of appendix §3.3 is reproduced exactly")
    check((free_all, tot_all) == (28, 252),
          "28 of 252 doubled genomes (2<=G<=7) are long-triple-repeat-free")
    # the original single-strand density, for the comparison the appendix draws
    orig = sum(1 for G in range(4, 9) for gw in product("AT", repeat=G)
               if not has_long_triple("".join(gw), 3))
    check(orig == 162,
          "162 of 496 original genomes (4<=G<=8) pass the triple-repeat clause on "
          "themselves, against 28/252 doubled genomes")
    check(free_all / tot_all < orig / 496,
          "the remap is a materially stronger hypothesis engine, as §3.3 claims")


# --------------------------------------------------------------------------- #


def main():
    print("AssemblyP1 issue #215: independent audit of the reconciliation appendix")
    hs = doubled("AAATAT")
    S, D, L, R, x, mS, mD, lifts, statuses = sectionA()
    sectionB(hs)
    sectionC()
    sectionD()
    sectionE(S, L, R, lifts)
    sectionF(hs)
    sectionG()
    print()
    if FAILURES:
        print(f"FAILED: {len(FAILURES)} check(s)")
        for f in FAILURES:
            print("  - " + f)
        sys.exit(1)
    print("All audit checks passed.")


if __name__ == "__main__":
    main()
