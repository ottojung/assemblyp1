#!/usr/bin/env python3
"""Independent verification of the (#215) V3 (Bresler 2G remap) compatibility.

This script is self-contained: it shares no code with
`scripts/verify_oriented_molecule_bridging.py`,
`scripts/audit_215_transfer_reconciliation.py`, or
`scripts/verify_two_disjoint_circles_duplex.py`, and it re-derives every number
in appendix section 11 and in `AssemblyP1/BreslerRemapCompatibility.lean` from
scratch on its own representation (genomes as `str`, spectra as `dict`).

It exits non-zero on the first failed assertion.

Claims re-derived here
----------------------
A. The `AAATAT` witness: `I_s` holds on the single strand, fails on the
   Bresler-doubled length-12 circle for *every* read set (R3 failure).
B. The `GGGA` witness: under the natural-seat reading the doubled circle
   `GGGATCCC` is `I_s`-feasible while `GGGA` is not (R1 failure); the two
   binding seats `6, 7` are spurious (their windows are `CCG`, `CGG`, not the
   wrapping read `GAG` and its reverse complement `CTC`).
C. Reading comparison: over binary and ternary genomes, `L = 3`, `3 <= G <= 7`,
   the natural-seat reading is unsound (V3 holds, V1/V2 fails) while the
   faithful-occurrence reading is sound in the searched scope.
D. R2: the doubled and two-disjoint-circles candidate spectra agree for exactly
   `254/508` binary words (`2 <= G <= 8`, `L = 3`).
E. V5 reconciliation: for the `GGGA` witness the V5 circle-by-circle reading
   fails on both circles, siding with V1/V2, not with the natural-seat V3.
"""

import sys
from itertools import combinations, combinations_with_replacement, product

FAILURES = 0


def check(cond, msg):
    global FAILURES
    if cond:
        print(f"  [ok]   {msg}")
    else:
        FAILURES += 1
        print(f"  [FAIL] {msg}")


def section(title):
    print()
    print(title)
    print("-" * len(title))


# --------------------------------------------------------------------------- #
# Self-contained transcription of the shared SourceFaithfulIs layer
# --------------------------------------------------------------------------- #

COMP = {"A": "T", "T": "A", "C": "G", "G": "C"}


def rc(w):
    return "".join(COMP[c] for c in reversed(w))


def window(g, e, r):
    G = len(g)
    return "".join(g[(r + i) % G] for i in range(e))


def preceding(g, t):
    return g[(t - 1) % len(g)]


def following(g, e, t):
    return g[(t + e) % len(g)]


def agree(g, e, a, b):
    return window(g, e, a) == window(g, e, b)


def is_triple_repeat(g, e, a, b, c):
    G = len(g)
    if not (1 <= e < G) or len({a, b, c}) != 3:
        return False
    if not (agree(g, e, a, b) and agree(g, e, a, c) and agree(g, e, b, c)):
        return False
    if preceding(g, a) == preceding(g, b) == preceding(g, c):
        return False
    if following(g, e, a) == following(g, e, b) == following(g, e, c):
        return False
    return True


def is_repeat_pair(g, e, a, b):
    G = len(g)
    if not (1 <= e < G) or a == b:
        return False
    if not agree(g, e, a, b):
        return False
    return preceding(g, a) != preceding(g, b) and following(g, e, a) != following(g, e, b)


def triple_repeats(g):
    G = len(g)
    out = []
    for e in range(1, G):
        groups = {}
        for t in range(G):
            groups.setdefault(window(g, e, t), []).append(t)
        for sts in groups.values():
            for a, b, c in combinations(sorted(sts), 3):
                if is_triple_repeat(g, e, a, b, c):
                    out.append((e, a, b, c))
    return out


def repeat_pairs(g):
    G = len(g)
    out = []
    for e in range(1, G):
        groups = {}
        for t in range(G):
            groups.setdefault(window(g, e, t), []).append(t)
        for sts in groups.values():
            for a, b in combinations(sorted(sts), 2):
                if is_repeat_pair(g, e, a, b):
                    out.append((e, a, b))
    return out


def in_open_arc(G, a, b, p):
    return 0 < (p + G - a) % G < (b + G - a) % G


def interleaved(G, a, b, c, d):
    if len({a, b, c, d}) != 4:
        return False
    return in_open_arc(G, a, b, c) != in_open_arc(G, a, b, d)


def bridges_copy(g, L, R, e, t):
    G = len(g)
    for r in R:
        for d in range(L):
            if d + e + 1 < L and (r + d + 1) % G == t:
                return True
    return False


def covers(g, L, R):
    G = len(g)
    return all(any(p == (r + d) % G for r in R for d in range(L)) for p in range(G))


def information_feasible(g, L, R):
    R = sorted(set(R))
    if not covers(g, L, R):
        return False
    for e, a, b, c in triple_repeats(g):
        if not all(bridges_copy(g, L, R, e, t) for t in (a, b, c)):
            return False
    rps = repeat_pairs(g)
    for i in range(len(rps)):
        for j in range(i + 1, len(rps)):
            e1, a, b = rps[i]
            e2, c, d = rps[j]
            if not interleaved(len(g), a, b, c, d):
                continue
            if not (any(bridges_copy(g, L, R, e1, t) for t in (a, b))
                    or any(bridges_copy(g, L, R, e2, t) for t in (c, d))):
                return False
    return True


# --------------------------------------------------------------------------- #
# Doubling and the two readings
# --------------------------------------------------------------------------- #


def doubled(g):
    return g + rc(g)


def natural_seat_placements(g, starts, L):
    """The appendix / Lean natural-seat doubling: `t` if non-wrapping else `G+t`,
    and the partner `2G - b - L`.  No occurrence check."""
    G = len(g)
    W = 2 * G
    out = set()
    for t in starts:
        base = t if t <= G - L else G + t
        out.add(base % W)
        out.add((W - base - L) % W)
    return sorted(out)


def faithful_placements(g, starts, L):
    """Place each realized read and its reverse complement at *every* genuine
    occurrence in the doubled circle.  This is the most generous faithful
    (occurrence-respecting) completion of the doubling."""
    hs = doubled(g)
    W = len(hs)
    words = set()
    for t in starts:
        w = window(g, L, t)
        words.add(w)
        words.add(rc(w))
    return sorted(b for b in range(W) if window(hs, L, b) in words)


def molecule_class(w):
    return min(w, rc(w))


def molecule_spectrum(g, e):
    spec = {}
    for t in range(len(g)):
        c = molecule_class(window(g, e, t))
        spec[c] = spec.get(c, 0) + 1
    return spec


def support(spec):
    return frozenset(c for c, v in spec.items() if v > 0)


def seam_windows(g, L):
    """The `2(L-1)` junction windows of `S · ρ(S)`: those crossing the seam at
    position `G` and those crossing the seam at position `2G`."""
    hs = doubled(g)
    G = len(g)
    W = 2 * G
    out = {}
    for b in list(range(G - L + 1, G)) + list(range(W - L + 1, W)):
        w = window(hs, L, b)
        out[w] = out.get(w, 0) + 1
    return out


def wrap_spectrum(g, e):
    G = len(g)
    out = {}
    for t in range(G - e + 1, G):
        w = window(g, e, t)
        out[w] = out.get(w, 0) + 1
    return out


def r2_holds(g, L):
    G = len(g)
    j = seam_windows(g, L)
    wr = wrap_spectrum(g, L)
    words = {window(g, L, t) for t in range(G)}
    return all(j.get(w, 0) == wr.get(w, 0) + wr.get(rc(w), 0) for w in words)


# --------------------------------------------------------------------------- #
# A. The AAATAT witness (R3)
# --------------------------------------------------------------------------- #


def section_A():
    section("A. AAATAT: V1/V2 holds, V3 fails for every read set (R3)")
    S, L, starts = "AAATAT", 3, [0, 0, 1, 3, 5]
    hs = doubled(S)
    check(hs == "AAATATATATTT", f"doubled(AAATAT) = {hs}")
    check(information_feasible(S, L, starts), "I_s(AAATAT, {0,1,3,5}) = True (V1/V2)")
    # R3 failure is placement-independent: a length-4 maximal triple repeat exists
    tr = [x for x in triple_repeats(hs) if x[0] >= L - 1]
    check(any(x == (4, 2, 4, 6) for x in tr),
          "doubled genome has the maximal triple repeat ATAT @ {2,4,6} of length 4")
    check(all(not information_feasible(hs, L, natural_seat_placements(S, list(R), L))
              for R in subsets_of(len(S), range(1, len(S) + 1))),
          "no read set makes the doubled instance I_s-feasible (R3 fails)")
    check(not information_feasible(hs, L, list(range(12))),
          "even the full read set {0..11} cannot bridge the length-4 repeat")


def subsets_of(n, sizes):
    for k in sizes:
        for c in combinations(range(n), k):
            yield c


# --------------------------------------------------------------------------- #
# B. The GGGA witness (R1)
# --------------------------------------------------------------------------- #


def section_B():
    section("B. GGGA: V3 (natural seats) holds, V1/V2 fails (R1)")
    S, L, starts = "GGGA", 3, [0, 1, 2]
    hs = doubled(S)
    check(hs == "GGGATCCC", f"doubled(GGGA) = {hs}")
    dpl = natural_seat_placements(S, starts, L)
    check(dpl == [0, 1, 4, 5, 6, 7], f"natural-seat doubled read set = {dpl}")
    check(information_feasible(hs, L, dpl), "I_s(GGGATCCC, natural seats) = True (V3)")
    check(not information_feasible(S, L, starts), "I_s(GGGA, {0,1,2}) = False (V1/V2)")
    # the binding seats 6 and 7 are spurious
    check(window(hs, L, 6) == "CCG" and window(hs, L, 7) == "CGG",
          "seat 6 window = CCG, seat 7 window = CGG")
    check(window(S, L, 2) == "GAG" and rc("GAG") == "CTC",
          "the wrapping read at S-start 2 is GAG, reverse complement CTC")
    check("GAG" not in {window(hs, L, b) for b in range(8)}
          and "CTC" not in {window(hs, L, b) for b in range(8)},
          "neither GAG nor CTC occurs in GGGATCCC (both natural seats spurious)")
    # removing the spurious pair restores soundness
    faithful = faithful_placements(S, starts, L)
    check(faithful == [0, 1, 4, 5], f"faithful doubled read set = {faithful}")
    check(not information_feasible(hs, L, faithful),
          "I_s(GGGATCCC, faithful seats) = False: soundness restored")


# --------------------------------------------------------------------------- #
# C. Reading comparison over a scope
# --------------------------------------------------------------------------- #


def all_genomes(G, alph):
    return ["".join(p) for p in product(alph, repeat=G)]


def canon(g, alph):
    G = len(g)
    forms = []
    for s in (g, rc(g)):
        for i in range(G):
            forms.append(s[i:] + s[:i])
    return min(forms)


def section_C():
    section("C. Natural-seat reading is unsound; faithful reading is sound in scope")
    total_nat = total_faith = 0
    unsound_nat = []
    unsound_faith = []
    for alph in ("AT", "ATG"):
        for G in range(3, 8):
            reps = sorted({canon(g, alph): g for g in all_genomes(G, alph)}.values())
            for S in reps:
                hs = doubled(S)
                for k in range(1, G + 1):
                    for R in combinations(range(G), k):
                        if not covers(S, 3, R):
                            continue
                        nat = natural_seat_placements(S, list(R), 3)
                        if information_feasible(hs, 3, nat):
                            total_nat += 1
                            if not information_feasible(S, 3, list(R)):
                                unsound_nat.append((S, R))
                        fth = faithful_placements(S, list(R), 3)
                        if information_feasible(hs, 3, fth):
                            total_faith += 1
                            if not information_feasible(S, 3, list(R)):
                                unsound_faith.append((S, R))
    check(len(unsound_nat) > 0,
          f"natural-seat reading is unsound: {len(unsound_nat)} witnesses "
          f"(e.g. {unsound_nat[:3]}), out of {total_nat} V3-feasible instances")
    check(len(unsound_faith) == 0,
          f"faithful-occurrence reading is sound in scope: "
          f"{total_faith} V3-feasible instances, 0 violations")
    check(any(w[0] == "GGGA" for w in unsound_nat),
          "GGGA is among the natural-seat unsoundness witnesses")


# --------------------------------------------------------------------------- #
# D. R2 spectrum agreement
# --------------------------------------------------------------------------- #


def section_D():
    section("D. V3 and V5 candidate spectra agree exactly when R2 holds")
    agree = total = 0
    per_G = {}
    for G in range(2, 9):
        a = t = 0
        for g in all_genomes(G, "AT"):
            t += 1
            if r2_holds(g, 3):
                a += 1
        agree += a
        total += t
        per_G[G] = (a, t)
    check((agree, total) == (254, 508),
          f"R2 holds for {agree}/{total} binary words (2<=G<=8, L=3)")
    check(all(a * 2 == t for a, t in per_G.values()),
          "exactly half at every G: " + ", ".join(f"G={G}:{a}/{t}" for G, (a, t) in per_G.items()))
    # failure witness AAGG: seam class absent from S's own molecule spectrum
    S = "AAGG"
    hs = doubled(S)
    seam_classes = {molecule_class(window(hs, 3, b)) for b in range(len(S) - 2, len(S) + 2)}
    own_classes = {molecule_class(window(S, 3, t)) for t in range(len(S))}
    check(not r2_holds(S, 3), "R2 fails at S = AAGG")
    check(seam_classes - own_classes,
          f"AAGG seam creates class(es) absent from S: {sorted(seam_classes - own_classes)}")


# --------------------------------------------------------------------------- #
# E. V5 reconciliation for GGGA
# --------------------------------------------------------------------------- #


def section_E():
    section("E. V5 reconciliation: GGGA fails circle-by-circle too")
    S, L, starts = "GGGA", 3, [0, 1, 2]
    R = rc(S)
    check(R == "TCCC", f"rc(GGGA) = {R}")
    partner = sorted({(len(S) - t - L) % len(S) for t in starts})
    check(partner == [0, 1, 3], f"V5 partner read set = {partner}")
    check(not information_feasible(S, L, starts), "V5 circle S fails I_s (matches V1/V2)")
    check(not information_feasible(R, L, partner), "V5 circle rc(S) fails I_s too")
    # the V5 candidate spectrum has no seam terms: spec_duplex = spec_S + spec_S o rc
    spec_duplex = {}
    for t in range(len(S)):
        for w in (window(S, L, t), window(R, L, t)):
            spec_duplex[w] = spec_duplex.get(w, 0) + 1
    expected = {}
    for t in range(len(S)):
        for w in (window(S, L, t), rc(window(S, L, t))):
            expected[w] = expected.get(w, 0) + 1
    check(spec_duplex == expected,
          "V5 duplex spectrum = spec_S + spec_S o rc (no seam terms)")


def main():
    section_A()
    section_B()
    section_C()
    section_D()
    section_E()
    print()
    if FAILURES:
        print(f"FAILED: {FAILURES} assertion(s) failed.")
        sys.exit(1)
    print("All Bresler-remap compatibility assertions passed.")


if __name__ == "__main__":
    main()
