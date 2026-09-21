#!/usr/bin/env python3
"""Candidate-intrinsic repeat/read-length admissibility for issue #48.

This script is a bounded evaluator for the *new repaired model* of issue #48,
not a source-faithful literature result and not a proof.  It checks, with exact
combinatorics and exact `fractions.Fraction` arithmetic, the following:

  A. Propositional relations between the candidate-intrinsic predicates
     TRF (no Bresler triple repeat of length >= L-1),
     ILF (no interleaved maximal-repeat pair with both lengths >= L-1),
     STRUCT = TRF & ILF (the structural assembly boundary),
     SW  (every length-(L-1) window occurs at most twice),
     PRIM (primitive circular word):
       (i)  SW  => TRF          (always);
       (ii) PRIM & TRF <=> PRIM & SW.
     Checked exhaustively on small scopes.

  B. Independence and root reduction:
       - TRF without PRIM: D = (ACGT)^2 is TRF and non-primitive and ties S=ACGT;
       - PRIM without TRF: D = AAAATT is primitive, fails TRF, beats S = AAATT;
       - non-primitive D = P^m has the same normalized spectrum as its primitive
         root P, and TRF(D) implies TRF(P).

  C. A bounded search for a counterexample to the *repaired* conjecture
     "every I_s-realizable truth is a maximizer among candidates satisfying the
     candidate-intrinsic predicate".  For a candidate D and truth S the exact
     multinomial admits a strict counterexample for some observation x with
     support in supp(spec_L(S)) iff some observed type w has
     d_D(w)/|D| > d_S(w)/|S|.  The script compares the predicates PRIM, ILF,
     TRF, PRIM&TRF, STRUCT, PRIM&STRUCT over exhaustive small scopes, under two
     support semantics:
       - "contain" (per-vertex/§6.2 lower bound, supp(D) superseteq supp(S)):
         even PRIM&STRUCT admits strict counterexamples;
       - "equal" (spelled-circuit, supp(D) = supp(S)): TRF alone has none.

Usage:
    python3 scripts/verify_intrinsic_admissibility.py            # quick
    python3 scripts/verify_intrinsic_admissibility.py --full     # wider scopes
"""

from __future__ import annotations

import sys
from fractions import Fraction
from itertools import combinations, product


# --------------------------------------------------------------------------- #
# Core oriented circular-string objects.
# --------------------------------------------------------------------------- #


def windows(s: tuple[str, ...], L: int) -> list[tuple[str, ...]]:
    G = len(s)
    return [tuple(s[(i + j) % G] for j in range(L)) for i in range(G)]


def spec(s: tuple[str, ...], L: int) -> dict[tuple[str, ...], int]:
    d: dict[tuple[str, ...], int] = {}
    for w in windows(s, L):
        d[w] = d.get(w, 0) + 1
    return d


def minmer_counts(s: tuple[str, ...], L: int) -> dict[tuple[str, ...], int]:
    d: dict[tuple[str, ...], int] = {}
    for w in windows(s, L - 1):
        d[w] = d.get(w, 0) + 1
    return d


def is_primitive(s: tuple[str, ...]) -> bool:
    p = len(s)
    for d in range(1, p):
        if p % d == 0 and all(s[i] == s[i % d] for i in range(p)):
            return False
    return True


def long_bresler_triple(s: tuple[str, ...], L: int):
    """A Bresler triple repeat of length >= L-1, or None."""
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


def TRF(s: tuple[str, ...], L: int) -> bool:
    """No Bresler triple repeat of length >= L-1."""
    return long_bresler_triple(s, L) is None


def SW(s: tuple[str, ...], L: int) -> bool:
    """Every length-(L-1) window occurs at most twice."""
    return all(v <= 2 for v in minmer_counts(s, L).values())


def maximal_repeat_length(s: tuple[str, ...], i: int, j: int) -> int:
    """Longest common extension of the two cyclic rotations from i and j (< G)."""
    G = len(s)
    ell = 0
    while ell < G and s[(i + ell) % G] == s[(j + ell) % G]:
        ell += 1
    return ell


def interleaved_long_pair(s: tuple[str, ...], L: int):
    """An interleaved pair of maximal repeats with both lengths >= L-1, or None.

    Two maximal repeats starting at (i,j) and (g,h) interleave when the four
    starts alternate around the circle (i,g,j,h or g,i,h,j).  This is the
    circular form of the Bresler/Ukkonen interleaved-repeat obstruction.
    """
    G = len(s)
    long_pairs = []
    for i in range(G):
        for j in range(i + 1, G):
            # A repeat is maximal on both sides: the longest common extension
            # blocks the right, and the preceding symbols must differ (else the
            # pair is not a maximal-repeat start pair and should be shifted left).
            if s[(i - 1) % G] == s[(j - 1) % G]:
                continue
            ell = maximal_repeat_length(s, i, j)
            if ell >= L - 1 and ell < G:
                long_pairs.append((i, j, ell))
    for a, b, _ in long_pairs:
        for c, d, _ in long_pairs:
            if (a, b) == (c, d):
                continue
            pts = {a, b, c, d}
            if len(pts) < 4:
                continue
            # do c and d separate a and b on the circle?
            def between(x, y, z):
                # is y strictly between x and z going forward?
                return (x < y < z) or (z < x < y) or (y < z < x)
            if between(a, c, b) != between(a, d, b):
                return (a, b, c, d)
    return None


def ILF(s: tuple[str, ...], L: int) -> bool:
    """No interleaved pair of maximal repeats with both lengths >= L-1."""
    return interleaved_long_pair(s, L) is None


def STRUCT(s: tuple[str, ...], L: int) -> bool:
    """Full Ukkonen/Bresler/Shomorony structural admissibility: TRF and ILF."""
    return TRF(s, L) and ILF(s, L)


def necklaces(alphabet, n):
    """One representative per rotation class of words of length n over alphabet."""
    seen = set()
    for t in product(alphabet, repeat=n):
        if t in seen:
            continue
        for i in range(n):
            seen.add(t[i:] + t[:i])
        yield t


def primitive_root(s: tuple[str, ...]) -> tuple[str, ...]:
    p = len(s)
    for d in range(1, p + 1):
        if p % d == 0 and all(s[i] == s[i % d] for i in range(p)):
            return s[:d]
    return s


# --------------------------------------------------------------------------- #
# A. Propositional relations, exhaustive in scope.
# --------------------------------------------------------------------------- #


def check_relations(alphabet, L, G, verbose=True):
    sw_not_trf = 0
    prim_trf_ne_sw = 0
    for s in necklaces(alphabet, G):
        t = TRF(s, L)
        w = SW(s, L)
        if w and not t:
            sw_not_trf += 1
        if is_primitive(s) and t != w:
            prim_trf_ne_sw += 1
    if verbose:
        print(
            f"  G={G:>2} L={L} sigma={len(alphabet)}: "
            f"SW&!TRF={sw_not_trf} PRIM&(TRF xor SW)={prim_trf_ne_sw}"
        )
    assert sw_not_trf == 0, "SW => TRF violated"
    assert prim_trf_ne_sw == 0, "PRIM & TRF <=> PRIM & SW violated"


# --------------------------------------------------------------------------- #
# B. Neither predicate alone suffices.
# --------------------------------------------------------------------------- #


def max_normalized_excess(dS, dD, GS, GD):
    """max over observed w of d_D(w)/|D| - d_S(w)/|S|, as an exact Fraction.

    A positive value means some observation concentrated on w strictly beats the
    truth under the exact candidate-intrinsic multinomial.
    """
    best = None
    best_w = None
    for w, c in dS.items():
        val = Fraction(dD.get(w, 0), GD) - Fraction(c, GS)
        if best is None or val > best:
            best, best_w = val, w
    return best, best_w


def full_ratio(x, S, D, L):
    """Exact candidate-intrinsic multinomial ratio for the given x."""
    dS, dD = spec(S, L), spec(D, L)
    r = Fraction(1)
    for w, xw in x.items():
        if xw == 0:
            continue
        r *= (Fraction(dD.get(w, 0), len(D)) / Fraction(dS[w], len(S))) ** xw
    return r


def witness_tandem_ties():
    """Whole-genome repetition: S^m ties S for every observation (TRF, not PRIM).

    This is the pure 'proportional-spectrum scale ambiguity' and shows PRIM is
    not implied by TRF and is *separately needed* for the uniqueness schema.
    """
    S = tuple("ACGT")          # repeat-free, I_s-realizable, primitive
    L = 2
    m = 2
    D = S * m                  # same normalized spectrum as S
    assert is_primitive(S) and TRF(S, L)
    assert TRF(D, L) and not is_primitive(D)
    assert spec(S, L).keys() == spec(D, L).keys()
    for x in (spec(S, L), {tuple("AC"): 5, tuple("CG"): 1,
                           tuple("GT"): 1, tuple("TA"): 1}):
        assert full_ratio(x, S, D, L) == 1
    excess, w = max_normalized_excess(spec(S, L), spec(D, L), len(S), len(D))
    assert excess == 0
    print(
        f"  (B.i)  S=ACGT D=(ACGT)^2 L=2: TRF(D)={TRF(D, L)} PRIM(D)="
        f"{is_primitive(D)} normalized spectra equal => ties for every x"
    )


def witness_primitive_no_trf():
    S = tuple("AAATT")
    L = 3
    D = tuple("AAAATT")
    assert TRF(S, L), "truth AAATT should be triple-repeat free at L=3"
    assert is_primitive(D) and not TRF(D, L)
    excess, w = max_normalized_excess(spec(S, L), spec(D, L), len(S), len(D))
    assert excess > 0
    dS, dD = spec(S, L), spec(D, L)
    M = 1
    ratio = Fraction(1)
    for u, cu in dS.items():
        xu = cu + (M if u == tuple("AAA") else 0)
        ratio *= (Fraction(dD.get(u, 0), len(D)) / Fraction(cu, len(S))) ** xu
    assert ratio > 1
    print(
        f"  (B.ii) S=AAATT D=AAAATT L=3: PRIM(D)={is_primitive(D)} "
        f"TRF(D)={TRF(D, L)} max_excess={excess} (w={''.join(w)}) "
        f"ratio(x=dS+{M}e_AAA)={ratio} > 1"
    )
    assert not SW(D, L), "AAAATT should fail SW"


def witness_struct_containment():
    """Counterexample A: PRIM & STRUCT fails under support containment."""
    S, D, L = tuple("AAAB"), tuple("AAABAB"), 3
    assert STRUCT(S, L) and STRUCT(D, L) and is_primitive(D)
    dS, dD = spec(S, L), spec(D, L)
    V = set(dS)
    assert V <= set(dD) and (set(dD) - V), "D must have extra (unobserved) support"
    excess, w = max_normalized_excess(dS, dD, len(S), len(D))
    assert excess > 0 and w == tuple("ABA")
    M = 4
    x = dict(dS)
    x[tuple("ABA")] = x.get(tuple("ABA"), 0) + M
    r = full_ratio(x, S, D, L)
    assert r > 1
    print(
        f"  (A) S=AAAB D=AAABAB L=3: STRUCT(S)={STRUCT(S, L)} "
        f"STRUCT(D)={STRUCT(D, L)} PRIM(D)={is_primitive(D)} "
        f"extra={sorted(''.join(e) for e in set(dD) - V)} "
        f"excess={excess} ratio(M={M})={r} > 1"
    )


def check_independence(verbose=True):
    """Proposition 3 independence witnesses."""
    cases = [
        ("TRF !-> PRIM", tuple("ACGTACGT"), 2, True, True, False),
        ("PRIM !-> TRF", tuple("AAAATT"), 3, False, True, True),
        ("TRF !-> ILF", tuple("AABABB"), 3, True, False, True),
        ("ILF !-> TRF", tuple("AAAAB"), 3, False, True, True),
    ]
    for label, s, L, trf, ilf, prim in cases:
        assert TRF(s, L) == trf, label
        assert ILF(s, L) == ilf, label
        assert is_primitive(s) == prim, label
        if verbose:
            print(
                f"  {label}: D={''.join(s)} L={L} PRIM={prim} TRF={trf} ILF={ilf}"
            )


def check_root_reduction(alphabet, L, Grange, verbose=True):
    """Non-primitive D = P^m: P has the same normalized spectrum, and TRF(D)
    implies TRF(P).  Hence a strict beating non-primitive candidate has a strict
    beating primitive root, so PRIM is not needed for the maximizer schema."""
    bad_spectrum = bad_trf = 0
    checked = 0
    for G in Grange:
        for D in necklaces(alphabet, G):
            if is_primitive(D):
                continue
            P = primitive_root(D)
            checked += 1
            dD, dP = spec(D, L), spec(P, L)
            # same normalized spectrum
            for w in set(dD) | set(dP):
                if Fraction(dD.get(w, 0), len(D)) != Fraction(dP.get(w, 0), len(P)):
                    bad_spectrum += 1
                    break
            if TRF(D, L) and not TRF(P, L):
                bad_trf += 1
    if verbose:
        print(
            f"  root reduction L={L} G<={max(Grange)}: checked={checked} "
            f"spectrum_mismatch={bad_spectrum} TRF_not_lifted={bad_trf}"
        )
    assert bad_spectrum == 0, "root does not share normalized spectrum"
    assert bad_trf == 0, "TRF(D) must imply TRF(root)"


# --------------------------------------------------------------------------- #
# C. Bounded search for a repaired-conjecture counterexample.
# --------------------------------------------------------------------------- #


_TRUTH_CACHE: dict = {}
_CAND_CACHE: dict = {}


def truth_pool(alphabet, L, G):
    """All I_s-structural truths of length G, with specs, cached."""
    key = (alphabet, L, G)
    if key not in _TRUTH_CACHE:
        pool = []
        for S in necklaces(alphabet, G):
            if STRUCT(S, L):
                pool.append((S, spec(S, L)))
        _TRUTH_CACHE[key] = pool
    return _TRUTH_CACHE[key]


def candidate_pool(alphabet, L, nD):
    """All necklaces of length nD with precomputed predicate flags, cached."""
    key = (alphabet, L, nD)
    if key not in _CAND_CACHE:
        pool = []
        for D in necklaces(alphabet, nD):
            pool.append((D, spec(D, L), is_primitive(D), TRF(D, L), ILF(D, L)))
        _CAND_CACHE[key] = pool
    return _CAND_CACHE[key]


def cand_pred(name, prim, trf, ilf):
    if name == "PRIM":
        return prim
    if name == "ILF":
        return ilf
    if name == "TRF":
        return trf
    if name == "PRIM&TRF":
        return prim and trf
    if name == "STRUCT=TRF&ILF":
        return trf and ilf
    if name == "PRIM&STRUCT":
        return prim and trf and ilf
    raise ValueError(name)


def search_repaired(alphabet, L, Grange, extra_len, pred_name, verbose=True,
                    support_mode="contain"):
    """For every I_s-structural truth S, every candidate D of length
    <= G+extra_len satisfying predicate `pred_name`, check whether some observed
    type has d_D(w)/|D| > d_S(w)/|S|.

    `support_mode="contain"` allows any D containing supp(spec_L(S)) (the
    per-vertex/§6.2 lower-bound reading); `support_mode="equal"` restricts to
    spelled candidates with supp(spec_L(D)) = supp(spec_L(S))."""
    hits = []
    scanned = 0
    for G in Grange:
        truths = truth_pool(alphabet, L, G)
        nDmax = G + extra_len
        cands = []
        for nD in range(L, nDmax + 1):
            for D, dD, prim, trf, ilf in candidate_pool(alphabet, L, nD):
                if cand_pred(pred_name, prim, trf, ilf):
                    cands.append((D, dD))
        for S, dS in truths:
            V = set(dS)
            for D, dD in cands:
                if any(w not in dD for w in V):
                    continue
                if support_mode == "equal" and any(w not in V for w in dD):
                    continue
                scanned += 1
                excess, w = max_normalized_excess(dS, dD, len(S), len(D))
                if excess > 0:
                    hits.append((S, D, L, w, excess))
        if verbose:
            print(f"    search G={G:>2} L={L}: cumulative hits={len(hits)}")
    return hits, scanned


def main(argv):
    full = "--full" in argv
    print("[A] propositional relations SW => TRF and PRIM&(TRF<=>SW)")
    rel_scopes = [
        (("A", "B"), 2, range(2, 15)),
        (("A", "B"), 3, range(3, 14)),
        (("A", "B"), 4, range(4, 12)),
        (("A", "B", "C"), 2, range(2, 11)),
        (("A", "B", "C"), 3, range(3, 10)),
    ]
    if full:
        rel_scopes = [
            (("A", "B"), 2, range(2, 18)),
            (("A", "B"), 3, range(3, 16)),
            (("A", "B"), 4, range(4, 14)),
            (("A", "B", "C"), 2, range(2, 12)),
            (("A", "B", "C"), 3, range(3, 11)),
        ]
    for alphabet, L, Grange in rel_scopes:
        for G in Grange:
            check_relations(alphabet, L, G)

    print("[B] independence, neither predicate alone suffices, root reduction")
    check_independence()
    witness_struct_containment()
    witness_tandem_ties()
    witness_primitive_no_trf()
    check_root_reduction(("A", "B", "C"), 3, range(4, 11))

    print("[C] bounded search over candidate-intrinsic predicates")
    search_scopes = [
        (("A", "B"), 2, range(4, 10), 3),
        (("A", "B"), 3, range(4, 9), 3),
        (("A", "B", "C"), 2, range(4, 8), 2),
    ]
    if full:
        search_scopes = [
            (("A", "B"), 2, range(4, 12), 3),
            (("A", "B"), 3, range(4, 11), 3),
            (("A", "B", "C"), 2, range(4, 9), 2),
            (("A", "B", "C"), 3, range(4, 8), 2),
        ]
    pred_names = ["PRIM", "ILF", "TRF", "PRIM&TRF", "STRUCT=TRF&ILF", "PRIM&STRUCT"]
    results = {}
    for mode in ("contain", "equal"):
        print(f"  -- support_mode={mode} --")
        for name in pred_names:
            hits = []
            for alphabet, L, Grange, extra in search_scopes:
                h, _ = search_repaired(alphabet, L, Grange, extra, name,
                                       verbose=False, support_mode=mode)
                hits.extend(h)
            results[(mode, name)] = hits
            print(f"  predicate {name}: {len(hits)} strict counterexample(s)")
            for S, D, L, w, excess in hits[:6]:
                print(
                    f"      S={''.join(S)} D={''.join(D)} L={L} "
                    f"w={''.join(w)} excess={excess}"
                )
    # Regression assertions for the documented findings:
    #  - under support containment even STRUCT admits strict counterexamples;
    #  - under support equality the weaker TRF has none in the searched scopes.
    assert results[("contain", "PRIM&STRUCT")], (
        "expected STRUCT counterexamples under support containment"
    )
    assert not results[("equal", "TRF")], (
        "expected no TRF counterexample under support equality"
    )
    print("documented intrinsic-admissibility findings reproduced")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
