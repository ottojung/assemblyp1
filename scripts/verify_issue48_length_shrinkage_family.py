#!/usr/bin/env python3
"""Issue #48: an explicit length-shrinkage family for the free-length objective.

Reproduction for docs/issue48-length-shrinkage-family.md.

Family (read length L >= 3, sample multiplicity x >= 1):

    S = A^(L-1) B B C      (truth,  G = L + 2)
    D = A^(L-1) B C        (competitor, n = L + 1)
    R = [0 repeated x times] + [L]        (latent read starts on S)

Claim (proved in the note, certified here with exact arithmetic):

  * R in I_s (strict source predicate; non-vacuous for L >= 4);
  * S and D are primitive;
  * S and D are STRONG (no (L-1)-mer occurs twice), hence also WEAK (P2) and
    admissible in the strongest candidate-intrinsic class;
  * the free-length exact Medvedev-Brudno ratio is

        L(D|x) / L(S|x) = ((L+2)/(L+1))^(x+1)  >  1,

    unbounded in x for fixed L, because the two observed read types
    u = A^(L-1) B and v = B C A^(L-2) each have multiplicity one in both S
    and D, so the ratio is exactly (|S|/|D|)^N.

The L = 3 member is S = AABBC, D = AABC (ratio 25/16), the issue #48 headline
witness.

This script is self-contained (it imports nothing from the other search
scripts), and additionally cross-checks the family against the two existing
independent implementations when they are importable.

Run:  python3 scripts/verify_issue48_length_shrinkage_family.py
"""
from __future__ import annotations

from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations

ALPH = "ABC"


def word_to_ints(s: str):
    order = []
    for ch in s:
        if ch not in order:
            order.append(ch)
    return tuple(order.index(ch) for ch in s)


def windows(w, L):
    n = len(w)
    return Counter(
        tuple(w[(i + j) % n] for j in range(L)) for i in range(n)
    )


def primitive(w):
    n = len(w)
    for p in range(1, n):
        if n % p == 0 and all(w[i] == w[i % p] for i in range(n)):
            return False
    return True


def strong(w, L):
    """No (L-1)-mer occurs twice; vacuously true when L-1 <= 0."""
    if L - 1 <= 0:
        return True
    return max(windows(w, L - 1).values()) <= 1


def maximal_pairs(w):
    n = len(w)
    out = []
    for ell in range(1, n):
        groups = defaultdict(list)
        for i in range(n):
            groups[tuple(w[(i + j) % n] for j in range(ell))].append(i)
        for key, ts in groups.items():
            for a, b in combinations(ts, 2):
                if (
                    w[(a - 1) % n] != w[(b - 1) % n]
                    and w[(a + ell) % n] != w[(b + ell) % n]
                ):
                    out.append((ell, (a, b)))
    return out


def triple_repeats(w):
    n = len(w)
    out = []
    for ell in range(1, n):
        groups = defaultdict(list)
        for i in range(n):
            groups[tuple(w[(i + j) % n] for j in range(ell))].append(i)
        for key, ts in groups.items():
            for tri in combinations(ts, 3):
                pres = {w[(t - 1) % n] for t in tri}
                posts = {w[(t + ell) % n] for t in tri}
                if len(pres) > 1 and len(posts) > 1:
                    out.append((ell, tuple(sorted(tri))))
    return out


def interleaved_pairs(w):
    reps = maximal_pairs(w)
    out = []
    for i in range(len(reps)):
        for j in range(i + 1, len(reps)):
            e1, p1 = reps[i]
            e2, p2 = reps[j]
            four = sorted(set(p1) | set(p2))
            if len(four) != 4:
                continue
            labels = [0 if p in p1 else 1 for p in four]
            if labels in ([0, 1, 0, 1], [1, 0, 1, 0]):
                out.append((reps[i], reps[j]))
    return out


def weak(w, L):
    """Full-read-set I_s shadow: triple and interleaved repeats bounded by L-2."""
    return all(ell <= L - 2 for ell, _ in triple_repeats(w)) and all(
        min(e1, e2) <= L - 2 for (e1, _p1), (e2, _p2) in interleaved_pairs(w)
    )


def covered(w, starts, L):
    n = len(w)
    cov = set()
    for r in starts:
        for o in range(L):
            cov.add((r + o) % n)
    return len(cov) == n


def copy_bridged(w, start_set, t, ell, L):
    """Strict two-sided extension: read start in {t-d : 1 <= d <= L-ell-1}."""
    if L - ell - 1 < 1:
        return False
    n = len(w)
    return any((t - d) % n in start_set for d in range(1, L - ell))


def in_Is(w, starts, L):
    start_set = set(starts)
    if not covered(w, starts, L):
        return False, "coverage"
    for ell, tri in triple_repeats(w):
        for t in tri:
            if not copy_bridged(w, start_set, t, ell, L):
                return False, "triple"
    for (e1, p1), (e2, p2) in interleaved_pairs(w):
        if not (
            any(copy_bridged(w, start_set, t, e1, L) for t in p1)
            or any(copy_bridged(w, start_set, t, e2, L) for t in p2)
        ):
            return False, "interleaved"
    return True, "ok"


def free_ratio(S, D, starts, L):
    G, n = len(S), len(D)
    dS, dD = windows(S, L), windows(D, L)
    obs = Counter(tuple(S[(r + j) % G] for j in range(L)) for r in starts)
    r = Fraction(1)
    for w, x in obs.items():
        if dS.get(w, 0) == 0:
            raise ValueError("observed type absent from truth")
        if dD.get(w, 0) == 0:
            return Fraction(0)
        r *= Fraction(G * dD[w], n * dS[w]) ** x
    return r


def family_member(L, x):
    S = word_to_ints("A" * (L - 1) + "BB" + "C")
    D = word_to_ints("A" * (L - 1) + "B" + "C")
    starts = (0,) * x + (L,)
    return S, D, starts


def check_family(Lmin=3, Lmax=14, xs=(1, 2, 3, 5, 8, 13)):
    print("=" * 74)
    print("Length-shrinkage family  S=A^(L-1)BB C,  D=A^(L-1)B C")
    print("=" * 74)
    ok = True
    for L in range(Lmin, Lmax + 1):
        S, D, _ = family_member(L, 1)
        G, n = len(S), len(D)
        tr = triple_repeats(S)
        for x in xs:
            S, D, starts = family_member(L, x)
            Is_ok, why = in_Is(S, starts, L)
            r = free_ratio(S, D, starts, L)
            exp = Fraction(G, n) ** (x + 1)
            good = (
                Is_ok
                and primitive(S)
                and primitive(D)
                and strong(S, L)
                and strong(D, L)
                and weak(S, L)
                and weak(D, L)
                and r == exp
                and r > 1
            )
            ok &= good
            if x == xs[0]:
                print(
                    f"L={L:2d} S={''.join(ALPH[c] for c in S):>{L + 2}} "
                    f"G={G} D={''.join(ALPH[c] for c in D):>{L + 1}} n={n} "
                    f"I_s={Is_ok}({why}) prim=({primitive(S)},{primitive(D)}) "
                    f"STRONG=({strong(S, L)},{strong(D, L)}) "
                    f"#triples={len(tr)}"
                )
                print(
                    f"        x={x}: ratio={r} = ((L+2)/(L+1))^(x+1)"
                    f" = {exp}  ({float(r):.6f})"
                )
            if not good:
                print(f"   FAIL L={L} x={x} r={r} exp={exp} Is={Is_ok}")
    print()
    print("family holds for all checked parameters:", ok)
    return ok


def cross_check():
    """Cross-check against both existing independent implementations."""
    import importlib
    import sys
    import os

    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    try:
        A = importlib.import_module("issue48_intrinsic_candidate_search")
        B = importlib.import_module("verify_issue48_intrinsic_admissibility")
    except Exception as exc:  # pragma: no cover
        print("cross-check skipped:", exc)
        return True

    print("=" * 74)
    print("Cross-check against existing independent implementations")
    print("=" * 74)
    bad = 0
    for L in range(3, 12):
        S, D, _ = family_member(L, 1)
        G, n = len(S), len(D)
        for x in (1, 3, 5):
            _, _, starts = family_member(L, x)
            okA, _ = A.check_Is(S, starts, L)
            obsA = Counter(
                tuple(S[(r + j) % G] for j in range(L)) for r in starts
            )
            rA = A.ratio(A.spectrum(S, L), G, A.spectrum(D, L), n, obsA)
            okB = B.check_I_s(S, list(starts), L)
            obsB = B.observed(S, list(starts), L)
            rB = B.ratio_free(S, D, obsB)
            good = (
                okA
                and okB
                and rA == rB == Fraction(G, n) ** (x + 1)
                and A.primitive(S)
                and A.primitive(D)
                and A.read_repetition_free(S, L)
                and A.read_repetition_free(D, L)
                and B.primitive(S)
                and B.primitive(D)
                and B.strong_admissible(S, L)
                and B.strong_admissible(D, L)
            )
            if not good:
                bad += 1
                print(f"   cross-check FAIL L={L} x={x}", okA, okB, rA, rB)
    print("cross-check failures:", bad)
    return bad == 0


def main():
    ok = check_family()
    ok &= cross_check()
    print()
    print("all checks passed:", ok)
    raise SystemExit(0 if ok else 1)


if __name__ == "__main__":
    main()
