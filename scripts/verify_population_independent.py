#!/usr/bin/env python3
"""
Independent verifier for the population / exact-frequency identifiability of
primitive P2 (= source-I_s-shadow = WEAK) circular genomes, including
proportional-spectrum (cross-length) mates.

This script was written independently of
`scripts/verify_population_identifiability.py` and
`scripts/bridging_spectrum_uniqueness.py`; it re-implements the circular
windows, the Bresler maximal-repeat / triple-repeat / interleaving predicates,
the two intrinsic predicates, primitivity, and the exact proportional-spectrum
relation from scratch.  It is exact (integers / `fractions.Fraction`) and
deterministic; it exits non-zero on any failed assertion.

It corroborates, and in two places sharpens, the claims of
`docs/population-identifiability-intrinsic-genomes.md` and
`docs/issue48-population-independent-verification-2026-09-21.md`.

Ranges can be widened with --full.
"""

from __future__ import annotations

import argparse
import sys
from collections import defaultdict
from itertools import combinations, product
from fractions import Fraction


# ---------------------------------------------------------------------------
# Circular words
# ---------------------------------------------------------------------------
def rotations(w):
    return [w[i:] + w[:i] for i in range(len(w))]


def canon(w):
    return min(rotations(w))


def is_primitive(w):
    n = len(w)
    return not any(n % p == 0 and w == w[:p] * (n // p) for p in range(1, n))


def windows(w, L):
    n = len(w)
    d = defaultdict(int)
    for i in range(n):
        d[w[i:i + L] if i + L <= n else (w[i:] + w[:i + L - n])] += 1
    return dict(d)


def normalized(w, L):
    n = len(w)
    return tuple(sorted((k, Fraction(v, n)) for k, v in windows(w, L).items()))


def proportional(w1, w2, L):
    """d_{w2} = (|w2|/|w1|) d_{w1}, by exact integer cross-multiplication."""
    n1, n2 = len(w1), len(w2)
    d1, d2 = windows(w1, L), windows(w2, L)
    for k in set(d1) | set(d2):
        if d1.get(k, 0) * n2 != d2.get(k, 0) * n1:
            return False
    return True


# ---------------------------------------------------------------------------
# Bresler repeat structures (maximal-repeat definitions, as in
# docs/bridging-source-semantics.md)
# ---------------------------------------------------------------------------
def triples(w):
    """All Bresler triple repeats of w: return list of (ell, (t1,t2,t3))."""
    n = len(w)
    out = []
    for ell in range(1, n + 1):
        groups = defaultdict(list)
        for i in range(n):
            groups[w[i:i + ell] if i + ell <= n
                   else (w[i:] + w[:i + ell - n])].append(i)
        for _, ts in groups.items():
            if len(ts) < 3:
                continue
            for a, b, c in combinations(ts, 3):
                pre = {w[(a - 1) % n], w[(b - 1) % n], w[(c - 1) % n]}
                post = {w[(a + ell) % n], w[(b + ell) % n], w[(c + ell) % n]}
                if len(pre) > 1 and len(post) > 1:
                    out.append((ell, (a, b, c)))
    return out


def maximal_pairs(w):
    """All maximal repeat pairs of w: list of (ell, (a,b))."""
    n = len(w)
    out = []
    for ell in range(1, n + 1):
        groups = defaultdict(list)
        for i in range(n):
            groups[w[i:i + ell] if i + ell <= n
                   else (w[i:] + w[:i + ell - n])].append(i)
        for _, ts in groups.items():
            for a, b in combinations(ts, 2):
                if w[(a - 1) % n] != w[(b - 1) % n] and \
                   w[(a + ell) % n] != w[(b + ell) % n]:
                    out.append((ell, (a, b)))
    return out


def interleaved_pairs(w):
    """All interleaved pairs of maximal repeat pairs: (ell1,ell2)."""
    n = len(w)
    res = []
    pairs = maximal_pairs(w)
    for i in range(len(pairs)):
        e1, p1 = pairs[i]
        for j in range(i + 1, len(pairs)):
            e2, p2 = pairs[j]
            four = sorted(set(p1) | set(p2))
            if len(four) != 4:
                continue
            labels = [0 if x in p1 else 1 for x in four]
            if labels == [0, 1, 0, 1] or labels == [1, 0, 1, 0]:
                res.append((e1, e2))
    return res


def TRF(w, L):
    return all(ell <= L - 2 for ell, _ in triples(w))


def ILF(w, L):
    return not any(e1 >= L - 1 and e2 >= L - 1 for e1, e2 in interleaved_pairs(w))


def WEAK(w, L):
    return TRF(w, L) and ILF(w, L)


def STRONG(w, L):
    return all(v <= 1 for v in windows(w, L - 1).values())


# ---------------------------------------------------------------------------
# Molecule panel
# ---------------------------------------------------------------------------
_COMP = {"A": "T", "T": "A", "C": "G", "G": "C"}


def revcomp(w):
    return "".join(_COMP[c] for c in reversed(w))


def molecule_spectrum(w, L):
    n = len(w)
    d = defaultdict(int)
    for k, v in windows(w, L).items():
        d[min(k, revcomp(k))] += v
    return tuple(sorted((k, Fraction(v, n)) for k, v in d.items()))


def dihedrally_equivalent(a, b):
    return any(canon(revcomp(r)) == canon(b) for r in rotations(a)) or canon(a) == canon(b)


# ---------------------------------------------------------------------------
# Enumeration helpers
# ---------------------------------------------------------------------------
def primitive_canonicals(n, q):
    for tup in product(range(q), repeat=n):
        w = "".join(chr(65 + x) for x in tup)
        if canon(w) == w and is_primitive(w):
            yield w


def words_up_to(nmax, q):
    by_len = defaultdict(list)
    for n in range(2, nmax + 1):
        for w in primitive_canonicals(n, q):
            by_len[n].append(w)
    return by_len


# ---------------------------------------------------------------------------
# Named checks
# ---------------------------------------------------------------------------
def named_witnesses():
    """Explicit sharpness witnesses; all verified exactly."""
    checks = []

    # (1) primitivity is necessary: AAB / (AAB)^2 share the population law.
    S, T, L = "AAB", "AABAAB", 3
    assert is_primitive(S) and not is_primitive(T)
    assert WEAK(S, L) and WEAK(T, L)
    assert proportional(S, T, L)
    assert canon(T) not in rotations(S)
    checks.append("primitivity necessary: AAB ~ AABAAB (L=3), T non-primitive")

    # (2) candidate admissibility is necessary: the *larger* mate may be
    #     primitive but fail TRF.  AAB / AAABAB at L=2 (c = 2).
    S, T, L = "AAB", "AAABAB", 2
    assert is_primitive(S) and is_primitive(T)
    assert WEAK(S, L) and not WEAK(T, L) and not TRF(T, L)
    assert proportional(S, T, L)
    assert canon(T) not in rotations(S)
    checks.append("admissibility necessary: AAB ~ AAABAB (L=2), T primitive but not TRF")

    # (3) larger-primitive-non-WEAK variant at L=3.
    S, T, L = "AAAB", "AAAABAAB", 3
    assert is_primitive(S) and is_primitive(T)
    assert WEAK(S, L) and not WEAK(T, L)
    assert proportional(S, T, L)
    assert canon(T) not in rotations(S)
    checks.append("admissibility necessary: AAAB ~ AAAABAAB (L=3), T primitive but not TRF")

    # (4) TRF alone is not enough for the equal-length step:
    #     AABABB / AABBAB have the same L=3 spectrum, are both TRF, not rotations.
    S, T, L = "AABABB", "AABBAB", 3
    assert is_primitive(S) and is_primitive(T)
    assert TRF(S, L) and TRF(T, L)
    assert normalized(S, L) == normalized(T, L)
    assert not ILF(S, L) and not ILF(T, L)
    assert canon(T) not in rotations(S)
    checks.append("TRF insufficient equal length: AABABB / AABBAB (L=3)")

    # (5) molecule-panel boundary: primitive STRONG equal-length genomes with the
    #     same molecule-class law but dihedrally inequivalent.
    S, T, L = "AACAGT", "AACTGT", 3
    assert is_primitive(S) and is_primitive(T)
    assert STRONG(S, L) and STRONG(T, L)
    assert molecule_spectrum(S, L) == molecule_spectrum(T, L)
    assert not dihedrally_equivalent(S, T)
    checks.append("molecule panel boundary: AACAGT / AACTGT (L=3)")

    return checks


# ---------------------------------------------------------------------------
# Exhaustive checks
# ---------------------------------------------------------------------------
def check_lemma_Lstar(ranges):
    """Primitive TRF => every (L-1)-mer occurs at most twice."""
    worst = 0
    for q, nmax, Lmax in ranges:
        for L in range(2, Lmax + 1):
            for n in range(L, nmax + 1):
                for w in primitive_canonicals(n, q):
                    if TRF(w, L):
                        m = max(windows(w, L - 1).values())
                        worst = max(worst, m)
                        assert m <= 2, (q, nmax, L, w, m)
    return worst


def check_cross_length(ranges):
    """No two primitive TRF words have proportional spectra of different lengths.

    Returns (instances, cross_collisions, same_length_collisions).  The
    same-length collisions are expected (TRF alone does not force equal-length
    uniqueness); only the cross-length count must be zero.
    """
    words = 0
    cross = 0
    same = 0
    for q, nmax, Lmax in ranges:
        by_len = words_up_to(nmax, q)
        for L in range(2, min(nmax, Lmax) + 1):
            groups = defaultdict(list)
            for n in range(L, nmax + 1):
                for w in by_len[n]:
                    if TRF(w, L):
                        words += 1
                        groups[normalized(w, L)].append(w)
            for ws in groups.values():
                for i in range(len(ws)):
                    for j in range(i + 1, len(ws)):
                        a, b = ws[i], ws[j]
                        if len(a) == len(b):
                            same += 1
                        else:
                            cross += 1
    assert cross == 0, "cross-length primitive-TRF proportional collision found"
    return words, cross, same


def check_equal_length(ranges):
    """Same-length equal-spectrum non-rotation pairs.

    Required claim: no pair with *both* sides WEAK (primitivity and WEAK on the
    truth side already imply primitivity here, since we enumerate primitive
    words only).  Stronger observation reported but not asserted as a theorem:
    no pair with *either* side WEAK.
    """
    total = 0
    both_weak = 0
    either_weak = 0
    for q, nmax, Lmax in ranges:
        by_len = words_up_to(nmax, q)
        for L in range(2, min(nmax, Lmax) + 1):
            groups = defaultdict(list)
            for n in range(L, nmax + 1):
                for w in by_len[n]:
                    groups[normalized(w, L)].append(w)
            for ws in groups.values():
                if len(ws) < 2:
                    continue
                weak = {w: WEAK(w, L) for w in ws}
                for i in range(len(ws)):
                    for j in range(i + 1, len(ws)):
                        a, b = ws[i], ws[j]
                        if len(a) != len(b) or canon(a) == canon(b):
                            continue
                        total += 1
                        both_weak += int(weak[a] and weak[b])
                        either_weak += int(weak[a] or weak[b])
    assert both_weak == 0, "equal-length collision with both sides WEAK"
    return total, both_weak, either_weak


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--full", action="store_true",
                    help="widen the exhaustive ranges (slower)")
    args = ap.parse_args()

    print("Independent population-identifiability verification")
    print("=" * 58)

    print("\n[1] Named sharpness / boundary witnesses")
    for line in named_witnesses():
        print("   ok:", line)

    if args.full:
        ranges = [(2, 16, 16), (3, 11, 6), (4, 9, 5)]
        eq_ranges = [(2, 16, 16), (3, 11, 11), (4, 10, 10)]
    else:
        ranges = [(2, 13, 13), (3, 9, 5)]
        eq_ranges = [(2, 14, 14), (3, 10, 10), (4, 9, 9)]

    print("\n[2] Lemma L*: primitive TRF => (L-1)-mer multiplicity <= 2")
    worst = check_lemma_Lstar(ranges)
    print(f"   ok: max observed multiplicity = {worst} (bound 2)")

    print("\n[3] Theorem P: primitive TRF cross-length proportional spectra")
    words, cross, same = check_cross_length(ranges)
    print(f"   ok: {words} primitive TRF instances; cross-length collisions = {cross} "
          f"(same-length collisions = {same}, expected under TRF alone)")

    print("\n[4] Equal length: no equal-spectrum non-rotation pair with both sides WEAK")
    total, both_weak, either_weak = check_equal_length(eq_ranges)
    print(f"   ok: {total} same-length spectral pairs inspected; "
          f"both-WEAK collisions = {both_weak}; either-WEAK = {either_weak} "
          f"(stronger observation, not asserted)")

    print("\nall independent population-identifiability checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
