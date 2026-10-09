#!/usr/bin/env python3
"""Tie-search for AssemblyP1 issue #211 (oriented same-length §6.2).

Question. Under the hypothesis surface of
`AssemblyP1.SameLength62Maximizer.informationFeasible_62_maximizer`
-- truth `S : Fin G -> alpha`, read length `2 <= L <= G`, `R ∈ I_s` at the
realized starts, truth a genuine §6.2 candidate -- can a *distinct* circular
genome `D` of the same length (not a cyclic shift of `S`) maximize the exact
same-length Medvedev-Brudno objective?

`AssemblyP1.MLEscape.Is_spectrum_eq_of_support_eq` (kernel-checked) says every
same-length word whose window support is the truth's has exactly the truth's
spectrum, so the tied maximizers are exactly the rotation classes in the fibre
of the truth's complete spectrum `c = specCount S`.  Hence tie freedom is
exactly `N(c) > 1` in the language of
`docs/exact-same-length-spectrum-fibre-count.md`, and a tie witness is an
`I_s`-feasible truth whose spectrum fibre has more than one rotation orbit.

The start set is taken to be `Finset.univ` (one read at every start).  It is the
most permissive start set: `Covers` and every `BridgesCopy` are monotone in `R`,
so `S ∈ I_s at R` implies `S ∈ I_s at univ`.  A witness below is therefore not an
artifact of the chosen start set, and a nonexistence result here covers every
start set.

With `R = univ` a copy of length `e` is bridged iff `e + 1 < L` (the read starts
at `t - 1`), so `I_s` reduces to: every triple repeat has length `<= L - 2`, and
no two repeats of length `>= L - 1` are interleaved.  The general definition is
still evaluated verbatim by `assert` statements against a brute-force predicate.

Usage:
    python3 scripts/verify_samelength62_tie_search_211.py            # quick
    python3 scripts/verify_samelength62_tie_search_211.py --full     # wide
"""

from __future__ import annotations

import argparse
import itertools
import sys
from collections import defaultdict
from typing import Dict, FrozenSet, List, Sequence, Set, Tuple

VERBOSE = False


def log(message: str) -> None:
    if VERBOSE:
        print(message, file=sys.stderr)


# ---------------------------------------------------------------- word layer


def cyc(S: Sequence[int], i: int) -> int:
    return S[i % len(S)]


def window(S: Sequence[int], e: int, r: int) -> Tuple[int, ...]:
    return tuple(cyc(S, r + d) for d in range(e))


def support(S: Word, L: int) -> FrozenSet[Word]:
    return frozenset(window(S, L, r) for r in range(len(S)))


def spec(S: Word, L: int) -> Dict[Word, int]:
    out: Dict[Word, int] = defaultdict(int)
    for r in range(len(S)):
        out[window(S, L, r)] += 1
    return dict(out)


def rotations(S: Word) -> Set[Word]:
    n = len(S)
    return {S[k:] + S[:k] for k in range(n)}


# ------------------------------------------------- SourceFaithfulIs (literal)


def preceding(S: Word, t: int) -> int:
    return cyc(S, t + len(S) - 1)


def following(S: Word, e: int, t: int) -> int:
    return cyc(S, t + e)


def is_repeat(S: Word, e: int, a: int, b: int) -> bool:
    G = len(S)
    if not (1 <= e < G and a != b):
        return False
    return (
        window(S, e, a) == window(S, e, b)
        and preceding(S, a) != preceding(S, b)
        and following(S, e, a) != following(S, e, b)
    )


def is_triple_repeat(S: Word, e: int, a: int, b: int, c: int) -> bool:
    G = len(S)
    if not (1 <= e < G and a != b and a != c and b != c):
        return False
    if window(S, e, a) != window(S, e, b) or window(S, e, a) != window(S, e, c):
        return False
    if preceding(S, a) == preceding(S, b) == preceding(S, c):
        return False
    if following(S, e, a) == following(S, e, b) == following(S, e, c):
        return False
    return True


def bridges_copy(S: Word, L: int, R: FrozenSet[int], e: int, t: int) -> bool:
    G = len(S)
    for r in R:
        for d in range(L):
            if d + e + 1 < L and (r + d + 1) % G == t:
                return True
    return False


def covers(S: Word, L: int, R: FrozenSet[int]) -> bool:
    G = len(S)
    for p in range(G):
        if not any(any(p == (r + d) % G for d in range(L)) for r in R):
            return False
    return True


def in_open_arc(G: int, a: int, b: int, p: int) -> bool:
    return 0 < (p + G - a) % G < (b + G - a) % G


def interleaved(G: int, a: int, b: int, c: int, d: int) -> bool:
    if len({a, b, c, d}) != 4:
        return False
    return in_open_arc(G, a, b, c) != in_open_arc(G, a, b, d)


def information_feasible_bruteforce(S: Word, L: int, R: FrozenSet[int]) -> bool:
    """The literal `SourceFaithfulIs.InformationFeasible`, verbatim."""
    if not covers(S, L, R):
        return False
    G = len(S)
    for e in range(1, G):
        for a in range(G):
            for b in range(G):
                for c in range(G):
                    if is_triple_repeat(S, e, a, b, c):
                        if not all(bridges_copy(S, L, R, e, t) for t in (a, b, c)):
                            return False
    pairs = [
        (e, a, b)
        for e in range(1, G)
        for a in range(G)
        for b in range(G)
        if is_repeat(S, e, a, b)
    ]
    for e1, a, b in pairs:
        for e2, c, d in pairs:
            if interleaved(G, a, b, c, d):
                if not any(
                    bridges_copy(S, L, R, x, t)
                    for x, t in ((e1, a), (e1, b), (e2, c), (e2, d))
                ):
                    return False
    return True


def triple_repeats_long(S: Word, band_lo: int) -> bool:
    """Some triple repeat of length >= band_lo (used with band_lo = L - 1)."""
    G = len(S)
    for e in range(band_lo, G):
        for a, b, c in itertools.combinations(range(G), 3):
            if is_triple_repeat(S, e, a, b, c):
                return True
    return False


def long_repeat_interleaved(S: Word, band_lo: int) -> bool:
    G = len(S)
    pairs = [
        (e, a, b)
        for e in range(band_lo, G)
        for a in range(G)
        for b in range(G)
        if is_repeat(S, e, a, b)
    ]
    for e1, a, b in pairs:
        for e2, c, d in pairs:
            if interleaved(G, a, b, c, d):
                return True
    return False


def information_feasible_univ(S: Word, L: int) -> bool:
    """`I_s` at `R = univ`; cross-checked against the brute-force predicate."""
    assert not triple_repeats_long(S, L - 1)
    assert not long_repeat_interleaved(S, L - 1)
    assert not triple_repeats_long(S, L - 1) and not long_repeat_interleaved(S, L - 1)
    return not triple_repeats_long(S, L - 1) and not long_repeat_interleaved(S, L - 1)


# -------------------------------------------------------------- fibre / tie


def orbit_count(group: Sequence[Word]) -> int:
    """Number of rotation orbits inside a set of words of common length."""
    remaining = set(group)
    orbits = 0
    while remaining:
        w = next(iter(remaining))
        rots = rotations(w)
        assert rots <= set(group), "rotation of a member must stay in the group"
        remaining -= rots
        orbits += 1
    return orbits


def scan(G: int, L: int, q: int, brute_check: bool = False) -> List[str]:
    words: List[Word] = list(itertools.product(range(q), repeat=G))
    univ: FrozenSet[int] = frozenset(range(G))

    # group by complete spectrum
    by_spec: Dict[Tuple[Tuple[Word, int], ...], List[Word]] = defaultdict(list)
    for w in words:
        key = tuple(sorted(spec(w, L).items()))
        by_spec[key].append(w)

    feasible = 0
    findings: List[str] = []
    for S in words:
        if triple_repeats_long(S, L - 1) or long_repeat_interleaved(S, L - 1):
            continue
        if brute_check:
            assert information_feasible_bruteforce(S, L, univ)
        feasible += 1
        key = tuple(sorted(spec(S, L).items()))
        group = by_spec[key]
        # support class of S inside the spectrum fibre
        sup = support(S, L)
        fibre = [D for D in group if support(D, L) == sup]
        orbits = orbit_count(fibre)
        if orbits > 1:
            findings.append(
                f"TIE G={G} L={L} q={q} S={S} spec={key} orbits={orbits}\n"
                f"    fibre={sorted(fibre)}"
            )
    return findings


def main() -> int:
    global VERBOSE
    ap = argparse.ArgumentParser()
    ap.add_argument("--full", action="store_true")
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args()
    VERBOSE = args.verbose

    scopes: List[Tuple[int, int, int]]
    if args.full:
        scopes = [
            (G, L, q)
            for q in (2, 3)
            for G in range(2, (14 if q == 2 else 9) + 1)
            for L in range(2, G + 1)
        ]
    else:
        scopes = [
            (G, L, q)
            for q in (2, 3)
            for G in range(2, (10 if q == 2 else 8) + 1)
            for L in range(2, G + 1)
        ]

    # brute-force cross-check of the specialized `univ` predicate on a small scope
    for (G, L, q) in [(6, 2, 2), (5, 3, 2), (7, 3, 2), (6, 4, 2)]:
        for S in itertools.product(range(q), repeat=G):
            fast = not (triple_repeats_long(S, L - 1) or long_repeat_interleaved(S, L - 1))
            slow = information_feasible_bruteforce(S, L, frozenset(range(G)))
            assert fast == slow, (S, G, L, fast, slow)
    print("cross-check: specialized I_s(univ) predicate == brute force ... ok")

    total_feasible = 0
    total_ties = 0
    for (G, L, q) in scopes:
        # skip hopelessly expensive scopes
        if q ** G > 200000:
            log(f"skip G={G} L={L} q={q}")
            continue
        findings = scan(G, L, q)
        total_ties += len(findings)
        for f in findings:
            print(f)
        print(f"G={G:2d} L={L:2d} q={q}: scoped, ties={len(findings)}")
    print(f"# total distinct tied-maximizer witnesses: {total_ties}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
