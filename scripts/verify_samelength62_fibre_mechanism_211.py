#!/usr/bin/env python3
"""MECHANISM for AssemblyP1 issue #211: why `I_s` leaves no tied maximizer.

`AssemblyP1.MLEscape.Is_spectrum_eq_of_support_eq` (kernel-checked) shows that
for an information-feasible truth every same-length word with the truth's window
support has the truth's spectrum.  So the tied maximizers of the exact
same-length Medvedev-Brudno objective are exactly the rotation classes in the
fibre of the truth's complete spectrum `c = specCount S` -- the same fibre that
`docs/exact-same-length-spectrum-fibre-count.md` counts with the BEST theorem.
A second tied genome exists iff that fibre has at least two rotation orbits.

This script tests the reduction that would close the uniqueness reading:

    (NON-UNIQUE)  the fibre of `specCount S` has >= 2 rotation orbits
        ==>  S carries either a triple repeat of length >= L - 1
            or two repeats of length >= L - 1 that interleave,

i.e. every word with a non-rigid spectrum fibre violates one of the two
length-sensitive clauses of `SourceFaithfulIs.InformationFeasible`.  Since
`SourceFaithfulIs.bridgesCopy_length` gives `e + 2 <= L` for every bridged copy,
an `I_s`-feasible truth can have neither, so `I_s` would force fibre singularity
and hence uniqueness of the maximizer up to rotation.

The converse direction needed for the residue statement is separately recorded:
`AssemblyP1.SameLength62TieUniqueness.bbt_premise_refuted_G6_L2` (kernel-checked)
shows that without `I_s` the fibre has two orbits at `G = 6`, `L = 2`.

Usage:
    python3 scripts/verify_samelength62_fibre_mechanism_211.py          # quick
    python3 scripts/verify_samelength62_fibre_mechanism_211.py --full   # wide
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


def cyc(S: Sequence[int], i: int) -> int:
    return S[i % len(S)]


def window(S: Sequence[int], e: int, r: int) -> Tuple[int, ...]:
    return tuple(cyc(S, r + d) for d in range(e))


def support(S: "Word", L: int) -> FrozenSet[Word]:
    return frozenset(window(S, L, r) for r in range(len(S)))


def spec(S: Word, L: int) -> Dict[Word, int]:
    out: Dict[Word, int] = defaultdict(int)
    for r in range(len(S)):
        out[window(S, L, r)] += 1
    return dict(out)


def rotations(S: Word) -> Set[Word]:
    n = len(S)
    return {S[k:] + S[:k] for k in range(n)}


def is_repeat(S: Word, e: int, a: int, b: int) -> bool:
    G = len(S)
    if not (1 <= e < G and a != b):
        return False
    return (
        window(S, e, a) == window(S, e, b)
        and cyc(S, a + G - 1) != cyc(S, b + G - 1)
        and cyc(S, a + e) != cyc(S, b + e)
    )


def is_triple_repeat(S: Word, e: int, a: int, b: int, c: int) -> bool:
    G = len(S)
    if not (1 <= e < G and a != b and a != c and b != c):
        return False
    if window(S, e, a) != window(S, e, b) or window(S, e, a) != window(S, e, c):
        return False
    if cyc(S, a + G - 1) == cyc(S, b + G - 1) == cyc(S, c + G - 1):
        return False
    if cyc(S, a + e) == cyc(S, b + e) == cyc(S, c + e):
        return False
    return True


def in_open_arc(G: int, a: int, b: int, p: int) -> bool:
    return 0 < (p + G - a) % G < (b + G - a) % G


def interleaved(G: int, a: int, b: int, c: int, d: int) -> bool:
    if len({a, b, c, d}) != 4:
        return False
    return in_open_arc(G, a, b, c) != in_open_arc(G, a, b, d)


def long_triple_repeat(S: Word, band_lo: int) -> bool:
    G = len(S)
    for e in range(band_lo, G):
        for a, b, c in itertools.combinations(range(G), 3):
            if is_triple_repeat(S, e, a, b, c):
                return True
    return False


def long_interleaved_repeats(S: Word, band_lo: int) -> bool:
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


def violates_I_s_length_clauses(S: Word, L: int) -> bool:
    """Something `I_s` cannot bridge: a long triple, or interleaved long repeats."""
    return long_triple_repeat(S, L - 1) or long_interleaved_repeats(S, L - 1)


def orbit_representatives(group: Sequence[Word]) -> List[Word]:
    seen: Set[Word] = set()
    reps: List[Word] = []
    for w in group:
        if w in seen:
            continue
        seen |= rotations(w)
        reps.append(w)
    return reps


def scan(G: int, L: int, q: int) -> Tuple[int, int, List[str]]:
    words: List[Word] = list(itertools.product(range(q), repeat=G))
    by_spec: Dict[Tuple[Tuple[Word, int], ...], List[Word]] = defaultdict(list)
    for w in words:
        by_spec[tuple(sorted(spec(w, L).items()))].append(w)

    nonunique = 0
    unexplained = 0
    notes: List[str] = []
    for S in words:
        key = tuple(sorted(spec(S, L).items()))
        reps = orbit_representatives(by_spec[key])
        if len(reps) < 2:
            continue
        nonunique += 1
        if not violates_I_s_length_clauses(S, L):
            unexplained += 1
            if len(notes) < 12:
                notes.append(
                    f"UNEXPLAINED G={G} L={L} q={q} S={S} orbits={len(reps)}"
                )
    return nonunique, unexplained, notes


def main() -> int:
    global VERBOSE
    ap = argparse.ArgumentParser()
    ap.add_argument("--full", action="store_true")
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args()
    VERBOSE = args.verbose

    gmax = 13 if args.full else 11
    qmax3 = 8 if args.full else 8
    scopes = [
        (G, L, 2)
        for G in range(2, gmax + 1)
        for L in range(2, G + 1)
    ] + [
        (G, L, 3)
        for G in range(2, qmax3 + 1)
        for L in range(2, G + 1)
    ]

    total_nonunique = 0
    total_unexplained = 0
    for (G, L, q) in scopes:
        if q ** G > 400000:
            continue
        nonunique, unexplained, notes = scan(G, L, q)
        total_nonunique += nonunique
        total_unexplained += unexplained
        for n in notes:
            print(n)
        print(
            f"G={G:2d} L={L:2d} q={q}: non-unique-fibre words={nonunique:5d} "
            f"(no I_s length violation {unexplained})"
        )
    print(
        f"# non-unique-fibre words: {total_nonunique}; "
        f"without an I_s length-clause violation: {total_unexplained}"
    )
    return 0 if total_unexplained == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
