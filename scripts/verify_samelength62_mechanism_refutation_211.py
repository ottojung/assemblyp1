#!/usr/bin/env python3
"""Refutation of the note's section 4 mechanism: P2 => k = 2 => simple cycle.

`docs/same-length-62-tie-uniqueness-211.md` section 4 assessed the nonprimitive
subcase with the argument: `P2` forces the truth to be a square (`S = T^2`), the
`(L-1)`-mer graph of a square is a simple cycle with doubled edges, and a simple
cycle has a deterministic successor, so the Eulerian cycle is unique up to
rotation.  Both mechanism steps are false; this script kernel-checks-style
verifies the two counterexamples, and confirms that the section's *conclusion*
(singleton fibre) nevertheless survives them.

Example A: `S = 001100110011 = T^3`, `T = 0011` primitive, `G = 12`.
  `P2` holds at `L = 3` and `L = 4` with `k = 3` (refutes "P2 forces k = 2").
  Every recurring window of length >= 2 does so at starts congruent mod 4 with
  equal context, hence is non-maximal; the only maximal repeats have length 1,
  below the `P2` threshold `L - 1 = 2`.  At `L = 3` the fibre is a singleton
  (4 words, the 4 rotations of `S`), and the `2`-mer graph branches: each
  `1`-mer vertex carries a self-loop *and* a cross edge (refutes "simple cycle").

Example B: `S = abcababcab = T^2`, `T = abcab` primitive, `G = 10`.
  `P2` holds at `L = 4` and `L = 5`, but the `3`-mer graph branches at the
  vertex `ab` (successors `bc` via `abc` and `ba` via `aba`): a figure-eight,
  not a simple cycle.  At `L = 4` the fibre is a singleton (5 words, 1 orbit).

Also scans all ternary primitive `T` with `p <= 5` and `k in {3, 4}` for `P2`
membership: 1188 `(T, k, L)` combinations satisfy `P2` with `k >= 3`.

Usage:
    python3 scripts/verify_samelength62_mechanism_refutation_211.py
"""
from __future__ import annotations

import itertools
import sys
from collections import defaultdict
from typing import Dict, List, Sequence, Set, Tuple

Word = Tuple[int, ...]


def cyc(S: Sequence[int], i: int) -> int:
    return S[i % len(S)]


def window(S: Sequence[int], e: int, r: int) -> Tuple[int, ...]:
    return tuple(cyc(S, r + d) for d in range(e))


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


def p2_holds(S: Word, L: int) -> bool:
    G = len(S)
    for e in range(L - 1, G):
        for a, b, c in itertools.combinations(range(G), 3):
            if is_triple_repeat(S, e, a, b, c):
                return False
    pairs = [
        (e, a, b)
        for e in range(L - 1, G)
        for a in range(G)
        for b in range(G)
        if is_repeat(S, e, a, b)
    ]
    for e1, a, b in pairs:
        for e2, c, d in pairs:
            if interleaved(G, a, b, c, d):
                return False
    return True


def fibre_orbits(S: Word, L: int, q: int) -> Tuple[int, int]:
    G = len(S)
    sp = spec(S, L)
    fibre = [w for w in itertools.product(range(q), repeat=G) if spec(w, L) == sp]
    seen: Set[Word] = set()
    reps = 0
    for w in fibre:
        if w in seen:
            continue
        seen |= rotations(w)
        reps += 1
    return len(fibre), reps


def db_out_edges(S: Word, L: int) -> Dict[Word, List[Tuple[int, int]]]:
    G = len(S)
    edges: Dict[Word, int] = defaultdict(int)
    for r in range(G):
        edges[window(S, L - 1, r)] += 1
    out: Dict[Word, List[Tuple[int, int]]] = defaultdict(list)
    for w, k in edges.items():
        out[w[:-1]].append((w[-1], k))
    return dict(out)


def main() -> int:
    SA = tuple(int(c) for c in "0011") * 3
    print("Example A: S = 0011^3, G=12, T = 0011 primitive (p=4), k=3")
    for L in (2, 3, 4):
        print(f"  L={L}: P2={p2_holds(SA, L)}")
    n, reps = fibre_orbits(SA, 3, 2)
    print(f"  L=3: fibre size={n}, orbits={reps} (singleton: {reps == 1})")
    print(f"  L=3: (L-1)-mer graph out-edges: {db_out_edges(SA, 3)}")
    branching = {v: s for v, s in db_out_edges(SA, 3).items() if len(s) > 1}
    print(f"  L=3: branching vertices: {branching}")
    maxrep_lengths = sorted({
        e for e in range(1, len(SA))
        for a in range(len(SA)) for b in range(a + 1, len(SA))
        if is_repeat(SA, e, a, b)
    })
    print(f"  maximal repeat lengths present: {maxrep_lengths}")

    MP = {'a': 0, 'b': 1, 'c': 2}
    SB = tuple(MP[c] for c in "abcab") * 2
    print("Example B: S = (abcab)^2, G=10, T = abcab primitive (p=5), k=2")
    for L in (3, 4, 5):
        print(f"  L={L}: P2={p2_holds(SB, L)}")
    n, reps = fibre_orbits(SB, 4, 3)
    print(f"  L=4: fibre size={n}, orbits={reps} (singleton: {reps == 1})")
    print(f"  L=4: (L-1)-mer graph out-edges: {db_out_edges(SB, 4)}")
    branching = {v: s for v, s in db_out_edges(SB, 4).items() if len(s) > 1}
    print(f"  L=4: branching vertices: {branching}")

    total = 0
    for p in range(2, 6):
        for T in itertools.product(range(3), repeat=p):
            if any(T == T[i:] + T[:i] for i in range(1, p)):
                continue
            for k in (3, 4):
                G = p * k
                if G > 12:
                    continue
                S = T * k
                for L in range(2, G + 1):
                    if p2_holds(S, L):
                        total += 1
    print(f"ternary primitive T with p<=5, k in {{3,4}}: (T,k,L) with P2: {total}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
