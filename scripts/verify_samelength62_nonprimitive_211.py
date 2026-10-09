#!/usr/bin/env python3
"""Corrected nonprimitive analysis for #211.

The note docs/same-length-62-tie-uniqueness-211.md §4 claims "P2 forces k = 2".
This script checks that claim and the corrected structural claims:

  A. counterexample_to_k2: a nonprimitive I_s-feasible word with k >= 3 and P2.
  B. no_branching: every nonprimitive P2 word has each (L-1)-mer followed by a
     unique symbol (deterministic successor).
  C. single_cycle: the successor map on distinct (L-1)-mers is one cycle.
  D. fibre_singleton: the L-spectrum fibre is a singleton up to rotation.
"""

from __future__ import annotations

import itertools
import sys
from collections import defaultdict
from typing import Dict, FrozenSet, List, Sequence, Set, Tuple

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


def has_long_triple(S: Word, L: int) -> bool:
    G = len(S)
    for e in range(L - 1, G):
        for a, b, c in itertools.combinations(range(G), 3):
            if is_triple_repeat(S, e, a, b, c):
                return True
    return False


def has_long_interleaved(S: Word, L: int) -> bool:
    G = len(S)
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
                return True
    return False


def P2(S: Word, L: int) -> bool:
    return not has_long_triple(S, L) and not has_long_interleaved(S, L)


def is_primitive(S: Word) -> bool:
    G = len(S)
    return len(rotations(S)) == G


def primitive_root_power(S: Word) -> Tuple[Word, int]:
    G = len(S)
    for p in range(1, G):
        if G % p == 0:
            k = G // p
            root = S[:p]
            if all(S[i] == root[i % p] for i in range(G)):
                if is_primitive(root):
                    return root, k
    raise ValueError("no primitive root")


def fibre(S: Word, L: int, alphabet: int) -> List[Word]:
    G = len(S)
    target = spec(S, L)
    out = []
    for tup in itertools.product(range(alphabet), repeat=G):
        if spec(tup, L) == target:
            out.append(tup)
    return out


def branching(S: Word, L: int) -> bool:
    """Some (L-1)-mer is followed by two distinct symbols."""
    G = len(S)
    if L - 1 < 1:
        return False
    seen: Dict[Word, Set[int]] = defaultdict(set)
    for r in range(G):
        v = window(S, L - 1, r)
        seen[v].add(cyc(S, r + L - 1))
    return any(len(foll) > 1 for foll in seen.values())


def successor_single_cycle(S: Word, L: int) -> bool:
    """The successor map on distinct (L-1)-mers is a single cycle."""
    G = len(S)
    if L - 1 < 1:
        return False
    succ: Dict[Word, Word] = {}
    for r in range(G):
        v = window(S, L - 1, r)
        nxt = window(S, L - 1, r + 1)
        if v in succ and succ[v] != nxt:
            return False
        succ[v] = nxt
    if not succ:
        return False
    start = next(iter(succ))
    cur = start
    for _ in range(len(succ)):
        cur = succ[cur]
    return cur == start


def check(alphabet: int, Gmax: int) -> None:
    counter_k2 = 0
    branch_fail = 0
    cycle_fail = 0
    fibre_fail = 0
    total = 0
    for G in range(2, Gmax + 1):
        for tup in itertools.product(range(alphabet), repeat=G):
            if is_primitive(tup):
                continue
            for L in range(2, G + 1):
                if not P2(tup, L):
                    continue
                total += 1
                root, k = primitive_root_power(tup)
                if k >= 3:
                    counter_k2 += 1
                    if counter_k2 <= 3:
                        print(f"  k>=3 counterexample: S={tup} L={L} root={root} k={k}")
                if branching(tup, L):
                    branch_fail += 1
                    if branch_fail <= 3:
                        print(f"  BRANCHING: S={tup} L={L}")
                if not successor_single_cycle(tup, L):
                    cycle_fail += 1
                    if cycle_fail <= 3:
                        print(f"  NOT SINGLE CYCLE: S={tup} L={L}")
                fib = fibre(tup, L, alphabet)
                if len(rotations(tup)) != len({r for w in fib for r in rotations(w)}):
                    fibre_fail += 1
                    if fibre_fail <= 3:
                        print(f"  FIBRE NOT SINGLETON: S={tup} L={L} fibre={fib}")
    print(f"alphabet={alphabet} G<={Gmax}: {total} nonprimitive P2 (S,L) pairs")
    print(f"  k>=3 counterexamples : {counter_k2}")
    print(f"  branching failures   : {branch_fail}")
    print(f"  non-single-cycle     : {cycle_fail}")
    print(f"  fibre not singleton  : {fibre_fail}")


if __name__ == "__main__":
    print("=== binary, G <= 10 ===")
    check(2, 10)
    print("=== ternary, G <= 8 ===")
    check(3, 8)
