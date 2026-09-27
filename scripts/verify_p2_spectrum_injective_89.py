#!/usr/bin/env python3
"""Is the complete L-spectrum injective up to rotation on the `P2` class? (#89)

Why this script exists
----------------------
`AssemblyP1.BBTEulerian.EulerianCycleObstruction` is the last unproved input of
`population_unique_ML_up_to_rotation`: an `Ukkonen` (hence `P2`) truth plus an
equal-spectrum candidate must be rotation-equivalent.  The whole reduction
chain around it is kernel-checked, so the only question is whether the
statement itself is true *and* whether its `Ukkonen`/`P2` hypothesis is
load-bearing, i.e. whether the theorem is false without it.

Two things are checked here, both exhaustively over all words of a given
alphabet and length (no sampling):

1. `spec_ambiguous`: the number of rotation classes sharing a complete
   `L`-spectrum, and how many of those classes have **all** members in `P2`.
   If a class of all-`P2` members existed, `EulerianCycleObstruction` would be
   false and the whole packet would have to be refuted instead of proved.
2. `p2_injective`: for words in `P2` only, the number of `L`-spectrum classes
   with more than one rotation class.  This is the statement the theorem
   asserts; `0` is the expected answer.

The `P2` test is the repository's own `SourceFaithfulIs` predicate, read off
the Lean definitions:

* `IsRepeat e a b`  = `1 ≤ e ∧ e < n ∧ a ≠ b ∧ agree e a b`
  `∧ preceding a ≠ preceding b ∧ following e a ≠ following e b`;
* `IsTripleRepeat e a b c` = the three starts pairwise distinct, pairwise
  `agree e`, and neither the preceding nor the following symbols all equal;
* `Interleaved a b c d` = the four starts pairwise distinct, and `c` lies in
  the open clockwise arc from `a` to `b` exactly when `d` does not;
* `P2` = no `IsTripleRepeat` of length `≥ L-1` and no `Interleaved` pair of
  `IsRepeat`s both of length `≥ L-1`.

Result (this run, `alphabet 2`, `G = 6 … 9`, all `2 ≤ L ≤ G`):

* 62 ambiguous `L`-spectrum classes overall, and **0** of them have all
  members in `P2`: every collision is excluded by the repeat hypothesis;
* on the `P2` class the `L`-spectrum is injective up to rotation in every
  one of the 25 `(G, L)` pairs (e.g. `G = 9`: 512 `P2` words in 60 spectrum
  classes, 0 collisions);
* the sample collision `S = 001101`, `E = 001011` at `G = 6`, `L = 3`
  (both have each of the six binary 3-mers once) is excluded by the
  **interleaved** clause, not the triple-repeat clause: `S` has interleaved
  maximal repeats `(e,a,b) = (2,1,4)` and `(2,3,5)`, and `E` has
  `(2,1,3)` and `(2,2,5)`.

This is evidence, not a proof: the completeness of the search is not itself
proved, and `G ≤ 9` is tiny.  What it does establish is that the residual is
not a tautology, and that the interleaved clause of `P2` is the load-bearing
part of the hypothesis.  See `docs/bbt-residual-89-rematch2.md` §1.
"""

from __future__ import annotations

from collections import defaultdict
from itertools import combinations, product


def rot(w, k):
    return w[k:] + w[:k]


def necklace(w):
    n = len(w)
    return min(rot(w, k) for k in range(n))


def spec(w, L):
    n = len(w)
    d = defaultdict(int)
    for i in range(n):
        d[tuple(w[(i + j) % n] for j in range(L))] += 1
    return tuple(sorted(d.items()))


def agree(w, e, a, b):
    n = len(w)
    return all(w[(a + d) % n] == w[(b + d) % n] for d in range(e))


def preceding(w, a):
    n = len(w)
    return w[(a + n - 1) % n]


def following(w, e, a):
    n = len(w)
    return w[(a + e) % n]


def is_repeat(w, e, a, b):
    n = len(w)
    return (
        1 <= e < n
        and a != b
        and agree(w, e, a, b)
        and preceding(w, a) != preceding(w, b)
        and following(w, e, a) != following(w, e, b)
    )


def is_triple_repeat(w, e, a, b, c):
    n = len(w)
    return (
        1 <= e < n
        and len({a, b, c}) == 3
        and agree(w, e, a, b)
        and agree(w, e, a, c)
        and agree(w, e, b, c)
        and not (preceding(w, a) == preceding(w, b) == preceding(w, c))
        and not (following(w, e, a) == following(w, e, b) == following(w, e, c))
    )


def in_open_arc(w, a, b, p):
    n = len(w)
    return 0 < (p + n - a) % n < (b + n - a) % n


def interleaved(w, a, b, c, d):
    if len({a, b, c, d}) != 4:
        return False
    return in_open_arc(w, a, b, c) != in_open_arc(w, a, b, d)


def is_p2(w, L):
    """`AssemblyP1.P2.P2` read off the `SourceFaithfulIs` predicates."""
    n = len(w)
    K = L - 1
    for e in range(K, n):
        for a, b, c in combinations(range(n), 3):
            if is_triple_repeat(w, e, a, b, c):
                return False
    reps = [
        (e, a, b)
        for e in range(1, n)
        for a, b in combinations(range(n), 2)
        if is_repeat(w, e, a, b)
    ]
    for (e1, a, b), (e2, c, d) in combinations(reps, 2):
        if e1 >= K and e2 >= K and interleaved(w, a, b, c, d):
            return False
    return True


def report(k, G, verbose=False):
    ambiguous = 0
    ambiguous_all_p2 = 0
    p2_words = 0
    p2_classes = defaultdict(set)
    for L in range(2, G + 1):
        groups = defaultdict(set)
        p2_of = {}
        for w in product(range(k), repeat=G):
            groups[spec(w, L)].add(necklace(w))
            p2_of[necklace(w)] = is_p2(list(w), L)
        for s, vs in groups.items():
            if len(vs) > 1:
                ambiguous += 1
                if all(p2_of[v] for v in vs):
                    ambiguous_all_p2 += 1
                    if verbose:
                        print(f"  COUNTEREXAMPLE a={k} G={G} L={L}: {sorted(vs)}")
        for w in product(range(k), repeat=G):
            if is_p2(list(w), L):
                p2_words += 1
                p2_classes[(L, spec(w, L))].add(necklace(w))
    collisions = sum(1 for v in p2_classes.values() if len(v) > 1)
    print(
        f"a={k} G={G}: ambiguous spectrum classes={ambiguous}, "
        f"of which all-P2={ambiguous_all_p2}; "
        f"on P2: {p2_words} word instances in {len(p2_classes)} classes, "
        f"collisions={collisions}"
    )
    return ambiguous, ambiguous_all_p2, collisions


def main():
    total_amb = total_all_p2 = total_col = 0
    for k, G in ((2, 6), (2, 7), (2, 8), (2, 9)):
        amb, all_p2, col = report(k, G)
        total_amb += amb
        total_all_p2 += all_p2
        total_col += col
    print(
        f"TOTAL: ambiguous={total_amb}, all-P2 ambiguous={total_all_p2}, "
        f"P2-class collisions={total_col}"
    )
    assert total_col == 0, "a collision inside the P2 class refutes the residual"
    print("no collision inside the P2 class: the residual is not a tautology")


if __name__ == "__main__":
    main()
