#!/usr/bin/env python3
"""Exhaustive check of the #89 raw-node-chord refutation (issue #89).

Word: S = 00101, G = 5, L = 3.  Claim checked here:

  * `S` satisfies the repository's P2 (`def:P1P2`) at read length L = 3;
  * the length-`(L-1)` = 2 mers `01` and `10` are each repeated, at the
    *crossing* pairs of starts {1,3} and {2,4};
  * neither pair is a maximal repeat (`IsRepeat` fails: {1,3} agrees on the
    following symbol, {2,4} agrees on the preceding symbol).

Consequence: crossing of raw `(L-1)`-mer pairs is compatible with P2, so the
"#89 route" instantiates of chords as raw node pairs cannot work; the argument
has to be organized around maximal-repeat blocks.  The crossing and
non-maximality parts are kernel-checked in
`AssemblyP1/BBTChords.lean` (`raw_node_crossing_not_maximal`); the P2 part is
checked here because the P2 predicate is not decidable by `decide` at this
quantifier depth in Lean (see the doc note).

Run:  python3 scripts/verify_raw_node_chord_refutation.py
"""

from itertools import combinations

S = [0, 0, 1, 0, 1]
G = 5
L = 3


def sym(i):
    return S[i % G]


def mers(e, r):
    return tuple(sym(r + d) for d in range(e))


def precedes(r):
    return sym(r + G - 1)


def follows(e, r):
    return sym(r + e)


def is_repeat(e, a, b):
    return (
        1 <= e < G
        and a != b
        and mers(e, a) == mers(e, b)
        and precedes(a) != precedes(b)
        and follows(e, a) != follows(e, b)
    )


def is_triple_repeat(e, a, b, c):
    return (
        1 <= e < G
        and mers(e, a) == mers(e, b) == mers(e, c)
        and not (precedes(a) == precedes(b) == precedes(c))
        and not (follows(e, a) == follows(e, b) == follows(e, c))
    )


def in_arc(a, b, p):
    return 0 < (p - a) % G < (b - a) % G


def interleaved(a, b, c, d):
    distinct = all(x != y for x, y in [(a, b), (a, c), (a, d), (b, c), (b, d), (c, d)])
    return distinct and (in_arc(a, b, c) != in_arc(a, b, d))


def p2(L):
    """`P2` of `def:P1P2` at read length `L`, verbatim."""
    for e in range(1, G):
        for a, b, c in combinations(range(G), 3):
            if is_triple_repeat(e, a, b, c) and not e < L - 1:
                return False, ("triple", e, a, b, c)
    for e1 in range(1, G):
        for e2 in range(1, G):
            for a, b in combinations(range(G), 2):
                if not is_repeat(e1, a, b):
                    continue
                for c, d in combinations(range(G), 2):
                    if not is_repeat(e2, c, d):
                        continue
                    if interleaved(a, b, c, d) and not (e1 <= L - 2 or e2 <= L - 2):
                        return False, ("interleaved", e1, e2, a, b, c, d)
    return True, None


def main():
    ok, why = p2(L)
    print(f"P2 satisfied at L={L}: {ok} ({why})")
    assert ok, why

    repeated = mers(2, 1) == mers(2, 3) and mers(2, 2) == mers(2, 4)
    print(f"two repeated length-2 mers at {{1,3}} and {{2,4}}: {repeated}")
    assert repeated

    cross = interleaved(1, 3, 2, 4)
    print(f"the two pairs cross (interleave): {cross}")
    assert cross

    print(f"IsRepeat(2, 1, 3): {is_repeat(2, 1, 3)}")
    print(f"IsRepeat(2, 2, 4): {is_repeat(2, 2, 4)}")
    assert not is_repeat(2, 1, 3)
    assert not is_repeat(2, 2, 4)

    print("OK: raw (L-1)-mer node chords cross under P2, so they cannot be the")
    print("    objects the P2 interleaved clause controls.")


if __name__ == "__main__":
    main()
