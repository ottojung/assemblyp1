#!/usr/bin/env python3
"""Exhaustive small-case check of the invariance claims used in
docs/source-notes/equivalence-and-tie-wellposedness.md.

For a circular candidate word `D` and a read length `L`, the exact read-count
likelihood of Medvedev-Brudno 2009 SS6.1 depends on `D` only through the length
`N(D)` and the occurrence counts of the length-`L` read types.  This script
checks, over all small circular words:

  (1) rotation:     occ(rot(D), t) = occ(D, t)            (oriented types)
  (2) revcomp:      occ(rc(D), t)   = occ(D, rc(t))       (oriented types)
  (3) molecule:     occ_class(rc(D), [t]) = occ_class(D, [t])
  (4) non-symmetry: for oriented types there exist D, t with
                    occ(rc(D), t) != occ(D, t)  (so rc is not a statistic
                    symmetry unless types are collapsed into rc classes)

Consequences (1) and (4) are what the note calls forced cyclic-shift
invariance and read-type/equivalence coupling.

Run:  python3 scripts/verify_equivalence_coupling.py
"""

from __future__ import annotations

from collections import Counter
from itertools import product

COMPLEMENTS = {
    "AT": {"A": "T", "T": "A"},
    "ACGT": {"A": "T", "T": "A", "C": "G", "G": "C"},
}


def rc_word(w: str, comp: dict[str, str]) -> str:
    return "".join(comp[c] for c in reversed(w))


def rotate(d: str) -> str:
    return d[1:] + d[:1]


def windows(d: str, length: int) -> list[str]:
    n = len(d)
    return ["".join(d[(i + j) % n] for j in range(length)) for i in range(n)]


def oriented_counts(d: str, length: int) -> Counter[str]:
    return Counter(windows(d, length))


def molecule_counts(d: str, length: int, comp: dict[str, str]) -> Counter[str]:
    """Counts of reverse-complement classes, represented by the canonical
    (lexicographically smaller) representative of each class."""
    out: Counter[str] = Counter()
    for w, k in oriented_counts(d, length).items():
        out[min(w, rc_word(w, comp))] += k
    return out


def main() -> int:
    checked = 0
    for name, comp in COMPLEMENTS.items():
        symbols = sorted(comp)
        max_n = 6 if name == "AT" else 5
        for n in range(1, max_n + 1):
            for tup in product(symbols, repeat=n):
                d = "".join(tup)
                for length in range(1, n + 1):
                    ori = oriented_counts(d, length)
                    mol = molecule_counts(d, length, comp)

                    # (1) rotation invariance of the oriented count vector
                    assert oriented_counts(rotate(d), length) == ori, (d, length)

                    # (2) reverse complement acts by relabelling oriented types
                    rc = rc_word(d, comp)
                    rc_counts = oriented_counts(rc, length)
                    for t, k in rc_counts.items():
                        assert ori[rc_word(t, comp)] == k, (d, length, t)

                    # (3) molecule-class counts are reverse-complement invariant
                    assert molecule_counts(rc, length, comp) == mol, (d, length)

                    checked += 1

    # (4) explicit non-symmetry of the oriented statistic
    witness = "AAAT"
    comp = COMPLEMENTS["AT"]
    oriented = oriented_counts(witness, 1)
    rc_oriented = oriented_counts(rc_word(witness, comp), 1)
    assert oriented != rc_oriented, (witness, oriented, rc_oriented)

    print(f"checked {checked} (circular word, read length) pairs")
    print(f"oriented non-symmetry witness: {witness} counts={dict(oriented)} "
          f"vs rc({witness}) counts={dict(rc_oriented)}")
    print("equivalence-coupling checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
