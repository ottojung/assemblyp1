#!/usr/bin/env python3
"""Independent verification for the structural-ambiguity opening counterexample.

This is the first-failure-mode example in
``docs/structural-ambiguity-two-failure-modes.md`` (issue #46): two genuinely
different circular DNA genomes that have *identical* length-``L`` read
multisets, so no amount of noiseless data distinguishes them.  It is the
classical repeat/read-length obstruction, kept separate from the finite-sample
frequency-fluctuation witnesses (failure mode 2).

The script is self-contained: it re-derives circular spectra, Bresler triple
repeats, and the bridging condition from scratch.  It uses exact integer
arithmetic, is deterministic, and exits non-zero on any failed assertion.

It checks:

  A. The witness ``S = AACAG``, ``D = AAGAC`` (``G = 5``, ``L = 2``) are
     distinct circular words (not equal up to cyclic shift or reverse
     complement) with identical length-1 and length-2 spectra, and hence
     identical likelihood for every observation under any objective that is a
     function of the observed read-type counts.
  B. The read-length boundary: increasing to ``L = 3`` separates the spectra.
  C. Minimality: no distinct circular DNA words collide on length-``L`` spectra
     for ``G <= 4`` with ``L >= 2``; the collision first appears at
     ``G = 5, L = 2``, and every minimal collision has the witness's equality
     pattern up to relabeling and rotation.
  D. The mechanism: ``S`` and ``D`` each carry a Bresler-maximal length-1 triple
     repeat of ``A`` at starts ``{0, 1, 3}``, and a length-``L`` read can bridge
     a copy of a repeat of length ``ell`` only if ``ell <= L - 2``.  At ``L = 2``
     the length-1 copies admit no bridge, which is exactly the critical case
     ``ell = L - 1``.

Usage:
    python3 scripts/verify_structural_ambiguity_opening.py
"""

from __future__ import annotations

import sys
from collections import Counter
from itertools import product

DNA = ("A", "C", "G", "T")
ALPHABETS = {
    "DNA2": ("A", "C"),
    "DNA3": ("A", "C", "G"),
    "DNA4": DNA,
}


# --------------------------------------------------------------------------- #
# Core circular-string primitives.
# --------------------------------------------------------------------------- #


def windows(word: str, L: int) -> list[str]:
    """The ``|word|`` circular windows of length ``L``, in start order."""
    n = len(word)
    return ["".join(word[(i + j) % n] for j in range(L)) for i in range(n)]


def spectrum(word: str, L: int) -> Counter:
    return Counter(windows(word, L))


def rotations(word: str) -> set[str]:
    n = len(word)
    return {word[i:] + word[:i] for i in range(n)}


def reverse_complement(word: str) -> str:
    return word.translate(str.maketrans("ACGT", "TGCA"))[::-1]


def canonical(word: str) -> str:
    """Lexicographically smallest rotation (a circular-word representative)."""
    return min(rotations(word))


def circ(word: str, i: int) -> str:
    return word[i % len(word)]


def equality_pattern(word: str) -> tuple[int, ...]:
    labels: dict[str, int] = {}
    pattern = []
    for ch in word:
        if ch not in labels:
            labels[ch] = len(labels)
        pattern.append(labels[ch])
    return tuple(pattern)


def canonical_pattern(word: str) -> tuple[int, ...]:
    return min(tuple(equality_pattern(rot)) for rot in rotations(word))


# --------------------------------------------------------------------------- #
# Checks.
# --------------------------------------------------------------------------- #


def check_witness() -> tuple[str, str]:
    S, D = "AACAG", "AAGAC"

    assert canonical(S) != canonical(D), "S and D are the same circular word"
    assert canonical(S) != canonical(reverse_complement(D)), (
        "S equals the reverse complement of D up to rotation"
    )

    assert spectrum(S, 1) == spectrum(D, 1), "length-1 spectra differ"
    assert spectrum(S, 2) == spectrum(D, 2), "length-2 spectra differ at the witness"
    expected = Counter({"AA": 1, "AC": 1, "CA": 1, "AG": 1, "GA": 1})
    assert spectrum(S, 2) == expected, spectrum(S, 2)

    # Identical spectra force identical likelihood for every observation.
    # Demonstrate exactly on the population spectrum and on skewed samples.
    samples = [
        Counter({"AA": 1, "AC": 1, "CA": 1, "AG": 1, "GA": 1}),
        Counter({"AA": 5, "AC": 1}),
        Counter({"AC": 2, "GA": 3, "AA": 1}),
    ]
    for x in samples:
        ratio_num = 1
        ratio_den = 1
        for w, count in x.items():
            assert spectrum(S, 2)[w] == spectrum(D, 2)[w]
            ratio_num *= spectrum(D, 2)[w] ** count
            ratio_den *= spectrum(S, 2)[w] ** count
        assert ratio_num == ratio_den, "likelihood ratio is not 1"

    return S, D


def check_read_length_boundary() -> None:
    S, D = "AACAG", "AAGAC"
    assert spectrum(S, 3) != spectrum(D, 3), "L=3 fails to separate the spectra"
    assert set(spectrum(S, 3)) == {"AAC", "ACA", "CAG", "AGA", "GAA"}, spectrum(S, 3)
    assert set(spectrum(D, 3)) == {"AAG", "AGA", "GAC", "ACA", "CAA"}, spectrum(D, 3)
    assert "CAG" in spectrum(S, 3) and "CAG" not in spectrum(D, 3)


def collisions_over(alpha: tuple[str, ...], G: int, L: int) -> list[list[str]]:
    buckets: dict[tuple, list[str]] = {}
    for tup in product(alpha, repeat=G):
        word = "".join(tup)
        if canonical(word) != word:
            continue
        key = tuple(sorted(spectrum(word, L).items()))
        buckets.setdefault(key, []).append(word)
    return [v for v in buckets.values() if len(v) > 1]


def check_minimality() -> None:
    # No collision at G <= 4 for any L >= 2, over every alphabet considered.
    for name, alpha in ALPHABETS.items():
        for G in range(2, 5):
            for L in range(2, G + 1):
                bad = collisions_over(alpha, G, L)
                assert not bad, f"collision in {name} at G={G}, L={L}: {bad[:1]}"

    # At G = 5, L = 2 collisions exist and share the witness's equality pattern
    # (a triple of one symbol, two copies adjacent) up to relabeling/rotation.
    collisions = collisions_over(DNA, 5, 2)
    assert collisions, "no G=5, L=2 collision found"
    patterns = {canonical_pattern(pair[0]) for pair in collisions}
    assert patterns == {(0, 0, 1, 0, 2)}, patterns


def bresler_triples(word: str, L: int) -> list[tuple[int, tuple[int, int, int]]]:
    """Maximal Bresler triple repeats of length >= 1.

    A triple repeat selects three distinct starts carrying an equal length-ell
    circular window whose preceding symbols are not all equal and whose
    following symbols are not all equal.
    """
    n = len(word)
    out = []
    for ell in range(1, L + 1):
        by_window: dict[str, list[int]] = {}
        for i in range(n):
            win = "".join(circ(word, i + k) for k in range(ell))
            by_window.setdefault(win, []).append(i)
        for starts in by_window.values():
            if len(starts) < 3:
                continue
            for a in range(len(starts)):
                for b in range(a + 1, len(starts)):
                    for c in range(b + 1, len(starts)):
                        i, j, k = starts[a], starts[b], starts[c]
                        prev = {circ(word, i - 1), circ(word, j - 1), circ(word, k - 1)}
                        nxt = {
                            circ(word, i + ell),
                            circ(word, j + ell),
                            circ(word, k + ell),
                        }
                        if len(prev) > 1 and len(nxt) > 1:
                            out.append((ell, (i, j, k)))
    return out


def bridges(reads: list[int], copy_t: int, ell: int, L: int, n: int) -> bool:
    """Does some realized read strictly extend beyond the copy on both sides?

    A read at lift position ``r`` occupies ``[r, r + L)``; the copy at lift
    position ``t`` occupies ``[t, t + ell)``.  Bridging is ``r < t`` and
    ``t + ell < r + L``, checked over a two-period lift of the circle.
    """
    for r0 in reads:
        for r in (r0, r0 + n):
            for t in (copy_t, copy_t + n):
                if r < t and t + ell < r + L:
                    return True
    return False


def check_critical_triple() -> None:
    S, D = "AACAG", "AAGAC"
    L = 2
    n = len(S)
    for word in (S, D):
        triples = bresler_triples(word, L=2)
        assert (1, (0, 1, 3)) in triples, (word, triples)
        assert all(ell == 1 for ell, _ in triples), (word, triples)

        # The read realization that samples every window once.
        starts = list(range(n))
        for t in range(n):
            assert not bridges(starts, t, ell=1, L=L, n=n), (
                f"a length-{L} read bridges the length-1 copy at {t}"
            )

    # Positive control: at L = 3 the same length-1 copies can be bridged.
    L3 = 3
    started = any(
        bridges(list(range(n)), t, ell=1, L=L3, n=n) for t in range(n)
    )
    assert started, "no length-3 read bridges any length-1 copy"
    assert 1 <= L3 - 2


def main(argv: list[str]) -> int:
    S, D = check_witness()
    print(f"[A] witness {S} / {D}: distinct circular words, identical L=1 and L=2 spectra")
    check_read_length_boundary()
    print("[B] read-length boundary: L=3 separates the two spectra")
    check_minimality()
    print("[C] minimality: no collision for G<=4, L>=2; minimal collision at G=5, L=2")
    check_critical_triple()
    print("[D] mechanism: maximal length-1 triple repeat, unbridgeable at L=2 (ell = L-1)")
    print("all structural-ambiguity opening checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
