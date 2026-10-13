#!/usr/bin/env python3
"""Finite exhaustive regression for MB09 §6.2 Observation 7 interpretation.

This checks oriented exact-read strings only; bidirected RC fidelity and
general statements require independent Lean and source review.
"""
from itertools import product
from collections import Counter

ALPHABET = "AT"
L = 3
UNIVERSE = ["".join(x) for x in product(ALPHABET, repeat=L)]


def overlap_edges(vertices, min_overlap=1):
    return {(u, v, ell) for u in vertices for v in vertices
            for ell in range(min_overlap, L) if u[-ell:] == v[:ell]}


def reducible_spelling(edge, vertices, min_overlap=1):
    u, v, ell = edge
    return any(u[-l1:] == m[:l1] and m[-l2:] == v[:l2]
               and l1 + l2 == L + ell
               for m in vertices
               for l1 in range(min_overlap, L)
               for l2 in range(min_overlap, L))


def reducible_literal_shorter_overlap(edge, vertices, min_overlap=1):
    u, v, ell = edge
    return any(u[-l1:] == m[:l1] and m[-l2:] == v[:l2]
               and l1 + l2 == L + ell and l1 < ell and l2 < ell
               for m in vertices
               for l1 in range(min_overlap, L)
               for l2 in range(min_overlap, L))


def skipped_windows(edge):
    u, v, ell = edge
    extension = L - ell
    spelled = u + v[ell:]
    return [spelled[t:t + L] for t in range(1, extension)]


def verify_all_small_edges():
    tested = 0
    for mask in range(1, 1 << len(UNIVERSE)):
        verts = [w for i, w in enumerate(UNIVERSE) if mask & (1 << i)]
        for edge in overlap_edges(verts):
            tested += 1
            assert not reducible_literal_shorter_overlap(edge, verts)
            skips_observed = any(m in verts for m in skipped_windows(edge))
            assert skips_observed == reducible_spelling(edge, verts), (
                verts, edge, skipped_windows(edge))
    return tested


def verify_circular_counterexample():
    verts = {"AAA", "AAT", "ATA", "TAA"}
    walk = [("AAA", "AAA", 2), ("AAA", "AAT", 2),
            ("AAT", "TAA", 1), ("TAA", "AAA", 2)]
    for edge in walk:
        assert edge in overlap_edges(verts)
        assert not reducible_literal_shorter_overlap(edge, verts)
    assert [reducible_spelling(e, verts) for e in walk] == [
        False, False, True, False]
    assert skipped_windows(walk[2]) == ["ATA"]
    lengths = [L - e[2] for e in walk]
    n = sum(lengths)
    concatenated = walk[0][0] + "".join(e[1][e[2]:] for e in walk)
    assert concatenated[:L] == concatenated[n:n + L]
    genome = concatenated[:n]
    assert genome == "AAAAT"  # rotation of AAATA
    starts, s = [], 0
    for d in lengths:
        starts.append(s)
        s += d
    inside = [(start + t) % n
              for start, d in zip(starts, lengths) for t in range(1, d)]
    assert set(starts).isdisjoint(inside)
    assert sorted(starts + inside) == list(range(n))

    def windows(positions):
        return Counter("".join(genome[(i + j) % n] for j in range(L))
                       for i in positions)

    complete = windows(range(n))
    visited = Counter(e[0] for e in walk)
    internal = windows(inside)
    assert complete == visited + internal
    assert complete == Counter({"AAA": 2, "AAT": 1, "ATA": 1, "TAA": 1})
    assert visited == Counter({"AAA": 2, "AAT": 1, "TAA": 1})
    assert internal == Counter({"ATA": 1})
    return genome


if __name__ == "__main__":
    tested = verify_all_small_edges()
    witness = verify_circular_counterexample()
    print(f"PASS: {tested} oriented overlap edges across every nonempty "
          f"subset of {len(UNIVERSE)} binary read types")
    print(f"PASS: literal-reduction arbitrary-walk counterexample {witness}")
