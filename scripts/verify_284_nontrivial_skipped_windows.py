#!/usr/bin/env python3
"""Independent finite check of a nontrivial d=2 reduced signed circuit.

This is a COMPUTATIONAL regression, not a substitute for the general Lean
proof in Section62GlobalSkippedBridge.lean. All overlaps and the precise
spelling-reduction predicate are checked explicitly.
"""

def overlap(u, v, ell):
    return (u[-ell:] if ell else ()) == v[:ell]


def is_reducible(u, v, ell, observed, L=3, o_min=1):
    for mid in observed:
        for l1 in range(o_min, L):
            for l2 in range(o_min, L):
                if l1 + l2 == L + ell and overlap(u, mid, l1) and overlap(mid, v, l2):
                    return True
    return False


def window(genome, L, start):
    return tuple(genome[(start + i) % len(genome)] for i in range(L))


def main():
    ABC, CDA = (0, 1, 2), (2, 3, 0)
    observed = [ABC, CDA]
    edges = [(ABC, CDA, 1), (CDA, ABC, 1)]
    L = 3
    D = (0, 1, 2, 3)
    assert all(overlap(u, v, ell) for u, v, ell in edges)
    assert all(not is_reducible(u, v, ell, observed) for u, v, ell in edges)
    assert [L - ell for _, _, ell in edges] == [2, 2]
    assert [window(D, L, s) for s in range(len(D))] == [
        ABC, (1, 2, 3), CDA, (3, 0, 1)]
    anchors, skipped = [0, 2], [1, 3]
    assert [window(D, L, s) for s in anchors] == [u for u, _, _ in edges]
    assert all(window(D, L, s) not in observed for s in skipped)
    assert all(
        sum(window(D, L, s) == w for s in range(len(D)))
        == sum(u == w for u, _, _ in edges)
        for w in observed
    )
    print("PASS: two nontrivial d=2 reduced edges; skipped BCD,DAB absent; counts match")


if __name__ == "__main__":
    main()
