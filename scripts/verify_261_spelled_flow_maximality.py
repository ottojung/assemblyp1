#!/usr/bin/env python3
"""Independent exact validation of the #261 spelled sub-class maximality transfer.

Scope: `AssemblyP1/Section62SpelledFlowMaximality.lean`, which continues
`AssemblyP1/Section62SpelledFlowAdapter.lean` (issue #261).  The Lean module
proves, for a circular spelling `sp` of `n` read positions:

  * `sum_visits_eq_n`       : sum over the visited molecule classes of
                              `Spelling.visits` equals `n` (the length universe);
  * `sum_throughput_eq_n`   : the walk flow's total throughput equals the same `n`;
  * `spelledVisitSet_subset_image` : the spelled visit vectors are contained in the
                              zero-terminal §6.2 feasible throughput image;
  * `spelled_maximal_of_flow_maximal` and
    `flow_not_maximal_of_spelled_witness` : the maximality-transfer statements.

This script recomputes the *length universe* from scratch, in exact integer
arithmetic and with no trust in the Lean output, and additionally demonstrates the
transfer statement on a small explicit finite candidate set (a brute-force check
that a spelled dominator really does witness non-maximality over a superset).

The script is deterministic, exits non-zero on any failed assertion, and shares no
code with the Lean module.
"""
from itertools import product

COMP = {"A": "T", "T": "A", "C": "G", "G": "C"}


def rc(w):
    return "".join(COMP[c] for c in reversed(w))


def canon(w):
    return min(w, rc(w))


def circular_window(S, t, L):
    G = len(S)
    return "".join(S[(t + j) % G] for j in range(L))


def strands(S, L):
    return [circular_window(S, t, L) for t in range(len(S))]


def visits(S, L, v):
    return sum(1 for s in strands(S, L) if canon(s) == v)


def visited_classes(S, L):
    return sorted({canon(s) for s in strands(S, L)})


def check_length_universe(S, L, verbose=False):
    """`sum_visits_eq_n`: the visit vector has total mass n = len(S)."""
    n = len(S)
    classes = visited_classes(S, L)
    total = sum(visits(S, L, v) for v in classes)
    assert total == n, (S, L, total, n)
    # Every position lands in exactly one class, so the classes partition the
    # positions: the sum is the number of positions.
    assert sum(visits(S, L, v) for v in classes) == len(strands(S, L))
    if verbose:
        print(f"[ok] S={S} L={L}: n={n} classes={classes} "
              f"visits={[visits(S, L, v) for v in classes]} sum={total}")
    return True


def maximal(candidates, score, A):
    """A is maximal over `candidates` under `score` iff no candidate scores above."""
    return all(score(B) <= score(A) for B in candidates)


def check_transfer_demo():
    """Brute-force demonstration of `flow_not_maximal_of_spelled_witness`.

    We take a small explicit superset `image` of count vectors, a spelled
    sub-class `spelled ⊆ image`, a truth `A`, and a score.  The Lean transfer
    theorem says: if some spelled vector strictly beats `A`, then `A` is not
    maximal over `image`.  We exhaustively confirm this on the finite instance.
    """
    image = [(1, 2, 0, 2), (2, 1, 0, 1), (3, 1, 0, 1), (0, 1, 0, 0)]
    spelled = [(1, 2, 0, 2), (2, 1, 0, 1)]  # a spelled sub-class of the image
    assert set(spelled) <= set(image)
    score = lambda d: d[0]  # arbitrary linear score with a spelled dominator
    A = (1, 2, 0, 2)
    dominators = [B for B in spelled if score(A) < score(B)]
    assert dominators, "expected a spelled dominator to exercise the transfer"
    # The theorem's conclusion must hold: A is not maximal over the image.
    assert not maximal(image, score, A), (image, A, dominators)
    print(f"[ok] transfer demo: image={image} spelled={spelled} A={A} "
          f"spelled_dominators={dominators} "
          f"maximal_over_image={maximal(image, score, A)}")
    return True


def main():
    instances = [
        ("AAA", 2),
        ("AATT", 2),
        ("AAATA", 3),
        ("ACGT", 2),
        ("ACGT", 3),
        ("AACCGGTT", 2),
        ("AACCGGTT", 3),
        ("AT", 1),
        ("ATAT", 2),
        ("AAATTT", 3),
    ]
    for S, L in instances:
        check_length_universe(S, L, verbose=True)

    # Exhaustive binary circular words up to length 8 at L = 2 and L = 3: a
    # finite family (not a proof) corroborating the length universe.
    swept = 0
    for length in range(1, 9):
        for tup in product("AT", repeat=length):
            S = "".join(tup)
            for L in (2, 3):
                if L <= length:
                    check_length_universe(S, L)
                    swept += 1
    print(f"[ok] exhaustive binary sweep: {swept} (S, L) instances checked")

    check_transfer_demo()
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
