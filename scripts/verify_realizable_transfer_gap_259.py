#!/usr/bin/env python3
"""Bounded exact-arithmetic step toward the realizable (balanced-spectrum)
restriction of board issue #259.

This does NOT import Lean.  It checks, with exact integer / Fraction
arithmetic, two claims that separate the proved full-class classification
(`AssemblyP1/ProductBinomialBoundaryFullClass`, every count vector of total
N admitted) from the still-open realizable classification (candidates
restricted to balanced spectra of circular genomes):

  1. Transfer balance classification (exact necessary/sufficient fragment):
     moving one unit `B = A - e_j + e_i` between distinct supported
     coordinates preserves balance on `supp A` iff the endpoint multisets
     agree, `{pre(i), suf(j)} = {pre(j), suf(i)}` (in particular every
     loop-to-loop transfer across nodes qualifies, e.g. `00 -> 11`).  Hence
     the full-class beating mechanism survives inside the same-support
     realizable class exactly in those cases; otherwise a realizable beater,
     if any, must use new support.  Both directions are checked exactly
     (integer balance equations) over binary necklaces.

  2. Full-vs-realizable gap census: for each realizable truth `A` (binary
     necklace spectrum, `q` positive on its support), compare the full-class
     verdict (kernel-checked iff: maximal iff concentrated or `{0,1}`-valued)
     against maximality over the realizable class (all necklace spectra of
     the same total, decided by the merged #259 covered-sample iff).  Gap
     cases (full-class-beaten yet realizable-maximal) are reported with the
     smallest explicit exact-rational witness: the full-class transfer
     beater `B*`, a covered sample `x` with exact `F_B*(x) > F_A(x)`, and a
     certificate that `B*` is not itself a necklace spectrum.

Exit code 0 means every check passed.  A census with no gap is bounded
evidence only, not a theorem; any gap case is an exact witness, not a
conjecture.
"""

from __future__ import annotations

import itertools
import sys
from collections import defaultdict
from fractions import Fraction

# ---------------------------------------------------------------------------
# Exact §6.1 arithmetic (same conventions as verify_product_binomial_rigidity_259.py)
# ---------------------------------------------------------------------------


def eff_weight(N: int, B: list[int], i: int) -> int:
    w = B[i]
    for j in range(len(B)):
        if j != i:
            w *= N - B[j]
    return w


def eff_product(N: int, B: list[int], x: list[int]) -> int:
    p = 1
    for i in range(len(B)):
        p *= eff_weight(N, B, i) ** x[i]
    return p


def support(B: list[int]) -> list[int]:
    return [i for i in range(len(B)) if B[i] > 0]


def zero_on_support(N: int, A: list[int], B: list[int]) -> bool:
    return any(eff_weight(N, B, i) == 0 for i in support(A))


def dominates_pointwise(N: int, A: list[int], B: list[int]) -> bool:
    return all(eff_weight(N, B, i) <= eff_weight(N, A, i) for i in support(A))


def beats(N: int, A: list[int], B: list[int]) -> bool:
    """Merged #259 covered-sample iff, failure branch: some covered sample
    strictly prefers B to A."""
    return not zero_on_support(N, A, B) and not dominates_pointwise(N, A, B)


def full_class_maximal(A: list[int]) -> bool:
    """Kernel-checked full-class predicate: concentrated or {0,1}-valued."""
    return len(support(A)) == 1 or all(a <= 1 for a in A)


# ---------------------------------------------------------------------------
# Necklace spectra (realizable = spectra of circular binary words)
# ---------------------------------------------------------------------------


def spec_vector(s, L: int, U: list) -> list[int]:
    c = defaultdict(int)
    for i in range(len(s)):
        c[tuple(s[(i + t) % len(s)] for t in range(L))] += 1
    return [c.get(w, 0) for w in U]


def necklaces(G: int):
    seen = set()
    for bits in itertools.product((0, 1), repeat=G):
        if bits in seen:
            continue
        seen.update(bits[k:] + bits[:k] for k in range(G))
        yield bits


def realizable_spectra(L: int, G: int, U: list):
    items: dict[tuple, tuple] = {}
    for s in necklaces(G):
        key = tuple(spec_vector(s, L, U))
        items.setdefault(key, s)
    return items


# ---------------------------------------------------------------------------
# Part 1: one-unit transfer balance classification.  Moving one unit
# B = A - e_j + e_i changes out-flow by -1 at pre(j), +1 at pre(i) and
# in-flow by -1 at suf(j), +1 at suf(i); the residual shift at node v is
#   delta(v) = [v==pre(i)] - [v==pre(j)] - [v==suf(i)] + [v==suf(j)],
# which vanishes for all v iff {pre(i),suf(j)} = {pre(j),suf(i)} as
# multisets.  Both directions are checked exactly below.
# ---------------------------------------------------------------------------


def balance_residual(edges: list, values: list[int]) -> list[int]:
    nodes: dict = {}
    for w in edges:
        nodes.setdefault(w[:-1], len(nodes))
        nodes.setdefault(w[1:], len(nodes))
    bal = [0] * len(nodes)
    for w, v in zip(edges, values):
        bal[nodes[w[:-1]]] += v
        bal[nodes[w[1:]]] -= v
    return bal


def endpoint_multisets(U: list, i: int, j: int) -> tuple:
    wi, wj = U[i], U[j]
    return (tuple(sorted((wi[:-1], wj[1:]))),
            tuple(sorted((wj[:-1], wi[1:]))))


def part_transfer_balance_class(L: int, G: int, U: list) -> tuple[int, int]:
    preserved = 0
    checks = 0
    for key, _s in realizable_spectra(L, G, U).items():
        A = list(key)
        edges = [w for w, a in zip(U, A) if a > 0]
        assert all(b == 0 for b in balance_residual(edges, [A[U.index(w)] for w in edges])), (
            f"necklace spectrum not balanced: A={A}")
        S = support(A)
        for j in S:
            if A[j] < 2:
                continue
            for i in S:
                if i == j:
                    continue
                B = list(A)
                B[j] -= 1
                B[i] += 1
                balanced = all(
                    b == 0 for b in balance_residual(edges, [B[U.index(w)] for w in edges]))
                multisets_agree = (endpoint_multisets(U, i, j)[0]
                                   == endpoint_multisets(U, i, j)[1])
                if balanced != multisets_agree:
                    raise AssertionError(
                        f"transfer-balance classification mismatch: L={L} G={G} "
                        f"A={A} i={U[i]} j={U[j]} B={B} balanced={balanced} "
                        f"multisets_agree={multisets_agree}")
                checks += 1
                preserved += balanced
    return checks, preserved


# ---------------------------------------------------------------------------
# Part 2: full-class vs realizable-class gap census with smallest witness.
# ---------------------------------------------------------------------------


def flooding_witness(N: int, A: list[int], B: list[int]):
    """Covered sample x (A <= x, on supp A) with exact F_B(x) > F_A(x),
    by flooding a coordinate where qB > qA.  Exact Fraction ratio."""
    S = support(A)
    i = next(k for k in S if eff_weight(N, B, k) > eff_weight(N, A, k))
    C = Fraction(1, 1)
    for k in range(len(A)):
        if k != i:
            C *= Fraction(eff_weight(N, B, k) ** A[k],
                          eff_weight(N, A, k) ** A[k])
    ratio_i = Fraction(eff_weight(N, B, i), eff_weight(N, A, i))
    t = A[i]
    while ratio_i ** t * C <= 1:
        t += 1
    x = list(A)
    x[i] = t
    return x, i


def part_gap_census(L: int, G: int, U: list):
    items = realizable_spectra(L, G, U)
    specs = sorted(items.items())
    real_set = set(k for k, _ in specs)
    gap = []  # (A, word, transfer beater B*)
    counts = {"both_max": 0, "both_beaten": 0, "gap": 0, "skipped_zero_q": 0}
    for keyA, sA in specs:
        A = list(keyA)
        if any(eff_weight(G, A, i) == 0 for i in support(A)):
            counts["skipped_zero_q"] += 1
            continue
        full = full_class_maximal(A)
        beater = None
        for keyB, _ in specs:
            if keyB == keyA:
                continue
            if beats(G, A, list(keyB)):
                beater = list(keyB)
                break
        real = beater is None
        if full and real:
            counts["both_max"] += 1
        elif not full and not real:
            counts["both_beaten"] += 1
        elif not full and real:
            counts["gap"] += 1
            # canonical full-class beater: one-unit transfer
            S = support(A)
            Bs = None
            for j in S:
                if A[j] < 2:
                    continue
                for i in S:
                    if i == j:
                        continue
                    cand = list(A)
                    cand[j] -= 1
                    cand[i] += 1
                    if beats(G, A, cand):
                        Bs = cand
                        break
                if Bs is not None:
                    break
            gap.append((A, sA, Bs))
        else:
            raise AssertionError(
                f"full-class maximal but realizable-beaten (impossible: "
                f"realizable class is a subclass): A={A}")
    return counts, gap, real_set


def main() -> int:
    transfer_checks = 0
    transfer_preserved = 0
    total_counts = {"both_max": 0, "both_beaten": 0, "gap": 0, "skipped_zero_q": 0}
    smallest_gap = None  # (G, A) of the first gap case in (G, lex) order
    smallest = None  # (L, G, A, word, Bs, x, flood_coord) first gap with transfer beater
    for L in (2, 3):
        U = list(itertools.product((0, 1), repeat=L))
        for G in range(L, 11):
            c, p = part_transfer_balance_class(L, G, U)
            transfer_checks += c
            transfer_preserved += p
            counts, gap, real_set = part_gap_census(L, G, U)
            for k in total_counts:
                total_counts[k] += counts[k]
            for (A, sA, Bs) in gap:
                if smallest_gap is None:
                    smallest_gap = (G, A)
                if Bs is not None and tuple(Bs) in real_set:
                    raise AssertionError(
                        f"transfer beater is itself realizable: A={A} Bs={Bs}")
                if Bs is not None and smallest is None:
                    x, i = flooding_witness(G, A, Bs)
                    # exact integer cross-check of the witness comparison
                    if not eff_product(G, Bs, x) > eff_product(G, A, x):
                        raise AssertionError(
                            f"flooding witness fails exact check: A={A} Bs={Bs} x={x}")
                    smallest = (L, G, A, sA, Bs, x, i)
    print("verify_realizable_transfer_gap_259.py")
    print(f"  transfer-balance classification: {transfer_checks} one-unit "
          f"transfers, {transfer_preserved} preserve same-support balance, "
          f"0 mismatches with the endpoint-multiset condition")
    print(f"  gap census (binary L in {{2,3}}, G <= 10): "
          f"both_max={total_counts['both_max']} "
          f"both_beaten={total_counts['both_beaten']} "
          f"gap(full-beaten,real-max)={total_counts['gap']} "
          f"skipped_zero_q={total_counts['skipped_zero_q']}")
    if smallest_gap is not None:
        print(f"  smallest gap truth: G={smallest_gap[0]} A={smallest_gap[1]}")
    if smallest is not None:
        L, G, A, sA, Bs, x, i = smallest
        print(f"  smallest gap witness: L={L} G={G} truth A={A} (word "
              f"{''.join(map(str, sA))}), full-class transfer beater Bs={Bs} "
              f"(not a necklace spectrum), covered sample x={x} flooding "
              f"coordinate {i} with exact F_Bs(x) > F_A(x)")
    else:
        print("  no full-vs-realizable gap in range (bounded evidence only)")
    print("verify_realizable_transfer_gap_259: ALL OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
