#!/usr/bin/env python3
"""Ternary-alphabet full-vs-realizable gap witness for board issue #259.

Extends `scripts/verify_realizable_transfer_gap_259.py` (binary necklaces)
to the first untouched cell of its scope matrix: ternary (`{0,1,2}`) 2-mer
necklace spectra.  Exact `int`/`Fraction` arithmetic, no Lean import.

Checks (all exact):
  1. Transfer-balance iff (endpoint-multiset condition, same statement as
     the binary script) over ternary necklace spectra, L=2, G<=6.
  2. Full-vs-realizable gap census over the same range; reports the
     smallest exact gap witness and asserts:
       - the full-class transfer beater is not a necklace spectrum,
       - the flooding covered sample satisfies F_Bs(x) > F_A(x) exactly.

Exit code 0 means every check passed.  Bounded evidence only, not a theorem.
"""

from __future__ import annotations

import itertools
import sys
from collections import defaultdict
from fractions import Fraction

sys.path.insert(0, "scripts")
from verify_realizable_transfer_gap_259 import (  # noqa: E402
    balance_residual,
    beats,
    eff_product,
    eff_weight,
    endpoint_multisets,
    flooding_witness,
    full_class_maximal,
    support,
)


def necklaces_alpha(G: int, alpha: int):
    seen = set()
    for w in itertools.product(range(alpha), repeat=G):
        if w in seen:
            continue
        for k in range(G):
            seen.add(w[k:] + w[:k])
        yield w


def realizable_spectra_alpha(L: int, G: int, U: list, alpha: int):
    items: dict[tuple, tuple] = {}
    for s in necklaces_alpha(G, alpha):
        c = defaultdict(int)
        for i in range(G):
            c[tuple(s[(i + t) % G] for t in range(L))] += 1
        key = tuple(c.get(w, 0) for w in U)
        items.setdefault(key, s)
    return items


def part_transfer_balance(L: int, G: int, U: list, alpha: int):
    checks = preserved = 0
    for key, _s in realizable_spectra_alpha(L, G, U, alpha).items():
        A = list(key)
        edges = [w for w, a in zip(U, A) if a > 0]
        assert all(b == 0 for b in balance_residual(
            edges, [A[U.index(w)] for w in edges])), f"unbalanced: A={A}"
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
                balanced = all(b == 0 for b in balance_residual(
                    edges, [B[U.index(w)] for w in edges]))
                agree = (endpoint_multisets(U, i, j)[0]
                         == endpoint_multisets(U, i, j)[1])
                if balanced != agree:
                    raise AssertionError(
                        f"transfer-balance mismatch: G={G} A={A} "
                        f"i={U[i]} j={U[j]} B={B}")
                checks += 1
                preserved += balanced
    return checks, preserved


def main() -> int:
    alpha, L = 3, 2
    U = list(itertools.product(range(alpha), repeat=L))
    t_checks = t_preserved = 0
    totals = {"both_max": 0, "both_beaten": 0, "gap": 0, "skipped": 0}
    smallest = None
    for G in range(2, 7):
        c, p = part_transfer_balance(L, G, U, alpha)
        t_checks += c
        t_preserved += p
        items = realizable_spectra_alpha(L, G, U, alpha)
        specs = sorted(items.items())
        real_set = set(k for k, _ in specs)
        for keyA, sA in specs:
            A = list(keyA)
            if any(eff_weight(G, A, i) == 0 for i in support(A)):
                totals["skipped"] += 1
                continue
            full = full_class_maximal(A)
            beater = next((list(kB) for kB, _ in specs
                           if kB != keyA and beats(G, A, list(kB))), None)
            real = beater is None
            if full and real:
                totals["both_max"] += 1
            elif (not full) and (not real):
                totals["both_beaten"] += 1
            elif (not full) and real:
                totals["gap"] += 1
                if smallest is None:
                    S = support(A)
                    Bs = next((cand for j in S if A[j] >= 2 for i in S
                               if i != j
                               for cand in [A[:j] + [A[j] - 1] + A[j + 1:]]
                               for cand in [[v + (1 if k == i else 0)
                                             for k, v in enumerate(cand)]]
                               if beats(G, A, cand)), None)
                    if Bs is not None:
                        if tuple(Bs) in real_set:
                            raise AssertionError(
                                f"transfer beater realizable: A={A} Bs={Bs}")
                        x, fcoord = flooding_witness(G, A, Bs)
                        if not eff_product(G, Bs, x) > eff_product(G, A, x):
                            raise AssertionError(
                                f"flooding witness fails: A={A} Bs={Bs} x={x}")
                        smallest = (G, A, sA, Bs, x, fcoord)
            else:
                raise AssertionError(
                    f"full-max but realizable-beaten: A={A}")
    print("verify_ternary_transfer_gap_259.py")
    print(f"  transfer-balance: {t_checks} transfers, {t_preserved} preserve, "
          f"0 mismatches (ternary L=2, G<=6)")
    print(f"  gap census (ternary L=2, G<=6): both_max={totals['both_max']} "
          f"both_beaten={totals['both_beaten']} gap={totals['gap']} "
          f"skipped={totals['skipped']}")
    if smallest is not None:
        G, A, sA, Bs, x, fcoord = smallest
        print(f"  smallest ternary gap: G={G} A={A} (word "
              f"{''.join(map(str, sA))}), beater Bs={Bs} (unbalanced, "
              f"unrealizable), covered sample x={x} flooding {fcoord}, "
              f"exact F_Bs(x) > F_A(x)")
    print("verify_ternary_transfer_gap_259: ALL OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
