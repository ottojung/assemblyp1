#!/usr/bin/env python3
"""Board 94, front 94cle: checks for the GF(2) parity step of the Cohn--Lempel
whole-interlace-component deletion corollary.

Companion to ``AssemblyP1/Issue94CLEDeletion.lean`` and
``docs/cohn-lempel-deletion-corollary-94.md``.

Nothing here is a proof and nothing here is a search for a counterexample to the
project's open problem.  The three checks below are *evidence about one purely
algebraic step* that the module deliberately isolates as an input
(``NonsingularHollowBlockEven``):

1. ``parity``: over GF(2), a hollow symmetric matrix is nonsingular only if its
   size is even (exhaustive over all hollow symmetric matrices up to size 6).
2. ``minor``: the tempting shortcut used by most informal write-ups --
   "the principal minor of a nonsingular alternating matrix is nonsingular" --
   is FALSE.  The script exhibits and checks the smallest witness.
3. ``corrected``: the statement that is actually true: deleting two indices
   ``i != j`` with ``A[i][j] = 1`` gives a matrix ``C + G`` on the complement,
   where ``C`` is the principal submatrix and ``G[k][m] = r_k u_m + u_k r_m``
   with ``r = A[i, -]``, ``u = A[j, -]``; ``C + G`` is again hollow symmetric,
   is nonsingular whenever ``A`` is, and ``A`` is nonsingular iff ``C + G`` is.

Run: ``python3 scripts/verify_cle_parity_94.py``
"""

from __future__ import annotations

import itertools
import sys

MOD2 = 2


def det_mod2(mat: list[list[int]]) -> int:
    """Determinant of a square GF(2) matrix by Gaussian elimination mod 2."""
    n = len(mat)
    a = [row[:] for row in mat]
    det = 1
    for col in range(n):
        pivot = next((r for r in range(col, n) if a[r][col] == 1), None)
        if pivot is None:
            return 0
        if pivot != col:
            a[col], a[pivot] = a[pivot], a[col]
            det = (det * -1) % MOD2
        for r in range(n):
            if r != col and a[r][col] == 1:
                a[r] = [(x + y) % MOD2 for x, y in zip(a[r], a[col])]
    return det % MOD2


def mul_vec(mat: list[list[int]], vec: list[int]) -> list[int]:
    return [sum(row[k] * vec[k] for k in range(len(vec))) % MOD2 for row in mat]


def hollow_symmetric(n: int):
    """All hollow symmetric GF(2) matrices of size ``n`` (upper triangle free)."""
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    for bits in itertools.product((0, 1), repeat=len(pairs)):
        mat = [[0] * n for _ in range(n)]
        for (i, j), b in zip(pairs, bits):
            mat[i][j] = mat[j][i] = b
        yield mat


def is_nonsingular(mat: list[list[int]]) -> bool:
    return det_mod2(mat) == 1


def principal_submatrix(mat: list[list[int]], drop: list[int]) -> list[list[int]]:
    keep = [k for k in range(len(mat)) if k not in drop]
    return [[mat[i][j] for j in keep] for i in keep]


def corrected_reduction(mat: list[list[int]], i: int, j: int) -> list[list[int]]:
    """``C + G`` on the complement of ``{i, j}``, with ``G[k][m] = r_k u_m + u_k r_m``.

    ``r = A[i, -]`` and ``u = A[j, -]`` are the two rows of ``A`` restricted to the
    complement.  This is the reduction that makes the parity induction go through
    (see the doc, section 3).
    """
    n = len(mat)
    keep = [k for k in range(n) if k not in (i, j)]
    r = [mat[i][k] for k in keep]
    u = [mat[j][k] for k in keep]
    return [
        [
            (mat[a][b] + r[p] * u[q] + u[p] * r[q]) % MOD2
            for q, b in enumerate(keep)
        ]
        for p, a in enumerate(keep)
    ]


def check_parity(max_n: int = 6) -> tuple[bool, dict]:
    """(1) nonsingular hollow symmetric over GF(2) => even size."""
    data = {}
    ok = True
    for n in range(0, max_n + 1):
        nonsing = 0
        odd_nonsing = 0
        for mat in hollow_symmetric(n):
            if is_nonsingular(mat):
                nonsing += 1
                if n % 2 == 1:
                    odd_nonsing += 1
        data[n] = (nonsing, odd_nonsing)
        if odd_nonsing != 0:
            ok = False
    return ok, data


def find_minor_counterexample(max_n: int = 5):
    """(2) smallest nonsingular hollow symmetric ``A`` with a singular principal minor."""
    for n in range(1, max_n + 1):
        for mat in hollow_symmetric(n):
            if not is_nonsingular(mat):
                continue
            for i, j in itertools.combinations(range(n), 2):
                if mat[i][j] != 1:
                    continue
                sub = principal_submatrix(mat, [i, j])
                if det_mod2(sub) == 0:
                    return n, mat, i, j, sub
    return None


def check_corrected(max_n: int = 5) -> tuple[bool, int]:
    """(3) the corrected reduction: ``A`` nonsingular <=> ``C + G`` nonsingular,
    and ``C + G`` is again hollow symmetric."""
    ok = True
    tested = 0
    for n in range(2, max_n + 1):
        for mat in hollow_symmetric(n):
            for i, j in itertools.combinations(range(n), 2):
                if mat[i][j] != 1:
                    continue
                red = corrected_reduction(mat, i, j)
                size = len(red)
                hollow = all(red[a][a] == 0 for a in range(size))
                sym = all(red[a][b] == red[b][a] for a in range(size)
                          for b in range(size))
                if not (hollow and sym):
                    ok = False
                if is_nonsingular(mat) != is_nonsingular(red):
                    ok = False
                tested += 1
    return ok, tested


def main() -> int:
    ok_parity, data = check_parity()
    print("1. parity: nonsingular hollow symmetric GF(2) matrices have even size")
    for n, (nonsing, odd) in sorted(data.items()):
        print(f"   n = {n}: nonsingular = {nonsing:6d}, nonsingular with odd n = {odd}")
    if not ok_parity:
        print("   FAIL: a nonsingular hollow symmetric GF(2) matrix of odd size exists")

    cex = find_minor_counterexample()
    if cex is None:
        print("2. minor: no counterexample found up to size 5 (unexpected)")
        ok_minor = False
    else:
        n, mat, i, j, sub = cex
        print("2. minor: 'principal minors stay nonsingular' is FALSE")
        print(f"   smallest witness: n = {n}, pivot ({i}, {j}), det A = {det_mod2(mat)}")
        for row in mat:
            print("     ", row)
        print(f"   principal submatrix on the complement (det = {det_mod2(sub)}):")
        for row in sub:
            print("     ", row)
        assert det_mod2(mat) == 1 and det_mod2(sub) == 0
        ok_minor = True

    ok_red, tested = check_corrected()
    print(f"3. corrected: the C + G reduction ({tested} matrices checked)")
    print(f"   hollow symmetric and nonsingular-equivalent: {ok_red}")
    if not ok_red:
        print("   FAIL: the corrected reduction does not preserve nonsingularity")

    all_ok = ok_parity and ok_minor and ok_red
    print("RESULT:", "all checks passed" if all_ok else "a check failed")
    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())
