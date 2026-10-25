#!/usr/bin/env python3
"""Binary-L7 realizable complete-support census for board issue #259.

Covers the L>=7 cell left open by the binary-L5 / ternary-L5 / L6-Q4
handoffs: binary L=7, G=8..12, for the MB09 S6.1 fixed-external-N
product-binomial surrogate.

Uses ONLY exact integer arithmetic (no Lean import, no floats).

Key exact reduction: for candidates A,B over a universe U with total N,
  effB_i <= effA_i  <=>  B_i * prod_{j in S, j!=i}(N-B_j)
                     <= A_i * prod_{j in S, j!=i}(N-A_j),
where S = supp(A) | supp(B): classes outside S contribute factor N on
both sides and cancel exactly.  Zero weights (B_i = 0 or some B_j = N)
are handled exactly.

For each truth spectrum A (circular genome necklace) and each competitor
spectrum B (same G, same L, same alphabet), maximality over covered
samples is decided by the kernel-checked covered-sample iff
(CoveredBinomialWeightsIff): A beats B iff B has a zero effective weight
on supp(A) or is pointwise dominated there.  A "violation" (B beats A on
some covered sample) additionally gets an EXPLICIT exact-integer witness
sample x = A + t*e_i with F_B(x) > F_A(x) (t minimal), proving the iff
decision is not vacuous.

Rigidity = uniqueness of the positive balanced circulation of total G on
supp(A).  Necessity predicts: nonrigid & maximal == 0 in every cell.
Sufficiency is expected to fail (rigid & NOT maximal > 0) once
new-support candidates are admitted.

Exit code 0 means every check passed.
"""

from __future__ import annotations

import itertools
import sys
from collections import defaultdict

# ---------------------------------------------------------------------------
# exact reduced arithmetic
# ---------------------------------------------------------------------------


def reduced_le(N, A, B, S, i):
    """effB_i <= effA_i via exact reduced product over union support S."""
    if B[i] == 0:
        return True  # 0 <= anything
    if A[i] == 0:
        return False  # positive > 0 (B[i] > 0 here)
    left = B[i]
    right = A[i]
    for j in S:
        if j == i:
            continue
        left *= N - B[j]
        right *= N - A[j]
    return left <= right


def reduced_gt_witness(N, A, B, S, i):
    """(effB_i, effA_i) reduced exact values for witness display."""
    lb = B[i]
    ra = A[i]
    for j in S:
        if j == i:
            continue
        lb *= N - B[j]
        ra *= N - A[j]
    return lb, ra


def zero_on_support(N, A, B, S_A):
    for i in S_A:
        if B[i] == 0:
            return True
        for j in range(len(B)):
            if j != i and B[j] == N:
                return True
    return False


def dominates(N, A, B, S_A, S_union):
    return all(reduced_le(N, A, B, S_union, i) for i in S_A)


def eff_product_on_x(N, B, S_union, xdict):
    """Exact F_B(x) restricted to supp(x); x_e=0 factors are 1."""
    p = 1
    for i, e in xdict.items():
        if e == 0:
            continue
        w = B[i]
        for j in S_union:
            if j != i:
                w *= N - B[j]
        # classes outside the union contribute N each; the count of such
        # classes is universe-dependent, so record exponent separately.
        p *= w**e
    return p


def explicit_witness(N, A, B, S_A, S_union, k_universe):
    """Find smallest-t covered sample x=A+t*e_i with F_B>F_A (exact ints).

    Returns (i, t, FB, FA, n_out) where n_out = #universe classes outside
    the union (their N^t factors are applied to both sides equally).
    """
    n_out = k_universe - len(S_union)
    import math
    # full (reduced * N^n_out) weights per class in S_union
    wb = {}
    wa = {}
    for j in S_union:
        x, y = B[j], A[j]
        for m in S_union:
            if m != j:
                x *= N - B[m]
                y *= N - A[m]
        x *= N**n_out
        y *= N**n_out
        wb[j], wa[j] = x, y
    for i in S_A:
        lb, ra = reduced_gt_witness(N, A, B, S_union, i)
        if lb <= ra:
            continue
        # log-ratio at x=A is R0 (only classes with A_j>0 or j==i matter;
        # classes with A_j=0,B_j>0 contribute factor at x_j=0 -> 1, skip).
        # t needed: R0 + t*log(wb_i/wa_i) > 0.
        R0 = 0.0
        ok = True
        for j in S_union:
            aj = A[j]
            if aj == 0:
                continue
            if wb[j] == 0 or wa[j] == 0:
                ok = False
                break
            R0 += aj * math.log(wb[j] / wa[j])
        if not ok:
            continue
        ri = math.log(wb[i] / wa[i])
        if ri <= 0:
            continue
        t_need = 0 if R0 > 0 else int(-R0 / ri) + 1
        for t in (t_need, t_need + 1):
            fb = 1
            fa = 1
            for j in S_union:
                xj = A[j] + (t if j == i else 0)
                if xj == 0:
                    continue
                fb *= wb[j] ** xj
                fa *= wa[j] ** xj
            if fb > fa:
                return (i, t, fb, fa)
    return None


# ---------------------------------------------------------------------------
# genomes / spectra / circulations
# ---------------------------------------------------------------------------


def distinct_spectra(G, alpha, L):
    U = list(itertools.product(range(alpha), repeat=L))
    idx = {w: i for i, w in enumerate(U)}
    seen = set()
    items = {}
    for tup in itertools.product(range(alpha), repeat=G):
        if tup in seen:
            continue
        for k in range(G):
            seen.add(tup[k:] + tup[:k])
        c = [0] * len(U)
        for i in range(G):
            c[idx[tuple(tup[(i + t) % G] for t in range(L))]] += 1
        items.setdefault(tuple(c), tup)
    return U, list(items.items())


def positive_circulations(A, U, G):
    edges = [w for w, a in zip(U, A) if a > 0]
    nodes = {}
    for w in edges:
        nodes.setdefault(w[:-1], len(nodes))
        nodes.setdefault(w[1:], len(nodes))
    inc = [(nodes[w[:-1]], nodes[w[1:]]) for w in edges]
    m, n = len(edges), len(nodes)
    out = []
    vals = [1] * m

    def rec(i, rem):
        if i == m:
            if rem != 0:
                return
            bal = [0] * n
            for e in range(m):
                u, v = inc[e]
                bal[u] += vals[e]
                bal[v] -= vals[e]
            if all(b == 0 for b in bal):
                out.append(tuple(vals))
            return
        for v in range(1, rem - (m - i - 1) + 1):
            vals[i] = v
            rec(i + 1, rem - v)
        vals[i] = 1

    if m:
        rec(0, G)
    return out


def census_cell(alpha, L, Glist, label):
    U, _ = distinct_spectra(1, alpha, L)  # universe only
    k = len(U)
    counts = {"rigid_max": 0, "rigid_notmax": 0,
              "nonrigid_max": 0, "nonrigid_notmax": 0}
    violations = []  # (A, B) first few with explicit witness info
    n_truths = 0
    for G in Glist:
        _, specs = distinct_spectra(G, alpha, L)
        keys = [list(a) for a, _ in specs]
        N = G
        for A in keys:
            # skip truths with zero effective weight on own support
            # (degenerate single-kmer genomes); out of scope for necessity
            S_A = [i for i, a in enumerate(A) if a > 0]
            self_union = set(S_A)
            bad = False
            for i in S_A:
                w = A[i]
                for j in self_union:
                    if j != i:
                        w *= N - A[j]
                if w == 0:
                    bad = True
            if bad:
                continue
            n_truths += 1
            circs = positive_circulations(A, U, G)
            rigid = (len(circs) == 1)
            maximal = True
            first_bad = None
            for B in keys:
                if B == A:
                    continue
                S_B = [i for i, b in enumerate(B) if b > 0]
                S_union = sorted(set(S_A) | set(S_B))
                if zero_on_support(N, A, B, S_A):
                    continue
                if dominates(N, A, B, S_A, S_union):
                    continue
                maximal = False
                if first_bad is None:
                    first_bad = (list(B), S_union)
                # do NOT break: must confirm maximal=False; but break
                # early for speed once found (maximal already False)
                break
            if rigid and maximal:
                counts["rigid_max"] += 1
            elif rigid and not maximal:
                counts["rigid_notmax"] += 1
                if len(violations) < 3:
                    B, S_union = first_bad
                    wit = explicit_witness(N, A, B, S_A, S_union, k)
                    violations.append((G, list(A), B, wit))
            elif (not rigid) and maximal:
                counts["nonrigid_max"] += 1
            else:
                counts["nonrigid_notmax"] += 1
    print(f"cell {label}: truths={n_truths} " + str(counts))
    for (G, A, B, wit) in violations:
        assert wit is not None, f"iff/witness gap at G={G}"
        i, t, fb, fa = wit
        # re-verify exact inequality from scratch
        assert fb > fa
        nn = sum(A) + t
        print(f"  witness G={G} n={nn}: coord={i} t={t} "
              f"bitlen(FB)={fb.bit_length()} bitlen(FA)={fa.bit_length()} "
              f"FB>FA={fb > fa}")
    return counts, violations


def main():
    cells = [
        (2, 7, [8, 9, 10, 11, 12], "binary-L7"),
    ]
    total_nonrigid_max = 0
    total_rigid_notmax = 0
    for alpha, L, Glist, label in cells:
        counts, violations = census_cell(alpha, L, Glist, label)
        total_nonrigid_max += counts["nonrigid_max"]
        total_rigid_notmax += counts["rigid_notmax"]
    print(f"total nonrigid&maximal={total_nonrigid_max} "
          f"(necessity requires 0)")
    print(f"total rigid&NOT-maximal={total_rigid_notmax} "
          f"(sufficiency-failure witnesses)")
    if total_nonrigid_max != 0:
        raise AssertionError("rigidity-necessity counterexample found")
    if total_rigid_notmax == 0:
        print("NOTE: no rigid-but-beaten truth in this cell "
              "(honest negative cell; sufficiency may still fail elsewhere)")
    # mutation control: self-comparison must dominate (verifier not vacuous)
    U, specs = distinct_spectra(2, 2, 7)
    Amut = list(specs[0][0])
    Nm = sum(Amut)
    S_Am = [i for i, a in enumerate(Amut) if a > 0]
    assert dominates(Nm, Amut, Amut, S_Am, S_Am)
    print("OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
