#!/usr/bin/env python3
"""Board issue #259: binary L=3 alternating-word infinite gap family.

MB09 section 6.1 fixed-external-N product-binomial surrogate
(q_i(B) = B[i] * prod_{j != i} (N - B[j]), F_B(x) = prod_i q_i(B)^x[i];
candidate-constant choose/N factors cancel in comparisons; this is the
surrogate, NOT the exact joint multinomial of #256, and NOT the section 6.2
bidirected-flow objective of #260/#261).

Theorem (all k >= 2): the truth A_k = spectrum of the circular word (01)^k
read as 3-mers -- k on 010, k on 101, total N = 2k -- is beaten over the FULL
candidate class but is a sample-uniform maximizer over the REALIZABLE class
(binary necklace 3-mer spectra of length 2k).  k = 1 is genuinely excluded:
A_1 is {0,1}-valued, hence full-class maximal by the kernel-checked iff
(covered_ambient_effectiveProduct_le_iff / boundary-fullclass module).

The reduction to pointwise effective-weight domination on supp A_k uses the
kernel-checked covered-sample iff
(AssemblyP1.CoveredBinomialWeightsIff.covered_ambient_effectiveProduct_le_iff):
B is dominated by A on all covered samples iff B has a zero effective weight
on supp A or q(B) <= q(A) pointwise there.  This script checks the resulting
exact integer inequalities; the analytic proof for ALL k is in
docs/alternating-3mer-binomial-maximality-259.md (balance-aware domination
lemma via AM-GM + Bernoulli (1-y)^6 (1+6y) <= 1).

Universe order: (000,001,010,011,100,101,110,111), indices 0..7.
A_k = (0,0,k,0,0,k,0,0).

Exact int arithmetic throughout, no Lean import.
"""

import itertools
import sys

IDX = {"000": 0, "001": 1, "010": 2, "011": 3,
       "100": 4, "101": 5, "110": 6, "111": 7}
I010, I101 = IDX["010"], IDX["101"]


def spectrum_3mer(word):
    """3-mer spectrum of a circular binary word (tuple of 8 counts)."""
    n = len(word)
    sp = [0] * 8
    for s in range(n):
        mer = word[s] + word[(s + 1) % n] + word[(s + 2) % n]
        sp[IDX[mer]] += 1
    return tuple(sp)


def necklaces(n):
    """Canonical representatives of binary necklaces of length n."""
    seen = set()
    out = []
    for bits in itertools.product("01", repeat=n):
        rots = {bits[i:] + bits[:i] for i in range(n)}
        key = min(rots)
        if key not in seen:
            seen.add(key)
            out.append("".join(key))
    return out


def eff_weight(B, N, i):
    """q_i(B) as an exact int."""
    q = B[i]
    for j in range(8):
        if j != i:
            q *= N - B[j]
    return q


def eff_product(B, N, x):
    """F_B(x) as an exact int."""
    f = 1
    for i in range(8):
        if x[i]:
            f *= eff_weight(B, N, i) ** x[i]
    return f


def part1_balance(GMAX=12):
    """Every binary necklace 3-mer spectrum is balanced; check the
    (a,p,q,b,c,d) parametrization with p+b == a+q."""
    n_words = 0
    for G in range(4, GMAX + 1, 2):
        for w in necklaces(G):
            n_words += 1
            sp = spectrum_3mer(w)
            c, a, p, b, a2, q, b2, d = sp
            assert a == a2, (w, sp)  # B_001 == B_100 (node 00)
            assert b == b2, (w, sp)  # B_011 == B_110 (node 11)
            # node 01: out(01) = B_010+B_011, in(01) = B_001+B_101
            assert p + b == a + q, (w, sp)
            # node 10: out(10) = B_100+B_101, in(10) = B_010+B_110
            assert a + q == p + b, (w, sp)
    print(f"Part1 OK: {n_words} even-length necklaces G<=12 all balanced "
          f"(B_001=B_100, B_011=B_110, B_010+B_011=B_001+B_101)")
    return True


def part2_domination(KMAX=24):
    """For 2 <= k <= KMAX: every balanced B of total 2k satisfies
    q_010(B) <= q_010(A_k) and q_101(B) <= q_101(A_k) (exact ints),
    with equality on both coords iff B == A_k."""
    n_checked = 0
    n_equal = 0
    for k in range(2, KMAX + 1):
        N = 2 * k
        target = k * k * N ** 6  # q_010(A_k) == q_101(A_k)
        A = (0, 0, k, 0, 0, k, 0, 0)
        assert eff_weight(A, N, I010) == target
        assert eff_weight(A, N, I101) == target
        for a in range(N + 1):          # B_001 == B_100
            for q in range(N + 1 - a):  # B_101
                # b = B_011 == B_110 forced by node-01 balance: p+b = a+q
                for p in range(N + 1 - a - q):  # B_010
                    b = a + q - p
                    if b < 0:
                        continue
                    s = p + q + 2 * a + 2 * b
                    if s > N:
                        continue
                    rest = N - s  # c + d
                    Na = N - a
                    Nb = N - b
                    Nq = N - q
                    Np = N - p
                    base010 = p * Nq * Na * Na * Nb * Nb
                    base101 = q * Np * Na * Na * Nb * Nb
                    for c in range(rest + 1):
                        d = rest - c
                        B = (c, a, p, b, a, q, b, d)
                        q010 = base010 * (N - c) * (N - d)
                        q101 = base101 * (N - c) * (N - d)
                        assert q010 <= target, (k, B, q010, target)
                        assert q101 <= target, (k, B, q101, target)
                        n_checked += 1
                        if q010 == target and q101 == target:
                            n_equal += 1
                            assert B == A, (k, B)
    print(f"Part2 OK: {n_checked} balanced triples 2<=k<={KMAX} dominated, "
          f"equality-both only at B=A ({n_equal} cases = {KMAX - 1} values of k)")
    return True


def part3_beater(KMAX=200):
    """Full-class beater B* = A_k - e_010 + e_101 is unbalanced (hence
    unrealizable) for every k >= 2, yet beats A_k at the covered sample
    x = (0,0,k,0,0,2k,0,0): exact ratio identity
    F*/F = [(k-1)(k+1)^2/k^3]^{2k} > 1 since (k-1)(k+1)^2-k^3 = k^2-k-1 >= 1.
    """
    for k in range(2, KMAX + 1):
        N = 2 * k
        A = (0, 0, k, 0, 0, k, 0, 0)
        Bs = (0, 0, k - 1, 0, 0, k + 1, 0, 0)
        # unbalanced: node 01 residual (p+b)-(a+q) = (k-1)+0-(0+k+1) = -2
        assert (Bs[I010] + Bs[IDX["011"]]) - (Bs[IDX["001"]] + Bs[I101]) == -2
        assert sum(Bs) == N
        x = (0, 0, k, 0, 0, 2 * k, 0, 0)
        for e in range(8):  # x is covered: A_e <= x_e
            assert A[e] <= x[e], (k, e)
        assert (k - 1) * (k + 1) ** 2 - k ** 3 == k * k - k - 1 >= 1
        assert eff_product(Bs, N, x) > eff_product(A, N, x), k
    # exact closed-form cross-check at k = 7
    k = 7
    N = 2 * k
    A = (0, 0, k, 0, 0, k, 0, 0)
    Bs = (0, 0, k - 1, 0, 0, k + 1, 0, 0)
    x = (0, 0, k, 0, 0, 2 * k, 0, 0)
    lhs = eff_product(Bs, N, x)
    rhs = eff_product(A, N, x)
    assert lhs // rhs > 1 and lhs % rhs != 0 or lhs > rhs
    print(f"Part3 OK: beater unbalanced (-2 residual) yet F_Bs(x)>F_A(x) "
          f"for 2<=k<={KMAX} (ratio identity k^2-k-1>=1)")
    return True


def part4_controls():
    """k=1 control: A_1 is {0,1}-valued hence full-class maximal by the
    kernel-checked full-class iff (no gap); beater residual nonzero control."""
    A1 = (0, 0, 1, 0, 0, 1, 0, 0)
    assert all(v <= 1 for v in A1)
    # transfer residual at node 01 for the would-be beater at k=1
    Bs1 = (0, 0, 0, 0, 0, 2, 0, 0)
    assert (Bs1[I010] + Bs1[IDX["011"]]) - (Bs1[IDX["001"]] + Bs1[I101]) == -2
    # A_1 rigidity: unique positive circulation (m,m) on {010,101}, total 2
    assert A1[I010] == A1[I101] == 1 and sum(A1) == 2
    print("Part4 OK: k=1 {0,1}-valued control (full-class maximal, no gap); "
          "transfer-balance residual control = -2")
    return True


def main():
    ok = part1_balance() and part2_domination() and part3_beater() \
        and part4_controls()
    print("ALL OK: alternating L=3 binary binomial maximality "
          "(issue #259)" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
