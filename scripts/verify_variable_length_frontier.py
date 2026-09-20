#!/usr/bin/env python3
"""Independent verification of the variable-length exact-multinomial ML frontier.

Question
--------
The repository kernel-checks a *fixed-length* exact counterexample
(``S = AAABB``, ``L = 3``, observed ``{AAA, AAB, BAA}``, same-length
competitor ``AAAAB``, ratio ``2``).  If the candidate genome length is allowed
to vary, as the literal Medvedev--Brudno section 6.1 objective prescribes
(candidate-dependent ``N(D)``, no external length restriction), does the truth
become maximum likelihood, or does the counterexample survive / strengthen?

This script is self-contained.  It re-derives ``L``-mer spectra from first
principles, uses only the standard library (``fractions.Fraction``), imports no
repository search code, and uses exact rational arithmetic throughout.  It does
not model the Section 6.2 flow-feasible set.

Objective (literal section 6.1, "Variant E")
--------------------------------------------
    P[x | D] = X! / (prod_i x_i!) * prod_i ( d_D(i) / N(D) )^{x_i},
where ``d_D(i)`` is the number of circular length-``L`` windows of ``D`` equal
to type ``i``, ``N(D) = |D|``, ``X = sum_i x_i``, and ``0^0 = 1``.  The
observation-only coefficient cancels in every ratio below.  A candidate with
``d_D(i) = 0`` for an observed type has likelihood ``0``.

Conventions
-----------
* genome = circular word over a finite alphabet;
* window at start ``r`` = ``(g[r], g[r+1], ..., g[r+L-1])``, circularly indexed;
* a circular word of length ``n`` whose de Bruijn graph is connected and
  Eulerian corresponds exactly to a candidate genome of length ``n``; every
  ``n >= 1`` is admitted, including ``n < L``.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import product

# ---------------------------------------------------------------------------
# exact likelihood
# ---------------------------------------------------------------------------


def windows(word: str, L: int):
    n = len(word)
    return [tuple(word[(r + d) % n] for d in range(L)) for r in range(n)]


def spectrum(word: str, L: int) -> dict:
    out: dict = {}
    for w in windows(word, L):
        out[w] = out.get(w, 0) + 1
    return out


def likelihood_part(candidate: str, sample: dict, L: int) -> Fraction:
    """prod_i (d_i / N(D))^{x_i}; 0 if an observed type is absent."""
    d = spectrum(candidate, L)
    n = len(candidate)
    val = Fraction(1)
    for typ, x in sample.items():
        di = d.get(typ, 0)
        if di == 0 and x > 0:
            return Fraction(0)
        val *= Fraction(di, n) ** x
    return val


def ratio(candidate: str, truth: str, sample: dict, L: int) -> Fraction:
    den = likelihood_part(truth, sample, L)
    num = likelihood_part(candidate, sample, L)
    return num / den


# ---------------------------------------------------------------------------
# Sources:  truth S = AAABB, L = 3, observed {AAA, AAB, BAA}
# ---------------------------------------------------------------------------

S_AAABB = "AAABB"
L3 = 3
SAMPLE_AAABB = {("A", "A", "A"): 1, ("A", "A", "B"): 1, ("B", "A", "A"): 1}
RATIO_SUP_AAABB = Fraction(500, 243)


def part_a_fixed_length_aaabb():
    print("=" * 74)
    print("A. Fixed-length baseline: S = AAABB, L = 3, G = 5")
    print("=" * 74)
    best, words = None, []
    for tup in product("ABCD", repeat=5):
        w = "".join(tup)
        r = ratio(w, S_AAABB, SAMPLE_AAABB, L3)
        if best is None or r > best:
            best, words = r, [w]
        elif r == best:
            words.append(w)
    print("   max same-length ratio over all 4^5 circular genomes:", best)
    print("   maximizers:", words)
    assert best == 2, best
    assert "AAAAB" in words
    return best


# ---------------------------------------------------------------------------
# Variable-length exhaustive search for S = AAABB
# ---------------------------------------------------------------------------


def aaabb_counts_from_bits(x: int, n: int):
    """(d(AAA), d(AAB), d(BAA)) of the binary circular word encoded by bits.

    Bit ``i`` of ``x`` is the symbol at position ``i`` (``A = 0``, ``B = 1``).
    The 3-bit little-endian pattern of the window starting at ``i`` is
    ``bit(i) + 2*bit(i+1) + 4*bit(i+2)``.  Self-checked against the string
    spectrum in :func:`check_bit_counter`."""
    a = b = c = 0
    if n < 3:
        s = "".join("AB"[(x >> i) & 1] for i in range(n))
        sp = spectrum(s, 3)
        return (sp.get(("A", "A", "A"), 0), sp.get(("A", "A", "B"), 0),
                sp.get(("B", "A", "A"), 0))
    mask = (1 << n) - 1
    for i in range(n):
        pat = (((x >> i) | (x << (n - i))) & mask) & 7
        if pat == 0b000:      # A A A
            a += 1
        elif pat == 0b001:    # B A A
            c += 1
        elif pat == 0b100:    # A A B
            b += 1
    return a, b, c


def check_bit_counter(max_n: int):
    for n in range(1, max_n + 1):
        for x in range(1 << n):
            s = "".join("AB"[(x >> i) & 1] for i in range(n))
            sp = spectrum(s, 3)
            ref = (sp.get(("A", "A", "A"), 0), sp.get(("A", "A", "B"), 0),
                   sp.get(("B", "A", "A"), 0))
            assert aaabb_counts_from_bits(x, n) == ref, (n, x, ref)


def part_b_variable_length_aaabb(binary_max_n: int, ternary_max_n: int):
    print()
    print("=" * 74)
    print("B. Variable-length search for S = AAABB (any candidate length)")
    print("=" * 74)
    check_bit_counter(min(binary_max_n, 12))
    # Alphabet-size monotonicity: projecting to {A,B} cannot lower the ratio,
    # so the binary exhaustive search bounds every larger alphabet.  We verify
    # this empirically over ternary words too.
    best, first = Fraction(0), None
    for n in range(1, binary_max_n + 1):
        for x in range(1 << n):
            a, b, c = aaabb_counts_from_bits(x, n)
            if a == 0 or b == 0 or c == 0:
                continue
            r = Fraction(125 * a * b * c, n ** 3)
            if r > best:
                best, first = r, (n, x)
    print("   exhaustive binary n <= %d: max ratio = %s = %.9f"
          % (binary_max_n, best, float(best)))
    assert best == RATIO_SUP_AAABB, best
    print("   first maximizer: n=%d word=%s"
          % (first[0], "".join("AB"[(first[1] >> i) & 1] for i in range(first[0]))))

    print("   exhaustive ternary (A,B,C) per length:")
    for n in range(1, ternary_max_n + 1):
        b = Fraction(0)
        for tup in product("ABC", repeat=n):
            r = ratio("".join(tup), S_AAABB, SAMPLE_AAABB, L3)
            if r > b:
                b = r
        assert b <= RATIO_SUP_AAABB, (n, b)
        print("      n=%2d max ratio = %s = %.6f" % (n, b, float(b)))
    return best


def part_b2_run_identities(binary_max_n: int):
    print()
    print("   proof-support run identities over all binary circular words n <= %d:"
          % binary_max_n)
    bad = 0
    for n in range(1, binary_max_n + 1):
        for x in range(1 << n):
            s = "".join("AB"[(x >> i) & 1] for i in range(n))
            if "A" not in s or "B" not in s:
                continue
            starts = [i for i in range(n) if s[i] == "A" and s[i - 1] != "A"]
            lens = []
            for st in starts:
                ln, j = 0, st
                while s[j % n] == "A":
                    ln += 1
                    j += 1
                lens.append(ln)
            alpha = sum(max(0, l - 2) for l in lens)
            xx = sum(1 for l in lens if l >= 2)
            s1 = sum(1 for l in lens if l == 1)
            sp = spectrum(s, 3)
            assert sp.get(("A", "A", "A"), 0) == alpha, s
            assert sp.get(("A", "A", "B"), 0) == xx, s
            assert sp.get(("B", "A", "A"), 0) == xx, s
            if n < alpha + 3 * xx:
                bad += 1
    print("      violations of n >= alpha + 3 x:", bad)
    assert bad == 0
    print("      relaxed AM-GM optimum max alpha*x^2 s.t. alpha+3x<=n is 4n^3/243,")
    print("      hence ratio <= 125*4/243 =", RATIO_SUP_AAABB)


def part_c_family_aaabb():
    print()
    print("   maximizer family D_k = (A^3 B A^4 B)^k, ratio exactly 500/243:")
    for k in (1, 2, 3, 4, 5, 10):
        d = ("AAAB" + "AAAAB") * k
        sp = spectrum(d, 3)
        r = ratio(d, S_AAABB, SAMPLE_AAABB, L3)
        print("      k=%2d len=%3d d(AAA)=%2d d(AAB)=%2d d(BAA)=%2d ratio=%s"
              % (k, len(d), sp.get(("A", "A", "A"), 0), sp.get(("A", "A", "B"), 0),
                 sp.get(("B", "A", "A"), 0), r))
        assert r == RATIO_SUP_AAABB, (k, r)


# ---------------------------------------------------------------------------
# L = 2 candidate instance: S = AACAGG, sample {AA:5, CA:1, GG:1}
# ---------------------------------------------------------------------------

S_AACAGG = "AACAGG"
L2 = 2
SAMPLE_AACAGG = {("A", "A"): 5, ("C", "A"): 1, ("G", "G"): 1}
SUP_AACAGG = Fraction(6 ** 7) * Fraction(5, 7) ** 5 * Fraction(1, 7) * Fraction(1, 14)


def connected_eulerian_matrices(n: int, m: int = 4):
    """All m x m nonnegative integer matrices with every row/column sum n and
    connected support on the vertices that appear.  These are exactly the
    2-mer count matrices of length-n circular words over an m-letter alphabet
    (de Bruijn B(1); self-loops allowed)."""

    def compositions(total, parts):
        if parts == 1:
            yield (total,)
            return
        for first in range(total + 1):
            for rest in compositions(total - first, parts - 1):
                yield (first,) + rest

    def distributions(total, caps):
        if len(caps) == 1:
            if total <= caps[0]:
                yield (total,)
            return
        for v in range(min(total, caps[0]) + 1):
            for rest in distributions(total - v, caps[1:]):
                yield (v,) + rest

    def fill(deg, row, colrem):
        if row == m:
            if all(c == 0 for c in colrem):
                yield []
            return
        for vec in distributions(deg[row], colrem):
            ncr = tuple(colrem[j] - vec[j] for j in range(m))
            if sum(ncr) != sum(deg[row + 1:]):
                continue
            for rest in fill(deg, row + 1, ncr):
                yield [list(vec)] + rest

    for deg in compositions(n, m):
        for mat in fill(deg, 0, deg):
            verts = set()
            adj = {v: set() for v in range(m)}
            for i in range(m):
                for j in range(m):
                    if mat[i][j] > 0:
                        verts.add(i)
                        verts.add(j)
                        adj[i].add(j)
                        adj[j].add(i)
            if not verts:
                continue
            seen, stack = set(), [next(iter(verts))]
            while stack:
                v = stack.pop()
                if v in seen:
                    continue
                seen.add(v)
                stack.extend(adj[v] - seen)
            if seen == verts:
                yield mat


def matrix_ratio(mat, L: int):
    labels = "ACGT"
    sp = {(labels[i], labels[j]): mat[i][j]
          for i in range(len(mat)) for j in range(len(mat)) if mat[i][j]}
    n = sum(sum(row) for row in mat)
    aa, ca, gg = sp.get(("A", "A"), 0), sp.get(("C", "A"), 0), sp.get(("G", "G"), 0)
    if aa == 0 or ca == 0 or gg == 0:
        return None, sp
    return Fraction(6 ** 7 * aa ** 5 * ca * gg, n ** 7), sp


def part_d_aacagg(max_n: int, lower_n: int):
    print()
    print("=" * 74)
    print("D. L = 2 exploratory instance S = AACAGG, sample {AA:5, CA:1, GG:1}")
    print("=" * 74)
    print("   truth L=2 spectrum:",
          {"".join(k): v for k, v in spectrum(S_AACAGG, 2).items()})
    print("   fixed-length competitor AAAGGC ratio:",
          ratio("AAAGGC", S_AACAGG, SAMPLE_AACAGG, 2))
    # Verify the structural lower bound n >= a+g+2c+1 on all connected Eulerian
    # matrices and record maxima for a range of lengths.
    for n in range(lower_n, max_n + 1):
        best, arg = Fraction(0), None
        for mat in connected_eulerian_matrices(n, 4):
            r, sp = matrix_ratio(mat, 2)
            if r is None:
                continue
            if r > best:
                best, arg = r, sp
        print("   exhaustive connected-Eulerian n=%2d  max ratio = %s = %.6f"
              % (n, best, float(best)))
        assert best < SUP_AACAGG, (n, best)
    return


def part_e_aacagg_bound(max_n: int):
    """Verify n >= a + g + 2c + 1 for every connected Eulerian 4x4 matrix whose
    AA, CA, GG entries are all positive, and record the growth family."""
    print()
    print("   structural bound n >= a+g+2c+1 over connected Eulerian matrices:")
    violations = 0
    for n in range(1, max_n + 1):
        for mat in connected_eulerian_matrices(n, 4):
            a = mat[0][0]
            c = mat[1][0]
            g = mat[2][2]
            tot = sum(sum(row) for row in mat)
            if a and c and g and tot < a + g + 2 * c + 1:
                violations += 1
    print("      violations for n <= %d:" % max_n, violations)
    assert violations == 0
    print("   growth family M(a,g,c): AA=a, GG=g, CA=c, AC=c-1, GC=1, AG=1")
    print("   (n = a+g+2c+1, connected and balanced), ratio -> supremum:")
    def family(a, g, c):
        n = a + g + 2 * c + 1
        return Fraction(6 ** 7 * a ** 5 * c * g, n ** 7), n
    for (a, g, c) in ((5, 1, 1), (15, 3, 1), (27, 6, 3), (71, 14, 7),
                      (356, 71, 36), (1427, 286, 143)):
        r, n = family(a, g, c)
        print("      n=%4d (a,g,c)=(%d,%d,%d) ratio=%.6f" % (n, a, g, c, float(r)))
        assert r < SUP_AACAGG
    print("   supremum (not attained by any finite candidate) =", SUP_AACAGG,
          "=", float(SUP_AACAGG))


def part_f_degeneracies():
    print()
    print("=" * 74)
    print("E. Well-definedness checks")
    print("=" * 74)
    print("   (1) each factor (d_i/N)^x_i <= 1, so the likelihood part f(D) <= 1:")
    print("       bounded; no unbounded-likelihood candidate.")
    print("   (2) short candidates for the AAABB sample (0 when a type is missing):")
    for w in ("A", "AA", "AAA", "AAAB", "AAAAB", "AAABAAAAB"):
        print("         %-10s f = %s  ratio = %s"
              % (w, likelihood_part(w, SAMPLE_AAABB, L3),
                 ratio(w, S_AAABB, SAMPLE_AAABB, L3)))
    print("   (3) AAABB: 500/243 is attained, at lengths 9,18,27,... (plateau).")
    print("       Truth is not a maximiser: variable length does not restore it.")
    print("   (4) AACAGG: supremum %s is approached but not attained, so the"
          % SUP_AACAGG)
    print("       variable-length exact-ML maximum does not exist for that sample.")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--bin-max", type=int, default=22)
    ap.add_argument("--tern-max", type=int, default=9)
    ap.add_argument("--aacagg-lower", type=int, default=13)
    ap.add_argument("--aacagg-max", type=int, default=21)
    ap.add_argument("--bound-max", type=int, default=14)
    args = ap.parse_args()

    part_a_fixed_length_aaabb()
    part_b_variable_length_aaabb(args.bin_max, args.tern_max)
    part_b2_run_identities(min(args.bin_max, 18))
    part_c_family_aaabb()
    part_d_aacagg(args.aacagg_max, args.aacagg_lower)
    part_e_aacagg_bound(args.bound_max)
    part_f_degeneracies()
    print()
    print("all assertions passed.")


if __name__ == "__main__":
    main()
