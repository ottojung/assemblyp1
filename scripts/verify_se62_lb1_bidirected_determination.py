#!/usr/bin/env python3
"""Source-faithful MB09 §6.2 determination under vertex lower bound 1.

Object fixed here (see docs/section62-bidirected-lowerbound1-determination.md):

* reads are DNA molecules = unordered reverse-complement pairs; the binary
  involution is 0 <-> 1 and a read type is the class min(w, rc(w));
* the read-overlap graph is bidirected with overlaps of length >= o_min and is
  transitively reduced (the reduction preserves the set of spelled molecules);
* every read vertex has lower bound 1, all other lower bounds 0, upper bounds
  infinity;
* a flow's vertex throughput is, by MB09 Observation 7, the number of
  occurrences of the read in the spelled molecule;
* the §6.2 objective is the §6.1 separable binomial with the external known
  genome length N: maximise prod_w (d_w/N)^{x_w} (1 - d_w/N)^{n-x_w}.

This script verifies, with exact fractions.Fraction arithmetic:

A.  A rigorous counterexample under this corrected model:
        truth      S = AAATT   (00011)   G = 5, L = 3, N = 5
        reads      starts (0, 1, 4), x = {000:1, 001:1, 100:1}
        truth flow d_S = {000:1, 001:2, 100:2}
        competitor D   = AAAATT (000011), d_D = {000:2, 001:2, 100:2}
    with strict source bridging I_s, both S and D spelled/feasible, and
    L(D)/L(S) = 9/8 > 1.  Also the larger AAATAT witness (ratio 1280/243).

B.  An adversarial correction of the unmerged "infinite bridging-insufficiency
    family" S = 0^(G-1)1, D = 0^(G-2)1, L = G-2: under the strict bridging
    predicate used by the repository, I_s FAILS for every G >= 6, because the
    maximal triple repeat of length ell = G-3 has no copy that a length-(G-2)
    read can strictly bridge (strict bridging of an ell-copy needs a read of
    length >= ell + 2 = G - 1 > L).  The family's certificate used a
    wrap-around "covers both flanks" test, which is not the accepted predicate.

Exits non-zero on any failed assertion.
"""

from fractions import Fraction
from itertools import combinations


# ---------------------------------------------------------------------------
# circular windows, molecule classes, spectra
# ---------------------------------------------------------------------------

def circ_word(seq, start, length):
    g = len(seq)
    return tuple(seq[(start + i) % g] for i in range(length))


def revcomp(w):
    return tuple(1 - b for b in reversed(w))


def mol_class(w):
    return min(w, revcomp(w))


def spec(seq, length, quotient=False):
    counts = {}
    for s in range(len(seq)):
        w = circ_word(seq, s, length)
        key = mol_class(w) if quotient else w
        counts[key] = counts.get(key, 0) + 1
    return counts


def observed(seq, starts, length, quotient=False):
    counts = {}
    for r in starts:
        w = circ_word(seq, r, length)
        key = mol_class(w) if quotient else w
        counts[key] = counts.get(key, 0) + 1
    return counts


# ---------------------------------------------------------------------------
# strict bridging and I_s (Bresler-Bresler-Tse / Shomorony-Kim-Courtade-Tse)
# ---------------------------------------------------------------------------

def bridges_copy(seq, read_starts, read_len, t, ell):
    """Some read strictly contains the copy [t, t+ell) on a common lift.

    Strict extension on both sides: r < t  and  t + ell < r + read_len.
    This is the repository's accepted normalization of the source's
    "covers at least one base on both sides of the occurrence".
    """
    g = len(seq)
    for r in read_starts:
        for k in (-2, -1, 0, 1, 2):
            rr = r + k * g
            if rr < t and t + ell < rr + read_len:
                return True
    return False


def maximal_repeat_pairs(seq, ell):
    g = len(seq)
    out = []
    for t1, t2 in combinations(range(g), 2):
        if circ_word(seq, t1, ell) != circ_word(seq, t2, ell):
            continue
        if seq[(t1 - 1) % g] == seq[(t2 - 1) % g]:
            continue
        if seq[(t1 + ell) % g] == seq[(t2 + ell) % g]:
            continue
        out.append((t1, t2))
    return out


def maximal_triple_repeats(seq, ell):
    g = len(seq)
    out = []
    for t1, t2, t3 in combinations(range(g), 3):
        if not (circ_word(seq, t1, ell) == circ_word(seq, t2, ell)
                == circ_word(seq, t3, ell)):
            continue
        pre = {seq[(t - 1) % g] for t in (t1, t2, t3)}
        post = {seq[(t + ell) % g] for t in (t1, t2, t3)}
        if len(pre) == 1 or len(post) == 1:
            continue
        out.append((t1, t2, t3))
    return out


def cyclically_interleaved(a, b, c, d, g):
    if len({a % g, b % g, c % g, d % g}) < 4:
        return False

    def between(x, lo, hi):
        return 0 < (x - lo) % g < (hi - lo) % g

    return ((between(c, a, b) and between(d, b, a))
            or (between(d, a, b) and between(c, b, a)))


def check_I_s(seq, read_starts, read_len):
    """Shomorony et al. Eq. (1): coverage, every triple repeat all-bridged,
    every interleaved pair bridged.  Returns (ok, failing_copies)."""
    g = len(seq)
    failures = []
    covered = set()
    for r in read_starts:
        for i in range(read_len):
            covered.add((r + i) % g)
    if covered != set(range(g)):
        failures.append(("coverage", sorted(set(range(g)) - covered)))

    for ell in range(1, g + 1):
        for triple in maximal_triple_repeats(seq, ell):
            for t in triple:
                if not bridges_copy(seq, read_starts, read_len, t, ell):
                    failures.append(("triple", ell, t))

    for ell1 in range(1, g + 1):
        p1 = maximal_repeat_pairs(seq, ell1)
        for ell2 in range(1, g + 1):
            p2 = maximal_repeat_pairs(seq, ell2)
            for (a, b) in p1:
                for (c, d) in p2:
                    if (a, b, c, d) == (c, d, a, b):
                        continue
                    if not cyclically_interleaved(a, b, c, d, g):
                        continue
                    bridged = any(
                        bridges_copy(seq, read_starts, read_len, t, ell)
                        for (t, ell) in ((a, ell1), (b, ell1), (c, ell2), (d, ell2)))
                    if not bridged:
                        failures.append(("interleaved", ell1, a, b, ell2, c, d))
    return (not failures), failures


# ---------------------------------------------------------------------------
# §6.2 separable binomial likelihood
# ---------------------------------------------------------------------------

def lik_ratio(x, dS, dD, n, N):
    def prod(d):
        out = Fraction(1)
        for w, xw in x.items():
            dw = d.get(w, 0)
            out *= Fraction(dw, N) ** xw * (Fraction(N - dw, N)) ** (n - xw)
        return out
    return prod(dD) / prod(dS)


def certificate(name, S, L, starts, D, N):
    G = len(S)
    ok, fails = check_I_s(S, starts, L)
    assert ok, f"{name}: I_s FAILED: {fails}"

    x = observed(S, starts, L, quotient=True)
    dS = spec(S, L, quotient=True)
    dD = spec(D, L, quotient=True)
    n = sum(x.values())

    # both are spelled molecules: every window is an observed read type
    assert set(x) == set(dS) == set(dD), f"{name}: support mismatch"
    # vertex lower bound 1 for every observed read vertex
    assert all(v >= 1 for v in dS.values()), f"{name}: dS below 1"
    assert all(v >= 1 for v in dD.values()), f"{name}: dD below 1"
    # binomial domain 0 <= d_w <= N
    assert all(0 <= v <= N for v in dS.values()), f"{name}: dS outside [0,N]"
    assert all(0 <= v <= N for v in dD.values()), f"{name}: dD outside [0,N]"

    ratio = lik_ratio(x, dS, dD, n, N)
    assert ratio > 1, f"{name}: ratio not > 1"
    print(f"[counterexample] {name}")
    print(f"    S={''.join(map(str, S))}  D={''.join(map(str, D))}  "
          f"G={G} L={L} N={N} starts={starts} n={n}")
    print(f"    x ={dict(sorted(x.items()))}")
    print(f"    dS={dict(sorted(dS.items()))}")
    print(f"    dD={dict(sorted(dD.items()))}")
    print(f"    L(D)/L(S) = {ratio} = {float(ratio):.6f} > 1")
    return ratio


def kkt_family_failure(G):
    """The unmerged family S = 0^(G-1)1, D = 0^(G-2)1, L = G-2, reads = the
    windows of D placed at {0} U {2,...,G-1}."""
    L = G - 2
    S = [0] * (G - 1) + [1]
    D = [0] * (G - 2) + [1]
    starts = [0] + list(range(2, G))
    ok, fails = check_I_s(S, starts, L)
    # every maximal triple repeat of length ell has a copy that cannot be
    # strictly bridged when ell + 2 > L; here ell_max = G - 3 and L = G - 2.
    ell_max = 0
    for ell in range(1, G + 1):
        if maximal_triple_repeats(S, ell):
            ell_max = ell
    return ok, fails, ell_max, L


def main():
    print("MB09 §6.2 lower-bound-1 bidirected determination\n" + "=" * 52 + "\n")

    # A. rigorous finite counterexamples
    certificate("AAATT -> AAAATT",
                [0, 0, 0, 1, 1], 3, [0, 1, 4],
                [0, 0, 0, 0, 1, 1], 5)
    print()
    certificate("AAATAT -> AAATA",
                [0, 0, 0, 1, 0, 1], 3, [0, 0, 1, 3, 5],
                [0, 0, 0, 1, 0], 6)
    print()

    # B. adversarial correction of the unmerged infinite family
    print("=" * 52)
    print("Adversarial check of the unmerged 'infinite family'")
    print("S=0^(G-1)1, D=0^(G-2)1, L=G-2, reads = windows of D in S")
    for G in range(6, 13):
        ok, fails, ell_max, L = kkt_family_failure(G)
        assert not ok, f"G={G}: unexpected I_s success"
        triples = [f for f in fails if f[0] == "triple"]
        print(f"    G={G:2d} L={L:2d} ell_max={ell_max:2d}  "
              f"I_s=False  first failures: {fails[:2]}")
        # strict bridging an ell_max-copy needs a read of length >= ell_max+2
        assert ell_max + 2 > L, f"G={G}: length argument mismatch"
    print("\n    Reason: strict bridging of an ell-copy needs a read length")
    print("    >= ell+2.  Here ell_max = G-3 and L = G-2, so G-1 > L:")
    print("    no length-L read can strictly bridge a maximal (G-3)-copy.")
    print("    The family's certificate used a wrap-around 'both flanks' test.\n")

    print("All assertions passed.")


if __name__ == "__main__":
    main()
