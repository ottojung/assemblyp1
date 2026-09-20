#!/usr/bin/env python3
"""
Membership of the repository's bridging/ML counterexamples in the
Medvedev-Brudno section 6.2 flow-feasible candidate set.

Two levels of section 6.2 feasibility are distinguished (see
docs/section-6-2-feasible-set-membership.md):

  * copy-vector (flow) level: an integer circulation on the read-overlap graph
    whose per-vertex out-value vector d/D projected onto the observed read
    vertices satisfies d_w >= x_w.  This is a (possibly non-contiguous)
    assembly, not a sequence.

  * sequence (walk-spelling) level: a circular genome D every length-L window
    of which is an observed read type (so a closed walk spells D), with each
    observed read occurrence used at least once.  Equivalently
    supp(spec(D)) subseteq supp(x) and d_D(w) >= x_w for all observed w.
    This is the level at which Observation 7 of the source holds: the number
    of times the walk visits a read equals the number of times it occurs as a
    submolecule of the spelled molecule.

All arithmetic is exact (fractions.Fraction).  Exits non-zero if any assertion
fails.
"""
from fractions import Fraction
from collections import Counter


def spec(seq, L):
    G = len(seq)
    return Counter(tuple(seq[(i + j) % G] for j in range(L)) for i in range(G))


def observed(seq, starts, L):
    G = len(seq)
    x = Counter()
    for r in starts:
        x[tuple(seq[(r + j) % G] for j in range(L))] += 1
    return x


def support_contained(dD, x):
    return set(dD) <= set(x)


def per_occurrence(dD, x):
    return all(dD.get(w, 0) >= c for w, c in x.items())


def unobserved(dD, x):
    return sorted("".join(w) for w in set(dD) - set(x))


def obs7_ok(D, L, placement):
    """Observation-7 admissibility of a cyclic placement of read occurrences.

    `placement` is a list of (start, read_type_string).  The induced window
    multiset must equal the full spectrum of D: every window of D must be a
    visited read.  A walk that overlaps reads by less than L-1 can leave an
    intermediate window of D unvisited, which violates Observation 7.
    """
    G = len(D)
    induced = Counter()
    for r, rd in placement:
        if tuple(D[(r + j) % G] for j in range(L)) != tuple(rd):
            return False, None, None
        induced[rd] += 1
    dD = Counter({tuple(k): v for k, v in spec(D, L).items()})
    induced_t = Counter({tuple(k): v for k, v in induced.items()})
    return induced_t == dD, dD, induced_t


def binomial62(seq, L, x, N):
    n = sum(x.values())
    d = spec(seq, L)
    prod = Fraction(1)
    for w, xw in x.items():
        dw = d.get(w, 0)
        if dw == 0:
            return Fraction(0)
        if dw > N:
            return Fraction(0)
        prod *= Fraction(dw, N) ** xw * Fraction(N - dw, N) ** (n - xw)
    return prod


# (name, S, D, L, starts).  `starts` are the realized latent start positions.
CASES = [
    ("kernel-checked fixed-length exact (AAABB->AAAAB)",
     "AAABB", "AAAAB", 3, [0, 1, 4]),
    ("fixed-length binomial (AAACC->AAAAC)",
     "AAACC", "AAAAC", 3, [0, 1, 4]),
    ("interleaved clause, same word (AAABACC->AAAABAC)",
     "AAABACC", "AAAABAC", 3, [0, 1, 3, 6]),
    ("interleaved clause, distinct words (ABACABC->ACABACB)",
     "ABACABC", "ACABACB", 3, [1, 1, 1, 3, 6]),
    ("read-tiled / per-occurrence (AAABCBC->AAAAABC)",
     "AAABCBC", "AAAAABC", 3, [0, 0, 0, 1, 2, 5, 6]),
    ("smallest flow-feasible (AACC->ACAC)",
     "AACC", "ACAC", 2, [1, 3]),
]


def main():
    print("=" * 78)
    print("Section 6.2 feasible-set membership of current counterexamples")
    print("=" * 78)
    ok = True
    for name, S, D, L, starts in CASES:
        x = observed(S, starts, L)
        dS, dD = spec(S, L), spec(D, L)
        in_SC_D = support_contained(dD, x)
        in_F_D = in_SC_D and per_occurrence(dD, x)
        in_SC_S = support_contained(dS, x)
        in_F_S = in_SC_S and per_occurrence(dS, x)
        print(f"\n{name}")
        print(f"  S={S} D={D} L={L} starts={starts}")
        print(f"  observed x = { {''.join(k): v for k, v in x.items()} }")
        print(f"  D: sequence-level feasible = {in_F_D}"
              + (f"   (D has unobserved windows {unobserved(dD, x)})"
                 if not in_SC_D else ""))
        print(f"  S: sequence-level feasible = {in_F_S}"
              + (f"   (S has unobserved windows {unobserved(dS, x)})"
                 if not in_SC_S else ""))
        if in_F_D:
            N = len(S)
            r = binomial62(D, L, x, N) / binomial62(S, L, x, N)
            print(f"  section 6.2 binomial objective ratio L(D)/L(S) = {r}"
                  f"  (>1: {r > 1})")

    # ---- The unmerged AAACC flow-feasibility claim under audit -------------
    print("\n" + "-" * 78)
    print("Audit: claimed section 6.2 walk for the AAACC competitor D=AAAAC")
    print("-" * 78)
    S, D, L = "AAACC", "AAAAC", 3
    x = observed(S, [0, 1, 4], L)
    dD = spec(D, L)
    print(f"  observed x = { {''.join(k): v for k, v in x.items()} }")
    print(f"  d_D = { {''.join(k): v for k, v in dD.items()} }")
    print(f"  D is sequence-level feasible: {support_contained(dD, x)}"
          f"  (unobserved windows {unobserved(dD, x)})")
    placement = [(0, "AAA"), (1, "AAA"), (2, "AAC"), (4, "CAA")]
    good, dD2, induced = obs7_ok(D, L, placement)
    print(f"  claimed placement {placement}")
    print(f"  placement is a valid spell of D and satisfies Observation 7: {good}")
    print(f"    induced visited windows = "
          f"{ {''.join(k): v for k, v in induced.items()} }")
    print(f"    full spectrum of D      = "
          f"{ {''.join(k): v for k, v in dD2.items()} }")
    print("  => the copy vector (AAA:2,AAC:1,CAA:1) is a feasible *flow* on the")
    print("     observed vertices, but it is a non-contiguous assembly; the")
    print("     genome D=AAAAC is NOT sequence-level section 6.2-feasible.")

    # assertions
    x62 = observed("AAACC", [0, 1, 4], 3)
    assert not support_contained(spec("AAAAC", 3), x62)
    assert per_occurrence(spec("AAAAC", 3), x62)  # counts pass, support fails
    assert not obs7_ok("AAAAC", 3, placement)[0]
    need_sc = support_contained(spec("AAAAABC", 3),
                                observed("AAABCBC", [0, 0, 0, 1, 2, 5, 6], 3))
    assert need_sc and per_occurrence(spec("AAAAABC", 3),
                                      observed("AAABCBC", [0, 0, 0, 1, 2, 5, 6], 3))
    assert support_contained(spec("ACAC", 2), observed("AACC", [1, 3], 2))
    assert per_occurrence(spec("ACAC", 2), observed("AACC", [1, 3], 2))
    print("\nALL ASSERTIONS PASS")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
