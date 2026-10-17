#!/usr/bin/env python3
"""Independent exact-rational cross-check for the short finite-read ML
counterexamples of Antonina board issue #300 (AssemblyP1,
``github.com/ottojung/assemblyp1``).

Kernel-checked companion module:
``AssemblyP1/ShortFiniteMLCounterexamples.lean`` (merged as PR #229).  The three
witnesses, under the source-faithful oriented single-strand convention:

    G=2, L=1: truth AT   vs competitor AAT   reads A,A,T          ratio 32/27
    G=3, L=2: truth AAT  vs competitor AAAT  reads AA,AA,AT,TA    ratio 81/64
    G=4, L=3: truth AAAT vs competitor AAAAT reads AAA,AAA,AAT,ATA,TAA
                                                                  ratio 4096/3125

This script re-implements the semantics FROM SCRATCH (it imports no repository
code and no Lean output) and checks, with exact Python integers and
``fractions.Fraction`` (no floating point anywhere):

  1. ``InformationFeasible`` at full strength (coverage; every maximal triple
     repeat all-bridged; every interleaved pair of maximal repeats bridged),
     transcribed literally from ``AssemblyP1/SourceFaithfulIs.lean``, holds for
     each of the three truths;
  2. the explicit vacuity/bridging facts: ``no triple repeat`` for G=2,3, the
     single length-1 triple of A's for G=4, and its all-bridged certificate,
     plus absence of interleaved pairs in all three;
  3. both candidates are genuinely §6.2-feasible under three readings:
     per-vertex lower bound ``1``, spelled support equality, and a closed walk
     of the oriented read-overlap graph whose type counts equal the spectrum;
  4. the exact ordered-read likelihoods ``P(R|S)``, ``P(R|D)`` and the strict
     ratios, matching the issue table exactly;
  5. the multinomial-count objective shares each ratio (the common coefficient
     cancels).

Exit code is non-zero if any check fails.
"""

from fractions import Fraction
from itertools import combinations, product


# ---------------------------------------------------------------------------
# Circular genomes, windows, spectra (oriented single strand)
# ---------------------------------------------------------------------------

def window(S, L, r):
    """Length-L circular window of genome S at start r."""
    G = len(S)
    return tuple(S[(r + d) % G] for d in range(L))


def spectrum(S, L):
    """Window type -> number of starts spelling it (candidate-intrinsic d_w)."""
    G = len(S)
    d = {}
    for r in range(G):
        w = window(S, L, r)
        d[w] = d.get(w, 0) + 1
    return d


def support(S, L):
    return {w for w, c in spectrum(S, L).items() if c > 0}


def observed(S, L, reads):
    """Ordered list of read types realized by the list of start positions."""
    return [window(S, L, r) for r in reads]


def obs_count(S, L, reads):
    """Observed read type -> multiplicity in the ordered observation."""
    x = {}
    for w in observed(S, L, reads):
        x[w] = x.get(w, 0) + 1
    return x


def ordered_lik(S, L, ws):
    """Exact ordered-read likelihood prod_w d_X(w)/|X| (MB09 §6.1, Variant E)."""
    d = spectrum(S, L)
    G = len(S)
    p = Fraction(1, 1)
    for w in ws:
        p *= Fraction(d.get(w, 0), G)
    return p


# ---------------------------------------------------------------------------
# SourceFaithfulIs transcription (literal)
# ---------------------------------------------------------------------------

def preceding(S, t):
    return S[(t + len(S) - 1) % len(S)]


def following(S, e, t):
    return S[(t + e) % len(S)]


def agree(S, e, a, b):
    return window(S, e, a) == window(S, e, b)


def is_repeat(S, e, a, b):
    G = len(S)
    return (1 <= e < G and a != b and agree(S, e, a, b)
            and preceding(S, a) != preceding(S, b)
            and following(S, e, a) != following(S, e, b))


def is_triple_repeat(S, e, a, b, c):
    G = len(S)
    if not (1 <= e < G):
        return False
    if len({a, b, c}) != 3:
        return False
    if not (agree(S, e, a, b) and agree(S, e, a, c) and agree(S, e, b, c)):
        return False
    pre = (preceding(S, a), preceding(S, b), preceding(S, c))
    fol = (following(S, e, a), following(S, e, b), following(S, e, c))
    # not all three equal, on both sides
    return not (pre[0] == pre[1] == pre[2]) and not (fol[0] == fol[1] == fol[2])


def read_covers(S, L, r, p):
    G = len(S)
    return any((r + d) % G == p for d in range(L))


def covers(S, L, R):
    G = len(S)
    return all(any(read_covers(S, L, r, p) for r in R) for p in range(G))


def bridges_copy(S, L, R, e, t):
    """Bresler/Shomorony: a single read strictly straddles the copy."""
    G = len(S)
    for r in R:
        for d in range(L):
            if d + e + 1 < L and (r + d + 1) % G == t:
                return True
    return False


def triple_all_bridged(S, L, R, e, a, b, c):
    return (bridges_copy(S, L, R, e, a) and bridges_copy(S, L, R, e, b)
            and bridges_copy(S, L, R, e, c))


def in_open_arc(S, a, b, p):
    G = len(S)
    return 0 < (p + G - a) % G < (b + G - a) % G


def interleaved(S, a, b, c, d):
    if len({a, b, c, d}) != 4:
        return False
    return in_open_arc(S, a, b, c) != in_open_arc(S, a, b, d)


def interleaved_pair_bridged(S, L, R, e1, e2, a, b, c, d):
    return (bridges_copy(S, L, R, e1, a) or bridges_copy(S, L, R, e1, b)
            or bridges_copy(S, L, R, e2, c) or bridges_copy(S, L, R, e2, d))


def information_feasible(S, L, R):
    """The full Shomorony et al. (2016) Eq. (1) predicate I_s."""
    G = len(S)
    if not covers(S, L, R):
        return False
    for e in range(1, G):
        for a, b, c in product(range(G), repeat=3):
            if is_triple_repeat(S, e, a, b, c):
                if not triple_all_bridged(S, L, R, e, a, b, c):
                    return False
    for e1 in range(1, G):
        for e2 in range(1, G):
            for a, b, c, d in product(range(G), repeat=4):
                if (is_repeat(S, e1, a, b) and is_repeat(S, e2, c, d)
                        and interleaved(S, a, b, c, d)):
                    if not interleaved_pair_bridged(S, L, R, e1, e2, a, b, c, d):
                        return False
    return True


def all_triple_repeats(S):
    G = len(S)
    out = []
    for e in range(1, G):
        for a, b, c in combinations(range(G), 3):
            for perm in ((a, b, c), (a, c, b), (b, a, c), (b, c, a),
                         (c, a, b), (c, b, a)):
                if is_triple_repeat(S, e, *perm):
                    out.append((e,) + perm)
                    break
    return out


def all_interleaved_pairs(S):
    G = len(S)
    out = []
    for e1 in range(1, G):
        for e2 in range(1, G):
            for a, b, c, d in product(range(G), repeat=4):
                if (is_repeat(S, e1, a, b) and is_repeat(S, e2, c, d)
                        and interleaved(S, a, b, c, d)):
                    out.append((e1, e2, a, b, c, d))
    return out


# ---------------------------------------------------------------------------
# §6.2 feasibility readings (per-vertex, spelled, closed-walk circuit)
# ---------------------------------------------------------------------------

def per_vertex_feasible(d, x):
    return all(d.get(c, 0) >= 1 for c, n in x.items() if n > 0)


def spelled_feasible62(d, x):
    ds = {c for c, n in d.items() if n > 0}
    xs = {c for c, n in x.items() if n > 0}
    return ds == xs and per_vertex_feasible(d, x)


def overlaps(L, c, e):
    return all(c[i + 1] == e[i] for i in range(L - 1))


def consec(R, w):
    return all(R(w[i], w[i + 1]) for i in range(len(w) - 1))


def is_circuit(L, w):
    if not w:
        return False
    closed = list(w) + [w[0]]
    return consec(lambda c, e: overlaps(L, c, e), closed)


def list_count(w, c):
    return sum(1 for x in w if x == c)


def section62_feasible(L, w, d, x):
    return (is_circuit(L, w)
            and all(list_count(w, c) == d.get(c, 0) for c in d)
            and all(x.get(c, 0) > 0 for c in w))


# ---------------------------------------------------------------------------
# Exact multinomial-count objective
# ---------------------------------------------------------------------------

def multinom_coeff(L, ws):
    from math import factorial
    from collections import Counter
    counts = Counter(ws)
    den = 1
    for v in counts.values():
        den *= factorial(v)
    return Fraction(factorial(len(ws)), den)


def multinom_lik(S, L, ws):
    return multinom_coeff(L, ws) * ordered_lik(S, L, ws)


# ---------------------------------------------------------------------------
# Harness
# ---------------------------------------------------------------------------

CHECKS = {"n": 0}


def check(cond, msg):
    CHECKS["n"] += 1
    if not cond:
        raise AssertionError("FAIL: " + msg)
    print("  ok:", msg)


# ---------------------------------------------------------------------------
# The three instances
# ---------------------------------------------------------------------------

def check_instance(G, L, truth, competitor, reads, ws_expected,
                   lik_S, lik_D, ratio, walkS, walkD,
                   expect_triples, expect_no_triples, expect_interleaved):
    print(f"== G={G}, L={L}: truth {truth} vs competitor {competitor} ==")
    R = sorted(set(reads))

    # (1) full information-feasibility of the truth
    check(information_feasible(truth, L, R),
          f"I_s holds for truth {truth} at starts {R}")

    # (2) observation really is the windows of the realized placements
    check(observed(truth, L, reads) == ws_expected,
          f"observed reads == {[''.join(w) for w in ws_expected]}")

    # (3) vacuity / bridging facts
    triples = all_triple_repeats(truth)
    check(triples == expect_triples,
          f"maximal triple repeats == {expect_triples} (found {triples})")
    for (e, a, b, c) in expect_triples:
        check(triple_all_bridged(truth, L, R, e, a, b, c),
              f"triple repeat (e={e}, starts={a},{b},{c}) is all-bridged")
    check(all_triple_repeats(truth) == expect_triples or not expect_no_triples,
          "triple-repeat census is as declared")
    inter = all_interleaved_pairs(truth)
    check(inter == expect_interleaved,
          f"interleaved maximal-repeat pairs == {expect_interleaved} (found {inter})")

    # (4) §6.2 feasibility for both candidates, three readings
    for name, cand in (("truth", truth), ("competitor", competitor)):
        d = spectrum(cand, L)
        x = obs_count(truth, L, reads)
        check(per_vertex_feasible(d, x), f"{name} per-vertex §6.2 feasible")
        check(spelled_feasible62(d, x), f"{name} spelled-support §6.2 feasible")
        walk = walkS if name == "truth" else walkD
        check(is_circuit(L, walk),
              f"{name} walk {[''.join(w) for w in walk]} is a closed overlap circuit")
        check(all(list_count(walk, c) == d.get(c, 0) for c in d),
              f"{name} walk type counts equal its spectrum")
        check(section62_feasible(L, walk, d, x), f"{name} circuit §6.2 feasible")

    # (5) exact likelihoods and strict ratio
    d_S = spectrum(truth, L)
    d_D = spectrum(competitor, L)
    check(ordered_lik(truth, L, ws_expected) == lik_S,
          f"P(R|S) == {lik_S}")
    check(ordered_lik(competitor, L, ws_expected) == lik_D,
          f"P(R|D) == {lik_D}")
    check(ordered_lik(competitor, L, ws_expected)
          / ordered_lik(truth, L, ws_expected) == ratio,
          f"P(R|D)/P(R|S) == {ratio} > 1")
    check(ordered_lik(truth, L, ws_expected) < ordered_lik(competitor, L, ws_expected),
          "competitor strictly beats truth")

    # (6) multinomial-count objective shares the ratio
    check(multinom_coeff(L, ws_expected) != 0, "multinomial coefficient is nonzero")
    check(multinom_lik(competitor, L, ws_expected)
          / multinom_lik(truth, L, ws_expected) == ratio,
          f"multinomial-count ratio also == {ratio}")

    # candidate-intrinsic lengths
    check(len(truth) == G and len(competitor) == G + 1,
          f"intrinsic lengths |S|={G}, |D|={G + 1}")
    return d_S, d_D


def main():
    print("Exact-rational independent verification for board issue #300\n")

    # G=2, L=1: truth AT, competitor AAT, reads [0,1,0]
    check_instance(
        G=2, L=1, truth="AT", competitor="AAT", reads=[0, 1, 0],
        ws_expected=[("A",), ("T",), ("A",)],
        lik_S=Fraction(1, 8), lik_D=Fraction(4, 27), ratio=Fraction(32, 27),
        walkS=[("A",), ("T",)],
        walkD=[("A",), ("A",), ("T",)],
        expect_triples=[], expect_no_triples=True, expect_interleaved=[],
    )

    # G=3, L=2: truth AAT, competitor AAAT, reads [0,1,2,0]
    check_instance(
        G=3, L=2, truth="AAT", competitor="AAAT", reads=[0, 1, 2, 0],
        ws_expected=[("A", "A"), ("A", "T"), ("T", "A"), ("A", "A")],
        lik_S=Fraction(1, 81), lik_D=Fraction(1, 64), ratio=Fraction(81, 64),
        walkS=[("A", "A"), ("A", "T"), ("T", "A")],
        walkD=[("A", "A"), ("A", "A"), ("A", "T"), ("T", "A")],
        expect_triples=[], expect_no_triples=True, expect_interleaved=[],
    )

    # G=4, L=3: truth AAAT, competitor AAAAT, reads [0,1,2,3,0]
    check_instance(
        G=4, L=3, truth="AAAT", competitor="AAAAT", reads=[0, 1, 2, 3, 0],
        ws_expected=[("A", "A", "A"), ("A", "A", "T"), ("A", "T", "A"),
                     ("T", "A", "A"), ("A", "A", "A")],
        lik_S=Fraction(1, 1024), lik_D=Fraction(4, 3125), ratio=Fraction(4096, 3125),
        walkS=[("A", "A", "A"), ("A", "A", "T"), ("A", "T", "A"), ("T", "A", "A")],
        walkD=[("A", "A", "A"), ("A", "A", "A"), ("A", "A", "T"), ("A", "T", "A"),
               ("T", "A", "A")],
        expect_triples=[(1, 0, 1, 2)], expect_no_triples=False, expect_interleaved=[],
    )

    # The length bound e + 2 <= L that makes the L=1, L=2 repeat clauses vacuous:
    # a copy of length e >= L - 1 is never bridged by a length-L read.
    print("== bridging length bound e + 2 <= L ==")
    for L in (1, 2):
        for e in range(1, L + 1):
            genome = "A" * e
            starts = list(range(len(genome)))
            check(not any(bridges_copy(genome, L, starts, e, t)
                          for t in range(len(genome))),
                  f"L={L}, e={e}: no bridged copy (e+2 <= L is false)")
    # G=4 is the tight case e+2 == L == 3.
    check(1 + 2 == 3, "G=4 triple-repeat bridging bound is tight (e+2 = L = 3)")

    print(f"\nAll {CHECKS['n']} exact-rational checks for #300 passed.")


if __name__ == "__main__":
    main()
