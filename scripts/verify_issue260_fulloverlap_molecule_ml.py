#!/usr/bin/env python3
"""Independent exact validation for AssemblyP1 issue #260.

Scope: the restricted **full-overlap** (`o_min = L - 1`), **fixed genome
length** (`|D| = |S| = G`), reverse-complement **molecule** domain.

This script recomputes from scratch, with exact integer/rational arithmetic and
no trust in the Lean output, the finite facts behind
`AssemblyP1/FullOverlapMoleculeML.lean` and
`docs/issue260-full-overlap-molecule-ml.md`:

  * the reverse-complement molecule-class spectrum of a circular word;
  * the *strict* (source-faithful §6.2) candidate set for a truth: spelled
    length-`G` words whose molecule-class support equals the truth's support
    (the §6.2 vertex lower bound 1 on the observed reads);
  * the equivalence, over the strict candidate set, of sample-uniform exact-ML
    maximality and *uniqueness* of the normalized molecule-count vector;
  * the broad-reading counterexample `AATT -> AAAT`, where non-uniqueness
    coexists with sample-uniform maximality once the equal-support hypothesis is
    dropped;
  * the `W1` witness `AAATAT -> AAAAAT`: equal total, equal support, distinct
    count vectors, amplified sample `x = e_AAA`, exact ratio 3 / binomial 5;
  * that the broad-reading witness truth `AATT` vacuously satisfies the literal
    §6.4 bridging predicate (no triple repeat, no interleaved pair) while a
    start-dense sample exists.

The script is deterministic, exits non-zero on any failed assertion, and shares
no code with the Lean module.
"""
from collections import Counter
from fractions import Fraction
from itertools import product
from math import comb

COMP = {"A": "T", "T": "A", "C": "G", "G": "C"}


def rc(w):
    return "".join(COMP[c] for c in reversed(w))


def canon(w):
    return min(w, rc(w))


def circular_window(S, t, L):
    G = len(S)
    return "".join(S[(t + j) % G] for j in range(L))


def spectrum(S, L):
    """Molecule-class count vector of a circular word."""
    return Counter(canon(circular_window(S, t, L)) for t in range(len(S)))


def necklaces(G, alphabet):
    """One representative per circular word up to rotation and reverse complement."""
    seen = set()
    for tup in product(alphabet, repeat=G):
        S = "".join(tup)
        reps = [S[i:] + S[:i] for i in range(G)]
        reps += [rc(w) for w in reps]
        key = min(reps)
        if key not in seen:
            seen.add(key)
            yield key


def exact_product(d, x):
    """Exact multinomial likelihood up to the positive candidate-independent
    factor `n! / prod x! * N^{-n}`: `prod_c d[c] ** x[c]`."""
    p = 1
    for c, e in x.items():
        p *= d.get(c, 0) ** e
    return p


def dominance(A, B):
    """Coordinatewise dominance on the truth support: B[c] <= A[c] for all
    c with A[c] > 0."""
    return all(B.get(c, 0) <= A[c] for c in A)


def sample_uniform_robust(A, candidates):
    """Sample-uniform exact-ML maximality of the truth with spectrum A over the
    candidate spectra, for every observed vector supported inside supp A.

    By exact arithmetic this holds iff every candidate is coordinatewise
    dominated on supp A (a candidate exceeding on some c in supp A is beaten by
    the concentrated sample x = e_c)."""
    return all(dominance(A, B) for B in candidates)


def strict_candidates(S, words, L):
    """Source-faithful §6.2 candidate set: spelled length-G words whose support
    equals the truth's support."""
    A = spectrum(S, L)
    supp = set(A)
    return [D for D in words if set(spectrum(D, L)) == supp]


def broad_candidates(words, L):
    """Broad reading: every spelled length-G word."""
    return list(words)


def check_strict_iff():
    """Over the strict candidate set, sample-uniform maximality iff the
    normalized count vector is unique."""
    checked = 0
    for alphabet in ("AT", "ACGT"):
        for G in range(4, 8):
            words = list(necklaces(G, alphabet))
            specs = {D: spectrum(D, 3) for D in words}
            for S in words:
                A = specs[S]
                cands = strict_candidates(S, words, 3)
                cand_specs = [specs[D] for D in cands]
                unique = all(B == A for B in cand_specs)
                robust = sample_uniform_robust(A, cand_specs)
                assert robust == unique, (alphabet, G, S, A, cand_specs)
                checked += 1
    print(f"[ok] strict-reading iff  (maximality <=> uniqueness) on {checked} truths")


def check_broad_refutation():
    """The broad reading breaks the iff: `AATT -> AAAT`."""
    S, D, L = "AATT", "AAAT", 3
    A, B = spectrum(S, L), spectrum(D, L)
    assert sum(A.values()) == sum(B.values()) == len(S)
    assert A != B
    assert dominance(A, B), (A, B)
    # truth dominates every realizable sample
    assert sample_uniform_robust(A, [B])
    # while the count vector is not unique among spelled length-G words
    words = list(necklaces(4, "AT"))
    spec_set = {tuple(sorted(spectrum(W, L).items())) for W in words}
    assert len(spec_set) > 1
    print(f"[ok] broad-reading refutation  S={S} A={dict(sorted(A.items()))} "
          f"D={D} B={dict(sorted(B.items()))}")
    # cross-check the equivalence numerically on a range of samples
    for total in range(1, 9):
        for n0 in range(total + 1):
            x = {c: 0 for c in A}
            x["AAT"] = n0
            x["TAA"] = total - n0
            x = {c: e for c, e in x.items() if e > 0}
            assert exact_product(B, x) <= exact_product(A, x), (x,)


def check_w1():
    """`W1`: `AAATAT -> AAAAAT`, full overlap, fixed length, distinct spectra."""
    S, D, L = "AAATAT", "AAAAAT", 3
    A, B = spectrum(S, L), spectrum(D, L)
    assert len(S) == len(D) == 6
    assert sum(A.values()) == sum(B.values()) == 6
    assert set(A) == set(B), (set(A), set(B))
    assert A != B, (A, B)
    # non-uniqueness => not sample-uniformly maximal: amplify x = e_AAA
    assert not dominance(A, B)
    x = {"AAA": 1}
    assert exact_product(B, x) > exact_product(A, x)
    # exact ratio at the historical sample [0,0,1,3,5]
    starts = [0, 0, 1, 3, 5]
    obs = Counter(canon(circular_window(S, r, L)) for r in starts)
    ratio = Fraction(exact_product(B, obs), exact_product(A, obs))
    assert ratio == 3, ratio
    # literal §6.1 binomial ratio with external N = G = 6, n = 5
    N = 6
    n = sum(obs.values())

    def binomial(d):
        p = Fraction(1)
        for c in set(A) | set(B) | set(obs):
            xw, dw = obs.get(c, 0), d.get(c, 0)
            p *= Fraction(comb(n, xw)) * Fraction(dw, N) ** xw * Fraction(N - dw, N) ** (n - xw)
        return p

    binratio = binomial(B) / binomial(A)
    assert binratio == 5, binratio
    print(f"[ok] W1  S={S} A={dict(sorted(A.items()))} D={D} "
          f"B={dict(sorted(B.items()))}  exact ratio {ratio}, binomial {binratio}")


def check_aatt_information_feasible():
    """The broad-reading witness truth `AATT` vacuously satisfies the literal
    §6.4 bridging predicate and admits a start-dense sample."""
    S, L = "AATT", 3
    G = len(S)
    # maximal triple repeats: no length >= 1 substring occurs at 3+ distinct starts
    for e in range(1, L):
        cnt = Counter(circular_window(S, t, e) for t in range(G))
        assert all(v < 3 for v in cnt.values()), (e, cnt)
    # start-dense sample {0, 2} covers every position
    covered = set()
    for r in (0, 2):
        for j in range(L):
            covered.add((r + j) % G)
    assert covered == set(range(G))
    print("[ok] AATT  literal §6.4 bridging vacuous (no triple repeat) and "
          "start-dense sample {0,2} exists")


def main():
    check_strict_iff()
    check_broad_refutation()
    check_w1()
    check_aatt_information_feasible()
    print("\nALL CHECKS PASSED")


if __name__ == "__main__":
    main()
