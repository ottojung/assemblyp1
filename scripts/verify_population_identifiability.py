#!/usr/bin/env python3
"""
Population / infinite-read identifiability for intrinsically admissible
primitive circular genomes (issue #48 optional population question; issue #45
data-regime analogue).

Question attacked
-----------------
For a fixed read length L, a circular genome D of length n induces the
*population read distribution* over length-L words

    p_D(w) = d_D(w) / n,      d_D(w) = #cyclic occurrences of w in D.

In the infinite-read (i.i.d. uniform start) limit this is the observed law.
The question is purely combinatorial:

    if p_D = p_S for two intrinsically admissible, primitive circular genomes,
    must D be a cyclic shift of S?

This script is a self-contained exact-arithmetic verifier for the statements of
`docs/population-identifiability-intrinsic-genomes.md`.  It does not decide the
published 2016 question and does not assume that the population regime is the
primary repair.

Conventions (fixed here, stated explicitly)
-------------------------------------------
* Alphabet: finite; witnesses use {A,B} / {A,B,C}.
* Strand/read type: single-strand *oriented* length-L reads (the
  Shomorony/Bresler panel).  Genome equivalence is cyclic shift.  A separate
  section checks the reverse-complement/molecule panel.
* Intrinsic candidate predicates on D (properties of D and L alone):
    STRONG(D) : no (L-1)-mer of D occurs twice.
    WEAK(D)   : every maximal triple repeat of D has length <= L-2 and every
                interleaved maximal-repeat pair has a constituent of length
                <= L-2.  This is the candidate-intrinsic shadow of the source
                read feasibility condition I_s at the full read set.
    primitive(D): D is not a nontrivial power w^m, m >= 2.
* Normalized spectrum: two words have the same population read distribution
  iff d_D(w)/|D| = d_S(w)/|S| for every w, i.e. d_D = c * d_S for a rational
  c > 0.

Checks (all exact / deterministic; exits non-zero on any failed assertion)
-------------------------------------------------------------------------
  A. Population consistency (Gibbs/KL): for a fixed candidate length G, the
     population objective ell(D) = sum_w p(w) log(d_D(w)/G) is maximized
     exactly by the spectra d_D = d_S.
  B. Lemma L*: a primitive WEAK-admissible word has every (L-1)-mer occurring
     at most twice.  Exhaustively checked on the stated ranges.
  C. Theorem P (cross-length exclusion): no two primitive WEAK-admissible
     words have proportional L-mer spectra with different lengths.  Exhaustive
     normalized-spectrum collision search on the stated ranges.
  D. Sharpness of the hypotheses:
       D1. primitivity is necessary  -- the tandem word S^2 is WEAK-admissible
           for explicitly verified S and has the same population distribution;
       D2. candidate-side WEAK-admissibility is necessary -- a primitive but
           non-WEAK word can share the truth's population distribution.
  E. Reverse-complement (molecule) panel boundary: even primitive STRONG
     equal-length genomes AACAGT / AACTGT share the same molecule-class
     population distribution without being cyclically or dihedrally related.
  F. STRONG sampling theorem (oriented): if S is STRONG then every word with
     the same population distribution is a power of S up to rotation, hence
     non-primitive unless equal to S.
"""

from __future__ import annotations

from collections import defaultdict
from fractions import Fraction
from itertools import combinations, product


# ---------------------------------------------------------------------------
# Circular words
# ---------------------------------------------------------------------------
def rotations(w):
    return [w[i:] + w[:i] for i in range(len(w))]


def canonical(w):
    return min(rotations(w))


def primitive(w):
    n = len(w)
    return not any(n % p == 0 and w == w[:p] * (n // p) for p in range(1, n))


def windows(w, L):
    n = len(w)
    d = defaultdict(int)
    for i in range(n):
        d[tuple(w[(i + j) % n] for j in range(L))] += 1
    return dict(d)


def normalized_spectrum(w, L):
    n = len(w)
    return tuple(sorted((k, Fraction(v, n)) for k, v in windows(w, L).items()))


# ---------------------------------------------------------------------------
# Bresler repeat structures and intrinsic admissibility
# ---------------------------------------------------------------------------
def maximal_pairs(word):
    n = len(word)
    out = []
    for ell in range(1, n):
        groups = defaultdict(list)
        for i in range(n):
            groups[tuple(word[(i + j) % n] for j in range(ell))].append(i)
        for _w, ts in groups.items():
            for a, b in combinations(ts, 2):
                if word[(a - 1) % n] != word[(b - 1) % n] and \
                   word[(a + ell) % n] != word[(b + ell) % n]:
                    out.append((ell, (a, b)))
    return out


def has_long_triple_repeat(word, L):
    """A Bresler triple repeat of length >= L-1."""
    n = len(word)
    for ell in range(max(1, L - 1), n):
        groups = defaultdict(list)
        for i in range(n):
            groups[tuple(word[(i + j) % n] for j in range(ell))].append(i)
        for _w, ts in groups.items():
            if len(ts) < 3:
                continue
            for tri in combinations(ts, 3):
                pres = {word[(t - 1) % n] for t in tri}
                posts = {word[(t + ell) % n] for t in tri}
                if len(pres) > 1 and len(posts) > 1:
                    return True
    return False


def has_long_interleaved_pair(word, L):
    """Two maximal repeat pairs, both legs >= L-1, alternating."""
    reps = [r for r in maximal_pairs(word) if r[0] >= L - 1]
    for (e1, p1), (e2, p2) in combinations(reps, 2):
        four = sorted(set(p1) | set(p2))
        if len(four) != 4:
            continue
        labels = [0 if p in p1 else 1 for p in four]
        if labels in ([0, 1, 0, 1], [1, 0, 1, 0]):
            return True
    return False


def trf_admissible(word, L):
    """No Bresler triple repeat of length >= L-1 (triple-repeat-free)."""
    return not has_long_triple_repeat(word, L)


def ilf_admissible(word, L):
    """No interleaved maximal-repeat pair with both legs >= L-1."""
    return not has_long_interleaved_pair(word, L)


def weak_admissible(word, L):
    """Candidate-intrinsic I_s shadow = TRF & ILF (full-read-set admissibility)."""
    return trf_admissible(word, L) and ilf_admissible(word, L)


def strong_admissible(word, L):
    """No (L-1)-mer occurs twice."""
    return all(v <= 1 for v in windows(word, L - 1).values())


# ---------------------------------------------------------------------------
# Reverse complement (molecule panel)
# ---------------------------------------------------------------------------
_COMP = {"A": "T", "T": "A", "C": "G", "G": "C"}


def revcomp(w):
    return tuple(_COMP[c] for c in reversed(w))


def molecule_class(w):
    r = revcomp(w)
    return min(w, r)


def molecule_spectrum(w, L):
    n = len(w)
    d = defaultdict(int)
    for k, v in windows(w, L).items():
        d[molecule_class(k)] += v
    return tuple(sorted((k, Fraction(v, n)) for k, v in d.items()))


# ---------------------------------------------------------------------------
# Checks
# ---------------------------------------------------------------------------
def check_A_population_consistency(alpha, sizes):
    """Fixed candidate length G: population objective is maximized at d_S."""
    import math

    for G in sizes:
        for L in range(2, G + 1):
            spectra = set()
            for w in product(alpha, repeat=G):
                spectra.add(tuple(sorted(windows(w, L).items())))
            reps = {canonical(w): w for w in product(alpha, repeat=G)}
            for w in reps.values():
                dS = windows(w, L)
                p = {t: Fraction(c, G) for t, c in dS.items()}
                best = None
                winners = []
                for ds in spectra:
                    dD = dict(ds)
                    if any(p.get(t, 0) > 0 and dD.get(t, 0) == 0 for t in p):
                        continue
                    val = sum(pt * math.log(dD[t] / G)
                              for t, pt in p.items() if pt > 0)
                    if best is None or val > best + 1e-12:
                        best, winners = val, [dD]
                    elif abs(val - best) <= 1e-12:
                        winners.append(dD)
                for dD in winners:
                    assert dD == dS, (G, L, w, dD, dS)
    return True


def _enumerate_primitive_canonicals(alpha, maxG, L):
    for n in range(L, maxG + 1):
        for w in product(alpha, repeat=n):
            if not primitive(w) or w != tuple(canonical(w)):
                continue
            yield w


def check_B_lemma_Lstar(alpha, maxG, maxL):
    """Primitive TRF => every (L-1)-mer occurs at most twice."""
    max_seen = 0
    for L in range(2, maxL + 1):
        for n in range(L, maxG + 1):
            for w in product(alpha, repeat=n):
                if w != tuple(canonical(w)) or not primitive(w):
                    continue
                if not trf_admissible(w, L):
                    continue
                m = max(windows(w, L - 1).values())
                max_seen = max(max_seen, m)
                assert m <= 2, (L, w, m)
    return max_seen


def check_C1_cross_length_trf(alpha, maxG, maxL):
    """No two primitive TRF words have proportional spectra of different lengths."""
    words = 0
    spectra = 0
    for L in range(2, maxL + 1):
        byn = defaultdict(dict)
        for w in _enumerate_primitive_canonicals(alpha, maxG, L):
            if not trf_admissible(w, L):
                continue
            words += 1
            byn[len(w)][w] = normalized_spectrum(w, L)
        seen = {}
        for n, table in byn.items():
            for w, key in table.items():
                spectra += 1
                if key in seen and seen[key][0] != n:
                    assert False, ("cross-length TRF collision", L, seen[key][1], w)
                seen[key] = (n, w)
    return words, spectra


def check_C2_same_length_weak(alpha, maxG, maxL):
    """No two primitive WEAK words of equal length share a normalized spectrum."""
    words = 0
    spectra = 0
    for L in range(2, maxL + 1):
        groups = defaultdict(list)
        for w in _enumerate_primitive_canonicals(alpha, maxG, L):
            if not weak_admissible(w, L):
                continue
            words += 1
            groups[normalized_spectrum(w, L)].append(w)
        spectra += len(groups)
        for ws in groups.values():
            if len(ws) < 2:
                continue
            for a, b in combinations(ws, 2):
                assert False, ("same-length WEAK collision", L, a, b)
    return words, spectra


def check_D1_primitivity_necessary():
    """S = AAB (L=3) is primitive WEAK; S^2 is WEAK, same population law."""
    S = tuple("AAB")
    D = S + S
    L = 3
    assert primitive(S)
    assert weak_admissible(S, L)
    assert not primitive(D)
    assert weak_admissible(D, L)
    assert normalized_spectrum(S, L) == normalized_spectrum(D, L)
    assert canonical(S) != canonical(D)
    # a second, shorter instance
    A = tuple("AB")
    B = A + A
    L2 = 2
    assert primitive(A) and weak_admissible(A, L2)
    assert not primitive(B) and weak_admissible(B, L2)
    assert normalized_spectrum(A, L2) == normalized_spectrum(B, L2)
    assert canonical(A) != canonical(B)
    return True


def check_D2_candidate_admissibility_necessary():
    """Primitive non-WEAK D shares a primitive WEAK truth's population law."""
    cases = [(tuple("AAAB"), tuple("AAAABAAB"), 3),
             (tuple("AAB"), tuple("AAABAB"), 2)]
    for S, D, L in cases:
        assert primitive(S), S
        assert weak_admissible(S, L), S
        assert primitive(D), D
        assert not weak_admissible(D, L), D
        assert not trf_admissible(D, L), D
        assert normalized_spectrum(S, L) == normalized_spectrum(D, L)
        assert canonical(S) != canonical(D)
    # A primitive TRF & ILF word need not have a proportional spectrum: the
    # finite-support failure S=AAAB, D=AAABAB (L=3) is not a population
    # collision (it has an extra type and a doubly counted type).
    S, D, L = tuple("AAAB"), tuple("AAABAB"), 3
    assert primitive(S) and primitive(D)
    assert trf_admissible(S, L) and ilf_admissible(S, L)
    assert trf_admissible(D, L) and ilf_admissible(D, L)
    assert normalized_spectrum(S, L) != normalized_spectrum(D, L)
    return True


def check_E_molecule_panel():
    """Molecule/revcomp panel: primitive STRONG equal-length counterexample."""
    S = tuple("AACAGT")
    D = tuple("AACTGT")
    L = 3
    assert primitive(S) and primitive(D)
    assert strong_admissible(S, L) and strong_admissible(D, L)
    assert molecule_spectrum(S, L) == molecule_spectrum(D, L)
    # not cyclically equivalent
    assert canonical(S) != canonical(D)
    # not dihedrally equivalent either
    dihedral = {canonical(S), canonical(revcomp(S))}
    assert canonical(D) not in dihedral
    return True


def check_F_strong_sampling(alpha, maxG, maxL):
    """STRONG truth: proportional-spectrum partners are powers of the truth."""
    for L in range(2, maxL + 1):
        words = [w for w in _enumerate_primitive_canonicals(alpha, maxG, L)
                 if strong_admissible(w, L)]
        for S in words:
            dS = windows(S, L)
            for n in range(L, maxG + 1):
                for D in product(alpha, repeat=n):
                    if D != tuple(canonical(D)):
                        continue
                    dD = windows(D, L)
                    if set(dD) != set(dS):
                        continue
                    c = Fraction(dD[next(iter(dS))], dS[next(iter(dS))])
                    if all(Fraction(dD[w], dS[w]) == c for w in dS):
                        # same ray: D must be a power of S up to rotation
                        if primitive(D):
                            assert canonical(D) == canonical(S), (L, S, D, c)
    return True


def main():
    results = {}

    # A: population consistency (fixed length)
    assert check_A_population_consistency(("A", "B"), [4, 5, 6])
    assert check_A_population_consistency(("A", "B", "C"), [4, 5])
    results["A"] = "population objective maximized at d_S"

    # B: Lemma L*
    m1 = check_B_lemma_Lstar(("A", "B"), 15, 5)
    m2 = check_B_lemma_Lstar(("A", "B", "C"), 11, 4)
    results["B"] = f"(L-1)-mer multiplicity bound = {max(m1, m2)}"

    # C1: cross-length exclusion (needs only TRF)
    c1 = check_C1_cross_length_trf(("A", "B"), 16, 5)
    c2 = check_C1_cross_length_trf(("A", "B", "C"), 11, 4)
    c3 = check_C1_cross_length_trf(("A", "B", "C", "D"), 8, 3)
    results["C1"] = (f"{c1[0] + c2[0] + c3[0]} primitive TRF words, "
                     f"0 cross-length proportional collisions")
    # C2: equal-length uniqueness (needs WEAK)
    d1 = check_C2_same_length_weak(("A", "B"), 15, 5)
    d2 = check_C2_same_length_weak(("A", "B", "C"), 11, 4)
    results["C2"] = (f"{d1[0] + d2[0]} primitive WEAK words, "
                     f"{d1[1] + d2[1]} distinct normalized spectra, 0 collisions")

    # D: sharpness
    assert check_D1_primitivity_necessary()
    assert check_D2_candidate_admissibility_necessary()
    results["D"] = "primitivity and candidate WEAK-admissibility are both necessary"

    # E: molecule panel
    assert check_E_molecule_panel()
    results["E"] = "AACAGT / AACTGT: same molecule-class law, dihedrally inequivalent"

    # F: STRONG sampling
    assert check_F_strong_sampling(("A", "B"), 10, 3)
    results["F"] = "STRONG truth => proportional partners are non-primitive powers"

    for key in sorted(results):
        print(f"  {key}. {results[key]}")
    print("all population-identifiability checks passed")


if __name__ == "__main__":
    main()
