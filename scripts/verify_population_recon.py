#!/usr/bin/env python3
"""Reconnaissance evaluator for the infinite-data positive analogue (issue #45).

Self-contained, deterministic.  No imports beyond the standard library.
Defines the circular-word population model, the exact multinomial ordering, and
checks three things that the reconnaissance note relies on.  Log comparisons use
floating point with a 1e-12 tolerance; the equalities actually asserted
(spectrum identity, rotation identity, proportionality) are structural and
exact.

  (A) POPULATION CONSISTENCY (fixed length).  For a truth S, the population
      objective  ell(D) = sum_t p_t log(d_D(t)/G),  with p = d_S/G, is uniquely
      maximized over *fixed-length* circular candidates by the spectrum fibre
      {D : d_D = d_S}.  Checked by exhaustive enumeration for small instances.

  (B) THE L-1 BOUNDARY IS SHARP FOR THE COMBINATORIAL HALF.  If no length-(L-1)
      window of S occurs twice, then every same-length candidate with the same
      L-mer spectrum is a cyclic rotation of S.  This is the elementary case of
      "spectrum determines the genome"; it is unconditional and does *not* need
      the source I_s conjecture.  Checked exhaustively for small instances.

  (C) SAMPLING REPAIR AT PROPORTIONALITY.  At exactly proportional counts
      x = c * d_S the truth is an exact ML maximizer over same-length candidates
      at finite n.  Checked on the repository's AAABB witness (G=5, L=3), where
      the *skewed* sample is the known failure.

The script exits non-zero on any failed assertion.  It is evidence about the
population idealization only; it does not settle any finite-per-instance
source reading.
"""

from fractions import Fraction
from itertools import product
from math import gcd


def cyclic_words(g, alphabet):
    """All linear representatives of circular words of length g (with repeats)."""
    return product(alphabet, repeat=g)


def rotations(w):
    return {w[i:] + w[:i] for i in range(len(w))}


def canonical(w):
    return min(rotations(w))


def spectrum(w, L):
    g = len(w)
    d = {}
    for t in range(g):
        win = tuple(w[(t + k) % g] for k in range(L))
        d[win] = d.get(win, 0) + 1
    return d


def all_spectra_of_length(g, L, alphabet):
    """Set of attainable L-mer spectra of length-g circular words over alphabet."""
    out = set()
    for w in cyclic_words(g, alphabet):
        d = spectrum(w, L)
        out.add(tuple(sorted(d.items())))
    return out


def population_objective(p, dD, G):
    """sum_t p_t log(dD_t / G); returns None if a supported type has zero count."""
    s = Fraction(0)
    for t, pt in p.items():
        dt = dD.get(t, 0)
        if pt > 0 and dt == 0:
            return None
        if pt > 0:
            s += pt * _log(Fraction(dt, G))
    return s


def _log(x):
    # Natural log as a Fraction-valued proxy is not exactly rational; use float
    # for the numeric comparison only.  The equalities we assert are structural
    # (support/proportionality), so float is safe here.
    import math
    return math.log(float(x))


def check_A(alphabet, sizes):
    for G in sizes:
        for L in range(2, G + 1):
            spectra = all_spectra_of_length(G, L, alphabet)
            for w in {canonical(x) for x in cyclic_words(G, alphabet)}:
                dS = spectrum(w, L)
                p = {t: Fraction(c, G) for t, c in dS.items()}
                best = None
                maximizers = []
                for ds in spectra:
                    dD = dict(ds)
                    val = population_objective(p, dD, G)
                    if val is None:
                        continue
                    if best is None or val > best + 1e-12:
                        best = val
                        maximizers = [dD]
                    elif abs(val - best) <= 1e-12:
                        maximizers.append(dD)
                # Every population maximizer must have spectrum exactly dS.
                for dD in maximizers:
                    assert dD == dS, (G, L, w, dD, dS)
    return True


def check_B(alphabet, sizes):
    for G in sizes:
        for L in range(2, G + 1):
            words = list({canonical(x) for x in cyclic_words(G, alphabet)})
            for S in words:
                # no repeated (L-1)-mer
                prev = spectrum(S, L - 1)
                if any(c > 1 for c in prev.values()):
                    continue
                dS = spectrum(S, L)
                for D in words:
                    if spectrum(D, L) == dS:
                        assert canonical(D) == canonical(S), (G, L, S, D)
    return True


def check_C():
    alphabet = ("A", "B")
    G, L = 5, 3
    S = tuple("AAABB")
    dS = spectrum(S, L)
    x = dS  # proportional counts c = 1
    # exact ordering over same-length candidates
    candidates = {canonical(w): w for w in cyclic_words(G, alphabet)}
    best = None
    winners = []
    for D in candidates.values():
        dD = spectrum(D, L)
        if any(x.get(t, 0) > 0 and dD.get(t, 0) == 0 for t in x):
            continue
        import math
        score = sum(x[t] * math.log(dD.get(t, 0) / G) for t in x if x.get(t, 0) > 0)
        if best is None or score > best + 1e-12:
            best = score
            winners = [D]
        elif abs(score - best) <= 1e-12:
            winners.append(D)
    assert all(canonical(w) == canonical(S) for w in winners), winners

    # The known skewed failure: x = {AAA:2,AAB:1,BAA:1} has competitor AAAAB
    # strictly better.  Record the crossover direction: population p = dS/G is
    # proportional, so it does not occur in the limit.
    return True


if __name__ == "__main__":
    assert check_A(("A", "B"), [4, 5, 6])
    assert check_A(("A", "B", "C"), [4, 5])
    assert check_B(("A", "B"), [4, 5, 6, 7])
    assert check_B(("A", "B", "C"), [4, 5])
    assert check_C()
    print("population recon checks A, B, C passed")
