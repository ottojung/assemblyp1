#!/usr/bin/env python3
"""Finite-model objective matrix for the AssemblyP1 ML frontier.

Self-contained, exact (fractions.Fraction), deterministic.  It crosses three
source-supported axes

    objective   : exact MB09 6.1 multinomial (candidate-intrinsic N(D))
                  vs. MB09 6.1 separable fixed-N product of binomial marginals
    strand      : oriented length-L reads (Shomorony 2016)
                  vs. reverse-complement k-molecule classes (MB09)
    candidate   : circular sequences (all candidates on the objective domain)
                  vs. MB09 6.2 spelled circuits (support equality / per-vertex LB 1)

and evaluates each of the four integrated kernel-checked witnesses

    W1  AAABB -> AAAAB    exact, fixed length 5, starts 0,1,4
    W2  AAACC -> AAAAC    literal fixed-N binomial, fixed length 5, starts 0,1,4
    W3  AAATT -> AAAATT   fixed-N binomial, variable length 5->6, starts 0,1,4
    W4  AAATAT -> AAAAAT  fixed-N binomial + exact, same length 6, starts 0,0,1,3,5

in every cell where the witness is admissible, and reports which cells the
integrated witnesses genuinely refute and which stay open.

It shares no code with the repository's other searches.  Exit status is non-zero
on any failed assertion.

Usage:
    python3 scripts/verify_finite_objective_matrix.py
"""

from fractions import Fraction
from collections import Counter
from math import comb

COMP = {"A": "T", "T": "A", "C": "G", "G": "C", "B": "B"}


def rc(w):
    return tuple(COMP[c] for c in reversed(w))


def canon_class(w):
    return min(w, rc(w))


def circular_windows(seq, k):
    n = len(seq)
    return [tuple(seq[(i + j) % n] for j in range(k)) for i in range(n)]


def spectrum(seq, k, by_class):
    c = Counter()
    for w in circular_windows(seq, k):
        c[canon_class(w) if by_class else w] += 1
    return dict(c)


def observed(starts, truth, k, by_class):
    c = Counter()
    windows = circular_windows(truth, k)
    for s in starts:
        c[canon_class(windows[s]) if by_class else windows[s]] += 1
    return dict(c)


def support(spec):
    return frozenset(w for w, v in spec.items() if v > 0)


def binom_likelihood(d_spec, x, n, N):
    """Literal MB09 6.1 product of binomial marginals (zero-count factors kept).

    Types with x_i = 0 and d_i = 0 contribute 1 and are omitted; types with
    x_i = 0 and d_i > 0 keep their (1 - d_i/N)^n factor.  A factor is zero when
    x_i > 0 and d_i = 0, or x_i < n and d_i = N.
    """
    keys = set(d_spec) | {w for w, v in x.items() if v > 0}
    val = Fraction(1)
    for w in keys:
        d = d_spec.get(w, 0)
        xi = x.get(w, 0)
        if d == 0 and xi == 0:
            continue
        if (d == 0 and xi > 0) or (d >= N and xi < n):
            return Fraction(0)
        val *= Fraction(comb(n, xi)) * Fraction(d, N) ** xi * Fraction(N - d, N) ** (n - xi)
    return val


def exact_likelihood(d_spec, x, length):
    """MB09 6.1 exact multinomial up to the observation-only coefficient."""
    val = Fraction(1)
    for w, xi in x.items():
        if xi == 0:
            continue
        d = d_spec.get(w, 0)
        val *= Fraction(d, length) ** xi
    return val


class Witness:
    def __init__(self, name, S, D, starts, k):
        self.name = name
        self.S, self.D, self.starts, self.k = S, D, starts, k
        self.n = len(starts)
        self.N = len(S)

    def evaluate(self, objective, by_class):
        ds = spectrum(self.S, self.k, by_class)
        dd = spectrum(self.D, self.k, by_class)
        x = observed(self.starts, self.S, self.k, by_class)
        if objective == "exact":
            ls = exact_likelihood(ds, x, len(self.S))
            ld = exact_likelihood(dd, x, len(self.D))
        else:
            ls = binom_likelihood(ds, x, self.n, self.N)
            ld = binom_likelihood(dd, x, self.n, self.N)
        ratio = ld / ls if ls != 0 else None
        spelled = support(ds) == support(x) and support(dd) == support(x)
        return dict(ds=ds, dd=dd, x=x, ratio=ratio, spelled=spelled)


W1 = Witness("AAABB->AAAAB", "AAABB", "AAAAB", [0, 1, 4], 3)
W2 = Witness("AAACC->AAAAC", "AAACC", "AAAAC", [0, 1, 4], 3)
W3 = Witness("AAATT->AAAATT", "AAATT", "AAAATT", [0, 1, 4], 3)
W4 = Witness("AAATAT->AAAAAT", "AAATAT", "AAAAAT", [0, 0, 1, 3, 5], 3)
WITNESSES = [W1, W2, W3, W4]

STRAND = {"oriented": False, "molecule": True}
CANDIDATE = {"sequence": None, "flow": True}  # flow requires spelled == True


def cell_status(objective, strand, candidate):
    """Return (status, best) where status in {'refuted','open'}."""
    by_class = STRAND[strand]
    require_spelled = CANDIDATE[candidate]
    hits = []
    for w in WITNESSES:
        ev = w.evaluate(objective, by_class)
        if require_spelled and not ev["spelled"]:
            continue
        if ev["ratio"] is not None and ev["ratio"] > 1:
            hits.append((w.name, ev["ratio"]))
    if hits:
        return "refuted", hits
    return "open", []


def main():
    print("Integrated witnesses (exact MB09 6.1 objective / literal fixed-N binomial):")
    for w in WITNESSES:
        for strand in ("oriented", "molecule"):
            by_class = STRAND[strand]
            e = w.evaluate("exact", by_class)
            b = w.evaluate("binomial", by_class)
            print(
                f"  {w.name:18s} {strand:8s} exact={str(e['ratio']):>10s} "
                f"binom={str(b['ratio']):>10s} spelled={e['spelled']}"
            )

    print("\n2x2x2 matrix (objective x strand x candidate class):")
    rows = []
    for objective in ("exact", "binomial"):
        for strand in ("oriented", "molecule"):
            for candidate in ("sequence", "flow"):
                status, hits = cell_status(objective, strand, candidate)
                rows.append((objective, strand, candidate, status, hits))
                detail = ", ".join(f"{n}:{r}" for n, r in hits) if hits else "-"
                print(f"  {objective:8s} {strand:8s} {candidate:8s} -> {status:8s} ({detail})")

    # --- assertions that pin the matrix ---
    def st(o, s, c):
        return cell_status(o, s, c)[0]

    # Source-faithful (molecule-class) cells are all closed negatively.
    assert st("exact", "molecule", "sequence") == "refuted"
    assert st("exact", "molecule", "flow") == "refuted"
    assert st("binomial", "molecule", "sequence") == "refuted"
    assert st("binomial", "molecule", "flow") == "refuted"
    # Oriented sequence cells are closed negatively (W1/W2 exact, W2 binomial).
    assert st("exact", "oriented", "sequence") == "refuted"
    assert st("binomial", "oriented", "sequence") == "refuted"
    # Oriented spelled-circuit cells have no integrated witness: open.
    assert st("exact", "oriented", "flow") == "open"
    assert st("binomial", "oriented", "flow") == "open"

    # Exact ratios of the integrated witnesses.
    assert W1.evaluate("exact", False)["ratio"] == Fraction(2)
    assert W2.evaluate("binomial", False)["ratio"] == Fraction(1125, 512)
    assert W2.evaluate("exact", False)["ratio"] == Fraction(2)
    assert W3.evaluate("binomial", True)["ratio"] == Fraction(9, 8)
    assert W3.evaluate("exact", True)["ratio"] == Fraction(125, 108)
    assert W4.evaluate("binomial", True)["ratio"] == Fraction(5)
    assert W4.evaluate("exact", True)["ratio"] == Fraction(3)
    # W4 inverts under strict oriented indexing: the observed oriented type TAT
    # is absent from D, so D's oriented likelihood factor is 0.
    assert W4.evaluate("exact", False)["ratio"] == Fraction(0)
    assert W4.evaluate("binomial", False)["ratio"] == Fraction(0)
    # W2's ratio is strand-independent (no reverse-complement collisions).
    assert W2.evaluate("binomial", True)["ratio"] == Fraction(1125, 512)
    # The molecule-class §6.2 witnesses are support-equal; the fixed-length
    # sequence witnesses are not §6.2-spellable under either strand reading.
    assert W3.evaluate("binomial", True)["spelled"] and W4.evaluate("binomial", True)["spelled"]
    assert not W1.evaluate("exact", False)["spelled"]
    assert not W2.evaluate("binomial", True)["spelled"]

    print("\nAll finite-objective-matrix assertions passed.")


if __name__ == "__main__":
    main()
