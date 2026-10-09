#!/usr/bin/env python3
"""Independent audit of the oriented -> double-strand bridging transfer (issue #215).

This script is self-contained: it re-implements the reverse-complement
involution, molecule classes, oriented/molecule spectra, the
Bresler-Shomorony information-feasible set `I_s` (transcribed from
`AssemblyP1/SourceFaithfulIs.lean`), the Bresler 2G doubled genome, and every
quantity reported in
`docs/source-notes/oriented-to-double-strand-bridging-transfer-2026-10-09.md`
from scratch.  It shares no code with any other repository script.  All
arithmetic is exact (integers and `fractions.Fraction`); it is deterministic and
exits non-zero on any failed assertion.

Alphabet `Σ` with involutive complement (`A<->T`, `C<->G`); `ρ` is reverse
complement.  A *molecule class* is a `ρ`-orbit.

Sections.

  0. Reproduction of the kernel-checked `AAATAT -> AAAAAT` molecule witness:
     spectra, supports, exact/binomial ratios, observed-multiplicity
     non-symmetry, per-vertex vs per-occurrence §6.2 admissibility.
  1. The observation map `Φ` and the molecule read-placement liftings `Ψ`.
     Bridging is *not* a function of molecule data: the three liftings of the
     witness observation have different `I_s` status.
  2. Bridging version V1/V2 (molecule likelihood + Shomorony placement
     bridging): the witness realization is `I_s`-feasible and its observation is
     in `Φ(I_s)`.
  3. Bridging version V3 (Bresler et al. 2G double-strand remap): the witness is
     *inadmissible* -- the doubled genome carries an unbridgeable maximal triple
     repeat.
  4. Structural non-equivalences: the class-coarsening kernel, the doubled
     spectrum junction formula, the exact compatibility condition, and the
     molecule candidate-set computation (why the oriented rigidity theorem does
     not transpose).
  5. Bounded searches: agreement rate of the two double-strand conventions,
     feasibility of the Bresler remap, and which extra hypothesis restores
     molecule-level rigidity.

Usage:
    python3 scripts/verify_oriented_molecule_bridging.py           # quick
    python3 scripts/verify_oriented_molecule_bridging.py --full     # wider scopes
"""

from __future__ import annotations

import sys
from fractions import Fraction
from itertools import combinations, product

FULL = "--full" in sys.argv[1:]

# --------------------------------------------------------------------------- #
# Alphabet, reverse complement, classes
# --------------------------------------------------------------------------- #

DNA = ("A", "C", "G", "T")
COMP = {"A": "T", "T": "A", "C": "G", "G": "C"}


def rc(w):
    """Reverse complement of a word (tuple of symbols)."""
    return tuple(COMP[c] for c in reversed(w))


def class_of(w):
    """Canonical representative of the reverse-complement orbit of `w`."""
    r = rc(w)
    return w if w <= r else r


def classes_of_length(e, alphabet=DNA):
    return sorted({class_of(w) for w in product(alphabet, repeat=e)})


def n_palindromes(e, alphabet=DNA):
    return sum(1 for w in product(alphabet, repeat=e) if rc(w) == w)


def molecule_spectrum(g, e):
    """`m_S(c)` = summed oriented occurrences of the words in class `c`."""
    G = len(g)
    m = {}
    for t in range(G):
        c = class_of(window(g, e, t))
        m[c] = m.get(c, 0) + 1
    return m


def spectrum(g, e):
    """Oriented length-`e` circular window counts of `g`."""
    G = len(g)
    s = {}
    for t in range(G):
        w = window(g, e, t)
        s[w] = s.get(w, 0) + 1
    return s


# --------------------------------------------------------------------------- #
# The oriented single-strand model (Shomorony et al. 2016 §§2-3 with the Bresler
# et al. 2013 repeat definitions), transcribed from
# `AssemblyP1/SourceFaithfulIs.lean`.
# --------------------------------------------------------------------------- #


def window(g, e, r):
    """Length-`e` circular window of `g` beginning at `r` (Lean `Genome.window`)."""
    G = len(g)
    return tuple(g[(r + i) % G] for i in range(e))


def preceding(g, t):
    return g[(t - 1) % len(g)]


def following(g, e, t):
    return g[(t + e) % len(g)]


def agree(g, e, a, b):
    return window(g, e, a) == window(g, e, b)


def is_repeat_pair(g, e, a, b):
    """Lean `Genome.IsRepeat`: two selected starts, maximal on both sides."""
    G = len(g)
    if not (1 <= e < G) or a == b:
        return False
    if not agree(g, e, a, b):
        return False
    return preceding(g, a) != preceding(g, b) and following(g, e, a) != following(g, e, b)


def is_triple_repeat(g, e, a, b, c):
    """Lean `Genome.IsTripleRepeat`: three selected starts, three-copy maximality."""
    G = len(g)
    if not (1 <= e < G):
        return False
    if a == b or a == c or b == c:
        return False
    if not (agree(g, e, a, b) and agree(g, e, a, c) and agree(g, e, b, c)):
        return False
    if preceding(g, a) == preceding(g, b) == preceding(g, c):
        return False
    if following(g, e, a) == following(g, e, b) == following(g, e, c):
        return False
    return True


def triple_repeats(g):
    """All maximal triple repeats `(e, a, b, c)` of `g`."""
    G = len(g)
    out = []
    for e in range(1, G):
        groups = {}
        for t in range(G):
            groups.setdefault(window(g, e, t), []).append(t)
        for _, sts in groups.items():
            if len(sts) < 3:
                continue
            for a, b, c in combinations(sorted(sts), 3):
                if preceding(g, a) == preceding(g, b) == preceding(g, c):
                    continue
                if following(g, e, a) == following(g, e, b) == following(g, e, c):
                    continue
                out.append((e, a, b, c))
    return out


def repeat_pairs(g):
    """All maximal two-start repeats `(e, a, b)` with `a < b`."""
    G = len(g)
    out = []
    for e in range(1, G):
        groups = {}
        for t in range(G):
            groups.setdefault(window(g, e, t), []).append(t)
        for _, sts in groups.items():
            for a, b in combinations(sorted(sts), 2):
                if is_repeat_pair(g, e, a, b):
                    out.append((e, a, b))
    return out


def bridges_copy(g, L, R, e, t):
    """Lean `BridgesCopy`: some realized read straddles the copy at `t`."""
    G = len(g)
    for r in R:
        for d in range(L):
            if d + e + 1 < L and (r + d + 1) % G == t:
                return True
    return False


def covers(g, L, R):
    """Lean `Covers`: every position lies in some realized read."""
    G = len(g)
    return all(
        any(any(p == (r + d) % G for d in range(L)) for r in R) for p in range(G)
    )


def in_open_arc(G, a, b, p):
    return 0 < (p + G - a) % G < (b + G - a) % G


def interleaved(G, a, b, c, d):
    """Lean `Interleaved`: cyclic alternation of the four selected starts."""
    if len({a, b, c, d}) != 4:
        return False
    return in_open_arc(G, a, b, c) != in_open_arc(G, a, b, d)


def information_feasible(g, L, R):
    """Lean `InformationFeasible`: the Shomorony et al. (2016) `I_s`, Eq. (1)."""
    G = len(g)
    R = sorted(set(R))
    if not covers(g, L, R):
        return False
    for e, a, b, c in triple_repeats(g):
        if not all(bridges_copy(g, L, R, e, t) for t in (a, b, c)):
            return False
    rps = repeat_pairs(g)
    for (e1, a, b), (e2, c, d) in combinations(rps, 2):
        if not interleaved(G, a, b, c, d):
            continue
        if not (
            any(bridges_copy(g, L, R, e1, t) for t in (a, b))
            or any(bridges_copy(g, L, R, e2, t) for t in (c, d))
        ):
            return False
    return True


def triple_repeat_obstruction(g, L, R):
    """A maximal triple repeat with an unbridged selected copy, if any exists."""
    for e, a, b, c in triple_repeats(g):
        if not all(bridges_copy(g, L, R, e, t) for t in (a, b, c)):
            return (e, a, b, c)
    return None


def has_long_triple_repeat(g, L):
    """`True` iff some maximal triple repeat has length `>= L-1`.

    Lemma B + Lemma C of `docs/source-notes/oriented-se62-rigidity-theorem.md`
    (mathematical proof on `main`) show this is equivalent to "some length-`(L-1)`
    window occurs at least three times"; the equivalence is re-checked
    exhaustively in §5 so the wider scan relies on a verified, not assumed, fact.
    """
    return any(e >= L - 1 for e, _, _, _ in triple_repeats(g))


def max_window_multiplicity(g, e):
    s = spectrum(g, e)
    return max(s.values()) if s else 0


def max_class_multiplicity(g, e):
    m = molecule_spectrum(g, e)
    return max(m.values()) if m else 0


# --------------------------------------------------------------------------- #
# Objectives (two distinct MB09 §6.1 objects, never fused)
# --------------------------------------------------------------------------- #


def _choose(n, k):
    r = 1
    for i in range(1, k + 1):
        r = r * (n - k + i) // i
    return r


def exact_ratio_molecule(x, m_S, m_D):
    """Exact candidate-intrinsic multinomial ratio `L_E(D)/L_E(S)` for two
    same-length candidates (the observation-only coefficient and the `N(D)`
    denominators cancel)."""
    total = Fraction(1)
    for c, xc in x.items():
        if xc == 0:
            continue
        if m_D.get(c, 0) == 0:
            return Fraction(0)
        total *= Fraction(m_D[c], m_S[c]) ** xc
    return total


def binomial_ratio_molecule(x, m_S, m_D, N):
    """Literal MB09 §6.1 separable fixed-`N` binomial ratio `L_A(D)/L_A(S)`."""
    n = sum(x.values())
    ratio = Fraction(1)
    for c, xc in x.items():
        dD, dS = m_D.get(c, 0), m_S[c]
        num = Fraction(_choose(n, xc)) * Fraction(dD, N) ** xc * (1 - Fraction(dD, N)) ** (n - xc)
        den = Fraction(_choose(n, xc)) * Fraction(dS, N) ** xc * (1 - Fraction(dS, N)) ** (n - xc)
        ratio *= num / den
    return ratio


# --------------------------------------------------------------------------- #
# The molecule (reverse-complement-collapsed) observation model
# --------------------------------------------------------------------------- #


def observed_molecule_classes(g, L, starts):
    """The MB09 observation `x`: molecule class counts of the realized reads."""
    x = {}
    for t in starts:
        c = class_of(window(g, L, t))
        x[c] = x.get(c, 0) + 1
    return x


def placements_by_class(g, L, classes):
    """`Ψ`: for each class, the start positions whose oriented window is in it."""
    G = len(g)
    out = {c: [] for c in classes}
    for t in range(G):
        c = class_of(window(g, L, t))
        if c in out:
            out[c].append(t)
    return out


def liftings(g, L, x):
    """All placement multiset choices consistent with the molecule observation `x`."""
    classes = [c for c, n in x.items() for _ in range(n)]
    P = placements_by_class(g, L, set(x))
    if any(len(P[c]) == 0 for c in P if x.get(c, 0) > 0):
        return []
    out = [[]]
    for c in classes:
        out = [cur + [t] for cur in out for t in P[c]]
    return sorted(tuple(sorted(l)) for l in out)


# --------------------------------------------------------------------------- #
# The Bresler et al. (2013) double-strand remap: genome `S · ρ(S)`, reads doubled
# --------------------------------------------------------------------------- #


def doubled_genome(g):
    return tuple(g) + tuple(rc(tuple(g)))


def doubled_placements(g, starts, L):
    """The Bresler doubling: every realized read becomes itself and its reverse
    complement, giving `2N` reads placed on the doubled genome.

    A length-`L` window of the circular `S` starting at `t <= G-L` sits at
    absolute position `t` of `S · ρ(S)`; a wrapping window (`t > G-L`) sits at
    absolute position `G+t` (across the other seam).  The reverse complement of a
    read at absolute position `b` sits at absolute position `2G-b-L`."""
    G = len(g)
    W = 2 * G
    out = []
    for t in starts:
        base = t if t <= G - L else G + t
        out.append(base % W)
        out.append((W - base - L) % W)
    return sorted(set(out))


def doubled_observation(g, L, starts):
    """Molecule class counts of the doubled read set."""
    hs = doubled_genome(g)
    x = {}
    for t in doubled_placements(g, starts, L):
        c = class_of(window(hs, L, t))
        x[c] = x.get(c, 0) + 1
    return x


def lint_spectrum(g, e):
    """Non-wrapping (linear) length-`e` occurrences of the words of `g`."""
    G = len(g)
    s = {}
    for t in range(0, G - e + 1):
        w = tuple(g[t : t + e])
        s[w] = s.get(w, 0) + 1
    return s


def wrap_spectrum(g, e):
    """Wrapping (circular-only) length-`e` occurrences of the words of `g`."""
    G = len(g)
    s = {}
    for t in range(G - e + 1, G):
        w = window(g, e, t)
        s[w] = s.get(w, 0) + 1
    return s


def seam_windows(g, L):
    """The `2(L-1)` junction windows of the doubled genome `S · ρ(S)`."""
    G = len(g)
    W = 2 * G
    hs = doubled_genome(g)
    out = {}
    for t in list(range(G - L + 1, G)) + list(range(W - L + 1, W)):
        w = window(hs, L, t)
        out[w] = out.get(w, 0) + 1
    return out


# --------------------------------------------------------------------------- #
# Positive circulations on the oriented de Bruijn graph of `Σ^L`
# --------------------------------------------------------------------------- #


def class_support(B):
    return {class_of(w) for w, n in B.items() if n > 0}


def is_balanced(B):
    """`B` is a circulation: at every `(L-1)`-node, inflow equals outflow."""
    bal = {}
    for w, n in B.items():
        if n == 0:
            continue
        p, s = w[:-1], w[1:]
        bal[p] = bal.get(p, 0) + n
        bal[s] = bal.get(s, 0) - n
    return all(v == 0 for v in bal.values())


def enumerate_circulations(alphabet, L, G, V):
    """All non-negative balanced integer vectors on `Σ^L` of total `G` whose
    molecule-class support is exactly `V` (the outer approximation of the
    same-length §6.2-spelled candidate set under class support `V`)."""
    words = list(product(alphabet, repeat=L))
    n = len(words)
    out = []

    def rec(i, remaining, cur):
        if i == n - 1:
            vec = cur + [remaining]
            if any(vec):
                B = dict(zip(words, vec))
                if class_support(B) == set(V) and is_balanced(B):
                    out.append({w: c for w, c in B.items() if c})
            return
        for v in range(remaining + 1):
            rec(i + 1, remaining - v, cur + [v])

    rec(0, G, [])
    return out


def molecule_candidate_spectra(g, L, alphabet=None):
    """Distinct molecule spectra of balanced integer vectors of total `G` whose
    class support equals the truth's class support (outer approximation of the
    molecule-model same-length candidate set)."""
    alphabet = tuple(sorted(set(g))) if alphabet is None else alphabet
    V = set(molecule_spectrum(g, L))
    seen = []
    for B in enumerate_circulations(alphabet, L, len(g), V):
        m = molecule_spectrum_from_vector(B)
        if m not in seen:
            seen.append(m)
    return seen


def molecule_spectrum_from_vector(B):
    m = {}
    for w, n in B.items():
        c = class_of(w)
        m[c] = m.get(c, 0) + n
    return m


def alphabet_of(g):
    return tuple(sorted(set(g)))


# --------------------------------------------------------------------------- #
# Reporting helpers
# --------------------------------------------------------------------------- #

FAILURES = []


def check(cond, msg):
    print(("  [ok]   " if cond else "  [FAIL] ") + msg)
    if not cond:
        FAILURES.append(msg)


def section(title):
    print()
    print(title)
    print("-" * len(title))


def fmt_counts(d):
    return "{" + ", ".join(f"{''.join(c)}:{d[c]}" for c in sorted(d)) + "}"


# --------------------------------------------------------------------------- #
# Section 0: the kernel-checked molecule witness, reproduced
# --------------------------------------------------------------------------- #

def section0():
    section("0. The integrated molecule witness `AAATAT -> AAAAAT`, reproduced independently")
    S = tuple("AAATAT")
    D = tuple("AAAAAT")
    L = 3
    starts = (0, 0, 1, 3, 5)
    check("".join(S) == "AAATAT" and len(S) == 6, "truth S = AAATAT, G = 6")
    check("".join(D) == "AAAAAT" and len(D) == 6, "competitor D = AAAAAT, |D| = 6")

    specS, specD = spectrum(S, L), spectrum(D, L)
    mS, mD = molecule_spectrum(S, L), molecule_spectrum(D, L)
    x = observed_molecule_classes(S, L, starts)
    print(f"  spec_3(S) oriented   = {fmt_counts(specS)}")
    print(f"  spec_3(D) oriented   = {fmt_counts(specD)}")
    print(f"  molecule spectrum d_S = {fmt_counts(mS)}")
    print(f"  molecule spectrum d_D = {fmt_counts(mD)}")
    print(f"  observation x         = {fmt_counts(x)}")

    check(specS == {("A", "A", "A"): 1, ("A", "A", "T"): 1, ("A", "T", "A"): 2,
                    ("T", "A", "T"): 1, ("T", "A", "A"): 1},
          "oriented spectrum of AAATAT is {AAA:1, AAT:1, ATA:2, TAT:1, TAA:1}")
    check(specD == {("A", "A", "A"): 3, ("A", "A", "T"): 1, ("A", "T", "A"): 1,
                    ("T", "A", "A"): 1},
          "oriented spectrum of AAAAAT is {AAA:3, AAT:1, ATA:1, TAA:1} (no TAT)")
    check(specS[("A", "T", "A")] == 2 and specS[("T", "A", "T")] == 1
          and mS[class_of(("A", "T", "A"))] == 3,
          "d_S(ATA) = 2 but d_S(TAT) = 1 while the class {ATA,TAT} has d_S = 3: "
          "the premise d_w = d_{ρ(w)} is false, and the class is not well split")
    check(set(mS) == set(mD) == set(x),
          "class support equality supp(d_S) = supp(d_D) = supp(x)")
    check(set(specS) != set(specD),
          "the oriented supports differ (D has no TAT window) although the class "
          "supports coincide: the class condition is strictly coarser")

    r_exact = exact_ratio_molecule(x, mS, mD)
    r_bin = binomial_ratio_molecule(x, mS, mD, 6)
    check(sum(mS.values()) == 6 and sum(mD.values()) == 6, "both spectra total G = 6")
    check(r_exact == 3, f"exact candidate-intrinsic multinomial ratio = {r_exact} = 3")
    check(r_bin == 5, f"literal §6.1 fixed-N binomial ratio = {r_bin} = 5")
    check(r_exact > 1 and r_bin > 1, "D strictly beats S under both objectives")

    per_occ_truth = all(mS.get(c, 0) >= n for c, n in x.items())
    per_occ_D = all(mD.get(c, 0) >= n for c, n in x.items())
    check(per_occ_D, "the competitor satisfies the per-occurrence strengthening d_D >= x")
    check(not per_occ_truth,
          "the truth does NOT satisfy d_S >= x (d_S(AAA) = 1 < x(AAA) = 2), so the "
          "per-occurrence strengthening makes this witness vacuous")

    gain = Fraction(mD[class_of(("A", "A", "A"))], mS[class_of(("A", "A", "A"))]) ** x[class_of(("A", "A", "A"))]
    loss = Fraction(mD[class_of(("A", "T", "A"))], mS[class_of(("A", "T", "A"))]) ** x[class_of(("A", "T", "A"))]
    check(gain == 9 and loss == Fraction(1, 3) and gain * loss == 3,
          "mechanism: (d_D/d_S)(AAA)^2 = 9 against (d_D/d_S)(ATA)^1 = 1/3; ratio 3")
    return S, D, L, starts, mS, mD, x


# --------------------------------------------------------------------------- #
# Section 1: the observation map Phi and the placement liftings Psi
# --------------------------------------------------------------------------- #

def section1(S, L, starts, x):
    section("1. The observation map Φ, the placement liftings Ψ, and the failure of Φ-invariance")
    for c in sorted(x):
        print(f"  Ψ(class {''.join(c)}) = {placements_by_class(S, L, set(x))[c]}")
    lifts = liftings(S, L, x)
    print(f"  placement multisets consistent with x: {len(lifts)}")
    for lift in lifts:
        print(f"    lifting {list(lift)}: I_s = {information_feasible(S, L, lift)}")
    check(len(lifts) == 3, "the observation x has exactly 3 liftings")
    statuses = {lift: information_feasible(S, L, lift) for lift in lifts}
    feas = [l for l, v in statuses.items() if v]
    infeas = [l for l, v in statuses.items() if not v]
    check(len(feas) == 1 and list(feas[0]) == [0, 0, 1, 3, 5],
          "the realized lifting {0,0,1,3,5} is the unique I_s-feasible one")
    check(len(infeas) == 2,
          "the two other liftings of the same molecule observation are NOT "
          "I_s-feasible")
    check(is_triple_repeat(S, 1, 1, 2, 4),
          "A@{1,2,4} is a maximal triple repeat of AAATAT")
    check(not bridges_copy(S, L, [0, 0, 1, 2, 5], 1, 4),
          "no read of the lifting {0,0,1,2,5} bridges the copy at 4 (a read at "
          "start 3 is required)")
    check(not information_feasible(S, L, [0, 0, 1, 2, 5])
          and not information_feasible(S, L, [0, 0, 1, 4, 5]),
          "so those liftings violate I_s: bridging is NOT a function of the "
          "molecule observation Φ(R)")


# --------------------------------------------------------------------------- #
# Section 2: bridging version V1/V2 -- molecule likelihood + Shomorony placement
# --------------------------------------------------------------------------- #

def section2(S, L, starts, x):
    section("2. Bridging V1/V2 (molecule objective + Shomorony placement bridging)")
    R = sorted(set(starts))
    check(covers(S, L, R), "coverage holds for the realized start set {0,1,3,5}")
    trs = triple_repeats(S)
    print(f"  maximal triple repeats of AAATAT: {[(e, a, b, c) for e, a, b, c in trs]}")
    check(all(bridges_copy(S, L, R, e, t) for e, a, b, c in trs for t in (a, b, c)),
          "every maximal triple repeat is all-bridged")
    inter = []
    rps = repeat_pairs(S)
    for (e1, a, b), (e2, c, d) in combinations(rps, 2):
        if interleaved(len(S), a, b, c, d):
            ok = any(bridges_copy(S, L, R, e1, t) for t in (a, b)) or \
                 any(bridges_copy(S, L, R, e2, t) for t in (c, d))
            inter.append((e1, a, b, e2, c, d, ok))
    print(f"  interleaved pairs of maximal repeats: "
          f"{[(e1, a, b, e2, c, d) for e1, a, b, e2, c, d, _ in inter]}")
    check(len(inter) > 0 and all(ok for *_, ok in inter),
          "the interleaving clause is non-vacuous and every interleaved pair is "
          "bridged (e.g. A@{{0,2}} with A@{{1,4}}: the copy at 0 is bridged by the "
          "read at start 5)")
    check(information_feasible(S, L, R),
          "V1: the realized read set {0,1,3,5} satisfies I_s (matches the "
          "kernel-checked certificate `truth_source_certificate` on main)")
    lifts = liftings(S, L, x)
    check(any(information_feasible(S, L, list(l)) for l in lifts),
          "V2: the molecule observation x is in Φ(I_s): it admits an I_s-satisfying "
          "lifting")
    n_ok = len([l for l in lifts if information_feasible(S, L, list(l))])
    check(0 < n_ok < len(lifts),
          "V2 is strictly weaker than V1: some liftings of x violate I_s, so "
          "'x is compatible with I_s' is not 'the realized read set is in I_s'")
    print("  Verdict: the AAATAT -> AAAAAT witness is a genuine counterexample under")
    print("  V1/V2: Shomorony's I_s jointly with the MB09 molecule objective.")


# --------------------------------------------------------------------------- #
# Section 3: bridging version V3 -- the Bresler 2G double-strand remap
# --------------------------------------------------------------------------- #

def section3(S, L, starts, x):
    section("3. Bridging V3 (Bresler et al. 2013 2G double-strand remap)")
    hs = doubled_genome(S)
    print(f"  doubled genome S·ρ(S) = {''.join(hs)}   (length {len(hs)})")
    pl = doubled_placements(S, starts, L)
    print(f"  doubled read placements (distinct starts): {pl}")
    check(covers(hs, L, pl),
          "coverage of the doubled genome holds under the generous string reading")

    # Bresler doubles every realized read, multiplicities included
    doubled_reads = []
    for t in starts:
        base = t if t <= len(S) - L else len(S) + t
        doubled_reads.append(base)
        doubled_reads.append((2 * len(S) - base - L) % (2 * len(S)))
    xd = {}
    for t in doubled_reads:
        c = class_of(window(hs, L, t))
        xd[c] = xd.get(c, 0) + 1
    print(f"  molecule observation of the 2N doubled reads = {fmt_counts(xd)}")
    print(f"  molecule observation of the N original reads = {fmt_counts(x)}")
    check(all(xd[c] == 2 * x[c] for c in x) and sum(xd.values()) == 2 * sum(x.values()),
          "the doubled read set has exactly twice the molecule class counts: each "
          "realized read contributes itself and its reverse complement, and the "
          "class of a read is strand-invariant")

    # the structural obstruction: a maximal triple repeat no length-L read can bridge
    long_trs = [t for t in triple_repeats(hs) if t[0] >= L - 1]
    print(f"  maximal triple repeats of the doubled genome with length >= L-1 = {L - 1}: "
          f"{[(e, a, b, c) for e, a, b, c in long_trs]}")
    check(len(long_trs) > 0, "the doubled genome carries a long triple repeat")
    e, a, b, c = max(long_trs, key=lambda t: t[0])
    word = "".join(window(hs, e, a))
    check(is_triple_repeat(hs, e, a, b, c),
          f"'{word}' @ {{{a},{b},{c}}} (length {e}) is a maximal triple repeat of the "
          f"doubled genome (preceding and following symbols not all equal)")
    check(e + 2 > L,
          f"length {e} >= L-1, so bridgesCopy_length (e + 2 <= L) forbids bridging "
          f"by ANY read of length L, whatever the read set")
    check(not any(bridges_copy(hs, L, list(range(2 * len(S))), e, t) for t in (a, b, c)),
          "even the full placement set {0,...,2G-1} cannot bridge that copy triple")
    obs = triple_repeat_obstruction(hs, L, pl)
    check(obs is not None,
          f"the realized doubled read set also fails all-bridgedness: {obs}")
    check(not information_feasible(hs, L, pl),
          "V3: the doubled instance is NOT I_s-feasible, so the AAATAT -> AAAAAT "
          "witness is inadmissible under the double-strand reading")
    print("  Verdict: the witness transmits nothing under V3 -- neither a")
    print("  counterexample nor a positive result; the remapped hypothesis is")
    print("  unsatisfiable for this instance.")


# --------------------------------------------------------------------------- #
# Section 4: structural non-equivalences
# --------------------------------------------------------------------------- #

def section4(S, D, L, mS, mD, x):
    section("4. Structural non-equivalences between the oriented and molecule models")
    # 4a. rc is an involution; the class-count formula (repository fact, re-derived)
    words3 = list(product(DNA, repeat=3))
    check(all(rc(rc(w)) == w for w in words3), "ρ is an involution on length-3 words")
    for e in range(1, 7):
        nw, np_, ncl = 4 ** e, n_palindromes(e), len(classes_of_length(e))
        check(ncl == (nw + np_) // 2,
              f"#length-{e} molecule classes = (4^{e} + {np_})/2 = {ncl}")

    # 4b. the class coarsening κ and the transfer gap
    specS, specD = spectrum(S, L), spectrum(D, L)
    check(molecule_spectrum_from_vector(specS) == mS
          and molecule_spectrum_from_vector(specD) == mD,
          "m_S = κ(spec_3(S)) and m_D = κ(spec_3(D)): the molecule spectrum is the "
          "class-summed image of the oriented spectrum")
    oriented_support_vectors = enumerate_circulations(("A", "T"), L, 6, set(specS))
    or_sup = [B for B in enumerate_circulations(("A", "T"), L, 6, set(mS))]
    # restrict to the truth's exact oriented support
    on_truth_support = [B for B in or_sup if set(B) == set(specS)]
    print(f"  balanced positive vectors of total 6 with the truth's CLASS support: "
          f"{len(or_sup)}")
    print(f"  ... of which with the truth's exact ORIENTED support: {len(on_truth_support)}")
    check(len(or_sup) >= 2,
          "the class-support condition admits several oriented circulations")
    check(len(on_truth_support) == 1 and on_truth_support[0] == specS,
          "the oriented-support condition admits exactly one, spec_3(S) itself: this "
          "is the oriented rigidity theorem (mathematical proof on main), "
          "reproduced here for the AAATAT instance")
    seen = {tuple(sorted(molecule_spectrum_from_vector(B).items())) for B in or_sup}
    check(len(seen) >= 2,
          "those circulations project to >= 2 distinct molecule spectra, so the "
          "class coarsening destroys the rigidity: this is the transfer gap")

    # 4c. I_s multiplicity bounds: 2 oriented, 4 per class (in general)
    check(max_window_multiplicity(S, 2) == 2,
          "for AAATAT every oriented 2-mer occurs at most twice (the I_s bound)")
    check(max_class_multiplicity(S, 3) == 3,
          "the molecule class {ATA,TAT} (an L-mer class) occurs 3 times")
    g = tuple("AAATTT")
    check(max_class_multiplicity(g, 2) == 4 and not has_long_triple_repeat(g, 3),
          "the class bound implied by I_s is 4, not 2, and it is sharp: AAATTT at "
          "L=3 is I_s-compatible yet its class {AA,TT} of 2-mers occurs 4 times")
    print("  Theorem A of the oriented rigidity proof needs 'every (L-1)-window")
    print("  <= 2'; at the class level I_s supplies only '<= 4' in general.")

    # 4d. doubled-spectrum junction formula and the exact compatibility condition
    def decomp_ok(g, e):
        specH = spectrum(doubled_genome(g), e)
        lint, wrap, seam = lint_spectrum(g, e), wrap_spectrum(g, e), seam_windows(g, e)
        if not all(specH.get(w, 0) == lint.get(w, 0) + lint.get(rc(w), 0) + seam.get(w, 0)
                   for w in set(specH) | set(lint) | set(seam)):
            return False
        return all(specH.get(w, 0) == specH.get(rc(w), 0) for w in specH)

    ok_scope = all(decomp_ok(tuple(gw), 3)
                   for G in range(2, 9) for gw in product(("A", "T"), repeat=G))
    check(ok_scope,
          "spec_{S·ρ(S)}(w) = lint_S(w) + lint_S(ρ(w)) + j_S(w) and the doubled "
          "spectrum is class-symmetric (exhaustive, binary, 2 <= G <= 8, L = 3)")

    def compat(g, e):
        """The two double-strand conventions induce the same read-type
        distribution iff j_S(w) = wrap_S(w) + wrap_S(ρ(w)) for every w."""
        seam, wrap = seam_windows(g, e), wrap_spectrum(g, e)
        return all(seam.get(w, 0) == wrap.get(w, 0) + wrap.get(rc(w), 0)
                   for w in set(seam) | set(wrap))

    tot = sum(1 for G in range(2, 9) for _ in product(("A", "T"), repeat=G))
    comp = sum(1 for G in range(2, 9) for gw in product(("A", "T"), repeat=G)
               if compat(tuple(gw), 3))
    print(f"  binary words 2 <= G <= 8, L = 3: {tot} total, {comp} with "
          f"j_S(w) = wrap_S(w) + wrap_S(ρ(w)) for every w")
    check(comp < tot,
          "the two double-strand conventions do NOT always induce the same "
          "read-type distribution")

    gg = tuple("AAGG")
    m_gg, specH_gg = molecule_spectrum(gg, 3), spectrum(doubled_genome(gg), 3)
    print(f"  S = AAGG, L = 3: molecule spectrum = {fmt_counts(m_gg)}")
    print(f"  doubled genome = {''.join(doubled_genome(gg))}: spec_3 = {fmt_counts(specH_gg)}")
    check(specH_gg.get(("G", "G", "C"), 0) > 0 and m_gg.get(class_of(("G", "G", "C")), 0) == 0,
          "the doubled genome creates the junction class {GGC,GCC}, absent from S's "
          "molecule spectrum: the MB09 molecule model and the Bresler 2G remap are "
          "not the same model, not even at read-type support level")

    # 4e. balance does not descend to class counts
    print("  The de Bruijn balance equations, summed over a class {v, ρ(v)} of")
    print("  (L-1)-mers, mix d_u with d_{ρ(u)} inside each L-mer class and hence are")
    print("  not functions of the molecule spectrum: κ does not preserve balance as")
    print("  a well-defined condition on class counts.")


# --------------------------------------------------------------------------- #
# Section 5: bounded searches
# --------------------------------------------------------------------------- #


def is_primitive(g):
    G = len(g)
    return not any(G % p == 0 and g[:p] * (G // p) == tuple(g) for p in range(1, G))


def validate_long_triple_equivalence():
    """For *primitive* genomes, 'a maximal triple repeat of length >= L-1 exists'
    iff 'some length-(L-1) window occurs at least 3 times' (Lemma B of the
    rigidity note).  For periodic genomes the window criterion is strictly
    stronger (maximality blocks the repeats), which is Lemma C's domain."""
    for G in range(2, 9):
        for gw in product(("A", "T"), repeat=G):
            g = tuple(gw)
            if not is_primitive(g):
                continue
            for L in (2, 3, 4):
                if L - 1 > G:
                    continue
                if has_long_triple_repeat(g, L) != (max_window_multiplicity(g, L - 1) >= 3):
                    return False, (g, L)
    return True, None


def count_periodic_gaps():
    """Periodic genomes where a window occurs >= 3 times yet no maximal triple
    repeat of length >= L-1 exists (the window criterion is not a shortcut for
    them)."""
    n = 0
    for G in range(2, 7):
        for gw in product(("A", "T"), repeat=G):
            g = tuple(gw)
            if is_primitive(g):
                continue
            for L in (2, 3, 4):
                if L - 1 > G:
                    continue
                if max_window_multiplicity(g, L - 1) >= 3 and not has_long_triple_repeat(g, L):
                    n += 1
    return n


def section5():
    section("5. Bounded searches")
    ok, bad = validate_long_triple_equivalence()
    check(ok,
          "control (primitive genomes): 'a maximal triple repeat of length >= L-1 "
          "exists' iff 'some length-(L-1) window occurs >= 3 times' (exhaustive, "
          "binary, G <= 8, L <= 4)")
    check(count_periodic_gaps() > 0,
          "for periodic genomes the window-multiplicity shortcut is NOT valid "
          "(maximality blocks the repeat), so the wider scan below uses the exact "
          "triple-repeat computation")

    results = {}
    # The exhaustive circulation enumeration is exponential in the number of
    # oriented words `|Σ|^L`; the wider L = 4 scope is therefore kept small.
    for L in ((3, 4) if FULL else (3,)):
        Gmax = (10 if L == 3 else 6) if FULL else 8
        if L + 1 > Gmax:
            continue
        rows = []
        for G in range(L + 1, Gmax + 1):
            for gw in product(("A", "T"), repeat=G):
                g = tuple(gw)
                if has_long_triple_repeat(g, L):
                    continue  # fails the triple-repeat clause of I_s outright
                cands = molecule_candidate_spectra(g, L, alphabet=("A", "T"))
                sup = set(spectrum(g, L))
                orc = [B for B in enumerate_circulations(("A", "T"), L, G,
                                                         set(molecule_spectrum(g, L)))
                       if set(B) == sup]
                s = spectrum(g, L)
                m, mm = molecule_spectrum(g, L), molecule_spectrum(g, L - 1)
                rows.append({
                    "g": g, "G": G, "molecule_nonrigid": len(cands) > 1,
                    "oriented_nonrigid": len(orc) != 1,
                    # candidate repairs, all project-level hypotheses (not source):
                    "h1 (L-1)-class <= 2": max(mm.values()) <= 2,
                    "h2 L-class <= 2": max(m.values()) <= 2,
                    "h3 class-symmetric spec": all(s[w] == s.get(rc(w), 0) for w in s),
                    "h5 L-class mult even": all(v % 2 == 0 for v in m.values()),
                    "h6 (L-1)-class mult even": all(v % 2 == 0 for v in mm.values()),
                    "h7 both class mults <= 2": (max(mm.values()) <= 2
                                                 and max(m.values()) <= 2),
                })
        n = len(rows)
        print(f"  I_s-compatible at the triple-repeat clause, binary, L = {L}, "
              f"G <= {Gmax}: {n} genomes")
        print(f"    molecule-non-rigid (candidate set has >= 2 spectra): "
              f"{sum(1 for r in rows if r['molecule_nonrigid'])}")
        print(f"    oriented-non-rigid (oriented rigidity theorem violated): "
              f"{sum(1 for r in rows if r['oriented_nonrigid'])}")
        for h in ("h1 (L-1)-class <= 2", "h2 L-class <= 2", "h3 class-symmetric spec",
                  "h5 L-class mult even", "h6 (L-1)-class mult even",
                  "h7 both class mults <= 2"):
            sat = [r for r in rows if r[h]]
            bad = [r for r in sat if r["molecule_nonrigid"]]
            ex = [''.join(r["g"]) for r in bad[:4]]
            print(f"    {h}: satisfied by {len(sat)}, still non-rigid {len(bad)}"
                  + (f" (e.g. {ex})" if ex else "  <- not refuted in scope"))
        check(sum(1 for r in rows if r["oriented_nonrigid"]) == 0,
              f"L = {L}: the oriented rigidity theorem holds on the whole searched scope")
        nr = sum(1 for r in rows if r["molecule_nonrigid"])
        print(f"    verdict for L = {L}: molecule rigidity fails for {nr}/{len(rows)} "
              f"genomes in scope")
        results[L] = (len(rows), nr, rows)
    check(results[3][1] > 0,
          "L = 3: the molecule coarsening destroys rigidity where the integrated "
          "witness lives (86/162 in the quick scope)")
    check(results.get(4, (0, 0, None))[1] == 0,
          "L = 4: no molecule-non-rigid genome was found in the (much smaller) "
          "searched scope, so the phenomenon is (G, L)-scattered, as the bounded "
          "molecule searches on main already recorded")
    rows3 = results[3][2]
    refuted = [h for h in ("h1 (L-1)-class <= 2", "h2 L-class <= 2",
                           "h3 class-symmetric spec", "h5 L-class mult even",
                           "h6 (L-1)-class mult even")
               if any(r[h] and r["molecule_nonrigid"] for r in rows3)]
    check(len(refuted) == 5,
          "five tempting class-level repairs are REFUTED in the L = 3 scope: "
          f"{refuted}")
    check(all(not r["molecule_nonrigid"] for r in rows3 if r["h7 both class mults <= 2"]),
          "the only repair not refuted at L = 3 is 'every (L-1)-mer class and every "
          "L-mer class occurs at most twice' (bounded evidence, no proof)")

    print()
    print("  Bresler 2G remap: when is the remapped genome free of triple repeats")
    print("  of length >= L-1 (a necessary condition for the remapped I_s)?")
    for L in (3,):
        free, tot = [], 0
        for G in range(2, 11 if FULL else 8):
            for gw in product(("A", "T"), repeat=G):
                g = tuple(gw)
                tot += 1
                if not has_long_triple_repeat(doubled_genome(g), L):
                    free.append((G, "".join(g)))
        byG = {}
        for G, _ in free:
            byG[G] = byG.get(G, 0) + 1
        nG = {G: 2 ** G for G in range(2, 11 if FULL else 8)}
        print("    L = %d: %d/%d doubled genomes are long-triple-repeat-free: %s"
              % (L, len(free), tot,
                 "; ".join(f"G={G}: {byG.get(G, 0)}/{nG[G]}" for G in sorted(nG))))
        print(f"    smallest examples: {[w for _, w in free[:10]]}")
        check(len(free) < tot // 2,
              "the remapped I_s is satisfiable for a sparse minority of u only, at a "
              "density far below the original single-strand I_s (bounded computation)")


def show(name, d, total=None):
    print(f"  {name}{fmt_counts(d) if isinstance(d, dict) else d}")


def main():
    print("AssemblyP1 issue #215: oriented single-strand I_s vs the MB09 molecule data")
    print("and the Bresler 2G double-strand remap -- independent exact audit")
    S, D, L, starts, mS, mD, x = section0()
    section1(S, L, starts, x)
    section2(S, L, starts, x)
    section3(S, L, starts, x)
    section4(S, D, L, mS, mD, x)
    section5()
    print()
    if FAILURES:
        print(f"FAILED: {len(FAILURES)} assertion(s)")
        for f in FAILURES:
            print(f"  - {f}")
        sys.exit(1)
    print("All assertions passed.")


if __name__ == "__main__":
    main()
