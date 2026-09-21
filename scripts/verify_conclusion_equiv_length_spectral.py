#!/usr/bin/env python3
"""
Independent verification for conclusion-semantics axes of the 2016 ML open
question: equivalence strength and candidate-length assumptions.

Claims checked (all exact integer / Fraction arithmetic, deterministic;
exits non-zero on any failed assertion):

  (1) Tandem invariance.  For a circular genome D, the k-fold tandem repeat
      D^k has N(D^k) = k*N(D) and d_{D^k}(w) = k*d_D(w), so the exact
      Medvedev-Brudno (2009) Section 6.1 probability d/N(D) is unchanged and
      L_exact(D^k | x) = L_exact(D | x) for EVERY observation x (up to the
      observation-only multinomial coefficient).  Hence, if free candidate
      length is allowed, every truth S is exactly tied by S^2 (length 2|S|,
      not cyclically/dihedrally equivalent), so the strong schema
      "every maximizer is the truth up to equivalence" is false for every
      truth and every equivalence that does not identify different lengths.

  (2) Spectral fibers.  The exact likelihood depends on a candidate only
      through (N(D), its L-mer spectrum).  Same-length same-spectrum
      candidates tie for every observation.  There exist same-length
      same-spectrum candidates that are not related by cyclic shift or by
      reverse complement (explicit minimal twins printed below).  Hence the
      strong schema requires the genome equivalence to collapse L-mer-spectrum
      fibers; cyclic shift alone and dihedral alone are insufficient in
      general.

  (3) The source-faithful (strict) bridging predicate.  A copy at t of length
      l is bridged by a read at r iff r is in {(t-d) mod G : 1 <= d <= L-l-1}
      (Bresler et al. 2013, Fig. 5).  The repository's exploratory predicate
      "(t-1) mod G and (t+l) mod G are both covered" can report a bridge via
      the complementary arc.  On the two integrated strict witnesses this
      looseness does NOT change the I_s verdict; both remain I_s-true under
      the strict predicate.

  (4) Bounded: no I_s-admissible truth (full read set, strict predicate) has a
      non-rotation same-length same-spectrum twin in the searched scope.  This
      is finite evidence for the repository's Conjecture 4 (I_s =>
      spectrum determines genome up to cyclic shift), not a proof.
"""

from collections import defaultdict
from fractions import Fraction
from itertools import product, combinations

# ---------------------------------------------------------------------------
# Basic circular-string utilities
# ---------------------------------------------------------------------------

def windows(w, L):
    n = len(w)
    return [tuple(w[(i + j) % n] for j in range(L)) for i in range(n)]


def spectrum(w, L):
    d = defaultdict(int)
    for x in windows(w, L):
        d[x] += 1
    return dict(d)


def rotations(w):
    n = len(w)
    return {tuple(w[(i + j) % n] for j in range(n)) for i in range(n)}


def canon(w):
    return min(rotations(w))


def rc(w, comp):
    return tuple(comp[c] for c in reversed(w))


def dihedral(w, comp):
    o = set()
    for r in rotations(w):
        o.add(r)
        o.add(rc(r, comp))
    return o


def tandem(w, k):
    return tuple(w[i % len(w)] for i in range(k * len(w)))


# ---------------------------------------------------------------------------
# Objectives (constants that cancel between same-length candidates dropped)
# ---------------------------------------------------------------------------

def observed(w, starts, L):
    x = defaultdict(int)
    n = len(w)
    for r in starts:
        x[tuple(w[(r + j) % n] for j in range(L))] += 1
    return dict(x)


def exact_product(D, x, L):
    """prod_w d_D(w)^{x_w}  (proportional to the exact multinomial likelihood
    for a fixed candidate length; and for variable length, the factor
    (N(D))^{-n} is included by the caller when comparing different lengths)."""
    d = spectrum(D, L)
    p = Fraction(1)
    for w, c in x.items():
        p *= Fraction(d.get(w, 0)) ** c
    return p


def exact_likelihood(D, x, L):
    """Exact MB09 6.1 likelihood up to the observation-only multinomial
    coefficient:  N(D)^{-n} * prod_w d_D(w)^{x_w}."""
    n = sum(x.values())
    return exact_product(D, x, L) / Fraction(len(D)) ** n


# ---------------------------------------------------------------------------
# Bridging predicates
# ---------------------------------------------------------------------------

def bridge_starts(G, L, t, l):
    """Source-faithful: reads whose forward interval strictly contains the copy."""
    if L - l - 1 < 1:
        return set()
    return {(t - d) % G for d in range(1, L - l)}


def strict_bridged(S, t, l, starts, L):
    G = len(S)
    return any(r in bridge_starts(G, L, t, l) for r in starts)


def loose_bridged(S, t, l, starts, L):
    G = len(S)
    for r in starts:
        cells = {(r + o) % G for o in range(L)}
        if (t - 1) % G in cells and (t + l) % G in cells:
            return True
    return False


def maximal_pairs(S):
    G = len(S); out = []
    for l in range(1, G):
        grp = defaultdict(list)
        for i in range(G):
            grp[tuple(S[(i + j) % G] for j in range(l))].append(i)
        for _, pos in grp.items():
            for a, b in combinations(pos, 2):
                if S[(a - 1) % G] != S[(b - 1) % G] and S[(a + l) % G] != S[(b + l) % G]:
                    out.append((l, tuple(sorted((a, b)))))
    return out


def triple_repeats(S):
    G = len(S); out = []
    for l in range(1, G):
        grp = defaultdict(list)
        for i in range(G):
            grp[tuple(S[(i + j) % G] for j in range(l))].append(i)
        for _, pos in grp.items():
            for tri in combinations(pos, 3):
                if (len({S[(t - 1) % G] for t in tri}) > 1
                        and len({S[(t + l) % G] for t in tri}) > 1):
                    out.append((l, tuple(sorted(tri))))
    return out


def interleaved_pairs(S):
    reps = maximal_pairs(S); out = []
    for i in range(len(reps)):
        e1, p1 = reps[i]
        for j in range(i + 1, len(reps)):
            e2, p2 = reps[j]
            four = sorted(set(p1) | set(p2))
            if len(four) != 4:
                continue
            lab = {p: 0 for p in p1}; lab.update({p: 1 for p in p2})
            if [lab[p] for p in four] in ([0, 1, 0, 1], [1, 0, 1, 0]):
                out.append(((e1, p1), (e2, p2)))
    return out


def check_I_s(S, starts, L, bridge):
    G = len(S)
    cov = set()
    for r in starts:
        for o in range(L):
            cov.add((r + o) % G)
    if len(cov) != G:
        return False
    for l, pos in triple_repeats(S):
        for t in pos:
            if not bridge(S, t, l, starts, L):
                return False
    for (e1, p1), (e2, p2) in interleaved_pairs(S):
        if not (any(bridge(S, t, e1, starts, L) for t in p1)
                or any(bridge(S, t, e2, starts, L) for t in p2)):
            return False
    return True


# ---------------------------------------------------------------------------
# Checks
# ---------------------------------------------------------------------------

def check_tandem_invariance():
    """(1) exact likelihood is tandem-invariant for all small genomes/samples."""
    tested = 0
    for alpha in (2, 3):
        for G in range(2, 8):
            for D in product(range(alpha), repeat=G):
                for L in range(2, G + 1):
                    # full-spectrum sample and the single-start samples
                    samples = [list(range(G)), [0], [0, 0, 1]]
                    for starts in samples:
                        x = observed(D, starts, L)
                        base = exact_likelihood(D, x, L)
                        for k in (2, 3):
                            assert exact_likelihood(tandem(D, k), x, L) == base, (D, L, starts, k)
                        tested += 1
    return tested


def minimal_spectral_twins(maxG=8):
    """(2) smallest same-length same-spectrum non-rotation pairs.

    Reports one representative pair per (alphabet, G, L) with a non-rotation
    twin, plus whether the pair is also non-dihedral (reverse-complement
    inequivalent).  For a 3-letter alphabet the involution used is A<->B with C
    fixed (any single-transposition involution exhibits the same phenomenon)."""
    comps = {2: {0: 1, 1: 0}, 3: {0: 1, 1: 0, 2: 2}}
    found = []
    for alpha in (2, 3):
        for G in range(4, maxG + 1):
            classes = {}
            for w in product(range(alpha), repeat=G):
                classes.setdefault(canon(w), w)
            reps = list(classes.values())
            for L in range(2, G + 1):
                byspec = defaultdict(list)
                for w in reps:
                    byspec[tuple(sorted(spectrum(w, L).items()))].append(w)
                shown = False
                for ws in byspec.values():
                    if shown or len(ws) < 2:
                        continue
                    for a, b in combinations(ws, 2):
                        if b in rotations(a):
                            continue
                        non_dih = b not in dihedral(a, comps[alpha])
                        found.append((alpha, G, L, a, b, non_dih))
                        shown = True
                        break
    found.sort(key=lambda r: (r[0], r[1], r[2]))
    return found


def strong_schema_free_length_witness():
    """(3) a truth tied by its tandem under free candidate length."""
    A, B = 0, 1
    S = (A, A, B)                      # AAB, G=3
    x = observed(S, [0, 1, 2], 2)      # complete 2-mer spectrum sample
    L = 2
    base = exact_likelihood(S, x, L)
    for k in (2, 3, 4):
        tk = tandem(S, k)
        assert tk != S and len(tk) != len(S)
        assert exact_likelihood(tk, x, L) == base
    return S, x, L, base


def witnesses_strict_vs_loose():
    """(3)/(4) integrated witnesses under both predicates."""
    out = []
    cases = [
        ("same-length AAATAT", (0, 0, 0, 1, 0, 1), (0, 0, 1, 3, 5), 3),
        ("variable AAATT", (0, 0, 0, 1, 1), (0, 0, 1, 2, 4), 3),
    ]
    for name, S, starts, L in cases:
        out.append((name,
                    check_I_s(S, starts, L, strict_bridged),
                    check_I_s(S, starts, L, loose_bridged)))
    return out


def i_s_admissible_spectral_twin_search(maxG, alpha):
    """(4) bounded: I_s-admissible truth with a non-rotation spectral twin."""
    hits = []
    for G in range(4, maxG + 1):
        classes = {}
        for w in product(range(alpha), repeat=G):
            classes.setdefault(canon(w), w)
        reps = list(classes.values())
        for L in range(3, G + 1):
            byspec = defaultdict(list)
            for w in reps:
                byspec[tuple(sorted(spectrum(w, L).items()))].append(w)
            for ws in byspec.values():
                if len(ws) < 2:
                    continue
                for S in ws:
                    if not check_I_s(S, list(range(G)), L, strict_bridged):
                        continue
                    twins = [d for d in ws if canon(d) != canon(S)]
                    if twins:
                        hits.append((alpha, G, L, S, twins))
    return hits


def main():
    t1 = check_tandem_invariance()
    print(f"(1) tandem invariance verified on {t1} (genome,L,sample) triples")

    twins = minimal_spectral_twins()
    print("(2) minimal same-length same-spectrum non-rotation twins:")
    shown = set()
    for alpha, G, L, a, b, nonrot in twins:
        key = (alpha, G, L)
        if key in shown:
            continue
        shown.add(key)
        if nonrot:
            w = "AB"[:alpha] if alpha == 2 else "ABC"
            print(f"    |Sigma|={alpha} G={G} L={L}: "
                  f"{''.join(w[c] for c in a)}  vs  {''.join(w[c] for c in b)}")
        if len(shown) >= 6:
            break

    S, x, L, base = strong_schema_free_length_witness()
    print(f"(3) free-length tandem tie: S={''.join('AB'[c] for c in S)} "
          f"tied by S^2,S^3,S^4 (likelihood {base})")

    for name, strict, loose in witnesses_strict_vs_loose():
        print(f"(4) witness {name}: I_s strict={strict} loose={loose}")
        assert strict, name

    hits = i_s_admissible_spectral_twin_search(9, 2)
    hits += i_s_admissible_spectral_twin_search(7, 3)
    print(f"(5) bounded I_s-admissible spectral-twin hits: {len(hits)}")
    assert not hits

    print("ALL CHECKS PASS")


if __name__ == "__main__":
    main()
