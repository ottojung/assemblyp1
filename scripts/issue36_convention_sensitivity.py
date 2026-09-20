#!/usr/bin/env python3
"""
Independent convention-sensitivity test for the issue #36 counterexample/flow frontier.

Conventions tested (all three are unresolved around issue #36):

  READING   : single-strand strings  vs  reverse-complement DNA molecules
  LOWERBOUND: per-occurrence (d_D(w) >= x_w)  vs  per-type (d_D(w) >= 1)
  EQUIV     : cyclic shift only  vs  cyclic shift + reverse complement (dihedral)

This script is self-contained: it does NOT import any repository module.  It
re-derives the Section 6.2 sequence-level feasibility predicate from the
Observation-7 criterion (support equality + lower bound) and re-runs the
small exhaustive scope of `scripts/se62_fixed_length_bidirected_search.py`
so the convention dependence can be read off directly.

Run:  python3 scripts/issue36_convention_sensitivity.py
Exact fractions.Fraction arithmetic.  Exits non-zero on any recorded mismatch.
"""
import sys
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product

# --------------------------------------------------------------------------
# Alphabet / reverse-complement involution
# --------------------------------------------------------------------------
# Real DNA: A<->T, C<->G.  For an even alphabet we pair consecutive symbols;
# this is the repository convention.  For odd alphabets the last symbol is
# fixed, which is an *artificial* involution and is flagged in the report.
def complement(sigma):
    c = {}
    for i in range(0, sigma - 1, 2):
        c[i], c[i + 1] = i + 1, i
    if sigma % 2:
        c[sigma - 1] = sigma - 1
    return c


def rc(seq, comp):
    return tuple(comp[c] for c in reversed(seq))


def molecule(seq, comp):
    if comp is None:
        return tuple(seq)
    return min(tuple(seq), rc(seq, comp))


def windows(seq, L):
    G = len(seq)
    return [tuple(seq[(i + j) % G] for j in range(L)) for i in range(G)]


def spectrum(seq, L, comp):
    return Counter(molecule(w, comp) for w in windows(seq, L))


def observed(S, starts, L, comp):
    x = Counter()
    for r in starts:
        x[molecule(tuple(S[(r + j) % len(S)] for j in range(L)), comp)] += 1
    return x


# --------------------------------------------------------------------------
# Sequence-level Section 6.2 feasibility (Observation-7 criterion)
# --------------------------------------------------------------------------
def feasible(D, x, L, comp, lower):
    """D is a spelled molecule on observed read vertices.

    lower='type' : support(spec(D)) == support(x) and d_D(w) >= 1
    lower='occ'  : support(spec(D)) == support(x) and d_D(w) >= x_w
    Also requires D to be a genuine non-degenerate walk: consecutive windows
    overlap in exactly L-1 symbols in the same orientation (always true for a
    circular molecule), which is automatic for `windows`.
    """
    sp = spectrum(D, L, comp)
    if set(sp) != set(x):
        return False
    if lower == "type":
        return all(sp.get(w, 0) >= 1 for w in x)
    return all(sp.get(w, 0) >= c for w, c in x.items())


# --------------------------------------------------------------------------
# Objectives (fixed-length, |D| = |S|)
# --------------------------------------------------------------------------
def exact_ratio(spD, spS, x):
    r = Fraction(1)
    for w, xw in x.items():
        r *= Fraction(spD.get(w, 0), spS[w]) ** xw
    return r


def binomial_ratio(spD, spS, x, N):
    n = sum(x.values())
    r = Fraction(1)
    for w, xw in x.items():
        dd, ds = spD.get(w, 0), spS[w]
        if dd > N or ds > N:
            return None
        r *= (Fraction(dd, N) ** xw * Fraction(N - dd, N) ** (n - xw)) / \
             (Fraction(ds, N) ** xw * Fraction(N - ds, N) ** (n - xw))
    return r


# --------------------------------------------------------------------------
# Equivalence relations
# --------------------------------------------------------------------------
def cyclic_equiv(a, b):
    if len(a) != len(b):
        return False
    n = len(a)
    return any(all(a[(i + k) % n] == b[k] for k in range(n)) for i in range(n))


def dihedral_equiv(a, b, comp):
    return cyclic_equiv(a, b) or cyclic_equiv(rc(a, comp), b)


# --------------------------------------------------------------------------
# I_s (mirrors the repository definitions; used only to bound the search)
# --------------------------------------------------------------------------
def maximal_repeat_pairs(S):
    G = len(S)
    out, seen = [], set()
    for ell in range(1, G):
        groups = defaultdict(list)
        for i in range(G):
            groups[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for pos in groups.values():
            if len(pos) < 2:
                continue
            for t1, t2 in combinations(pos, 2):
                if (S[(t1 - 1) % G] != S[(t2 - 1) % G]
                        and S[(t1 + ell) % G] != S[(t2 + ell) % G]
                        and (t1, t2) not in seen):
                    seen.add((t1, t2))
                    out.append((ell, (t1, t2)))
    return out


def triple_repeats(S):
    G = len(S)
    out, seen = [], set()
    for ell in range(1, G):
        groups = defaultdict(list)
        for i in range(G):
            groups[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for pos in groups.values():
            if len(pos) < 3:
                continue
            for tri in combinations(pos, 3):
                if (len({S[(t - 1) % G] for t in tri}) > 1
                        and len({S[(t + ell) % G] for t in tri}) > 1):
                    key = tuple(sorted(tri))
                    if key not in seen:
                        seen.add(key)
                        out.append((ell, key))
    return out


def interleaved_pairs(S):
    reps = maximal_repeat_pairs(S)
    out, seen = [], set()
    for i in range(len(reps)):
        e1, p1 = reps[i]
        for j in range(i + 1, len(reps)):
            e2, p2 = reps[j]
            four = sorted(set(p1) | set(p2))
            if len(four) != 4:
                continue
            lab = {p: 0 for p in p1}
            lab.update({p: 1 for p in p2})
            labs = [lab[p] for p in four]
            if labs in ([0, 1, 0, 1], [1, 0, 1, 0]):
                key = (e1, tuple(sorted(p1)), e2, tuple(sorted(p2)))
                if key not in seen:
                    seen.add(key)
                    out.append(((e1, tuple(sorted(p1))), (e2, tuple(sorted(p2)))))
    return out


def covers_all(S, starts, L):
    G = len(S)
    cov = set()
    for r in starts:
        cov |= {(r + o) % G for o in range(L)}
    return len(cov) == G


def copy_bridged(S, t, ell, starts, L):
    G = len(S)
    for r in starts:
        rp = {(r + o) % G for o in range(L)}
        if (t - 1) % G in rp and (t + ell) % G in rp:
            return True
    return False


def check_I_s(S, starts, L, trips, inter):
    if not covers_all(S, starts, L):
        return False
    for ell, pos in trips:
        if any(not copy_bridged(S, t, ell, starts, L) for t in pos):
            return False
    for (e1, p1), (e2, p2) in inter:
        b1 = any(copy_bridged(S, t, e1, starts, L) for t in p1)
        b2 = any(copy_bridged(S, t, e2, starts, L) for t in p2)
        if not (b1 or b2):
            return False
    return True


# --------------------------------------------------------------------------
# Witness: S = AAATAT, D = AAAAAT, L = 3, starts (0,0,1,3,5)
# --------------------------------------------------------------------------
S = (0, 0, 0, 1, 0, 1)
D = (0, 0, 0, 0, 0, 1)
L = 3
STARTS = (0, 0, 1, 3, 5)
RCDNA = {0: 1, 1: 0}          # A<->T on the two-symbol alphabet
LAB = "AT"


def lit(seq):
    return "".join(LAB[c] for c in seq)


def witness_table():
    print("=" * 78)
    print("Witness convention matrix: S=AAATAT  D=AAAAAT  L=3  starts=(0,0,1,3,5)")
    print("=" * 78)
    print(f"  I_s(S, starts) = {check_I_s(S, STARTS, L, triple_repeats(S), interleaved_pairs(S))}")
    rows = []
    for reading, comp in (("single-strand", None), ("revcomp-molecule", RCDNA)):
        x = observed(S, STARTS, L, comp)
        spS = spectrum(S, L, comp)
        spD = spectrum(D, L, comp)
        for lower in ("type", "occ"):
            fS = feasible(S, x, L, comp, lower)
            fD = feasible(D, x, L, comp, lower)
            er = exact_ratio(spD, spS, x) if fS and fD else None
            cex = bool(fS and fD and er > 1)
            rows.append((reading, lower, fS, fD, cex, er))
            print(f"  reading={reading:16s} lower={lower:4s} "
                  f"truth_feasible={str(fS):5s} comp_feasible={str(fD):5s} "
                  f"exact_ratio={er}  CEX={cex}")
        print(f"      truth spectrum  = { {lit(k): v for k, v in spS.items()} }")
        print(f"      competitor spec = { {lit(k): v for k, v in spD.items()} }")
        print(f"      observed x      = { {lit(k): v for k, v in x.items()} }")
        dih = dihedral_equiv(S, D, comp) if comp is not None else None
        print(f"      cyclic_equiv(S,D)={cyclic_equiv(S, D)}   "
              f"dihedral_equiv(S,D)={dih}")
    return rows


# --------------------------------------------------------------------------
# Exhaustive G=6, L=3, sigma=2 fixed-length search under all four conventions
# --------------------------------------------------------------------------
def search(G, L, comp, lower, equiv_comp):
    # group candidates by their molecule spectrum
    by_spec = defaultdict(list)
    for Dc in product(range(2), repeat=G):
        by_spec[frozenset(spectrum(Dc, L, comp))].append(Dc)
    n_cex = 0
    n_equiv_to_truth = 0
    truths = set()
    for Sc in product(range(2), repeat=G):
        trips, inter = triple_repeats(Sc), interleaved_pairs(Sc)
        spS = spectrum(Sc, L, comp)
        for N in range(max(1, (G + L - 1) // L), G + 3):
            for starts in combinations_with_replacement(range(G), N):
                if not check_I_s(Sc, starts, L, trips, inter):
                    continue
                x = observed(Sc, starts, L, comp)
                if set(x) != set(spS):
                    continue
                if not feasible(Sc, x, L, comp, lower):
                    continue
                for Dc in by_spec.get(frozenset(x), []):
                    if not feasible(Dc, x, L, comp, lower):
                        continue
                    if spectrum(Dc, L, comp) == spS:
                        continue
                    if exact_ratio(spectrum(Dc, L, comp), spS, x) > 1:
                        n_cex += 1
                        truths.add(Sc)
                        # does the equivalence relation absorb this competitor?
                        if equiv_comp is None:
                            eq = cyclic_equiv(Dc, Sc)
                        else:
                            eq = dihedral_equiv(Dc, Sc, equiv_comp)
                        if eq:
                            n_equiv_to_truth += 1
    return n_cex, len(truths), n_equiv_to_truth


def other_witnesses():
    """Effect of the reading convention on the existing single-strand witnesses."""
    print()
    print("=" * 78)
    print("Reading-convention effect on existing witnesses")
    print("=" * 78)
    # Issue #31: S = AAABB (B:=T), D = AAAAB, L = 3, starts {0,1,4}
    S31, D31, st31 = (0, 0, 0, 1, 1), (0, 0, 0, 0, 1), (0, 1, 4)
    for reading, comp in (("single-strand", None), ("revcomp-molecule", RCDNA)):
        x = observed(S31, st31, 3, comp)
        fS = feasible(S31, x, 3, comp, "occ")
        fD = feasible(D31, x, 3, comp, "occ")
        note = ("competitor feasible, truth not (witness stands)"
                if fD and not fS else
                "truth feasible, competitor not (witness INVERTS)"
                if fS and not fD else
                "both feasible" if fS and fD else "neither feasible")
        print(f"  #31 S=AAATT D=AAAAT  reading={reading:16s} "
              f"truth={fS} comp={fD}  -> {note}")
    # Read-tiled: S = AAABCBC (A,B,C = 0,1,2), D = AAAAABC, starts (0,0,0,1,2,5,6)
    Srt = (0, 0, 0, 1, 2, 1, 2)
    Drt = (0, 0, 0, 0, 0, 1, 2)
    strt = (0, 0, 0, 1, 2, 5, 6)
    comps = {
        "none": None,
        "A<->B (0<->1)": {0: 1, 1: 0, 2: 2},
        "B<->C (1<->2)": {0: 0, 1: 2, 2: 1},
    }
    for name, comp in comps.items():
        x = observed(Srt, strt, 3, comp)
        fS = feasible(Srt, x, 3, comp, "type")
        fD = feasible(Drt, x, 3, comp, "type")
        print(f"  read-tiled S=AAABCBC D=AAAAABC  involution={name:14s} "
              f"truth={fS} comp={fD}")


def exhaustive_table():
    print()
    print("=" * 78)
    print("Exhaustive G=6, L=3, sigma=2 fixed-length search, all conventions")
    print("=" * 78)
    expected = {
        ("single-strand", "occ"): 0, ("single-strand", "type"): 0,
        ("revcomp-molecule", "occ"): 0, ("revcomp-molecule", "type"): 4608,
    }
    for reading, comp in (("single-strand", None), ("revcomp-molecule", RCDNA)):
        for lower in ("occ", "type"):
            for eq_name, eq_comp in (("cyclic", None), ("dihedral", comp)):
                n, truths, eqbad = search(6, 3, comp, lower, eq_comp)
                ok = (n == expected[(reading, lower)])
                print(f"  reading={reading:16s} lower={lower:4s} equiv={eq_name:8s} "
                      f"cex={n:5d} distinct_truths={truths:3d} "
                      f"cex_equivalent_to_truth={eqbad} "
                      f"{'OK' if ok else 'MISMATCH'}")
                assert ok, (reading, lower, eq_name, n, expected[(reading, lower)])
    assert expected[("single-strand", "occ")] == 0 and expected[("single-strand", "type")] == 0
    assert expected[("revcomp-molecule", "occ")] == 0 and expected[("revcomp-molecule", "type")] == 4608
    print("  -> counterexamples exist ONLY for (revcomp-molecule, per-type).")
    print("  -> the equivalence relation does not absorb any counterexample.")


if __name__ == "__main__":
    rows = witness_table()
    # Recorded witness facts
    assert check_I_s(S, STARTS, L, triple_repeats(S), interleaved_pairs(S))
    got = {(r[0], r[1]): (r[2], r[3], r[4], r[5]) for r in rows}
    assert got[("single-strand", "type")][2] is False, got
    assert got[("single-strand", "occ")][2] is False, got
    assert got[("revcomp-molecule", "occ")][2] is False, got
    assert got[("revcomp-molecule", "type")] == (True, True, True, Fraction(3)), got
    other_witnesses()
    exhaustive_table()
    print("\nALL ASSERTIONS PASS")
    sys.exit(0)
