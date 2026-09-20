#!/usr/bin/env python3
"""Uniform-strand-convention search: bridging `I_s` vs. maximum-likelihood.

Read-only-packet reproducibility script for the note
`docs/source-notes/uniform-strand-convention-search-2026-09-20.md`.

Two conventions are implemented end-to-end, never mixed:

  SINGLE-STRAND (Shomorony oriented semantics)
      read type = oriented length-L window (no reverse complement);
      candidate genome = oriented circular string of length G;
      objective = Medvedev-Brudno 6.1 exact multinomial (candidate-intrinsic
      N(D); for same-length candidates only the product of d^ x survives).

  DOUBLE-STRAND MOLECULE (Medvedev-Brudno read molecules / Bresler rc collapse)
      read type = reverse-complement class {w, revcomp(w)};
      candidate genome = circular string, spectrum grouped by molecule class;
      objective = the same exact multinomial over molecule classes.

Bridging `I_s` is always the source predicate on the plus-strand placement:
a read [r, r+L) bridges a copy [t, t+ell) iff, on the integer lift,
r < t and t + ell < r + L.  Coverage, all-bridged maximal triple repeats, and
bridged interleaved pairs are checked exactly as in Bresler et al. (2013) /
Shomorony et al. (2016) Eq. (1).

The script exits non-zero on any failed assertion.

Usage:
    python3 scripts/uniform_strand_semantics_search.py --witness
    python3 scripts/uniform_strand_semantics_search.py --search
"""
from __future__ import annotations

import argparse
import sys
import time
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, product

# ---------------------------------------------------------------------------
# Conventions
# ---------------------------------------------------------------------------

DNA4 = "ACGT"

def alphabet_for(sigma):
    return {2: "AT", 3: "ATC", 4: "ACGT"}[sigma]
COMP = {"A": "T", "T": "A", "C": "G", "G": "C"}


def revcomp(w, alphabet):
    return tuple(alphabet.index(COMP[alphabet[c]]) for c in reversed(w))


def read_type(w, alphabet, double):
    return frozenset((tuple(w), revcomp(w, alphabet))) if double else tuple(w)


def circular_windows(g, L):
    G = len(g)
    return [tuple(g[(i + j) % G] for j in range(L)) for i in range(G)]


def spectrum(g, L, alphabet, double):
    return Counter(read_type(w, alphabet, double) for w in circular_windows(g, L))


def observed(S, starts, L, alphabet, double):
    x = Counter()
    for r in starts:
        w = tuple(S[(r + j) % len(S)] for j in range(L))
        x[read_type(w, alphabet, double)] += 1
    return x


def exact_ratio(spec_S, spec_D, x, NS, ND):
    """L(D|x)/L(S|x) for the candidate-intrinsic exact multinomial."""
    r = Fraction(1)
    for c, xc in x.items():
        dS, dD = spec_S.get(c, 0), spec_D.get(c, 0)
        if dS == 0 or dD == 0:
            return Fraction(0)
        r *= (Fraction(dD, ND) / Fraction(dS, NS)) ** xc
    return r


# ---------------------------------------------------------------------------
# I_s (Bresler et al. 2013 / Shomorony et al. 2016, Eq. (1))
# ---------------------------------------------------------------------------

def covers(S, starts, L):
    G = len(S)
    cov = set()
    for r in starts:
        for o in range(L):
            cov.add((r + o) % G)
    return len(cov) == G


def maximal_pairs(S):
    G = len(S)
    out = []
    for ell in range(1, G):
        grp = defaultdict(list)
        for i in range(G):
            grp[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for pos in grp.values():
            for a, b in combinations(pos, 2):
                if (S[(a - 1) % G] != S[(b - 1) % G]
                        and S[(a + ell) % G] != S[(b + ell) % G]):
                    out.append((ell, tuple(sorted((a, b)))))
    return out


def triple_repeats(S):
    G = len(S)
    out = []
    for ell in range(1, G):
        grp = defaultdict(list)
        for i in range(G):
            grp[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for pos in grp.values():
            for tri in combinations(pos, 3):
                if (len({S[(t - 1) % G] for t in tri}) > 1
                        and len({S[(t + ell) % G] for t in tri}) > 1):
                    out.append((ell, tuple(sorted(tri))))
    return out


def interleaved_pairs(S):
    reps = maximal_pairs(S)
    out = []
    for i in range(len(reps)):
        e1, p1 = reps[i]
        for j in range(i + 1, len(reps)):
            e2, p2 = reps[j]
            four = sorted(set(p1) | set(p2))
            if len(four) != 4:
                continue
            lab = {p: 0 for p in p1}
            lab.update({p: 1 for p in p2})
            if [lab[p] for p in four] in ([0, 1, 0, 1], [1, 0, 1, 0]):
                out.append(((e1, p1), (e2, p2)))
    return out


def copy_bridged(S, t, ell, starts, L):
    """Strict source predicate on the integer lift: r < t and t+ell < r+L."""
    G = len(S)
    for r in starts:
        for tl in (t - G, t, t + G):
            if r < tl and tl + ell < r + L:
                return True
    return False


def check_Is(S, starts, L):
    return (covers(S, starts, L)
            and all(copy_bridged(S, t, ell, starts, L)
                    for ell, tri in triple_repeats(S) for t in tri)
            and all(any(copy_bridged(S, t, ell, starts, L) for t in p1)
                    or any(copy_bridged(S, t, ell2, starts, L) for t in p2)
                    for (ell, p1), (ell2, p2) in interleaved_pairs(S)))


# ---------------------------------------------------------------------------
# Witnesses
# ---------------------------------------------------------------------------

def show(g, alphabet):
    return "".join(alphabet[i] for i in g)


def verify_ss_witness():
    """Strict single-strand, sequence-level exact counterexample."""
    alphabet = "AT"
    S = (0, 0, 0, 1, 1)      # AAATT
    D = (0, 0, 0, 0, 1)      # AAAAT
    starts = (0, 1, 4)
    L, G = 3, 5
    assert check_Is(S, starts, L), "I_s must hold"
    spS = spectrum(S, L, alphabet, False)
    spD = spectrum(D, L, alphabet, False)
    x = observed(S, starts, L, alphabet, False)
    assert all(spD.get(c, 0) > 0 for c in x), "competitor must share support"
    r = exact_ratio(spS, spD, x, G, G)
    assert r == Fraction(2), r
    # no reverse complement is used anywhere in this block
    print("SINGLE-STRAND witness:")
    print(f"  S={show(S, alphabet)}  D={show(D, alphabet)}  G={G} L={L} starts={starts}")
    def fmt(c):
        return show(c, alphabet)

    dS_tbl = {fmt(k): v for k, v in sorted(spS.items())}
    dD_tbl = {fmt(k): v for k, v in sorted(spD.items())}
    x_tbl = {fmt(k): v for k, v in sorted(x.items())}
    print("  d_S=", dS_tbl)
    print("  d_D=", dD_tbl)
    print("  x  =", x_tbl)
    print(f"  strict I_s: {check_Is(S, starts, L)}   exact ratio D/S = {r}")
    return r


def verify_ds_witness():
    """Integrated G=6 molecule convention witness, and the single-strand tilt."""
    alphabet = "AT"
    S = (0, 0, 0, 1, 0, 1)   # AAATAT
    D = (0, 0, 0, 0, 0, 1)   # AAAAAT
    starts = (0, 0, 1, 3, 5)
    L, G = 3, 6
    assert check_Is(S, starts, L), "I_s must hold"
    out = {}
    for double in (False, True):
        spS = spectrum(S, L, alphabet, double)
        spD = spectrum(D, L, alphabet, double)
        x = observed(S, starts, L, alphabet, double)
        r = exact_ratio(spS, spD, x, G, G) if all(
            spS.get(c, 0) > 0 for c in x) else None
        out[double] = (spS, spD, x, r)
        tag = "MOLECULE" if double else "SINGLE-STRAND"
        suppS_eq = set(spS) == set(x)
        print(f"{tag}: supp(d_S)=supp(x)? {suppS_eq}  exact ratio D/S = {r}")
    # single-strand must fail because the observed oriented type TAT is absent
    # from D; molecule collapse makes TAT = ATA, restoring the witness.
    assert out[True][3] == Fraction(3), out[True][3]
    assert set(out[False][2]) != set(out[False][0]), "ss support differs"
    return out


# ---------------------------------------------------------------------------
# Bounded exhaustive search
# ---------------------------------------------------------------------------

def necklaces(G, sigma):
    seen = set()
    for tup in product(range(sigma), repeat=G):
        if tup in seen:
            continue
        orbit = {tuple(tup[(s + j) % G] for j in range(G)) for s in range(G)}
        seen |= orbit
        yield tup


def search(G, L, maxmul, sigma, double, support_equality):
    """Exhaustive over truth necklaces, start-multiplicity vectors 0..maxmul,
    and all competitor necklaces.  Optionally impose §6.2 support equality
    (spelled-circuit feasibility): supp(d_S)=supp(x)=supp(d_D)."""
    alphabet = alphabet_for(sigma)
    cands = list(necklaces(G, sigma))
    specs = [(D, spectrum(D, L, alphabet, double)) for D in cands]
    n_inst, cex = 0, []
    for S in necklaces(G, sigma):
        spS = spectrum(S, L, alphabet, double)
        trips = triple_repeats(S)
        inter = interleaved_pairs(S)
        for counts in product(range(maxmul + 1), repeat=G):
            if sum(counts) == 0:
                continue
            starts = tuple(p for p, c in enumerate(counts) for _ in range(c))
            if not (covers(S, starts, L)
                    and all(copy_bridged(S, t, e, starts, L) for e, tri in trips for t in tri)
                    and all(any(copy_bridged(S, t, e, starts, L) for t in p1)
                            or any(copy_bridged(S, t, e2, starts, L) for t in p2)
                            for (e, p1), (e2, p2) in inter)):
                continue
            x = observed(S, starts, L, alphabet, double)
            if support_equality and set(spS) != set(x):
                continue
            if any(spS.get(c, 0) == 0 for c in x):
                continue
            n_inst += 1
            for D, spD in specs:
                if spD == spS:
                    continue
                if support_equality and set(spD) != set(x):
                    continue
                if any(spD.get(c, 0) == 0 for c in x):
                    continue
                r = exact_ratio(spS, spD, x, G, G)
                if r > 1:
                    cex.append((S, D, starts, r))
    return n_inst, cex


def run_search(verbose=True):
    rows = [
        # (label, G, L, maxmul, sigma, double, support_equality)
        ("single-strand, sequence-level", 5, 3, 3, 2, False, False),
        ("single-strand, sequence-level", 6, 3, 3, 2, False, False),
        ("single-strand, §6.2 support", 5, 3, 3, 2, False, True),
        ("single-strand, §6.2 support", 6, 3, 3, 2, False, True),
        ("single-strand, §6.2 support", 6, 3, 4, 2, False, True),
        ("single-strand, §6.2 support", 7, 3, 3, 2, False, True),
        ("single-strand, §6.2 support", 5, 4, 3, 2, False, True),
        ("single-strand, §6.2 support", 6, 4, 3, 2, False, True),
        ("single-strand, §6.2 support", 6, 3, 2, 3, False, True),
        ("single-strand, §6.2 support", 5, 3, 2, 4, False, True),
        ("molecule, §6.2 support", 5, 3, 4, 2, True, True),
        ("molecule, §6.2 support", 6, 3, 4, 2, True, True),
        ("molecule, §6.2 support", 7, 3, 4, 2, True, True),
        ("molecule, §6.2 support", 6, 4, 4, 2, True, True),
        ("molecule, §6.2 support", 8, 3, 3, 2, True, True),
    ]
    all_cex = {}
    for label, G, L, mm, sig, dbl, se in rows:
        t0 = time.time()
        n, cex = search(G, L, mm, sig, dbl, se)
        dt = time.time() - t0
        all_cex[(label, G, L, mm, sig)] = cex
        if verbose:
            print(f"{label:32s} sigma={sig} G={G} L={L} maxmul={mm}: "
                  f"instances={n} cex={len(cex)} ({dt:.1f}s)")
    # single-strand sequence-level must find the AAATT orbit
    assert any(len(c) for k, c in all_cex.items() if "sequence-level" in k[0]), \
        "expected a single-strand sequence-level counterexample"
    # molecule §6.2 at G=6 must find the AAATAT orbit
    assert len(all_cex[("molecule, §6.2 support", 6, 3, 4, 2)]) > 0
    return all_cex


# ---------------------------------------------------------------------------
# Bresler et al. (2013) double-strand remap
# ---------------------------------------------------------------------------

def bresler_ds_search(G, L, maxmul, sigma):
    """Source: Bresler-Bresler-Tse 2013, 'Discussions and extensions', double
    strand: s = u . revcomp(u) has length 2G; each read is replaced by itself
    and its reverse complement (2N oriented reads); the single-strand I_s is
    applied to s.  A candidate genome is a length-G strand v, represented by
    s' = v . revcomp(v).  Objective: exact multinomial on s (N(D)=2G)."""
    alphabet = alphabet_for(sigma)
    twoG = 2 * G

    def strand_class(g):
        return g + revcomp(tuple(g), alphabet)

    us = list(necklaces(G, sigma))
    cands = [(v, strand_class(v)) for v in us]
    specs = [(v, Counter(circular_windows(sp, L))) for v, sp in cands]
    n_inst, cex = 0, []
    for u in us:
        s = strand_class(u)
        spS = Counter(circular_windows(s, L))
        trips = triple_repeats(s)
        inter = interleaved_pairs(s)
        for counts in product(range(maxmul + 1), repeat=G):
            if sum(counts) == 0:
                continue
            starts = tuple(p for p, c in enumerate(counts) for _ in range(c))
            ds = []
            for t in starts:
                ds.append(t)
                ds.append((twoG - L - t) % twoG)
            if not (covers(s, ds, L)
                    and all(copy_bridged(s, t, e, ds, L) for e, tri in trips for t in tri)
                    and all(any(copy_bridged(s, t, e, ds, L) for t in p1)
                            or any(copy_bridged(s, t, e2, ds, L) for t in p2)
                            for (e, p1), (e2, p2) in inter)):
                continue
            x = Counter(tuple(s[(r + j) % twoG] for j in range(L)) for r in ds)
            if set(spS) != set(x):
                continue
            n_inst += 1
            for v, spD in specs:
                if spD == spS or any(spD.get(c, 0) == 0 for c in x):
                    continue
                r = exact_ratio(spS, spD, x, twoG, twoG)
                if r > 1:
                    cex.append((u, v, starts, r))
    return n_inst, cex


def run_bresler_ds(verbose=True):
    rows = [(3, 2, 4, 2), (4, 2, 5, 2), (4, 3, 4, 2),
            (5, 3, 6, 2), (5, 4, 6, 2), (6, 3, 7, 2), (6, 4, 6, 2)]
    total_cex = 0
    for G, L, mm, sig in rows:
        t0 = time.time()
        n, cex = bresler_ds_search(G, L, mm, sig)
        dt = time.time() - t0
        total_cex += len(cex)
        if verbose:
            print(f"Bresler-DS remap sigma={sig} G={G} L={L} maxmul={mm}: "
                  f"instances={n} cex={len(cex)} ({dt:.1f}s)")
    return total_cex


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--witness", action="store_true")
    ap.add_argument("--search", action="store_true")
    ap.add_argument("--bresler-ds", action="store_true")
    args = ap.parse_args()
    if not (args.witness or args.search or args.bresler_ds):
        args.witness = args.search = args.bresler_ds = True
    if args.witness:
        print("=" * 70)
        verify_ss_witness()
        print("=" * 70)
        verify_ds_witness()
    if args.search:
        print("=" * 70)
        run_search()
    if args.bresler_ds:
        print("=" * 70)
        run_bresler_ds()
    print("all checks passed")


if __name__ == "__main__":
    main()
