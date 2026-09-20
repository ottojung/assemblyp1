#!/usr/bin/env python3
"""
Same-length per-occurrence (`d >= x`) counterexample under the Shomorony
bridging hypothesis I_s, beyond the previously searched scope.

Question (adjacent exploration, not source intent)
--------------------------------------------------
The repository's main-branch note
`docs/section62-same-length-bidirected-counterexample.md` records the
strengthened candidate rule

    d_D(w) >= x_w   for every observed type w        ("per-occurrence", (P_fix))

as OPEN in its bounded scope (``G = 6, L = 3``, binary alphabet, bidirected
reading, 667 instances, 0 beats).  This script exhibits a counterexample
*beyond* that scope and verifies it with exact arithmetic and the corrected
strict bridging predicate of `docs/copy-bridging-predicate-correction.md`.

Witness (bidirected / reverse-complement molecule reading)
----------------------------------------------------------
    alphabet    {A, B, C}, reverse-complement A <-> B, C fixed
    L = 3
    truth       S = ABABACAC          (G = 8)
    competitor  D = ABACACAC          (G = 8, |D| = |S|)
    read starts T = (1, 3, 5, 7)  plus one ACA read at position 4 or 6
    observed    x = { ABA:1, BAC:1, ACA:2, CAC:1, ABC:1 }   (n = 6 < G)

d_S = { ABA:3, BAC:1, ACA:2, CAC:1, ABC:1 }
d_D = { ABA:1, BAC:1, ACA:3, CAC:2, ABC:1 }
exact same-length multinomial ratio  prod_w (d_D(w)/d_S(w))^{x_w} = 3/2 > 1.

I_s holds for the read set under the *strict* source predicate (the copy at
`t` of length `ell` is bridged by a read start `r` iff r = t-d mod G with
1 <= d <= L-ell-1); the truth and the competitor are both per-occurrence
feasible (support equality and d >= x); D is not a cyclic shift or reverse
complement of S.

A parametric family S_k = A^k ABABACAC, D_k = A^k ABACACAC works for k = 0,1,2
(G = 8,9,10) and stops at k = 3 because S_3 then contains an unbridgeable
length-(L-1) triple repeat "AA" and is not I_s-admissible.

Single-strand status
--------------------
No single-strand per-occurrence counterexample was found in the extended
scopes searched by --search (G <= 8, L in {3,4}, sigma <= 3, plus larger
one-off sweeps recorded in the companion note).  Without I_s the single-strand
rule is *false* (e.g. S = AAAAAAAB, D = AAAABAAB, exact ratio 16/5), so I_s is
essential and the single-strand statement stays open.

Usage
-----
    python3 scripts/verify_peroccurrence_samelength_counterexample.py
    python3 scripts/verify_peroccurrence_samelength_counterexample.py --search

Exact ``fractions.Fraction`` arithmetic throughout; exits non-zero on any
failed assertion.
"""
import argparse
import math
import sys
import time
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, product


# --------------------------------------------------------------------------
# Core model
# --------------------------------------------------------------------------
def make_comp(sigma):
    """Reverse-complement involution: 0<->1, 2<->3, ... (last fixed if odd)."""
    c = {}
    for i in range(0, sigma - 1, 2):
        c[i] = i + 1
        c[i + 1] = i
    if sigma % 2:
        c[sigma - 1] = sigma - 1
    return c


def mol(seq, comp):
    if comp is None:
        return tuple(seq)
    rc = tuple(comp[c] for c in reversed(seq))
    return min(tuple(seq), rc)


def windows(seq, L):
    G = len(seq)
    return [tuple(seq[(i + j) % G] for j in range(L)) for i in range(G)]


def spec_mol(seq, L, comp):
    return Counter(mol(w, comp) for w in windows(seq, L))


def observed(S, starts, L, comp):
    x = Counter()
    for r in starts:
        x[mol(tuple(S[(r + j) % len(S)] for j in range(L)), comp)] += 1
    return x


# --------------------------------------------------------------------------
# I_s under the corrected strict bridging predicate
# --------------------------------------------------------------------------
def maximal_repeat_pairs(S):
    G = len(S)
    out, seen = [], set()
    for ell in range(1, G):
        groups = defaultdict(list)
        for i in range(G):
            groups[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for _, pos in groups.items():
            if len(pos) < 2:
                continue
            for pair in combinations(pos, 2):
                t1, t2 = pair
                if (S[(t1 - 1) % G] != S[(t2 - 1) % G]
                        and S[(t1 + ell) % G] != S[(t2 + ell) % G]
                        and pair not in seen):
                    seen.add(pair)
                    out.append((ell, pair))
    return out


def triple_repeats(S):
    G = len(S)
    out, seen = [], set()
    for ell in range(1, G):
        groups = defaultdict(list)
        for i in range(G):
            groups[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for _, pos in groups.items():
            if len(pos) < 3:
                continue
            for tri in combinations(pos, 3):
                pre = {S[(t - 1) % G] for t in tri}
                post = {S[(t + ell) % G] for t in tri}
                if len(pre) > 1 and len(post) > 1:
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
            four = sorted(set(list(p1) + list(p2)))
            if len(four) != 4:
                continue
            lab = {p: 0 for p in p1}
            for p in p2:
                lab[p] = 1
            seq = [lab[p] for p in four]
            if seq in ([0, 1, 0, 1], [1, 0, 1, 0]):
                key = (e1, tuple(sorted(p1)), e2, tuple(sorted(p2)))
                if key not in seen:
                    seen.add(key)
                    out.append(((e1, tuple(sorted(p1))),
                                (e2, tuple(sorted(p2)))))
    return out


def strict_bridge_mask(G, t, ell, L):
    """Corrected source predicate: r = t-d (mod G), 1 <= d <= L-ell-1."""
    if L - ell - 1 < 1:
        return 0
    m = 0
    for d in range(1, L - ell):
        m |= 1 << ((t - d) % G)
    return m


def check_is_strict(S, starts, L, comp):
    """Direct I_s check for a concrete start multiset under the strict predicate."""
    G = len(S)
    cov = 0
    for r in starts:
        for o in range(L):
            cov |= 1 << ((r + o) % G)
    if cov != (1 << G) - 1:
        return False
    for ell, pos in triple_repeats(S):
        for t in pos:
            bm = strict_bridge_mask(G, t, ell, L)
            if not any((1 << r) & bm for r in starts):
                return False
    for (e1, p1), (e2, p2) in interleaved_pairs(S):
        b1 = any(any((1 << r) & strict_bridge_mask(G, t, e1, L)
                     for r in starts) for t in p1)
        b2 = any(any((1 << r) & strict_bridge_mask(G, t, e2, L)
                     for r in starts) for t in p2)
        if not (b1 or b2):
            return False
    return True


def valid_start_sets(S, L, comp):
    """All distinct-start sets T with I_s (strict predicate) and their type counts."""
    G = len(S)
    win = [mol(tuple(S[(r + j) % G] for j in range(L)), comp) for r in range(G)]
    covmask = [sum(1 << ((r + o) % G) for o in range(L)) for r in range(G)]
    full = (1 << G) - 1
    trip_masks = [strict_bridge_mask(G, t, ell, L)
                  for ell, pos in triple_repeats(S) for t in pos]
    inter_masks = []
    for (e1, p1), (e2, p2) in interleaved_pairs(S):
        m1 = m2 = 0
        for t in p1:
            m1 |= strict_bridge_mask(G, t, e1, L)
        for t in p2:
            m2 |= strict_bridge_mask(G, t, e2, L)
        inter_masks.append((m1, m2))
    out = []
    for mask in range(1, 1 << G):
        cm = 0
        mm = mask
        while mm:
            b = mm & (-mm)
            cm |= covmask[b.bit_length() - 1]
            mm ^= b
        if cm != full:
            continue
        if any(mask & bm == 0 for bm in trip_masks):
            continue
        if any(mask & m1 == 0 and mask & m2 == 0 for m1, m2 in inter_masks):
            continue
        c = Counter()
        mm = mask
        while mm:
            b = mm & (-mm)
            c[win[b.bit_length() - 1]] += 1
            mm ^= b
        out.append((mask, c))
    return out


# --------------------------------------------------------------------------
# Feasibility and objective
# --------------------------------------------------------------------------
def exact_ratio(spD, spS, x):
    r = Fraction(1)
    for w, xw in x.items():
        r *= Fraction(spD.get(w, 0), spS[w]) ** xw
    return r


def beats(S, D, L, comp):
    """Return (T_mask, x) if D beats S under per-occurrence, else None.

    Enumerates I_s-valid distinct-start sets T and, for each, the feasible
    x-box lo_w = max(c_w(T),1) <= x_w <= min(d_S(w), d_D(w)) with
    sum(x) <= G-1.  Maximising sum x_w log(d_D(w)/d_S(w)) over that box is a
    unit-weight fractional knapsack (spend spare budget on positive-ratio
    coordinates, largest first).
    """
    G = len(S)
    spS = spec_mol(S, L, comp)
    spD = spec_mol(D, L, comp)
    W = frozenset(spS)
    if frozenset(spD) != W:
        return None
    vs = valid_start_sets(S, L, comp)
    for mask, c in vs:
        rs = {}
        for w in W:
            dd = spD[w]
            if dd < 1:
                rs = None
                break
            rs[w] = (math.log(dd) - math.log(spS[w]), spS[w], dd)
        if rs is None:
            continue
        lo = {w: max(c.get(w, 0), 1) for w in W}
        sumlo = sum(lo.values())
        if sumlo > G - 1:
            continue
        budget = (G - 1) - sumlo
        order = sorted(W, key=lambda w: -rs[w][0])
        base = sum(lo[w] * rs[w][0] for w in W)
        val = base
        b = budget
        for w in order:
            if b <= 0:
                break
            r, ds, dd = rs[w]
            if r <= 0:
                break
            take = min(min(ds, dd) - lo[w], b)
            val += take * r
            b -= take
        if val <= 0:
            continue
        x = dict(lo)
        b = budget
        for w in order:
            if b <= 0:
                break
            r, ds, dd = rs[w]
            if r <= 0:
                break
            take = min(min(ds, dd) - lo[w], b)
            x[w] += take
            b -= take
        x = {w: v for w, v in x.items() if v > 0}
        if exact_ratio(spD, spS, x) > 1:
            return mask, x
    return None


def cyclic_or_rc_equivalent(A, B, comp):
    G = len(A)
    for i in range(G):
        if A[i:] + A[:i] == B:
            return True
        if comp is not None:
            rc = tuple(comp[c] for c in reversed(A[i:] + A[:i]))
            if rc == B:
                return True
    return False


# --------------------------------------------------------------------------
# Witness verification
# --------------------------------------------------------------------------
def lit(seq, alphabet="ABC"):
    return "".join(alphabet[c] for c in seq)


def verify_family_witness(k, verbose=True):
    """S_k = A^k ABABACAC, D_k = A^k ABACACAC; returns verified (mask,x) or None."""
    base_S = [0, 1, 0, 1, 0, 2, 0, 2]      # ABABACAC
    base_D = [0, 1, 0, 2, 0, 2, 0, 2]      # ABACACAC
    S = tuple([0] * k + base_S)
    D = tuple([0] * k + base_D)
    comp = make_comp(3)
    L = 3
    G = len(S)
    if not valid_start_sets(S, L, comp):
        return None
    res = beats(S, D, L, comp)
    if res is None:
        return None
    mask, x = res
    T = tuple(r for r in range(G) if mask >> r & 1)
    # independent checks
    spS = spec_mol(S, L, comp)
    spD = spec_mol(D, L, comp)
    assert set(x) == set(spS) == set(spD), "support equality failed"
    assert all(spS[w] >= v for w, v in x.items()), "truth not per-occurrence"
    assert all(spD[w] >= v for w, v in x.items()), "candidate not per-occurrence"
    assert sum(x.values()) < G, "degenerate n >= G"
    assert exact_ratio(spD, spS, x) == Fraction(3, 2), "family ratio != 3/2"
    assert not cyclic_or_rc_equivalent(S, D, comp), "D equivalent to S"
    # materialise the full read multiset (T plus padding) and re-check I_s and x
    win = [mol(tuple(S[(r + j) % G] for j in range(L)), comp) for r in range(G)]
    starts = list(T)
    c = Counter(win[r] for r in T)
    for w, need in x.items():
        extra = need - c.get(w, 0)
        assert extra >= 0, "padding negative"
        pos = [r for r in range(G) if win[r] == w]
        for i in range(extra):
            starts.append(pos[i % len(pos)])
    assert check_is_strict(S, starts, L, comp), "materialised read set fails I_s"
    assert observed(S, starts, L, comp) == Counter(x), "observed counts mismatch"
    if verbose:
        print(f"  k={k} G={G}  S={lit(S)}  D={lit(D)}  ratio=3/2  n={sum(x.values())}")
        print(f"      T={T}  x={ {lit(w): v for w, v in x.items()} }")
    return S, D, T, x


# --------------------------------------------------------------------------
# Bounded census (distinct (S, D) pairs) with strict I_s
# --------------------------------------------------------------------------
def census(G, L, sigma, comp):
    genomes = list(product(range(sigma), repeat=G))
    specs = [spec_mol(g, L, comp) for g in genomes]
    by = defaultdict(list)
    for i, sp in enumerate(specs):
        by[frozenset(sp)].append(i)
    seen = set()
    out = []
    for si, S in enumerate(genomes):
        spS = specs[si]
        W = frozenset(spS)
        if not valid_start_sets(S, L, comp):
            continue
        for di in by.get(W, []):
            if di == si:
                continue
            spD = specs[di]
            if any(spD.get(w, 0) < 1 for w in W):
                continue
            if (S, genomes[di]) in seen:
                continue
            if beats(S, genomes[di], L, comp) is not None:
                seen.add((S, genomes[di]))
                out.append((S, genomes[di]))
    return out


RECORDED = {
    (6, 3, 2, "ss"): 0, (6, 3, 2, "rc"): 0,
    (7, 3, 2, "ss"): 0, (7, 3, 2, "rc"): 0,
    (8, 3, 2, "ss"): 0, (8, 3, 2, "rc"): 0,
    (6, 3, 3, "ss"): 0, (6, 3, 3, "rc"): 0,
    (7, 3, 3, "ss"): 0, (7, 3, 3, "rc"): 0,
    (8, 3, 3, "ss"): 0, (8, 3, 3, "rc"): 256,
    (8, 4, 3, "ss"): 0, (8, 4, 3, "rc"): 0,
}


def run_census():
    print("=" * 78)
    print("Bounded census, fixed-length per-occurrence (d >= x), strict I_s")
    print("distinct (truth S, competitor D) pairs with a length-G beating D")
    print("=" * 78)
    total = 0
    for (G, L, sigma, reading), expected in RECORDED.items():
        comp = None if reading == "ss" else make_comp(sigma)
        t0 = time.time()
        out = census(G, L, sigma, comp)
        total += len(out)
        status = "OK" if len(out) == expected else "MISMATCH"
        print(f"  reading={reading:2} G={G} L={L} sigma={sigma}: "
              f"beats={len(out):>4} (recorded {expected}) [{status}] "
              f"({time.time()-t0:.1f}s)")
        assert len(out) == expected, \
            f"census regression at {(G, L, sigma, reading)}"
        if out:
            truths = {lit(t) for t, _ in out}
            print(f"      distinct truths: {sorted(truths)}")
    print(f"  total beating (S,D) pairs in census: {total}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--search", action="store_true",
                    help="run the extended bounded census (slower)")
    args = ap.parse_args()

    print("=" * 78)
    print("Same-length per-occurrence counterexample under I_s (bidirected)")
    print("=" * 78)
    witnesses = []
    for k in (0, 1, 2):
        w = verify_family_witness(k)
        assert w is not None, f"family witness k={k} failed"
        witnesses.append(w)

    # the k = 3 member must fail because S_3 is not I_s-admissible
    S3 = tuple([0] * 3 + [0, 1, 0, 1, 0, 2, 0, 2])
    assert not valid_start_sets(S3, 3, make_comp(3)), \
        "S_3 unexpectedly I_s-admissible"
    print("  k=3 stopper: S=AAABABACAC has no I_s start set (unbridgeable")
    print("               length-(L-1) triple repeat 'AA'); family stops here")

    # single-strand control: without I_s the rule is false, showing I_s matters
    S_ss = (0, 0, 0, 0, 0, 0, 0, 1)          # AAAAAAAB
    D_ss = (0, 0, 0, 0, 1, 0, 0, 1)          # AAAABAAB
    spSs, spDs = spec_mol(S_ss, 3, None), spec_mol(D_ss, 3, None)
    assert set(spSs) == set(spDs)
    x_ss = {w: 1 for w in spSs}
    assert exact_ratio(spDs, spSs, x_ss) == Fraction(16, 5)
    assert not valid_start_sets(S_ss, 3, None), "control truth unexpectedly I_s"
    print("  single-strand control WITHOUT I_s: S=AAAAAAAB D=AAAABAAB ratio=16/5;")
    print("      that truth is not I_s-admissible, so it is not a counterexample")

    if args.search:
        print()
        run_census()

    print("\nALL ASSERTIONS PASS")
    return 0


if __name__ == "__main__":
    if "--search" in sys.argv:
        sys.setrecursionlimit(10000)
    raise SystemExit(main())
