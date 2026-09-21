#!/usr/bin/env python3
"""Independent checks for docs/reconciliation-issue46-unlock-48-45-2026-09-21.md.

Self-contained, deterministic, exact arithmetic (fractions.Fraction). Exits
non-zero on any failed assertion. Bounded searches are evidence for the tested
scope only; they do not prove absence.

Run:  python3 scripts/verify_reconciliation_48_45.py
"""

from __future__ import annotations

import itertools
from collections import defaultdict
from fractions import Fraction


def windows(word, L):
    n = len(word)
    d = defaultdict(int)
    for i in range(n):
        d[tuple(word[(i + j) % n] for j in range(L))] += 1
    return dict(d)


def observed(word, starts, L):
    d = defaultdict(int)
    n = len(word)
    for r in starts:
        d[tuple(word[(r + j) % n] for j in range(L))] += 1
    return dict(d)


def covered(word, starts, L):
    n = len(word)
    cov = set()
    for r in starts:
        for o in range(L):
            cov.add((r + o) % n)
    return len(cov) == n


def maximal_pairs(word):
    n = len(word)
    out = []
    for ell in range(1, n):
        groups = defaultdict(list)
        for i in range(n):
            groups[tuple(word[(i + j) % n] for j in range(ell))].append(i)
        for _w, ts in groups.items():
            for a, b in itertools.combinations(ts, 2):
                if word[(a - 1) % n] != word[(b - 1) % n] and \
                   word[(a + ell) % n] != word[(b + ell) % n]:
                    out.append((ell, (a, b), _w))
    return out


def triple_repeats(word):
    n = len(word)
    out = []
    for ell in range(1, n):
        groups = defaultdict(list)
        for i in range(n):
            groups[tuple(word[(i + j) % n] for j in range(ell))].append(i)
        for _w, ts in groups.items():
            for tri in itertools.combinations(ts, 3):
                pres = {word[(t - 1) % n] for t in tri}
                posts = {word[(t + ell) % n] for t in tri}
                if len(pres) > 1 and len(posts) > 1:
                    out.append((ell, tuple(sorted(tri)), _w))
    return out


def interleaved_pairs(word):
    reps = maximal_pairs(word)
    out = []
    for i in range(len(reps)):
        for j in range(i + 1, len(reps)):
            e1, p1, w1 = reps[i]
            e2, p2, w2 = reps[j]
            four = sorted(set(p1) | set(p2))
            if len(four) != 4:
                continue
            labels = [0 if p in p1 else 1 for p in four]
            if labels in ([0, 1, 0, 1], [1, 0, 1, 0]):
                out.append((reps[i], reps[j]))
    return out


def copy_bridged(word, starts, t, ell, L):
    n = len(word)
    for r in starts:
        for m in range(-3, 4):
            rp = r + m * n
            if rp < t and t + ell < rp + L:
                return True
    return False


def check_I_s(word, starts, L):
    n = len(word)
    if not covered(word, starts, L):
        return False
    for ell, tri, _w in triple_repeats(word):
        for t in tri:
            if not copy_bridged(word, starts, t, ell, L):
                return False
    for (e1, p1, _w1), (e2, p2, _w2) in interleaved_pairs(word):
        b1 = any(copy_bridged(word, starts, t, e1, L) for t in p1)
        b2 = any(copy_bridged(word, starts, t, e2, L) for t in p2)
        if not (b1 or b2):
            return False
    return True


def strong_admissible(word, L):
    return all(v <= 1 for v in windows(word, L - 1).values())


def weak_admissible(word, L):
    for ell, _tri, _w in triple_repeats(word):
        if ell > L - 2:
            return False
    for (e1, _p1, _w1), (e2, _p2, _w2) in interleaved_pairs(word):
        if min(e1, e2) > L - 2:
            return False
    return True


def primitive(word):
    n = len(word)
    for p in range(1, n):
        if n % p == 0 and word == word[:p] * (n // p):
            return False
    return True


def ratio_free(S, D, obs):
    """Candidate-intrinsic (PO) ratio, N(D)=|D|."""
    nS, nD = len(S), len(D)
    L = len(next(iter(obs)))
    dS, dD = windows(S, L), windows(D, L)
    r = Fraction(1)
    for w, x in obs.items():
        if dD.get(w, 0) == 0:
            return Fraction(0)
        r *= Fraction(nS * dD[w], nD * dS[w]) ** x
    return r


def ratio_fixed(S, D, obs):
    """FN0 ratio: zero-count factors dropped, no length normalization."""
    L = len(next(iter(obs)))
    dS, dD = windows(S, L), windows(D, L)
    r = Fraction(1)
    for w, x in obs.items():
        if dD.get(w, 0) == 0:
            return Fraction(0)
        r *= Fraction(dD[w], dS[w]) ** x
    return r


def mol_canon(w):
    rc = w.translate(str.maketrans("ACGT", "TGCA"))[::-1]
    return min(w, rc)


def check_witness(name, S, D, starts, L, exp_free, exp_fixed, flow, truth_weak=None):
    S, D = list(S), list(D)
    obs = observed(S, starts, L)
    ok = True
    checks = {
        "truth primitive": primitive(S),
        "cand primitive": primitive(D),
        "truth I_s": check_I_s(S, starts, L),
    }
    if truth_weak is not None:
        checks["truth weak"] = weak_admissible(S, L) == truth_weak
    for k, v in checks.items():
        if not v:
            print(f"  FAIL {name}: {k}")
            ok = False
    rf, rx = ratio_free(S, D, obs), ratio_fixed(S, D, obs)
    if rf != exp_free:
        print(f"  FAIL {name}: free {rf} != {exp_free}")
        ok = False
    if rx != exp_fixed:
        print(f"  FAIL {name}: fixed {rx} != {exp_fixed}")
        ok = False
    flow_actual = set(windows(D, L)) == set(obs)
    if flow_actual != flow:
        print(f"  FAIL {name}: flow {flow_actual} != {flow}")
        ok = False
    print(f"  {name}: free={rf} fixed={rx} flow={flow_actual} ok={ok}")
    return ok


def search_flow_fixed_zero(alpha, maxG, maxL, maxN):
    """Bounded count of strict FLOW counterexamples under FN0."""
    hits = []
    for L in range(2, maxL + 1):
        for G in range(L, maxG + 1):
            for S in itertools.product(alpha, repeat=G):
                S = list(S)
                if not primitive(S) or not weak_admissible(S, L):
                    continue
                for N in range(L, maxN + 1):
                    for starts in itertools.combinations_with_replacement(range(G), N):
                        if not check_I_s(S, starts, L):
                            continue
                        obs = observed(S, starts, L)
                        supp = set(obs)
                        for nD in range(L, maxG + 1):
                            for D in itertools.product(alpha, repeat=nD):
                                D = list(D)
                                if not primitive(D) or not weak_admissible(D, L):
                                    continue
                                if set(windows(D, L)) != supp:
                                    continue
                                if ratio_fixed(S, D, obs) > 1:
                                    hits.append((G, L, "".join(S), starts,
                                                 "".join(D), ratio_fixed(S, D, obs)))
    return hits


def main():
    all_ok = True
    print("A. #48 finite witnesses (independent reproduction)")
    # N1: headline STRONG, SEQ, free-only strict
    all_ok &= check_witness("N1 AABBC->AABC", "AABBC", "AABC", [0, 3], 3,
                            Fraction(25, 16), Fraction(1), flow=False,
                            truth_weak=True)
    # N2: minimal coherent STRONG
    all_ok &= check_witness("N2 AABB->AAB", "AABB", "AAB", [0, 3], 3,
                            Fraction(16, 9), Fraction(1), flow=False,
                            truth_weak=True)
    # N3: FLOW-compatible free-length witness
    all_ok &= check_witness("N3 AAB->AB (FLOW)", "AAB", "AB", [1, 2], 2,
                            Fraction(9, 4), Fraction(1), flow=True,
                            truth_weak=True)
    # N4: FIXED, WEAK, SEQ, strict under both objectives
    all_ok &= check_witness("N4 AABBC->ABABC", "AABBC", "ABABC", [1, 3, 4], 2,
                            Fraction(2), Fraction(2), flow=False,
                            truth_weak=True)

    print("B. F1: any STRONG candidate with support containing obs has FN0 <= 1")
    # exhaustive small check
    f1_ok = True
    for L in (2, 3, 4):
        for nD in range(L, 7):
            for D in itertools.product("AB", repeat=nD):
                D = list(D)
                if not strong_admissible(D, L):
                    continue
                for G in range(L, 7):
                    for S in itertools.product("ABC", repeat=G):
                        S = list(S)
                        for starts in itertools.combinations_with_replacement(range(G), min(3, G)):
                            obs = observed(S, starts, L)
                            supp = set(obs)
                            if not supp.issubset(set(windows(D, L))):
                                continue
                            if ratio_fixed(S, D, obs) > 1:
                                f1_ok = False
                                print("  FAIL F1", S, D, starts, L)
    print(f"  F1 exhaustive small check: {'pass' if f1_ok else 'FAIL'}")
    all_ok &= f1_ok

    print("C. Bounded FLOW + FN0 strict counterexamples (expect 0)")
    hits = search_flow_fixed_zero("AB", 5, 2, 3)
    print(f"  alpha=AB G<=5 L<=2 N<=3: {len(hits)} hits")
    all_ok &= (len(hits) == 0)

    print("D. Population removes N1's strict win")
    S, D, L = list("AABBC"), list("AABC"), 3
    x = windows(S, L)  # population law
    pop_free = ratio_free(S, D, x)
    print(f"  population PO ratio AABC/AABBC = {pop_free}")
    all_ok &= (pop_free == 0)

    print("E. Molecule-panel collision AACAGT / AACTGT")
    S, T, L = list("AACAGT"), list("AACTGT"), 3
    sp = {mol_canon("".join(w)): v for w, v in windows(S, L).items()}
    tp = {mol_canon("".join(w)): v for w, v in windows(T, L).items()}
    eq = {k: Fraction(v, len(S)) for k, v in sp.items()} == \
         {k: Fraction(v, len(T)) for k, v in tp.items()}
    rots = {"".join(S[i:] + S[:i]) for i in range(len(S))}
    rc = "".join(S).translate(str.maketrans("ACGT", "TGCA"))[::-1]
    rc_rots = {rc[i:] + rc[:i] for i in range(len(S))}
    dihed = "".join(T) not in (rots | rc_rots)
    print(f"  equal normalized mol spectra={eq} primitive_strong="
          f"{primitive(S) and primitive(T) and strong_admissible(S, L) and strong_admissible(T, L)} "
          f"dihedrally_inequivalent={dihed}")
    all_ok &= (eq and primitive(S) and primitive(T) and dihed)

    print()
    print("ALL CHECKS PASSED" if all_ok else "SOME CHECKS FAILED")
    return 0 if all_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
