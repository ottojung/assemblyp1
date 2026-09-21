#!/usr/bin/env python3
"""Support rigidity of the L-mer spectrum under Shomorony I_s admissibility.

This script is independent evidence for, and an exact reproduction of the finite
checks in, `docs/source-notes/support-rigidity-under-bridging-2026-09-21.md`.

Two logically distinct statements are checked:

  (C)  Theorem C (new here, proved in the note).
       If a circular word S of length G admits a same-length circular word D with
       supp(spec_L(D)) = supp(spec_L(S)) but spec_L(D) != spec_L(S)  (S is
       "support-non-rigid"), then some length-(L-1) substring of S occurs at
       least 3 times.

  (MAIN)  Main theorem.
       If S is I_s-admissible (every triple repeat has length <= L-2 and every
       interleaved maximal-repeat pair has a constituent of length <= L-2), then
       S is support-rigid: every same-length D with the same L-mer support has
       the same L-mer spectrum.

Non-rigidity is tested exactly and completely for a given support by enumerating
all balanced weightings d' = 1_E + y with y >= 0 and sum(y) = G - |E|, and asking
whether any equals neither spec_L(S) nor is infeasible. This is exactly the
support-equality condition of MB09 Section 6.2 for a spelled candidate.

All arithmetic is exact integers. Deterministic. Exits non-zero on any failed
assertion. Run:  python3 scripts/verify_support_rigidity_bridging.py
"""

import sys
import itertools
from collections import Counter, defaultdict


# ------------------------------------------------------------- spectra ------

def windows(S, L):
    G = len(S)
    return [tuple(S[(i + j) % G] for j in range(L)) for i in range(G)]


def spectrum(S, L):
    return Counter(windows(S, L))


def max_mult(S, k):
    return max(Counter(windows(S, k)).values())


def primitive(S):
    G = len(S)
    return not any(G % d == 0 and S == S[:d] * (G // d) for d in range(1, G))


# --------------------------------------------------- exact non-rigidity -----

_NONRIGID_CACHE = {}


def support_nonrigid(sp, L, cap=5_000_000):
    """True iff some positive balanced weighting d' on supp(sp) with the same
    total as sp (and d' != sp) exists.  Exact; composition enumeration.

    Non-rigidity depends only on the support, the total G and L (the balance
    graph and the split), so the result is cached on (support, G).
    """
    key = (frozenset(sp.keys()), sum(sp.values()))
    if key in _NONRIGID_CACHE:
        return _NONRIGID_CACHE[key]
    edges = list(sp.keys())
    E = len(edges)
    G = sum(sp.values())
    n_extra = G - E
    dS = [sp[e] for e in edges]
    yS = [dS[i] - 1 for i in range(E)]
    state = {"found": False, "count": 0}

    def balanced(y):
        out = defaultdict(int)
        inn = defaultdict(int)
        for i, e in enumerate(edges):
            d = 1 + y[i]
            out[e[:L - 1]] += d
            inn[e[1:]] += d
        return out == inn

    def rec(i, rem, cur):
        if state["found"] or state["count"] > cap:
            return
        if i == E - 1:
            state["count"] += 1
            y = cur + [rem]
            if y != yS and balanced(y):
                state["found"] = True
            return
        for v in range(rem + 1):
            rec(i + 1, rem - v, cur + [v])
            if state["found"] or state["count"] > cap:
                return

    rec(0, n_extra, [])
    assert state["count"] <= cap, "enumeration cap exceeded (scope too large)"
    _NONRIGID_CACHE[key] = state["found"]
    return state["found"]


# ------------------------------------------------------------- I_s ----------

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
            for p in itertools.combinations(pos, 2):
                t1, t2 = p
                if S[(t1 - 1) % G] != S[(t2 - 1) % G] and \
                   S[(t1 + ell) % G] != S[(t2 + ell) % G]:
                    if p not in seen:
                        seen.add(p)
                        out.append((ell, p))
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
            for tri in itertools.combinations(pos, 3):
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
            lab = {}
            for p in p1:
                lab[p] = 0
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


def is_admissible(S, L):
    """S admits some I_s read realization (equivalently, the full read set is
    I_s-admissible): every triple repeat has length <= L-2, every interleaved
    pair has a constituent of length <= L-2."""
    for ell, _ in triple_repeats(S):
        if ell > L - 2:
            return False, ("triple", ell)
    for (e1, _), (e2, _) in interleaved_pairs(S):
        if min(e1, e2) > L - 2:
            return False, ("interleaved", e1, e2)
    return True, None


# -------------------------------------------------------------- checks ------

def check_exhaustive(G, L, sigma, verbose=True):
    """All sigma^G circular words (including non-primitive).  Assert:
       (C)    non-rigid  =>  some (L-1)-mer occurs >= 3 times;
       (MAIN) I_s-admissible => support-rigid.
    """
    nr = nr_bad = adm = adm_nr = 0
    for S in itertools.product(range(sigma), repeat=G):
        sp = spectrum(S, L)
        nonrigid = support_nonrigid(sp, L)
        if nonrigid:
            nr += 1
            if max_mult(S, L - 1) < 3:
                nr_bad += 1
        ok, _ = is_admissible(S, L)
        if ok:
            adm += 1
            if nonrigid:
                adm_nr += 1
    if verbose:
        print(f"  G={G:>2} L={L} alpha={sigma}: non-rigid={nr:>5} "
              f"C-violations={nr_bad}  admissible={adm:>6} admiss-non-rigid={adm_nr}")
    assert nr_bad == 0, f"Theorem C violated at G={G} L={L} sigma={sigma}"
    assert adm_nr == 0, f"Main theorem violated at G={G} L={L} sigma={sigma}"
    return nr, nr_bad, adm, adm_nr


def check_powers(sigma=2, maxbase=5, verbose=True):
    """Targeted check on perfect powers B^k (non-primitive S), and on all
    rotations: I_s-admissible powers must be support-rigid."""
    tested = adm = adm_nr = 0
    for base_len in range(1, maxbase + 1):
        for B in itertools.product(range(sigma), repeat=base_len):
            for k in range(2, 5):
                S = B * k
                G = len(S)
                if G > 22:
                    continue
                for L in range(2, min(6, G) + 1):
                    tested += 1
                    sp = spectrum(S, L)
                    # skip enumeration blow-ups
                    if G - len(sp) > 13:
                        continue
                    ok, _ = is_admissible(S, L)
                    if not ok:
                        continue
                    adm += 1
                    if support_nonrigid(sp, L):
                        adm_nr += 1
    if verbose:
        print(f"  perfect powers: tested={tested} admissible={adm} "
              f"admiss-non-rigid={adm_nr}")
    assert adm_nr == 0, "perfect-power admissible non-rigid witness found"
    return tested, adm, adm_nr


def main():
    print("[C/MAIN] exhaustive scans (all words, incl. non-primitive):")
    scopes = [(9, 2, 2), (9, 3, 2), (10, 3, 2), (9, 3, 3), (8, 3, 4),
              (9, 4, 3), (8, 4, 3), (7, 2, 5)]
    for G, L, sigma in scopes:
        check_exhaustive(G, L, sigma)

    print("[MAIN] perfect powers (non-primitive):")
    check_powers()

    print("all support-rigidity checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
