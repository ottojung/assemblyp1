#!/usr/bin/env python3
"""Independent verifier for AssemblyP1/FiniteSourceDefinedWeakest.lean (#272b).

Verifies the two concrete models kernel-checked by the Lean module:

1. AmbiguousRead (TwoCandidate): two candidates, one ambiguous read, distinct
   orbits.  The source-defined family has NO weakest sufficient promise.

2. UnambiguousExample: two candidates, two reads, each read produced by exactly
   one candidate.  The source-defined family HAS a weakest sufficient promise
   (the vacuous promise True).

This is a computational cross-check of the Lean witnesses; the Lean kernel is
the source of truth.  Run:  python3 scripts/verify_272_source_defined.py
"""

import itertools
import sys


def orbit(x):
    return x


def sufficient(E, pi, p, orbit, candidates, reads):
    for g in candidates:
        if pi[g] <= 0:
            continue
        for r in reads:
            if p[g][r] <= 0:
                continue
            if not E[g][r]:
                continue
            for h in candidates:
                if pi[h] <= 0:
                    continue
                if p[h][r] <= 0:
                    continue
                if not E[h][r]:
                    continue
                if orbit(h) != orbit(g):
                    return False
    return True


def unambiguous(pi, p, orbit, candidates, reads):
    for r in reads:
        seen = set()
        for g in candidates:
            if pi[g] > 0 and p[g][r] > 0:
                seen.add(orbit(g))
        if len(seen) > 1:
            return False
    return True


def adm_read_only(E, candidates, reads):
    for g in candidates:
        for gp in candidates:
            for r in reads:
                if E[g][r] != E[gp][r]:
                    return False
    return True


def adm_truth_only(E, candidates, reads):
    for g in candidates:
        for r in reads:
            for rp in reads:
                if E[g][r] != E[g][rp]:
                    return False
    return True


def adm_source_defined(E, candidates, reads):
    return adm_read_only(E, candidates, reads) or adm_truth_only(E, candidates, reads)


def all_source_defined_promises(candidates, reads):
    promises = []
    for g in candidates:
        for r in reads:
            pass
    for mask in range(1, 2 ** (len(candidates) * len(reads))):
        E = {}
        idx = 0
        for g in candidates:
            E[g] = {}
            for r in reads:
                E[g][r] = bool(mask & (1 << idx))
                idx += 1
        if adm_source_defined(E, candidates, reads):
            promises.append(E)
    return promises


def check_ambiguous():
    candidates = [0, 1]
    reads = [0]
    pi = {0: 0.5, 1: 0.5}
    p = {0: {0: 1.0}, 1: {0: 1.0}}

    assert not unambiguous(pi, p, orbit, candidates, reads), "should be ambiguous"

    sufficient_promises = [
        E for E in all_source_defined_promises(candidates, reads)
        if sufficient(E, pi, p, orbit, candidates, reads)
    ]
    assert len(sufficient_promises) > 0, "singletons should be sufficient"

    union = {}
    for g in candidates:
        union[g] = {}
        for r in reads:
            union[g][r] = any(E[g][r] for E in sufficient_promises)
    assert all(union[g][r] for g in candidates for r in reads), "union should be True"

    assert not sufficient(union, pi, p, orbit, candidates, reads), "union should NOT be sufficient"
    return True


def check_unambiguous():
    candidates = [0, 1]
    reads = [0, 1]
    pi = {0: 0.5, 1: 0.5}
    p = {0: {0: 1.0, 1: 0.0}, 1: {0: 0.0, 1: 1.0}}

    assert unambiguous(pi, p, orbit, candidates, reads), "should be unambiguous"

    E_true = {g: {r: True for r in reads} for g in candidates}
    assert sufficient(E_true, pi, p, orbit, candidates, reads), "True should be sufficient"
    return True


if __name__ == "__main__":
    ok = True
    try:
        check_ambiguous()
        print("Ambiguous model: PASS (no weakest source-defined promise)")
    except AssertionError as e:
        print(f"ambiguous model: FAIL ({e})")
        ok = False
    try:
        check_unambiguous()
        print("unambiguous model: PASS (weakest source-defined promise = True)")
    except AssertionError as e:
        print(f"unambiguous model: FAIL ({e})")
        ok = False
    sys.exit(0 if ok else 1)
