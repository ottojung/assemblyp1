#!/usr/bin/env python3
"""Weakest-information witness for #272 (target: weakest conditioning).

Complements verify_272_minimal_sufficient.py and verify_272_source_defined.py
by framing the result explicitly as an implication (informativeness) order:

  E <= F  (E stronger / more informative, E implies F)  iff
  forall g r, E(g,r) -> F(g,r).  Weaker = larger admission set.

Checks, by brute force over the finite promise space:

1. Ambiguous TwoCandidate model (two candidates, one read, both realizable,
   distinct orbits): the sufficient promises are exactly {empty, D0, D1}.
   D0 and D1 are both *maximal-sufficient* (no sufficient strict superset:
   the only common superset is True, which is insufficient), hence both are
   minimal-information (weakest-candidate) promises; they are incomparable,
   so NO weakest sufficient promise exists.
2. Unambiguous model (reads separate the candidates): every promise is
   sufficient, so True is the unique weakest sufficient promise (every
   sufficient promise implies it).

The Lean kernel is the source of truth; this is an independent computational
cross-check.  Run:  python3 scripts/verify_272_weakest_witness.py
"""

import sys

CANDIDATES = [0, 1]
READS = [0]


def orbit(x):
    return x


def promises():
    for e00 in (False, True):
        for e10 in (False, True):
            yield (e00, e10)


def E_val(e, g, r):
    return e[g]


def sufficient(e, pi, p):
    for g in CANDIDATES:
        for r in READS:
            if pi(g) <= 0 or p(g, r) <= 0 or not E_val(e, g, r):
                continue
            for h in CANDIDATES:
                if pi(h) <= 0 or p(h, r) <= 0 or not E_val(e, h, r):
                    continue
                if orbit(h) != orbit(g):
                    return False
    return True


def implies(a, b):
    """a implies b (a stronger / more informative than b)."""
    return all((not E_val(a, g, r)) or E_val(b, g, r)
               for g in CANDIDATES for r in READS)


def strict_superset(a, b):
    """b is a strict superset of a (b strictly weaker than a)."""
    return a != b and implies(a, b)


def check_ambiguous_no_weakest():
    pi = lambda g: 0.5
    p = lambda g, r: 1.0
    suff = [e for e in promises() if sufficient(e, pi, p)]
    assert len(suff) == 3, f"expected 3 sufficient promises, got {suff}"
    D0 = (True, False)
    D1 = (False, True)
    empty = (False, False)
    assert sorted(suff) == sorted([empty, D0, D1]), f"suff={suff}"
    # D0, D1 are maximal-sufficient: no sufficient strict superset.
    for d in (D0, D1):
        wider = [e for e in promises()
                 if strict_superset(d, e) and sufficient(e, pi, p)]
        assert wider == [], f"{d} has sufficient strict superset {wider}"
    # Incomparable: neither implies the other.
    assert not implies(D0, D1) and not implies(D1, D0)
    # No weakest: the only common weakening (True) is insufficient.
    true = (True, True)
    assert all(implies(e, true) for e in suff)
    assert not sufficient(true, pi, p)


def check_unambiguous_weakest_true():
    # Modelled with reads separating candidates: reuse single-read frame with
    # likelihoods that never collide. Here both candidates cannot share a
    # positive read, so every promise is vacuously sufficient on each fibre.
    pi = lambda g: 0.5
    # candidate 0 only produces read 0; emulate by zeroing cross terms is
    # impossible with one read, so check the general claim instead: the
    # vacuous promise True is sufficient whenever each read fibre is
    # orbit-pure; verify on a two-read extension inline.
    cands = [0, 1]
    reads = [0, 1]
    pp = {(0, 0): 1.0, (0, 1): 0.0, (1, 0): 0.0, (1, 1): 1.0}

    def suff2(mask):
        E = {(g, r): bool(mask & (1 << (g * 2 + r)))
             for g in cands for r in reads}
        for g in cands:
            for r in reads:
                if pp[(g, r)] <= 0 or not E[(g, r)]:
                    continue
                for h in cands:
                    if pp[(h, r)] <= 0 or not E[(h, r)]:
                        continue
                    if h != g:
                        return False
        return True

    assert all(suff2(m) for m in range(16)), "all promises should be sufficient"
    # True (mask 15) is implied by every promise: it is the weakest.
    assert all(all(not (m & (1 << k)) or (15 & (1 << k)) for k in range(4))
               for m in range(16))


if __name__ == "__main__":
    ok = True
    for name, fn in [("ambiguous_no_weakest_two_maximal",
                      check_ambiguous_no_weakest),
                     ("unambiguous_weakest_is_true",
                      check_unambiguous_weakest_true)]:
        try:
            fn()
            print(f"{name}: PASS")
        except AssertionError as e:
            print(f"{name}: FAIL ({e})")
            ok = False
    sys.exit(0 if ok else 1)
