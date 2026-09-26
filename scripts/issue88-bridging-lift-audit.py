#!/usr/bin/env python3
"""Audit of every `InformationFeasible` witness in the repository against the
**corrected same-lift** bridging predicate.

Old (endpoint-only, modular) `BridgesCopy`:
    exists r in R, ReadCovers L r ((t+G-1) % G) and ReadCovers L r ((t+e) % G)

Corrected (same-lift) `BridgesCopyLift`:
    exists r in R, exists d, d + e + 1 < L
        and (r+d) % G = (t+G-1) % G
        and (r+d+e+1) % G = (t+e) % G

which is the modular form of the lifted interval condition
`r' < t'` and `t'+e < r'+L` of `docs/bridging-source-semantics.md`; the third
alternative form is checked as well (`lift_interval`), so the three readings
are cross-verified computationally.
"""
import sys
from itertools import product
from importlib.machinery import SourceFileLoader

m = SourceFileLoader("er", "scripts/issue88-exact-range-search.py").load_module()


def bridges_copy_lift(L, R, e, t, G):
    return any((r + d) % G == (t + G - 1) % G
               and (r + d + e + 1) % G == (t + e) % G
               for r in R for d in range(L)
               if d + e + 1 < L)


def bridges_copy_lift_interval(L, R, e, t, G):
    """The lifted half-open interval formula, searched over lifts of r and t."""
    return any(rp < tp and tp + e < rp + L
               for r in R
               for rp in {r + k * G for k in range(-G, 2 * G + 1)}
               for tp in {t + k * G for k in range(-G, 2 * G + 1)})


def triple_repeats(S, G):
    for e in range(1, G):
        for a, b, c in product(range(G), repeat=3):
            if m.is_triple_repeat(S, e, a, b, c, G):
                yield e, a, b, c


def interleaved_pairs(S, G):
    for e1, e2 in product(range(1, G), repeat=2):
        for a, b, c, d in product(range(G), repeat=4):
            if (m.is_repeat(S, e1, a, b, G) and m.is_repeat(S, e2, c, d, G)
                    and m.interleaved(S, a, b, c, d, G)):
                yield e1, e2, a, b, c, d


def clause2(S, L, R, G, br):
    return all(all(br(L, R, e, t, G) for t in (a, b, c))
               for e, a, b, c in triple_repeats(S, G))


def clause3(S, L, R, G, br):
    return all(br(L, R, e1, a, G) or br(L, R, e1, b, G)
               or br(L, R, e2, c, G) or br(L, R, e2, d, G)
               for e1, e2, a, b, c, d in interleaved_pairs(S, G))


def I_s(S, L, R, G, br):
    return (m.covers(L, R, G) and clause2(S, L, R, G, br)
            and clause3(S, L, R, G, br))


INSTANCES = [
    # (module, S, L, R, note)
    ("WraparoundTripleRepeat", tuple("AAAAB"), 3, frozenset(range(5)),
     "wraparound-mode I_s instance used to show the regime non-empty"),
    ("MLEscape.truth0", tuple("0000001"), 3, frozenset(range(7)),
     "the non-vacuous culprit instance (claimed NOT I_s-feasible)"),

    ("SameLength62Maximizer", tuple("AAAAB"), 3, frozenset(range(5)),
     "the AAAAB I_s instance that the maximizer module uses to show the "
     "residual long-triple-repeat regime is non-empty"),
    ("SameLengthExactMLCounterexample", tuple("AABB"), 2, frozenset({1, 3}),
     "counterexample #88 (weakening I_s keeps it valid)"),
    ("FixedLengthExactCounterexample", tuple("AAABB"), 3, frozenset({0, 1, 4}),
     "counterexample (fixed length / exact ML)"),
    ("FiniteSamplingCounterexample", tuple("AABBC"), 3, frozenset({0, 3}),
     "counterexample (finite sampling)"),
    ("FixedLengthBinomialCounterexample", tuple("AAACC"), 3,
     frozenset({0, 1, 4}), "counterexample (fixed length / binomial)"),
    ("ExactVariantECounterexample", tuple("ACGT"), 2, frozenset({0, 2}),
     "counterexample (exact variant e)"),
    ("SameLengthSection62Counterexample", tuple("AAATAT"), 3,
     frozenset({0, 1, 3, 5}), "counterexample (same-length section 6.2)"),
    ("Section62BridgingCounterexample", tuple("AAATT"), 3,
     frozenset({0, 1, 4}), "counterexample (section 6.2 bridging)"),
]


def i_s_options(S, L, G):
    """Requirements of corrected `I_s` as option lists (same-lift bridging)."""
    opts = []
    for e in range(1, G):
        for a, b, c in product(range(G), repeat=3):
            if m.is_triple_repeat(S, e, a, b, c, G):
                opts.append([frozenset(r for r in range(G)
                                       if bridges_copy_lift(L, range(G), e, t, G))
                             for t in (a, b, c)])
        for e1, e2 in product(range(1, G), repeat=2):
            for a, b, c, d in product(range(G), repeat=4):
                if (m.is_repeat(S, e1, a, b, G) and m.is_repeat(S, e2, c, d, G)
                        and m.interleaved(S, a, b, c, d, G)):
                    opts.append([frozenset(r for r in range(G)
                                           if bridges_copy_lift(L, range(G), e, t, G))
                                 for e, t in ((e1, a), (e1, b), (e2, c), (e2, d))])
    return opts


def feasible(R, L, G, opts):
    if not m.covers(L, R, G):
        return False
    return all(any(R & o for o in options) for options in opts)


def corrected_feasible_census(Gmax=6, k=2, Lmax=None):
    """Search-level corroboration of `informationFeasibleLift_no_longTripleRepeat`:
    no corrected-`I_s`-feasible instance carries a long Bresler triple repeat,
    and the corrected predicate is non-vacuous."""
    feas = 0
    with_long = 0
    for G in range(3, Gmax + 1):
        for S in product(range(k), repeat=G):
            tl = m.maximal_triple_lengths(S, G)
            for L in range(2, (Lmax or G) + 1):
                opts = i_s_options(S, L, G)
                for r in range(G):
                    for R in product(range(G), repeat=r):
                        if not feasible(frozenset(R), L, G, opts):
                            continue
                        feas += 1
                        if any(l >= L - 1 for l in tl):
                            with_long += 1
    return feas, with_long


def main():
    G_of = {}
    print(f"{'module':38s} {'G':>2s} {'L':>2s}  old_I_s  new_I_s  verdict")
    for mod, S, L, R, note in INSTANCES:
        G = len(S)
        old = I_s(S, L, R, G, m.bridges_copy)
        new = I_s(S, L, R, G, bridges_copy_lift)
        # cross-check the three readings of the corrected predicate
        agree = True
        for e in range(1, G):
            for t in range(G):
                agree &= (bridges_copy_lift(L, R, e, t, G)
                          == bridges_copy_lift_interval(L, R, e, t, G))
        verdict = ("kept" if (old and new) else
                   "REPLACE (wraparound bridging)" if old and not new else
                   "not I_s-feasible in either reading")
        print(f"{mod:38s} {G:2d} {L:2d}  {str(old):7s}  {str(new):7s}  {verdict}"
              f"   [lift readings agree: {agree}]  {note}")
        if old and not new:
            for e, a, b, c in triple_repeats(S, G):
                oldb = [t for t in (a, b, c) if m.bridges_copy(L, R, e, t, G)]
                newb = [t for t in (a, b, c) if bridges_copy_lift(L, R, e, t, G)]
                print(f"    triple repeat e={e} at starts {(a, b, c)}: "
                      f"old-bridged copies {oldb}, new-bridged copies {newb}, "
                      f"e+2={e+2} > L={L}" if e + 2 > L else
                      f"    triple repeat e={e} at {(a, b, c)}: old {oldb} new {newb}")
    nfeas, nlong = corrected_feasible_census()
    print(f"\ncorrected-I_s census (binary, G in [3,6], 2 <= L <= G, all R): "
          f"corrected-feasible (S, L, R) = {nfeas}, of which carry a long "
          f"(l >= L-1) maximal triple repeat: {nlong}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
