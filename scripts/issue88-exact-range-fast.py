#!/usr/bin/env python3
"""#88 audit search under **exact-range** `I_s` semantics (fast version).

Same exact transcriptions as `issue88-exact-range-search.py`; the only
difference is that `I_s` is evaluated as a hitting-set condition: for each
triple repeat (resp. interleaved pair) the acceptable options are the
`BridgesCopy` sets of its three (resp. four) selected copies, so feasibility of
a candidate `R` is decided by intersecting precomputed option sets instead of
re-running the full clause scan for every subset.  This is an optimisation
only: the option sets are exactly `BridgesCopy S L R e t` as defined in
`SourceFaithfulIs`, with `R = [r]` for the single start `r`.

Each requirement carries the quantifier the corresponding `I_s` clause uses:
`all` for a triple repeat (every selected copy must be bridged) and `any` for
an interleaved pair (at least one of the four copies).  Moreover the *option set
of a copy* is the set of starts that bridge **that copy by themselves**,
`{r : BridgesCopy L [r] e t}`, not `{r : BridgesCopy L (all starts) e t}`: the
latter is a statement about the whole set and is true as soon as *some* read
bridges, which would make every bridging option set the full set of starts and
silently void clauses 2 and 3.  `feasible` below is checked against
`issue88-exact-range-search.py`'s `information_feasible` set by set at binary
`G = 5`, all `2 <= L <= 5` (agreement on all 32 truths, all 31 nonempty start
subsets each), for **both** bridging readings.

`--bridge canonical` (default) uses the canonical single-lift span condition
`SourceFaithfulIs.BridgesCopy`; `--bridge endpoint` uses the weaker
pre-migration endpoint-only reading, kept only so that
`docs/bridging-lift-audit.md` can quote both sets of counts.

Usage: exact_range_fast.py [G] [alphabet] [nmax] [Lmin] [Lmax] [--bridge canonical|endpoint]
"""
import sys
from itertools import product
from importlib.machinery import SourceFileLoader
from importlib.util import spec_from_loader, module_from_spec

_spec = spec_from_loader("er", SourceFileLoader("er", "scripts/issue88-exact-range-search.py"))
_m = module_from_spec(_spec)
_spec.loader.exec_module(_m)

BRIDGES = {"canonical": _m.bridges_copy, "endpoint": _m.bridges_copy_endpoint_only}


def i_s_options(S, L, G, bridge):
    """Requirements of `InformationFeasible <G,_,S> L R` as `(quantifier, options)`."""
    opts = []
    for e in range(1, G):
        for a, b, c in product(range(G), repeat=3):
            if _m.is_triple_repeat(S, e, a, b, c, G):
                # clause 2: EVERY selected copy of a triple repeat is bridged
                opts.append(("all", [frozenset(r for r in range(G)
                                               if bridge(L, [r], e, t, G))
                                     for t in (a, b, c)]))
        for e1, e2 in product(range(1, G), repeat=2):
            for a, b, c, d in product(range(G), repeat=4):
                if (_m.is_repeat(S, e1, a, b, G) and _m.is_repeat(S, e2, c, d, G)
                        and _m.interleaved(S, a, b, c, d, G)):
                    # clause 3: AT LEAST ONE of the four selected copies is bridged
                    opts.append(("any", [frozenset(r for r in range(G)
                                                   if bridge(L, [r], e, t, G))
                                         for e, t in ((e1, a), (e1, b), (e2, c), (e2, d))]))
    return opts


def feasible(R, L, G, opts):
    if not _m.covers(L, R, G):
        return False
    for quant, options in opts:
        hits = [bool(R & o) for o in options]
        if not (all(hits) if quant == "all" else any(hits)):
            return False
    return True


def feasible_set(S, L, G, bridge):
    opts = i_s_options(S, L, G, bridge)
    return set(frozenset(R) for r in range(G)
               for R in product(range(G), repeat=r)
               if feasible(frozenset(R), L, G, opts))


def cross_check(G, Lmin, Lmax, k, bridges):
    """The two harnesses must agree set by set, for every bridging reading."""
    words = list(product(range(k), repeat=G))
    subsets = [frozenset(R) for r in range(G) for R in product(range(G), repeat=r)]
    for S in words:
        for L in range(Lmin, Lmax + 1):
            for name, b in bridges.items():
                slow = set(R for R in subsets
                           if _m.information_feasible(S, L, R, G, b))
                fast = feasible_set(S, L, G, b)
                if fast != slow:
                    print("  MISMATCH bridge=%s S=%s L=%d: fast-only=%s slow-only=%s"
                          % (name, "".join(map(str, S)), L,
                             sorted(tuple(sorted(x)) for x in fast - slow)[:5],
                             sorted(tuple(sorted(x)) for x in slow - fast)[:5]))
                    return False
    return True


def census(S, L, G, k, nmax, bridge, report_diffs=4):
    words = list(product(range(k), repeat=G))
    feasset = feasible_set(S, L, G, bridge)
    feas = sorted(feasset, key=len)
    dS = _m.spec(S, L, G)
    if not dS:
        return dict(exact=0, super=0, diff=0, mlfail=0, viol=0), [], []
    supS = frozenset(dS)
    cands = [D for D in words if frozenset(_m.spec(D, L, G)) == supS]
    tl = _m.maximal_triple_lengths(S, G)
    st = dict(exact=0, super=0, diff=0, mlfail=0, viol=0)
    viols, diffs = [], []
    for n in range(1, nmax + 1):
        for v in _m.start_count_vectors(G, n):
            R = frozenset(i for i in range(G) if v[i] > 0)
            exact = R in feasset
            superset_ok = any(R <= F for F in feas)
            st["exact"] += exact
            st["super"] += superset_ok
            if superset_ok and not exact:
                st["diff"] += 1
                if len(diffs) < report_diffs:
                    diffs.append((L, tuple(sorted(R)),
                                  min((tuple(sorted(F)) for F in feas if R <= F),
                                      key=len)))
            if not exact:
                continue
            starts = [i for i in range(G) for _ in range(v[i])]
            x = _m.observed_of(S, L, starts, G)
            sS = _m.score(dS, x, G)
            beaten = [D for D in cands if _m.score(_m.spec(D, L, G), x, G) > sS]
            if beaten:
                st["mlfail"] += 1
                if not _m.has_band(S, L - 1, G - L, G):
                    st["viol"] += 1
                    viols.append((L, tuple(sorted(R)), beaten[0], x, sorted(tl)))
    return st, diffs, viols


def main():
    argv = sys.argv[1:]
    tag = "canonical"
    if "--bridge" in argv:
        i = argv.index("--bridge")
        tag = argv[i + 1]
        del argv[i:i + 2]
    want_check = "--cross-check" in argv
    argv = [a for a in argv if a != "--cross-check"]
    bridge = BRIDGES[tag]
    G = int(argv[0]); k = int(argv[1]); nmax = int(argv[2])
    Lmin = int(argv[3]); Lmax = int(argv[4])
    if want_check:
        ok = cross_check(G, Lmin, Lmax, k, BRIDGES)
        print("cross-check of the two harnesses (all bridging readings, every "
              "truth, every start subset): %s" % ("AGREE" if ok else "DISAGREE"))
        if not ok:
            return 1
    words = list(product(range(k), repeat=G))
    tot = dict(exact=0, super=0, diff=0, mlfail=0, viol=0)
    viols, diffs = [], []
    for S in words:
        for L in range(Lmin, Lmax + 1):
            st, d, v = census(S, L, G, k, nmax, bridge)
            for key in tot:
                tot[key] += st[key]
            diffs += [(S,) + x for x in d][:4]
            viols += [(S,) + x for x in v][:4]
    print(f"[{tag}] G={G} k={k} L in [{Lmin},{Lmax}] nmax={nmax}: "
          f"exact-range feasible={tot['exact']}, "
          f"subset-only feasible={tot['super']}, "
          f"subset-only but not exact={tot['diff']}, "
          f"ML failures at exact-feasible data={tot['mlfail']}, "
          f"without mid-range triple repeat={tot['viol']}")
    for S, L, R, F in diffs:
        print("  DIFF S=", "".join(map(str, S)), "L=", L, "range=", R,
              "minimal feasible superset R'=", F)
    for S, L, R, D, x, tl in viols[:10]:
        print("  VIOLATION S=", "".join(map(str, S)), "L=", L, "range=", R,
              "D=", "".join(map(str, D)), "x=", x, "triplelens=", tl)
    return 1 if tot["viol"] else 0


if __name__ == "__main__":
    sys.exit(main())
