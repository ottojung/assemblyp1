#!/usr/bin/env python3
"""#88 audit search under **exact-range** `I_s` semantics (fast version).

Same exact transcriptions as `issue88-exact-range-search.py`; the only
difference is that `I_s` is evaluated as a hitting-set condition: for each
triple repeat (resp. interleaved pair) the acceptable options are the
`BridgesCopy` sets of its three (resp. four) selected copies, so feasibility of
a candidate `R` is decided by intersecting precomputed option sets instead of
re-running the full clause scan for every subset.  This is an optimisation
only: the option sets are exactly `BridgesCopy S L R e t` as defined in
`SourceFaithfulIs`, evaluated at `R = all starts` (a set is a superset of
itself, and `ReadCovers` does not mention `R`).
"""
import sys
from itertools import product
from importlib.machinery import SourceFileLoader

_m = SourceFileLoader("er", "scripts/issue88-exact-range-search.py").load_module()


def i_s_options(S, L, G):
    """Requirements of `InformationFeasible ⟨G,_,S⟩ L R` as option lists."""
    opts = []
    for e in range(1, G):
        for a, b, c in product(range(G), repeat=3):
            if _m.is_triple_repeat(S, e, a, b, c, G):
                opts.append([frozenset(r for r in range(G)
                                       if _m.bridges_copy(L, range(G), e, t, G))
                             for t in (a, b, c)])
        for e1, e2 in product(range(1, G), repeat=2):
            for a, b, c, d in product(range(G), repeat=4):
                if (_m.is_repeat(S, e1, a, b, G) and _m.is_repeat(S, e2, c, d, G)
                        and _m.interleaved(S, a, b, c, d, G)):
                    opts.append([frozenset(r for r in range(G)
                                           if _m.bridges_copy(L, range(G), e, t, G))
                                 for e, t in ((e1, a), (e1, b), (e2, c), (e2, d))])
    return opts


def feasible(R, L, G, opts):
    if not _m.covers(L, R, G):
        return False
    for options in opts:
        if not any(R & o for o in options):
            return False
    return True


def main():
    G = int(sys.argv[1]); k = int(sys.argv[2]); nmax = int(sys.argv[3])
    Lmin = int(sys.argv[4]); Lmax = int(sys.argv[5])
    words = list(product(range(k), repeat=G))
    tot = ex = sup = mlf = viol = diff = 0
    viols, diffs = [], []
    for S in words:
        tl = _m.maximal_triple_lengths(S, G)
        for L in range(Lmin, Lmax + 1):
            opts = i_s_options(S, L, G)
            dS = _m.spec(S, L, G)
            if not dS:
                continue
            supS = frozenset(dS)
            cands = [D for D in words if frozenset(_m.spec(D, L, G)) == supS]
            feas = [frozenset(R) for r in range(G)
                    for R in product(range(G), repeat=r)
                    if feasible(frozenset(R), L, G, opts)]
            feasset = set(feas)
            for n in range(1, nmax + 1):
                for v in _m.start_count_vectors(G, n):
                    R = frozenset(i for i in range(G) if v[i] > 0)
                    tot += 1
                    exact = R in feasset
                    superset_ok = any(R <= F for F in feas)
                    ex += exact
                    sup += superset_ok
                    if superset_ok and not exact:
                        diff += 1
                        if len(diffs) < 4:
                            diffs.append((S, L, tuple(sorted(R)),
                                          min((tuple(sorted(F)) for F in feas
                                               if R <= F), key=len)))
                    if not exact:
                        continue
                    starts = [i for i in range(G) for _ in range(v[i])]
                    x = _m.observed_of(S, L, starts, G)
                    sS = _m.score(dS, x, G)
                    beaten = [D for D in cands if _m.score(_m.spec(D, L, G), x, G) > sS]
                    if beaten:
                        mlf += 1
                        if not _m.has_band(S, L - 1, G - L, G):
                            viol += 1
                            viols.append((S, L, tuple(sorted(R)), beaten[0],
                                          x, sorted(tl)))
    print(f"G={G} k={k} L in [{Lmin},{Lmax}] nmax={nmax}: realizations={tot}, "
          f"exact-range feasible={ex}, subset-only feasible={sup}, "
          f"subset-only but not exact={diff}, "
          f"ML failures at exact-feasible data={mlf}, "
          f"without mid-range triple repeat={viol}")
    for S, L, R, F in diffs:
        print("  DIFF S=", "".join(map(str, S)), "L=", L, "range=", R,
              "minimal feasible superset R'=", F)
    for S, L, R, D, x, tl in viols[:10]:
        print("  VIOLATION S=", "".join(map(str, S)), "L=", L, "range=", R,
              "D=", "".join(map(str, D)), "x=", x, "triplelens=", tl)
    return 1 if viol else 0


if __name__ == "__main__":
    sys.exit(main())
