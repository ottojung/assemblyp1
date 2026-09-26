#!/usr/bin/env python3
"""#88 audit search under **exact-range** `I_s` semantics.

Transcribes the Lean definitions literally:

* `SourceFaithfulIs.Genome.cycl / window / Agree / Preceding / Following`,
  `Genome.IsRepeat`, `Genome.IsTripleRepeat`, `Interleaved`, `InOpenArc`,
  `FourDistinct`, `ReadCovers`, `Covers`, `BridgesCopy`, `IsTripleRepeatAllBridged`,
  `IsInterleavedPairBridged`, `InformationFeasible`;
* `OrientedSameLengthML.observedOf` (read-type counts of a realization),
  `OrientedRigidity.support / specCount`, `OrientedSameLengthML.exactLik`;
* `RepeatAdapter.TripleAgree / IsMaximalTriple`,
  `MLEscape.HasMidRangeTripleRepeat` / `HasLongTripleRepeat` / `HasWraparoundTripleRepeat`.

Exact-range semantics: the certificate set is **the realized start range**
`R = {ρ i}`, not a possibly larger `R ⊇ range ρ`.  Every bridging witness in
`I_s` is therefore a read that was actually drawn, and so contributes to the
observation `x` used by the likelihood.

The likelihood comparison is exact integer arithmetic: with `x` supported on
the common support and `n = totalReads x`,

    exactLik(D, x) = ( prod_w d_D w ^ (x w) ) / G ^ n,

so comparing two candidates with the same observation is comparing the integer
numerators (`G ^ n` is common and positive).  No floating point is used.

Usage: exact_range_search.py [G] [alphabet] [nmax] [Lmin] [Lmax]
"""
import sys
from itertools import product, combinations
from math import comb


# ---------------------------------------------------------------- genome layer
def cycl(S, i, G):
    return S[i % G]


def window(S, e, r, G):
    return tuple(cycl(S, r + d, G) for d in range(e))


def agree(S, e, r, t, G):
    return all(cycl(S, r + d, G) == cycl(S, t + d, G) for d in range(e))


def preceding(S, t, G):
    return cycl(S, t + G - 1, G)


def following(S, e, t, G):
    return cycl(S, t + e, G)


def is_repeat(S, e, a, b, G):
    return (1 <= e < G and a != b and agree(S, e, a, b, G)
            and preceding(S, a, G) != preceding(S, b, G)
            and following(S, e, a, G) != following(S, e, b, G))


def is_triple_repeat(S, e, a, b, c, G):
    return (1 <= e < G and a != b and a != c and b != c
            and agree(S, e, a, b, G) and agree(S, e, a, c, G)
            and agree(S, e, b, c, G)
            and not (preceding(S, a, G) == preceding(S, b, G)
                     and preceding(S, b, G) == preceding(S, c, G))
            and not (following(S, e, a, G) == following(S, e, b, G)
                     and following(S, e, b, G) == following(S, e, c, G)))


def in_open_arc(S, a, b, p, G):
    da = (p + G - a) % G
    db = (b + G - a) % G
    return 0 < da < db


def four_distinct(a, b, c, d):
    return len({a, b, c, d}) == 4


def interleaved(S, a, b, c, d, G):
    # Lean: `InOpenArc S a b c ↔ ¬ InOpenArc S a b d`, i.e. exactly one of
    # `c, d` lies in the open clockwise arc from `a` to `b`.
    return four_distinct(a, b, c, d) and (
        in_open_arc(S, a, b, c, G) != in_open_arc(S, a, b, d, G))


# ---------------------------------------------------------------- bridging / I_s
def read_covers(L, r, p, G):
    return any(p == (r + d) % G for d in range(L))


def covers(L, R, G):
    return all(any(read_covers(L, r, p, G) for r in R) for p in range(G))


def bridges_copy(L, R, e, t, G):
    return any(read_covers(L, r, (t + G - 1) % G, G)
               and read_covers(L, r, (t + e) % G, G) for r in R)


def information_feasible(S, L, R, G):
    """`InformationFeasible ⟨G, _, S⟩ L R` for R a subset of range(G)."""
    if not covers(L, R, G):
        return False
    for e in range(1, G):
        for a, b, c in product(range(G), repeat=3):
            if is_triple_repeat(S, e, a, b, c, G):
                if not all(bridges_copy(L, R, e, t, G) for t in (a, b, c)):
                    return False
        for e1, e2 in product(range(1, G), repeat=2):
            for a, b, c, d in product(range(G), repeat=4):
                if (is_repeat(S, e1, a, b, G) and is_repeat(S, e2, c, d, G)
                        and interleaved(S, a, b, c, d, G)):
                    if not (bridges_copy(L, R, e1, a, G)
                            or bridges_copy(L, R, e1, b, G)
                            or bridges_copy(L, R, e2, c, G)
                            or bridges_copy(L, R, e2, d, G)):
                        return False
    return True


def feasible_supersets(S, L, G):
    """All R with I_s, by monotonicity it suffices to know whether the
    maximal one (all starts) works; return the full list anyway."""
    return [frozenset(R) for r in range(G)
            for R in combinations(range(G), r)
            if information_feasible(S, L, R, G)]


# ---------------------------------------------------------------- spectrum layer
def spec(S, e, G):
    cnt = {}
    for r in range(G):
        w = window(S, e, r, G)
        cnt[w] = cnt.get(w, 0) + 1
    return cnt


def observed_of(S, e, starts, G):
    """`observedOf hG S ρ` as a read-type count map."""
    x = {}
    for r in starts:
        w = window(S, e, r, G)
        x[w] = x.get(w, 0) + 1
    return x


def score(cnt, x, G):
    """prod_w cnt(w) ^ x(w) : the integer numerator of exactLik."""
    s = 1
    for w, k in x.items():
        s *= pow(cnt.get(w, 0), k)
    return s


# ---------------------------------------------------------------- repeats (bands)
def triple_agree(S, a, b, c, l, G):
    return all(cycl(S, a + d, G) == cycl(S, b + d, G) == cycl(S, c + d, G)
               for d in range(l))


def is_maximal_triple(S, a, b, c, l, G):
    if not triple_agree(S, a, b, c, l, G):
        return False
    if (preceding(S, a, G) == preceding(S, b, G)
            and preceding(S, b, G) == preceding(S, c, G)):
        return False
    if (following(S, l, a, G) == following(S, l, b, G)
            and following(S, l, b, G) == following(S, l, c, G)):
        return False
    return True


def maximal_triple_lengths(S, G):
    out = set()
    for a, b, c, l in product(range(G), range(G), range(G), range(0, G)):
        if len({a % G, b % G, c % G}) < 3:
            continue
        if is_maximal_triple(S, a, b, c, l, G):
            out.add(l)
    return out


def has_band(S, lo, hi, G):
    """maximal triple repeat with length in [lo, hi) (hi may be empty)."""
    for a, b, c, l in product(range(G), range(G), range(G), range(lo, hi)):
        if len({a % G, b % G, c % G}) < 3:
            continue
        if is_maximal_triple(S, a, b, c, l, G):
            return True
    return False


# ---------------------------------------------------------------- search
def start_count_vectors(G, n):
    """count vectors on starts with total n, as tuples (index -> count)."""
    if G == 0:
        if n == 0:
            yield ()
        return
    for first in range(n + 1):
        for rest in start_count_vectors(G - 1, n - first):
            yield (first,) + rest


def main():
    G = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    k = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    nmax = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    Lmin = int(sys.argv[4]) if len(sys.argv) > 4 else 2
    Lmax = int(sys.argv[5]) if len(sys.argv) > 5 else G
    words = [w for w in product(range(k), repeat=G)]
    cands = {w: spec(w, 0, 0) for w in []}  # placeholder
    stats = dict(S=0, feas_exact=0, feas_super=0, mlfail=0, viol=0,
                 diff=0)
    viols, diffs = [], []
    for S in words:
        tl = maximal_triple_lengths(S, G)
        feas = feasible_supersets(S, Lmin, G)  # placeholder, recomputed per L
        for L in range(Lmin, Lmax + 1):
            feas = feasible_supersets(S, L, G)
            allst = frozenset(range(G))
            feasible_all = allst in feas
            dS = spec(S, L, G)
            supS = frozenset(dS)
            if not dS:
                continue
            # candidates: same window support, any circular word of length G
            cands = [D for D in words if frozenset(spec(D, L, G)) == supS]
            for n in range(1, nmax + 1):
                for v in start_count_vectors(G, n):
                    R = frozenset(i for i in range(G) if v[i] > 0)
                    starts = [i for i in range(G) for _ in range(v[i])]
                    x = observed_of(S, L, starts, G)
                    stats["S"] += 1
                    # --- exact-range semantics
                    exact = R in feas
                    # --- subset-only semantics: some R' ⊇ R feasible
                    superset_ok = any(R <= F for F in feas)
                    if exact:
                        stats["feas_exact"] += 1
                    if superset_ok:
                        stats["feas_super"] += 1
                    if superset_ok and not exact:
                        stats["diff"] += 1
                        if len(diffs) < 6:
                            diffs.append((S, L, tuple(sorted(R)),
                                          [tuple(sorted(F)) for F in feas
                                           if R <= F][:2]))
                    if not exact:
                        continue
                    sS = score(dS, x, G)
                    beaten = [D for D in cands if score(spec(D, L, G), x, G) > sS]
                    if beaten:
                        stats["mlfail"] += 1
                        if not has_band(S, L - 1, G - L, G):
                            stats["viol"] += 1
                            viols.append((S, L, tuple(sorted(R)),
                                          beaten[0], x, sorted(tl)))
    print(f"G={G} k={k} L in [{Lmin},{Lmax}] nmax={nmax}: "
          f"realizations checked={stats['S']}, "
          f"exact-range I_s feasible={stats['feas_exact']}, "
          f"subset-only I_s feasible={stats['feas_super']}, "
          f"realizations feasible subset-only but NOT exact={stats['diff']}, "
          f"ML failures at exact-range-feasible data={stats['mlfail']}, "
          f"of those without a mid-range triple repeat={stats['viol']}")
    for S, L, R, F in diffs:
        print("  DIFF S=", "".join(map(str, S)), "L=", L, "range=", R,
              "but feasible for R'=", F)
    for S, L, R, D, x, tl in viols[:10]:
        print("  VIOLATION S=", "".join(map(str, S)), "L=", L, "range=", R,
              "D=", "".join(map(str, D)), "x=", x, "triplelens=", tl)
    return 1 if stats["viol"] else 0


if __name__ == "__main__":
    sys.exit(main())
