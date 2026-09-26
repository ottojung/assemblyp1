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
  `MLEscape.HasMidRangeTripleRepeat` / `HasLongTripleRepeat`.

Exact-range semantics: the certificate set is **the realized start range**
`R = {ρ i}`, not a possibly larger `R ⊇ range ρ`.  Every bridging witness in
`I_s` is therefore a read that was actually drawn, and so contributes to the
observation `x` used by the likelihood.

The likelihood comparison is exact integer arithmetic: with `x` supported on
the common support and `n = totalReads x`,

    exactLik(D, x) = ( prod_w d_D w ^ (x w) ) / G ^ n,

so comparing two candidates with the same observation is comparing the integer
numerators (`G ^ n` is common and positive).  No floating point is used.

## Bridging, and the endpoint-only reading

`bridges_copy` below is the **canonical** `SourceFaithfulIs.BridgesCopy`: the
source's single-lift *span* condition, one realized read, one offset `d`, the
copy at offset `d + 1`, with `d + e + 1 < L`.  It is a strict-extension clause
and forces `e + 2 <= L`.

`bridges_copy_endpoint_only` is the **weaker endpoint-only** reading that
`SourceFaithfulIs.BridgesCopy` carried before the migration: some read covers
`(t - 1) % G` and covers `(t + e) % G`.  It is *not* the source's condition --
a read can reach a long copy's two endpoints by travelling the complementary
circular arc without containing the copy -- and it is kept here only so that
`docs/bridging-lift-audit.md` can quote the endpoint-only numbers of the
original audit alongside the canonical ones.  Select it with `--endpoint-only`;
`issue88-exact-range-fast.py` implements both readings and cross-checks them.

Usage: exact_range_search.py [G] [alphabet] [nmax] [Lmin] [Lmax] [--endpoint-only]
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
    # Lean: `InOpenArc S a b c <-> not InOpenArc S a b d`, i.e. exactly one of
    # `c, d` lies in the open clockwise arc from `a` to `b`.
    return four_distinct(a, b, c, d) and (
        in_open_arc(S, a, b, c, G) != in_open_arc(S, a, b, d, G))


# ---------------------------------------------------------------- bridging / I_s
def read_covers(L, r, p, G):
    return any(p == (r + d) % G for d in range(L))


def covers(L, R, G):
    return all(any(read_covers(L, r, p, G) for r in R) for p in range(G))


def bridges_copy(L, R, e, t, G):
    """Canonical `SourceFaithfulIs.BridgesCopy`: the single-lift span condition.

    One realized read `r`, one offset `d < L`, the copy's start at offset
    `d + 1` of that read, and the copy's successor still inside the read, i.e.
    `d + e + 1 < L`.  Equivalently `r < t'` and `t' + e < r + L` for a suitable
    lift `t'`, which is the source's interval formulation.
    """
    return any((r + d + 1) % G == t and d + e + 1 < L for r in R for d in range(L))


def bridges_copy_endpoint_only(L, R, e, t, G):
    """The pre-migration endpoint-only reading.  **Not** the source's condition.

    Kept only to reproduce the endpoint-only figures quoted in
    `docs/bridging-lift-audit.md`; `--endpoint-only` selects it.
    """
    return any(read_covers(L, r, (t + G - 1) % G, G)
               and read_covers(L, r, (t + e) % G, G) for r in R)


def information_feasible(S, L, R, G, bridge=bridges_copy):
    """`InformationFeasible <G, _, S> L R` for R a subset of range(G)."""
    if not covers(L, R, G):
        return False
    for e in range(1, G):
        for a, b, c in product(range(G), repeat=3):
            if is_triple_repeat(S, e, a, b, c, G):
                if not all(bridge(L, R, e, t, G) for t in (a, b, c)):
                    return False
        for e1, e2 in product(range(1, G), repeat=2):
            for a, b, c, d in product(range(G), repeat=4):
                if (is_repeat(S, e1, a, b, G) and is_repeat(S, e2, c, d, G)
                        and interleaved(S, a, b, c, d, G)):
                    if not (bridge(L, R, e1, a, G)
                            or bridge(L, R, e1, b, G)
                            or bridge(L, R, e2, c, G)
                            or bridge(L, R, e2, d, G)):
                        return False
    return True


def feasible_supersets(S, L, G, bridge=bridges_copy):
    """All R with I_s, by monotonicity it suffices to know whether the
    maximal one (all starts) works; return the full list anyway."""
    return [frozenset(R) for r in range(G)
            for R in combinations(range(G), r)
            if information_feasible(S, L, R, G, bridge)]


# ---------------------------------------------------------------- spectrum layer
def spec(S, e, G):
    cnt = {}
    for r in range(G):
        w = window(S, e, r, G)
        cnt[w] = cnt.get(w, 0) + 1
    return cnt


def observed_of(S, e, starts, G):
    """`observedOf hG S rho` as a read-type count map."""
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
    argv = [a for a in sys.argv[1:] if not a.startswith("--")]
    endpoint_only = "--endpoint-only" in sys.argv[1:]
    bridge = bridges_copy_endpoint_only if endpoint_only else bridges_copy
    G = int(argv[0]) if len(argv) > 0 else 6
    k = int(argv[1]) if len(argv) > 1 else 2
    nmax = int(argv[2]) if len(argv) > 2 else 3
    Lmin = int(argv[3]) if len(argv) > 3 else 2
    Lmax = int(argv[4]) if len(argv) > 4 else G
    words = [w for w in product(range(k), repeat=G)]
    stats = dict(S=0, feas_exact=0, feas_super=0, mlfail=0, viol=0,
                 diff=0)
    viols, diffs = [], []
    for S in words:
        tl = maximal_triple_lengths(S, G)
        for L in range(Lmin, Lmax + 1):
            feas = feasible_supersets(S, L, G, bridge)
            dS = spec(S, L, G)
            if not dS:
                continue
            supS = frozenset(dS)
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
                    # --- subset-only semantics: some R' >= R feasible
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
    tag = "endpoint-only" if endpoint_only else "canonical"
    print(f"[{tag}] G={G} k={k} L in [{Lmin},{Lmax}] nmax={nmax}: "
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
