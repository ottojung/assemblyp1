#!/usr/bin/env python3
"""Exhaustive search for the `#89` ladder / support-block structure.

This is the search behind `docs/bbt-ladder-blocks-89.md`.  It is **evidence,
not a proof**: the completeness of the search is not itself established in the
kernel.  What it does establish is a *refutation* of two candidate lemmas that
were being considered, which is a finite certificate:

  * `nextSupport (f x) = f (nextSupport x)` for `x ∈ Support f`  -- REFUTED
    at `G = 10` (`S = 0010010101`, `L = 5`);
  * "`Support f` is the disjoint union of the full ladders of the maximal
    repeats of length `>= L-1`"  -- REFUTED, because a traversal need not
    swap at *every* branch vertex.

Setup, per word `S` of length `G`, per read length `2 <= L <= G`:

  * `K = L - 1`;  `vtx(x)` = the `K`-mer at start `x`;
  * `f` ranges over the **involutions** of `Fin G` that preserve `vtx` --
    these are exactly the `AltF` of a genuine alternative traversal, once
    `P2` + primitivity have made `f` an involution (`BBTLadder.AltF_sq`);
  * a candidate is a *genuine traversal* when `J = f o nextPos` is a single
    `G`-cycle, which is `BBTEulerian.EulerianCycle`'s `single` clause read in
    the `J = f o rho` representation;
  * `VertexCycleEq` is checked by reconstructing the listing `sigma`
    (`sigma (i+1) = J (sigma i)`) and asking whether
    `vtx (sigma i) = vtx ((i + k) % G)` for some `k`.

Everything is filtered by the *source-faithful* `P2` of
`AssemblyP1/P2.lean` (a direct transcription of `SourceFaithfulIs`'s
`IsRepeat` / `IsTripleRepeat` / `Interleaved` / `P2`) and by primitivity.

Usage:  python3 scripts/verify_ladder_blocks_89.py [--bin G] [--tri G]
"""

import argparse
import itertools
import sys

# ---------------------------------------------------------------- the source
# Transcription of AssemblyP1/SourceFaithfulIs.lean (lines 95-129, 355-366)
# and of def:P2 in AssemblyP1/P2.lean.


def cyc(w, t):
    return w[t % len(w)]


def window(w, e, r, d):
    return cyc(w, r + d)


def Agree(w, e, r, t):
    return all(window(w, e, r, d) == window(w, e, t, d) for d in range(e))


def Preceding(w, t):
    return cyc(w, t - 1)


def Following(w, e, t):
    return cyc(w, t + e)


def IsRepeat(w, e, a, b):
    return (1 <= e < len(w) and a != b and Agree(w, e, a, b)
            and Preceding(w, a) != Preceding(w, b)
            and Following(w, e, a) != Following(w, e, b))


def IsTripleRepeat(w, e, a, b, c):
    return (1 <= e < len(w) and len({a, b, c}) == 3
            and Agree(w, e, a, b) and Agree(w, e, a, c) and Agree(w, e, b, c)
            and not (Preceding(w, a) == Preceding(w, b) == Preceding(w, c))
            and not (Following(w, e, a) == Following(w, e, b) == Following(w, e, c)))


def InOpenArc(w, a, b, p):
    n = len(w)
    return 0 < (p + n - a) % n < (b + n - a) % n


def Interleaved(w, a, b, c, d):
    if len({a, b, c, d}) != 4:
        return False
    return InOpenArc(w, a, b, c) != InOpenArc(w, a, b, d)


def P2(w, L):
    """def:P2 at read length `L`: no maximal triple repeat of length >= L-1,
    and no interleaved maximal repeat pair with both lengths >= L-2."""
    n = len(w)
    for e in range(1, n):
        for a in range(n):
            for b in range(n):
                for c in range(n):
                    if IsTripleRepeat(w, e, a, b, c) and not e < L - 1:
                        return False
    R = [(e, a, b) for e in range(1, n) for a in range(n) for b in range(n)
         if IsRepeat(w, e, a, b)]
    for (e1, a1, b1) in R:
        for (e2, c1, d1) in R:
            if Interleaved(w, a1, b1, c1, d1) and not (e1 <= L - 2 or e2 <= L - 2):
                return False
    return True


# ------------------------------------------------------------------ the graph


def vtx(w, x, L):
    n = len(w)
    K = L - 1
    return tuple(w[(x + i) % n] for i in range(K))


def is_primitive(w):
    n = len(w)
    return all(w != w[s:] + w[:s] for s in range(1, n))


def fibres(w, L):
    out = {}
    for x in range(len(w)):
        out.setdefault(vtx(w, x, L), []).append(x)
    return out


def involutions_preserving(w, L):
    """Every involution of `Fin G` preserving `vtx`.  Under `P2` + primitivity
    these are exactly the `AltF` of genuine traversals (`BBTLadder.AltF_sq`),
    so the search is complete for the class of objects the library talks
    about."""
    n = len(w)
    fib = fibres(w, L)
    if any(len(v) > 2 for v in fib.values()):
        return []                      # P2 + primitivity rules this out
    pairs = [tuple(v) for v in fib.values() if len(v) == 2]
    out = []
    for mask in range(1 << len(pairs)):
        f = list(range(n))
        for i, (a, b) in enumerate(pairs):
            if mask >> i & 1:
                f[a], f[b] = b, a
        out.append(f)
    return out


def is_G_cycle(J):
    n = len(J)
    seen = set()
    x = 0
    while x not in seen:
        seen.add(x)
        x = J[x]
    return x == 0 and len(seen) == n


def genuine(w, f):
    """`EulerianCycle`'s `single` clause, in the `J = f o rho` representation:
    `J` must be a single `G`-cycle."""
    n = len(w)
    return is_G_cycle([f[(x + 1) % n] for x in range(n)])


def listing(w, f):
    """The presentation `sigma` with `sigma (i+1) = J (sigma i)`."""
    n = len(w)
    for q in range(n):
        seq = [q]
        x = q
        for _ in range(n - 1):
            x = f[(x + 1) % n]
            if x in seq:
                break
            seq.append(x)
        if len(seq) == n:
            return seq
    return None


def vertex_cycle_is_rotation(w, L, f):
    """`BBTEulerian.VertexCycleEq f (refl)`."""
    n = len(w)
    seq = listing(w, f)
    if seq is None:
        return False
    return any(all(vtx(w, seq[i], L) == vtx(w, (i + k) % n, L)
                   for i in range(n)) for k in range(n))


# ------------------------------------------------------- the support geometry


def support(f):
    return [x for x in range(len(f)) if f[x] != x]


def nxt(sup, x):
    return sup[(sup.index(x) + 1) % len(sup)]


def commutation_holds(f):
    """`nextSupport (f x) = f (nextSupport x)` for every support point."""
    sup = support(f)
    return all(nxt(sup, f[x]) == f[nxt(sup, x)] for x in sup)


def agree_len(w, a, b):
    n = len(w)
    k = 0
    while k < n and w[(a + k) % n] == w[(b + k) % n]:
        k += 1
    return k


def max_pair(w, a, b):
    """The deterministic maximal extension of the pair `(a, b)`, as
    `(start_a, start_b, length)`, matching `maxPairStart` and `maxPairLen`:

      * the two starts are the agreeing starts shifted back by the maximal
        backward agreement `pairBack` (`maxPairStart`);
      * the length is the forward agreement of the *shifted* pair, i.e. the
        agreement measured from offset `pairBack` (`maxPairLen`), so the
        maximal repeat is the window
        `[start_a, start_a + length)`.  Equivalently: `pairBack` backward
        agreements plus the forward agreements measured from offset `0`, which
        is what the loop below computes.

    Only the first two components are used by the predicates below; they are
    compared as an unordered pair, because `maxPairStart a b` and
    `maxPairStart b a` are the two swapped starts of one repeat.
    """
    n = len(w)
    back = 0
    while back < n and w[(a - 1 - back) % n] == w[(b - 1 - back) % n]:
        back += 1
    fwd = 0
    while fwd < n - back and w[(a + fwd) % n] == w[(b + fwd) % n]:
        fwd += 1
    return ((a - back) % n, (b - back) % n, back + fwd)


def single_ladder(w, f):
    """Every transposition orbit of `f` carries the *same* deterministic
    maximal extension (compared as an unordered pair of starts)."""
    sup = support(f)
    return len({frozenset(max_pair(w, x, f[x])[:2]) for x in sup}) == 1


def chords(f):
    """The transposition orbits of `f`, each once, as an unordered pair."""
    out = []
    for x in support(f):
        c = (min(x, f[x]), max(x, f[x]))
        if c not in out:
            out.append(c)
    return out


def crossing_chords_coalesce(w, f):
    """`CrossingChordsCoalesce`: two *crossing* support chords carry the same
    deterministic maximal extension.  Note the direction -- coalescence is
    forced by crossing, not assumed."""
    ch = chords(f)
    for i in range(len(ch)):
        for j in range(i + 1, len(ch)):
            (a, b), (c, d) = ch[i], ch[j]
            if Interleaved(w, a, b, c, d):
                if frozenset(max_pair(w, a, b)[:2]) != frozenset(max_pair(w, c, d)[:2]):
                    return False
    return True


def is_max_repeat(w, e, a, b):
    n = len(w)
    if not (1 <= e < n) or a == b:
        return False
    if agree_len(w, a, b) < e:
        return False
    if w[(a - 1) % n] == w[(b - 1) % n]:
        return False
    if w[(a + e) % n] == w[(b + e) % n]:
        return False
    return True


def full_ladder_union(w, L):
    """The union, over all maximal repeats of length `>= L-1`, of the full
    ladders `{p+i, q+i : 0 <= i <= e-(L-1)}`."""
    n = len(w)
    K = L - 1
    U = set()
    for e in range(K, n):
        for a in range(n):
            for b in range(a + 1, n):
                if is_max_repeat(w, e, a, b):
                    for i in range(e - K + 1):
                        U.add((a + i) % n)
                        U.add((b + i) % n)
    return U


# ------------------------------------------------------------------ the search


def run(alphabet, gmax):
    stats = dict(traversals=0, not_rotation=0, commutation_failures=[],
                 single_ladder=0, single_ladder_failures=[],
                 full_ladder_union_failures=[], coalesce_failures=[])
    for n in range(2, gmax + 1):
        for wv in itertools.product(range(alphabet), repeat=n):
            w = tuple(wv)
            if not is_primitive(w):
                continue
            for L in range(2, n + 1):
                if not P2(w, L):
                    continue
                U = full_ladder_union(w, L)
                for f in involutions_preserving(w, L):
                    if not support(f) or not genuine(w, f):
                        continue
                    stats['traversals'] += 1
                    tag = (''.join(map(str, w)), L, tuple(f), tuple(support(f)))
                    if not vertex_cycle_is_rotation(w, L, f):
                        stats['not_rotation'] += 1
                    if not commutation_holds(f):
                        stats['commutation_failures'].append(tag)
                    if not crossing_chords_coalesce(w, f):
                        stats['coalesce_failures'].append(tag)
                    if single_ladder(w, f):
                        stats['single_ladder'] += 1
                    else:
                        stats['single_ladder_failures'].append(tag)
                    if set(support(f)) != U:
                        stats['full_ladder_union_failures'].append(tag)
        sys.stdout.write('  ... G=%d done, %d traversals so far\n'
                         % (n, stats['traversals']))
        sys.stdout.flush()
    return stats


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--bin', type=int, default=10)
    ap.add_argument('--tri', type=int, default=7)
    args = ap.parse_args()
    for alphabet, gmax in ((2, args.bin), (3, args.tri)):
        print('=== alphabet %d, G <= %d, primitive + P2 ===' % (alphabet, gmax))
        s = run(alphabet, gmax)
        print('  genuine traversals with nontrivial support : %d' % s['traversals'])
        print('  VertexCycleEq failures                     : %d'
              % s['not_rotation'])
        print('  support-commutation failures               : %d'
              % len(s['commutation_failures']))
        for t in s['commutation_failures'][:3]:
            print('      REFUTES commutation: S=%s L=%d f=%s supp=%s' % t)
        print('  CrossingChordsCoalesce failures              : %d'
              % len(s['coalesce_failures']))
        for t in s['coalesce_failures'][:3]:
            print('      REFUTES CrossingChordsCoalesce: S=%s L=%d f=%s supp=%s' % t)
        print('  single-ladder (all orbits share one maxPair): %d'
              % s['single_ladder'])
        print('  single-ladder failures                     : %d'
              % len(s['single_ladder_failures']))
        for t in s['single_ladder_failures'][:3]:
            print('      REFUTES single-ladder: S=%s L=%d f=%s supp=%s' % t)
        print('  full-ladder-union failures                 : %d'
              % len(s['full_ladder_union_failures']))
        for t in s['full_ladder_union_failures'][:3]:
            print('      REFUTES full-ladder-union: S=%s L=%d f=%s supp=%s' % t)
        sys.stdout.flush()


if __name__ == '__main__':
    main()
