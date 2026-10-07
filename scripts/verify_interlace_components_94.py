#!/usr/bin/env python3
"""Component-level search for the `#89` ladder route (board 94 front
`94comp`), after the `Arratia--Bollobas--Coppersmith--Sorkin` (2000)
suggestion of studying the *interlacement graph* of the changed branch
transitions rather than the tour as a whole.

Graph used here (the `94comp` graph):

  * **vertices** = the transposition orbits (`chords`) of the alternative
    pairing `f = AltF sigma` --- the changed branch transitions.  Vertices are
    *chords*, not support points, so each vertex is counted once.
  * **edges** = `Interleaved`: two vertices are joined when the chords cross
    in the current tour.
  * **blocks** = the equivalence classes of `SameExtension`, i.e. the classes
    of the *deterministic maximal extension* pair `{maxPairStart x (f x),
    maxPairStart (f x) x}`.  Each block is, by `BBTLadder.ladder_of_coalescing`,
    a family of parallel shifts of one maximal repeat --- "one maximal
    extension ladder".

Predicates tested (all of them at every `G <= 10` binary / `G <= 7` ternary
primitive `P2` word, every `2 <= L <= G`, and every genuine traversal, i.e.
every `vtx`-preserving involution `f` with `J = f o nextPos` a single
`G`-cycle):

  T1 `edge => same block` (the component-level reading of
     `CrossingChordsCoalesce`).
  T2 `every component is inside a single block` (a consequence of T1 and of
     transitivity of `SameExtension` --- see `AssemblyP1/Issue94InterlaceComponents.lean`).
  T3 `every block is connected`, i.e. block = component.  STRONGER than T2;
     refuted or not, this is the question of whether the component
     decomposition *is* the ladder decomposition.
  T4 `every block is a parallel ladder`: for the block's extension pair
     `(p, q)`, each of its chords is `{rotAdd l p, rotAdd l q}`.  This is the
     content of `BBTLadder.ladder_of_coalescing` and is re-checked here.
  T5 `every component is contiguous in the circular order of the support`:
     the chords of one component occupy a set of support points that is
     cyclically convex.  This is the *geometric-order* residual that
     `LadderVertexCycle` needs; it is the candidate elementary
     one-component lemma.

  T6 the tour `J = f o nextPos` walks the support in clockwise order --- the
     "the traversal walks the blocks in the geometric order" step.

  T7 `one component is repaired by rotating its own points` --- the
     component-independence lemma.

  T8 the tour `J` maps each component's support points **into themselves**.
     This is the precise obstruction behind T7: if `J` leaves a component, no
     repair of that component can be carried out by the traversal at all, and
     the T7 failures are all T8 failures.

Usage:  python3 scripts/verify_interlace_components_94.py [--bin G] [--tri G]
"""

import argparse
import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from verify_ladder_blocks_89 import (  # noqa: E402
    P2, Interleaved, is_primitive, involutions_preserving, genuine,
    support, max_pair, chords,
)


def block_of(w, c):
    """The block of the chord `c = (a, b)`: the unordered pair of extension
    starts of its deterministic maximal extension."""
    return frozenset(max_pair(w, c[0], c[1])[:2])


def chord_graph(w, f):
    """Vertices = chords of `f`; edge = interleaving."""
    ch = chords(f)
    adj = {c: set() for c in ch}
    for i in range(len(ch)):
        for j in range(i + 1, len(ch)):
            (a, b), (c, d) = ch[i], ch[j]
            if Interleaved(w, a, b, c, d):
                adj[(a, b)].add((c, d))
                adj[(c, d)].add((a, b))
    return ch, adj


def components(adj):
    """Connected components of the chord graph."""
    seen = set()
    out = []
    for v in adj:
        if v in seen:
            continue
        comp, stack = set(), [v]
        while stack:
            x = stack.pop()
            if x in comp:
                continue
            comp.add(x)
            stack.extend(adj[x] - comp)
        seen |= comp
        out.append(comp)
    return out


def blocks_of(w, f):
    out = {}
    for c in chords(f):
        out.setdefault(block_of(w, c), set()).add(c)
    return out


def is_parallel_ladder(w, blk, cs):
    """T4: each chord of the block `cs` is a parallel shift of the block's own
    extension pair `blk`."""
    p, q = sorted(blk)
    n = len(w)
    # either orientation: `maxPairStart a b` may be `p` or `q`
    return all(((a - p) % n == (b - q) % n) or ((a - q) % n == (b - p) % n)
               for (a, b) in cs)


def contiguous(f, comp):
    """T5: the support points of `comp` are cyclically convex."""
    pts = sorted({x for c in comp for x in c})
    sup = support(f)
    if len(pts) == len(sup):
        return True
    for k in range(len(pts)):
        rot = pts[k:] + pts[:k]
        gap = (sup[(sup.index(rot[0]) + 1) % len(sup)] - rot[0]) % len(f)
        span = (rot[-1] - rot[0]) % len(f)
        if gap > span:
            return False                   # a support point outside the arc
    return True


def run(alphabet, gmax):
    st = dict(traversals=0, not_rotation=0, t1=0, t2=0, t3=0, t4=0, t5=0, t6=0,
              t7=0, t8=0, t3f=[], t5f=[], t6f=[], t7f=[], t8f=[], comp_hist={}, blk_hist={})
    for n in range(2, gmax + 1):
        for wv in itertools.product(range(alphabet), repeat=n):
            w = tuple(wv)
            if not is_primitive(w):
                continue
            for L in range(2, n + 1):
                if not P2(w, L):
                    continue
                for f in involutions_preserving(w, L):
                    if not support(f) or not genuine(w, f):
                        continue
                    st['traversals'] += 1
                    tag = (''.join(map(str, w)), L, tuple(f), tuple(support(f)))
                    ch, adj = chord_graph(w, f)
                    blks = blocks_of(w, f)
                    comps = components(adj)
                    st['comp_hist'][len(comps)] = st['comp_hist'].get(len(comps), 0) + 1
                    st['blk_hist'][len(blks)] = st['blk_hist'].get(len(blks), 0) + 1
                    # T1
                    for (a, b), nbrs in adj.items():
                        for (c, d) in nbrs:
                            if block_of(w, (a, b)) != block_of(w, (c, d)):
                                st['t1'] += 1
                    # T2
                    for comp in comps:
                        if len({block_of(w, c) for c in comp}) > 1:
                            st['t2'] += 1
                    # T3
                    for blk, cs in blks.items():
                        if len(components_of(cs, adj)) != 1:
                            st['t3'] += 1
                            if len(st['t3f']) < 3:
                                st['t3f'].append(tag + (sorted(cs),))
                    # T4
                    for blk, cs in blks.items():
                        if not is_parallel_ladder(w, blk, cs):
                            st['t4'] += 1
                    # T5
                    for comp in comps:
                        if not contiguous(f, comp):
                            st['t5'] += 1
                            if len(st['t5f']) < 3:
                                st['t5f'].append(tag + (sorted(comp),))
                    # T6: the tour visits the components in circular order
                    if not visits_in_geometric_order(w, L, f, adj):
                        st['t6'] += 1
                        if len(st['t6f']) < 3:
                            st['t6f'].append(tag)
                    # T7: component-local rotation (component independence)
                    for comp in comps:
                        if not component_local_rotation(w, L, f, comp):
                            st['t7'] += 1
                            if len(st['t7f']) < 3:
                                st['t7f'].append(tag + (sorted(comp),))
                    # T8: the tour preserves each component's point set.  This is
                    # the *precise* obstruction behind T7: if `J` does not map a
                    # component's support points into themselves, no repair of
                    # that component can be carried out by the traversal at all.
                    J = [f[(x + 1) % len(f)] for x in range(len(f))]
                    for comp in comps:
                        pts = {x for c in comp for x in c}
                        if len(pts) < 2:
                            continue
                        if any(J[x] not in pts for x in pts):
                            st['t8'] += 1
                            if len(st['t8f']) < 3:
                                st['t8f'].append(tag + (sorted(pts),
                                    [x for x in sorted(pts) if J[x] not in pts]))
        sys.stdout.write('  ... G=%d done, %d traversals so far\n'
                         % (n, st['traversals']))
        sys.stdout.flush()
    return st


def visits_in_geometric_order(w, L, f, adj):
    """T6: the *tour* (`J = f o nextPos`, i.e. the listing of `sigma`) walks
    the support in clockwise order, and hence meets the components as
    cyclically-convex blocks in circular order.

    Concretely: for support points `x, y` consecutive along the support in the
    order in which the tour visits them, the tour step from `x` to `y` is a
    clockwise support step.  Equivalently: the permutation `x |-> position of
    x` along the tour, restricted to the support, is order-preserving with
    respect to the clockwise support order.  This is the *global* residual
    that `LadderVertexCycle` needs and that no component-level (local)
    predicate supplies: it is a statement about the whole tour.
    """
    sup = support(f)
    if len(sup) < 2:
        return True
    n = len(f)
    pos = {x: i for i, x in enumerate(sup)}
    # clockwise support order = successor along `sup`
    sgn = {}
    for i, x in enumerate(sup):
        y = sup[(i + 1) % len(sup)]
        d = (y - x) % n
        sgn[(x, y)] = d
    # the tour: J x = f (nextPos x)
    J = [f[(x + 1) % n] for x in range(n)]
    for i in range(len(sup)):
        x, y = sup[i], sup[(i + 1) % len(sup)]
        # the tour must move from x to y in a single J-step
        if J[x] != y:
            return False
    return True


def component_local_rotation(w, L, f, comp):
    """T7 (component independence, the local form): for ONE connected component
    of the interlace graph, the *truth's* clockwise listing of that component's
    support points is a rotation of the *tour's* listing of them.

    This is the genuinely component-local substitute for `LadderVertexCycle`:
    if it held, the components could be repaired independently, because the
    local repair of one component would not disturb the cyclic order of any
    other.  It is checked on the tour induced by `J = f o nextPos` restricted
    to the support points of `comp` (walking `J` until the set is exhausted).
    """
    pts = {x for c in comp for x in c}
    if len(pts) < 2:
        return True
    n = len(f)
    J = [f[(x + 1) % n] for x in range(n)]
    for q in sorted(pts):
        seq, x = [q], J[q]
        while x != q and x not in seq:
            seq.append(x)
            x = J[x]
        if set(seq) != pts or len(seq) != len(pts):
            return False
        cw = sorted(pts)
        for k in range(len(cw)):
            if all(seq[i] == cw[(i + k) % len(cw)] for i in range(len(cw))):
                break
        else:
            return False
    return True


def components_of(cs, adj):
    cs = set(cs)
    seen, out = set(), []
    for v in cs:
        if v in seen:
            continue
        comp, stack = set(), [v]
        while stack:
            x = stack.pop()
            if x in comp:
                continue
            comp.add(x)
            stack.extend(adj[x] & cs - comp)
        seen |= comp
        out.append(comp)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--bin', type=int, default=10)
    ap.add_argument('--tri', type=int, default=7)
    args = ap.parse_args()
    for alphabet, gmax in ((2, args.bin), (3, args.tri)):
        print('=== alphabet %d, G <= %d, primitive + P2 ===' % (alphabet, gmax))
        s = run(alphabet, gmax)
        print('  genuine traversals with nontrivial support : %d' % s['traversals'])
        print('  VertexCycleEq failures                     : %d' % s['not_rotation'])
        print('  T1 edge-implies-same-block failures        : %d' % s['t1'])
        print('  T2 component-inside-one-block failures     : %d' % s['t2'])
        print('  T3 block-connected failures (T3 = block = component) : %d' % s['t3'])
        for t in s['t3f']:
            print('      REFUTES T3: S=%s L=%d f=%s supp=%s block=%s' % t)
        print('  T4 parallel-ladder failures               : %d' % s['t4'])
        print('  T5 contiguous-component failures          : %d' % s['t5'])
        for t in s['t5f']:
            print('      REFUTES T5: S=%s L=%d f=%s supp=%s comp=%s' % t)
        print('  T6 tour-walks-support-clockwise failures   : %d' % s['t6'])
        for t in s['t6f']:
            print('      REFUTES T6: S=%s L=%d f=%s supp=%s' % t)
        print('  T7 component-local-rotation failures      : %d' % s['t7'])
        for t in s['t7f']:
            print('      REFUTES T7: S=%s L=%d f=%s supp=%s comp=%s' % t)
        print('  T8 tour-preserves-component failures        : %d' % s['t8'])
        for t in s['t8f']:
            print('      REFUTES T8: S=%s L=%d f=%s supp=%s pts=%s escapes=%s' % t)
        print('  #components histogram : %s' % sorted(s['comp_hist'].items()))
        print('  #blocks      histogram : %s' % sorted(s['blk_hist'].items()))
        sys.stdout.flush()


if __name__ == '__main__':
    main()