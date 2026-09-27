#!/usr/bin/env python3
"""Exhaustive verification of the #89 rematch/ladder layer.

Checks, over all primitive circular words of length G, all read lengths
L, and every window-preserving *involution* f of the starts whose
`f o nextPos` is a G-cycle (i.e. every genuine alternative traversal of the
(L-1)-mer multigraph, in the sense of AssemblyP1.BBTEulerian):

  1. `AltF_sq`: f is an involution whose two-element orbits are doubled
     (L-1)-mer pairs (P2 bounds the fibre of a vertex by 2).
  2. `isRepeat_len_unique` / `ladder_len`: if two orbits of f collapse onto
     one maximal repeat, their maximal-extension lengths agree.
  3. `ladder_of_coalescing`: two orbits with the same maximal extension are
     two distinct rotations of the same pair, and the chords are parallel
     (equal length, equal spacing).
  4. `ladder_arc_eq`: inside one maximal repeat the two shifted copies spell
     the same vertices.
  5. THE AUDITED CLAIM (`LadderRotationGap`): a genuine Eulerian cycle whose
     support chords coalesce still has the vertex cycle of a rotation of the
     truth.  Reported as a count of violations, which is 0.

Also reports the structural census: how many genuine traversals have crossing
support chords, and how many maximal repeats the support lives in (the
"one ladder" / "two ladders" split).

This is evidence, not a proof: the completeness of the search is not itself
proved.  Usage:  python3 scripts/verify_ladder_rematch_89.py [maxG] [maxAlphabet]
"""

import itertools
import sys
from collections import Counter, defaultdict

# ---------------------------------------------------------------- the word layer


def mers(S, K):
    G = len(S)
    return [tuple(S[(i + d) % G] for d in range(K)) for i in range(G)]


def interleave(a, b, c, d, G):
    """cyclic alternation of the four starts, as in SourceFaithfulIs.Interleaved"""
    arc = lambda p: (p - a) % G
    return (0 < arc(c) < arc(b)) != (0 < arc(d) < arc(b))


def agree(S, a, b, e):
    G = len(S)
    return all(S[(a + t) % G] == S[(b + t) % G] for t in range(e))


def primitive(S):
    G = len(S)
    return all(
        not all(S[(i + d) % G] == S[i] for i in range(G)) for d in range(1, G)
    )


def backlen(S, a, b):
    """maximal backward agreement: the largest p with S[a-t] = S[b-t], t <= p"""
    G = len(S)
    p = 0
    while p + 1 <= G and S[(a - (p + 1)) % G] == S[(b - (p + 1)) % G]:
        p += 1
    return p


def fwdlen(S, a, b, K):
    """maximal forward agreement beyond the K-window already agreed on"""
    G = len(S)
    r = 0
    while K + r < G and S[(a + K + r) % G] == S[(b + K + r) % G]:
        r += 1
    return r


def maxext(S, a, b, K):
    """the deterministic two-sided maximal extension, as (e, a', b'), or None.

    Mirrors maxPairStart / maxPairLen: shift back by the maximal backward
    agreement, then take the maximal forward agreement there.  None means the
    shift is a period, which cannot happen on a primitive circle.
    """
    G = len(S)
    if not agree(S, a, b, K):
        return None
    l = backlen(S, a, b)
    r = fwdlen(S, a, b, K)
    e = K + l + r
    if e >= G:
        return None
    return (e, (a - l) % G, (b - l) % G)


def isrepeat(S, a, b, e):
    G = len(S)
    return (
        1 <= e < G
        and a != b
        and agree(S, a, b, e)
        and S[(a - 1) % G] != S[(b - 1) % G]
        and S[(a + e) % G] != S[(b + e) % G]
    )


def p2(S, G, L):
    """actual P2 at L, clause by clause"""
    reps = set()
    for K in range(1, G + 1):
        for a in range(G):
            for b in range(a + 1, G):
                m = maxext(S, a, b, K)
                if m and isrepeat(S, m[1], m[2], m[0]):
                    reps.add((m[0], frozenset((m[1], m[2]))))
    for a in range(G):
        for b in range(a + 1, G):
            for c in range(b + 1, G):
                e = 0
                while e < G and all(S[(a + e) % G] == S[(x + e) % G] for x in (b, c)):
                    e += 1
                if e == 0 or e >= G:
                    continue
                if all(S[(x - 1) % G] == S[(a - 1) % G] for x in (b, c)):
                    continue
                if all(S[(x + e) % G] == S[(a + e) % G] for x in (b, c)):
                    continue
                if e >= L - 1:
                    return False
    for (e1, p1) in reps:
        for (e2, p2) in reps:
            if p1 == p2:
                continue
            if e1 >= L - 1 and e2 >= L - 1:
                x, y = sorted(p1)
                u, v = sorted(p2)
                if interleave(x, y, u, v, G):
                    return False
    return True


def doubled_pairs(S, K):
    G = len(S)
    grp = defaultdict(list)
    for i, w in enumerate(mers(S, K)):
        grp[w].append(i)
    return [tuple(v) for v in grp.values() if len(v) == 2]


def vertex_cycle_is_rotation(S, K, f):
    """the walk x -> f (x+1) reads the same cyclic sequence of (L-1)-mers
    as the truth, up to a cyclic shift (VertexCycleEq)"""
    G = len(S)
    m = mers(S, K)
    for k in range(G):
        x, ok = 0, True
        for n in range(G):
            if m[x] != m[(k + n) % G]:
                ok = False
                break
            x = f[(x + 1) % G]
        if ok:
            return True
    return False


# ------------------------------------------------------------------- the census


def main():
    maxG = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    maxA = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    cnt = Counter()
    ladder_bad = []
    rotation_bad = []
    examples = {}

    for alpha in range(2, maxA + 1):
        for G in range(3, maxG + 1):
            for S in itertools.product(range(alpha), repeat=G):
                S = list(S)
                if not primitive(S):
                    continue
                for L in range(2, G + 1):
                    K = L - 1
                    if not p2(S, G, L):
                        continue
                    dp = doubled_pairs(S, K)
                    for mask in range(1 << len(dp)):
                        f = list(range(G))
                        sel = [dp[i] for i in range(len(dp)) if mask >> i & 1]
                        for (a, b) in sel:
                            f[a], f[b] = b, a
                        # (2) f is an involution: it is a product of transpositions
                        if any(f[f[i]] != i for i in range(G)):
                            cnt["NOT-INVOLUTION"] += 1
                        # the walk is one G-cycle?
                        x, seen, ok = 0, set(), True
                        for _ in range(G):
                            if x in seen:
                                ok = False
                                break
                            seen.add(x)
                            x = f[(x + 1) % G]
                        if not ok or len(seen) != G:
                            continue
                        cnt["genuine-traversals"] += 1
                        supp = sorted(i for i in range(G) if f[i] != i)
                        if not supp:
                            cnt["identity-support"] += 1
                            continue
                        cnt["nontrivial-support"] += 1
                        # (1) every orbit is a doubled (L-1)-mer pair
                        for (a, b) in sel:
                            if mers(S, K)[a] != mers(S, K)[b]:
                                cnt["ORBIT-NOT-EQUAL-MER"] += 1
                        # (3)(4) the extension structure of the support chords
                        ext = {}
                        for (a, b) in sel:
                            m = maxext(S, a, b, K)
                            ext[(a, b)] = m
                            cnt["extension-len-%s" % ("<K" if m[0] < K else ">=K")] += 1
                        groups = defaultdict(list)
                        for pr, m in ext.items():
                            groups[(m[0], m[1], m[2])].append(pr)
                        cnt["ladders-%d" % len(groups)] += 1
                        for (e, u, v), prs in groups.items():
                            if len(prs) < 2:
                                continue
                            # (3) one length per extension
                            if any(maxext(S, x, y, K)[0] != e for (x, y) in prs):
                                cnt["LADDER-LEN-MISMATCH"] += 1
                            # (4) the pairs are distinct rotations of the same
                            #     pair, with equal chord length and spacing
                            offs = []
                            for (x, y) in prs:
                                ix = (x - u) % G
                                iy = (y - v) % G
                                if ix != iy:
                                    cnt["LADDER-NOT-ROTATION"] += 1
                                offs.append(ix)
                            if len(set(offs)) != len(offs):
                                cnt["LADDER-REPEATED-OFFSET"] += 1
                            if any((y - x) % G != (v - u) % G for (x, y) in prs):
                                cnt["LADDER-CHORD-LENGTH"] += 1
                            sp = sorted(offs)
                            if any(
                                (u + sp[i + 1] - u) % G
                                != (v + sp[i + 1] - v) % G
                                for i in range(len(sp) - 1)
                            ):
                                cnt["LADDER-SPACING"] += 1
                            # (4) the two shifted copies spell the same vertices
                            for i in offs:
                                for j in range(L - 1):
                                    if (
                                        S[(u + i + j) % G] != S[(v + i + j) % G]
                                    ):
                                        cnt["LADDER-ARC"] += 1
                        # (5) THE AUDITED CLAIM
                        crossing = [
                            (p, q)
                            for p, q in itertools.combinations(sel, 2)
                            if interleave(p[0], p[1], q[0], q[1], G)
                        ]
                        collapse = [
                            (p, q)
                            for p, q in itertools.combinations(sel, 2)
                            if ext[p][:2] == ext[q][:2]
                        ]
                        if crossing:
                            cnt["crossing-chords"] += 1
                            for p, q in crossing:
                                mp, mq = ext[p], ext[q]
                                if interleave(mp[1], mp[2], mq[1], mq[2], G):
                                    cnt["crossing-with-INTERLEAVED-extensions"] += 1
                                elif (mp[1], mp[2]) == (mq[1], mq[2]):
                                    cnt["crossing-with-COLLAPSING-extensions"] += 1
                                else:
                                    cnt["crossing-with-OTHER-extensions"] += 1
                            if collapse:
                                cnt["crossing-and-collapse"] += 1
                                if not vertex_cycle_is_rotation(S, K, f):
                                    cnt["COLLAPSE-NOT-ROTATION"] += 1
                                    rotation_bad.append(
                                        ("".join(map(str, S)), G, L, sel)
                                    )
                        if not vertex_cycle_is_rotation(S, K, f):
                            cnt["NOT-ROTATION"] += 1
                            rotation_bad.append(("".join(map(str, S)), G, L, sel))
                        key = (bool(collapse), bool(crossing))
                        if sel and key not in examples:
                            examples[key] = (
                                "".join(map(str, S)),
                                G,
                                L,
                                [(a + 1, b + 1) for a, b in sel],
                                [(a, b) for a, b in sel],
                            )

    print("maxG = %d, alphabet <= %d" % (maxG, maxA))
    for k in sorted(cnt, key=str):
        print("  %-28s %d" % (k, cnt[k]))
    print("violations of the audited claim (COLLAPSE-NOT-ROTATION / NOT-ROTATION): %d"
          % (cnt["COLLAPSE-NOT-ROTATION"] + cnt["NOT-ROTATION"]))
    if ladder_bad or rotation_bad:
        print("COUNTEREXAMPLES:", (ladder_bad + rotation_bad)[:5])
    print("first instance of each crossing/collapse pattern:")
    for k in sorted(examples, key=str):
        print("  %-22s %s" % (str(k), examples[k]))

if __name__ == "__main__":
    main()
