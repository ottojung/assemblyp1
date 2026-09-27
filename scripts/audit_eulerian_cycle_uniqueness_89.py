#!/usr/bin/env python3
"""Independent audit of the #89 statement (`AssemblyP1.BBTEulerian.EulerianCycleObstruction`).

A *second, independent* search of the same statement as
`scripts/verify_eulerian_cycle_uniqueness_89.py`, written from the Lean
definitions of `AssemblyP1/SourceFaithfulIs.lean`,
`AssemblyP1/BBTCondense.lean` (`vtx`) and `AssemblyP1/BBTEulerian.lean`
(`EulerianCycle`, `VertexCycleEq`), and organised around an exact
reduction that makes the search cheap and complete.

Definitions mirrored (verbatim from the Lean sources)
----------------------------------------------------
  cycl(i)        = S[i mod G]
  window(e,r)[d] = S[(r+d) mod G]
  Preceding(t)   = S[(t-1) mod G]
  Following(e,t) = S[(t+e) mod G]
  IsRepeat e a b := 1 <= e < G, a != b, window e a = window e b,
                     Preceding a != Preceding b, Following e a != Following e b
  IsTripleRepeat e a b c := 1 <= e < G, a,b,c pairwise distinct, all three
                     windows equal, not (all three preceding equal),
                     not (all three following equal)
  Interleaved a b c d := a,b,c,d pairwise distinct, and exactly one of c,d
                     lies on the open clockwise arc from a to b
  vtx(r)         = window (L-1) r                      -- the K-mer at r
  traverses       vtx (sigma (i+1)) = window (L-1) ((sigma i) + 1)
  one circuit     the successor x |-> sigma ((sigma^-1 x) + 1) is a G-cycle
  VertexCycleEq sigma id := exists k, forall i,
                     vtx (sigma i) = vtx ((id i) + k)

The exact reduction used here
-----------------------------
Write `mer(p)` for the `(K+1)`-mer at `p`.  The traversal condition is

    vtx (sigma (i+1)) = vtx (sigma i + 1)                      (*)

Let `C` be the multiset of `(K+1)`-mers of `S` (each of the `G` positions
contributes one).  A **class sequence** is a cyclic listing
`(c_0, ..., c_{G-1})` of the elements of `C` obeying

    c_{i+1}[:K] = c_i[1:]      for every i, cyclically.               (**)

Two facts make (**) an exact model of the vertex cycles:

  (F1) *Realizability.*  A cyclic class sequence satisfying (**) is
  realized by a single-circuit traversal: choose any `p_i` of class `c_i`;
  then `vtx (p_{i+1}) = c_{i+1}[:K] = c_i[1:] = vtx (p_i + 1)`, which is
  (*), and the `p_i` are distinct because the classes are used with
  multiplicity.  (Single circuit: the listing is a cycle through all `G`
  positions.)

  (F2) *The vertex cycle is the class sequence.*  If two traversals have
  the same vertex cycle then, for each `i`, `vtx (sigma i) = vtx (tau i)` and
  `S[sigma i + K] = S[tau i + K]` (the latter because `vtx (sigma i + 1) =
  vtx (sigma (i+1)) = vtx (tau (i+1)) = vtx (tau i + 1)`), so
  `mer (sigma i) = mer (tau i)`.  Conversely a class sequence determines the
  vertex cycle, because the class sequence determines the cyclic word (its
  first letters) and the cyclic word determines the cyclic `K`-mer sequence.

So the set of vertex cycles of the single-circuit traversals is *exactly*
the set of cyclic words spelled by the class sequences of (**).  The search
therefore enumerates class sequences, which is exponentially smaller than
traversals (in particular it is trivial for the degenerate words such as
`0^G`, where there is a single class and hence a single class sequence).

Two independent enumerators are implemented and, wherever both terminate,
their verdicts are compared:

  * `cls`  -- enumeration of valid cyclic class sequences (the method above);
  * `pos`  -- direct enumeration of single-circuit traversals with
    de-duplication by vertex cycle (the naive method, kept as a check).

Verdicts
--------
  forced   the successor of every position is unique, so the traversal is
           forced and the vertex cycle is the truth's;
  unique   every valid class sequence (traversal) spells a cyclic shift of S;
  counter  some valid class sequence (traversal) spells a cyclic word that is
           *not* a cyclic shift of S -- a counterexample to #89;
  skipped  the enumeration hit the safety cap (no verdict).

The script also reports, for every instance, which clause of
`LongObstruction` holds (maximal triple repeat of length `>= K`; two
interleaved maximal repeats both of length `>= K`), so that one can see
empirically whether either clause is ever needed, and whether any instance
is left undecided by the dichotomy.

Run:  python3 scripts/audit_eulerian_cycle_uniqueness_89.py [maxG] [alphabet] [cap]
"""

import sys
from collections import Counter


# ----------------------------------------------------------------- words ---

def mers(S, G, e):
    return [tuple(S[(r + i) % G] for i in range(e)) for r in range(G)]


def maximal_repeats(S, G):
    """(repeat_pairs, triple_repeats, interleaved_pairs); K-independent.

    `repeat_pairs` lists every `IsRepeat` of `S` (i.e. every maximal repeat,
    in the two-sided sense of `SourceFaithfulIs`), and likewise for
    `IsTripleRepeat`.  All admissible lengths are scanned, since the
    maximality conditions are not monotone in the length.
    """
    S2 = S + S
    prec = [(t - 1) % G for t in range(G)]

    def ext(ts):
        """longest common extension of the copies at `ts`, capped at G"""
        n = 0
        for i in range(G):
            v = S2[ts[0] + i]
            for t in ts[1:]:
                if S2[t + i] != v:
                    return n
            n += 1
        return n

    rep = []
    for a in range(G):
        for b in range(G):
            if a == b:
                continue
            E = ext((a, b))
            if E < 1 or E >= G:
                continue
            if S[prec[a]] == S[prec[b]]:
                continue
            for e in range(1, E + 1):
                if S2[a + e] != S2[b + e]:
                    rep.append((e, a, b))
    tri = []
    for a in range(G):
        for b in range(a + 1, G):
            for c in range(b + 1, G):
                E = ext((a, b, c))
                if E < 1 or E >= G:
                    continue
                if S[prec[a]] == S[prec[b]] == S[prec[c]]:
                    continue
                for e in range(1, E + 1):
                    if not (S2[a + e] == S2[b + e] == S2[c + e]):
                        tri.append((e, a, b, c))

    def inarc(a, b, p):
        return 0 < (p - a) % G < (b - a) % G

    inter = []
    for (e1, a, b) in rep:
        for (e2, c, d) in rep:
            if len({a, b, c, d}) < 4:
                continue
            if inarc(a, b, c) != inarc(a, b, d):
                inter.append((min(e1, e2), (e1, a, b), (e2, c, d)))
    return rep, tri, inter


def obstruction(tri, inter, K):
    """Which clauses of `LongObstruction` hold at read length `K`?"""
    t = any(e >= K for (e, _, _, _) in tri)
    i = any(m >= K for (m, _, _) in inter)
    return t, i


# ------------------------------------------------------- class sequences ---

def class_sequences(S, G, K, cap):
    """Enumerate the valid cyclic class sequences of the `(K+1)`-mers.

    Returns the set of cyclic words spelled by them (as canonical rotations).
    """
    spec = mers(S, G, K + 1)              # the (K+1)-spectrum, with multiplicity
    classes = sorted(set(spec))
    cid = {c: i for i, c in enumerate(classes)}
    cnt = Counter(cid[m] for m in spec)
    # successor classes: those whose K-mer is c[1:]
    succ = {i: [j for j, c in enumerate(classes) if c[:K] == classes[i][1:]]
            for i in range(len(classes))}
    letter = [c[0] for c in classes]
    n = len(classes)
    words = set()
    budget = [cap]
    seq = []

    def canon(seq):
        return min(tuple(seq[i:] + seq[:i]) for i in range(len(seq)))

    def dfs(cur, remaining):
        # `cur` is the class sequence built so far, starting at class 0
        budget[0] -= 1
        if budget[0] < 0:
            raise TimeoutError
        used = total - sum(remaining.values())
        if used == total:
            # close the cycle: class after the last must be class 0
            if 0 in succ[seq[-1]]:
                words.add(canon([letter[i] for i in seq]))
            return
        for j in succ[cur]:
            if remaining[j] == 0:
                continue
            remaining[j] -= 1
            seq.append(j)
            dfs(j, remaining)
            seq.pop()
            remaining[j] += 1
            if budget[0] < 0:
                raise TimeoutError

    total = sum(cnt.values())
    try:
        start = 0
        cnt[start] -= 1
        seq.append(start)
        dfs(start, cnt)
    except (TimeoutError, RecursionError):
        return None
    return words


# ------------------------------------------------- positional traversals ---

def traversals(S, G, K, cap):
    """Direct enumeration of single-circuit traversals, de-duplicated by
    vertex cycle (the naive method, kept as an independent check)."""
    vtx = mers(S, G, K)
    ids = {}
    v = [ids.setdefault(m, len(ids)) for m in vtx]
    nxt = {r: [s for s in range(G) if vtx[s] == vtx[(r + 1) % G]] for r in range(G)}
    if all(len(x) == 1 for x in nxt.values()):
        return 'forced'
    seen = set()
    path = []
    vis = [False] * G
    budget = [cap]
    found = [False]

    def canon(seq):
        return min(tuple(seq[i:] + seq[:i]) for i in range(G))

    def dfs(pos):
        budget[0] -= 1
        if budget[0] < 0:
            raise TimeoutError
        path.append(pos)
        if len(path) == G:
            if 0 in nxt[pos]:
                c = canon([v[p] for p in path])
                if c not in seen:
                    seen.add(c)
                    if len(seen) >= 2:
                        found[0] = True
        else:
            vis[pos] = True
            for s in nxt[pos]:
                if not vis[s]:
                    dfs(s)
                    if found[0] or budget[0] < 0:
                        break
            vis[pos] = False
        path.pop()

    vis[0] = True
    try:
        dfs(0)
    except (TimeoutError, RecursionError):
        return 'skipped'
    return 'counter' if found[0] else 'unique'


# ------------------------------------------------------------------- main ---

def main():
    maxG = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    Q = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    cap = int(sys.argv[3]) if len(sys.argv) > 3 else 200000
    crosscheck = len(sys.argv) > 4 and sys.argv[4] == 'crosscheck'
    stats = Counter()
    table = Counter()
    for G in range(1, maxG + 1):
        for code in range(Q ** G):
            S = []
            c = code
            for _ in range(G):
                S.append(c % Q)
                c //= Q
            # keep rotation-canonical representatives only
            skip = False
            for s in range(1, G):
                if [S[(i + s) % G] for i in range(G)] < S:
                    skip = True
                    break
            if skip:
                continue
            stats['words'] += 1
            tri, inter = maximal_repeats(S, G)[1:]
            for K in range(1, G + 4):
                stats['pairs'] += 1
                t, i = obstruction(tri, inter, K)
                if t or i:
                    table['obstruction:triple' if t else 'obstruction:interleaved-only'] += 1
                    continue
                stats['P2'] += 1
                words = class_sequences(S, G, K, cap)
                if words is None:
                    kind = 'skipped'
                else:
                    # the truth's own cyclic word, as a canonical rotation
                    truth = min(tuple(S[i:] + S[:i]) for i in range(G))
                    kind = 'unique' if words == {truth} else 'counter'
                if crosscheck:
                    k2 = traversals(S, G, K, cap)
                    if k2 != 'skipped' and k2 not in (kind, 'forced'):
                        print("DISAGREE G=%d K=%d word=%s cls=%s pos=%s"
                              % (G, K, ''.join(map(str, S)), kind, k2))
                        sys.stdout.flush()
                stats[kind] += 1
                if kind in ('counter', 'skipped'):
                    print("%s G=%d K=%d word=%s" % (kind.upper(), G, K,
                                                   ''.join(map(str, S))))
                    sys.stdout.flush()
        print("G=%d %s" % (G, dict(stats)))
        sys.stdout.flush()
    print("SUMMARY %s" % dict(stats))
    print("OBSTRUCTION-TABLE %s" % dict(table))


if __name__ == '__main__':
    main()
