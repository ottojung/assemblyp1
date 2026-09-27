#!/usr/bin/env python3
"""Search for the *collapse / ladder* regime of the #89 crossing-chord route.

Setup, all as in `scripts/verify_support_chord_dichotomy_89.py`: a word `S`
of length `G`, read length `K` (`L = K+1`), labelling `W` of the starts by
their `K`-mer, an alternative Eulerian cycle presented by a listing `sigma`
(valid traversal + single circuit), and the associated label-preserving
permutation `f = AltF sigma = Succ sigma . prevPos`.

The route needs a **doubled pair** `{a,b}` (`W a = W b`, `a != b`) to be
*usable*: a maximal repeat must exist at exactly the starts `a`, `b`.  By
`AssemblyP1.BBTMaximalExtension.maximalRepeat_of_branch` that requires the
preceding symbols to differ, so a doubled pair with `prec(a) == prec(b)`
carries **no** maximal repeat at any length below `G` and can only be used
after a *backward* shift of the pair, which may destroy the interleaving.

So for every alternative Eulerian cycle with all `K`-mer fibres of size
<= 2 (so `f` is a product of disjoint transpositions) and with at least one
**crossing** pair of doubled pairs, this script records

  * `USABLE`   : every crossing pair admits a maximal repeat at its own
                 starts, hence the interleaving-extension case is available;
  * `COLLAPSE` : some crossing pair does not, hence the pair must be
                 shifted and the extensions may coincide or fail to
                 interleave.

and, for each, whether the alternative traversal has the *same* vertex
cycle as the truth.  The ladder/collapse lemma to be proved says the
`COLLAPSE` rows are all `same vertex cycle`; a `COLLAPSE` row with a
*different* vertex cycle would be a counterexample to that lemma.

Usage:  python3 scripts/verify_crossing_collapse_89.py [Gmax] [alphabet]
"""

import sys
from itertools import product


def win(S, e, r):
    return tuple(S[(r + i) % len(S)] for i in range(e))


def prec(S, t):
    return S[(t - 1) % len(S)]


def foll(S, e, t):
    return S[(t + e) % len(S)]


def is_repeat(S, e, a, b):
    G = len(S)
    return (1 <= e < G and a != b and win(S, e, a) == win(S, e, b)
            and prec(S, a) != prec(S, b) and foll(S, e, a) != foll(S, e, b))


def any_maximal_repeat_at(S, a, b):
    G = len(S)
    return any(is_repeat(S, e, a, b) for e in range(1, G))


def in_arc(G, a, b, p):
    return 0 < (p - a) % G < (b - a) % G


def interleaved(G, a, b, c, d):
    return (a != b and a != c and a != d and b != c and b != d and c != d
            and in_arc(G, a, b, c) != in_arc(G, a, b, d))


def traversals(S, K):
    G = len(S)
    W = [win(S, K, i) for i in range(G)]
    fib = {}
    for i in range(G):
        fib.setdefault(W[i], []).append(i)
    succ = {x: fib[W[(x + 1) % G]] for x in range(G)}
    out, used, path = [], [False] * G, []

    def dfs(x):
        if len(path) == G:
            if W[(path[-1] + 1) % G] == W[0]:
                out.append(tuple(path))
            return
        for y in succ[x]:
            if not used[y]:
                used[y] = True
                path.append(y)
                dfs(y)
                path.pop()
                used[y] = False

    used[0] = True
    path.append(0)
    dfs(0)
    return out


def vertex_cycle(S, K, listing):
    W = [win(S, K, i) for i in range(len(S))]
    seq = [W[x] for x in listing]
    return min(tuple(seq[k:] + seq[:k]) for k in range(len(seq)))


def main():
    Gmax = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    q = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    tot = dict(usable=0, collapse=0, collapse_same=0, collapse_diff=0)
    ex_collapse_same = None
    ex_collapse_diff = None
    ex_usable = None
    for G in range(1, Gmax + 1):
        for S in product(range(q), repeat=G):
            S = list(S)
            for K in range(1, G + 1):
                W = [win(S, K, i) for i in range(G)]
                # node fibres <= 2, so that f is a product of transpositions
                fib = {}
                for i in range(G):
                    fib.setdefault(W[i], []).append(i)
                if any(len(v) > 2 for v in fib.values()):
                    continue
                pairs = [(a, b) for (a, b) in itertools_combinations(fib)
                         if a != b and W[a] == W[b]]
                cross = [(a, b, c, d) for (a, b) in pairs for (c, d) in pairs
                         if interleaved(G, a, b, c, d)]
                if not cross:
                    continue
                truth = vertex_cycle(S, K, list(range(G)))
                for listing in traversals(S, K):
                    same = vertex_cycle(S, K, listing) == truth
                    usable = all(any_maximal_repeat_at(S, a, b)
                                 and any_maximal_repeat_at(S, c, d)
                                 for (a, b, c, d) in cross)
                    rec = ("".join(map(str, S)), G, K, listing, cross, same)
                    if usable:
                        tot['usable'] += 1
                        if ex_usable is None:
                            ex_usable = rec
                    else:
                        tot['collapse'] += 1
                        if same:
                            tot['collapse_same'] += 1
                            if ex_collapse_same is None:
                                ex_collapse_same = rec
                        else:
                            tot['collapse_diff'] += 1
                            if ex_collapse_diff is None:
                                ex_collapse_diff = rec
        print("G = %2d : usable %d | collapse %d (same vertex cycle %d, "
              "DIFFERENT %d)" % (G, tot['usable'], tot['collapse'],
                                 tot['collapse_same'], tot['collapse_diff']))
        sys.stdout.flush()
    print()
    print("totals:", tot)
    for name, rec in (("usable", ex_usable),
                      ("collapse+same", ex_collapse_same),
                      ("collapse+different", ex_collapse_diff)):
        if rec:
            print("example %-19s S=%s G=%d K=%d listing=%s crossing=%s same=%s"
                  % (name, rec[0], rec[1], rec[2], list(rec[3]),
                     [list(t) for t in rec[4][:2]], rec[5]))
    # the ladder/collapse lemma is refuted exactly by a `collapse+different` row
    return 1 if tot['collapse_diff'] else 0


def itertools_combinations(fib):
    for v in fib.values():
        for i in range(len(v)):
            for j in range(i + 1, len(v)):
                yield v[i], v[j]


if __name__ == "__main__":
    sys.exit(main())
