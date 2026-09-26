#!/usr/bin/env python3
"""Exhaustive search behind `docs/issue88-wraparound-contrapositive.md`.

Every predicate here is a transcription of the corresponding Lean definition in
`AssemblyP1.SourceFaithfulIs`, `AssemblyP1.RepeatAdapter` and
`AssemblyP1.OrientedRigidity`, at the same conventions:

* circular words of length `G` over an alphabet, indexed modulo `G`
  (`SourceFaithfulIs.Genome.cycl`, `OrientedRigidity.cyc`);
* oriented single-strand length-`L` windows, no reverse-complement collapse
  (`OrientedRigidity.window`, `OrientedRigidity.specCount`,
  `OrientedRigidity.support`);
* `InformationFeasible` = coverage + every maximal triple repeat all-bridged +
  every interleaved repeat pair bridged, over all admissible repeat lengths
  (Bresler two-sided maximality, as in `SourceFaithfulIs.Genome.IsRepeat` /
  `IsTripleRepeat`);
* bridging is strict on both sides: a read must cover a base strictly before
  and strictly after the copy (`SourceFaithfulIs.BridgesCopy`);
* `IsMaximalTriple`: three distinct residues with equal windows whose three
  preceding symbols are not all equal and whose three following symbols are not
  all equal (`AssemblyP1.RepeatAdapter.IsMaximalTriple`).

`I_s` is *monotone in the start set*: every clause is a "some read does ..."
condition or a coverage condition, so a superset of a feasible start set is
feasible.  Hence `R in I_s` is satisfiable for some `R` if and only if it is
satisfiable for the maximal start set `R = Fin G`, and the search only has to
check that one.

The four questions asked, for every genome length and read length in range:

Q1  does a same-support same-length candidate ever strictly exceed the truth's
    spectrum on a window support read type?  ("escape")
Q2  when it does, does the truth carry a maximal triple repeat of length in the
    mid-range band `L - 1 <= l < G - L`?  (the culprit statement)
Q3  how often is full `I_s` satisfiable at all?
Q4  is full `I_s` satisfiable *and* an escape present?  (a counterexample to the
    #88 theorem of `AssemblyP1.MLEscape`)

Usage:

    python3 scripts/issue88-wraparound-search.py 9 2      # binary, G <= 9
    python3 scripts/issue88-wraparound-search.py 7 3      # 3-letter, G <= 7

This is a search, not a proof: it is evidence for the culprit statement and,
more importantly, it is the reason no counterexample to the #88 theorem is
claimed.  The Lean-side non-vacuous instance is
`AssemblyP1.MLEscape.culprit_instance_checked`.
"""

import itertools
import sys
from collections import Counter

# ---------------------------------------------------------------- genomes


def cyc(S, i):
    return S[i % len(S)]


def win(S, L, r):
    return tuple(cyc(S, r + d) for d in range(L))


def spec(S, L):
    return Counter(win(S, L, r) for r in range(len(S)))


# ---------------------------------------------------------------- repeats


def triples(S):
    """All maximal triple repeats: (length, a, b, c)."""
    G = len(S)
    for e in range(1, G):
        for a, b, c in itertools.permutations(range(G), 3):
            w = win(S, e, a)
            if win(S, e, b) == w and win(S, e, c) == w:
                pre = [cyc(S, t + G - 1) for t in (a, b, c)]
                fol = [cyc(S, t + e) for t in (a, b, c)]
                if len(set(pre)) == 1 or len(set(fol)) == 1:
                    continue
                yield (e, a, b, c)


def max_triple_ge(S, L):
    best = -1
    for (e, _, _, _) in triples(S):
        if e >= L - 1:
            best = max(best, e)
    return best


def repeats(S):
    G = len(S)
    for e in range(1, G):
        for a, b in itertools.permutations(range(G), 2):
            if win(S, e, a) == win(S, e, b):
                if cyc(S, a + G - 1) != cyc(S, b + G - 1) and \
                   cyc(S, a + e) != cyc(S, b + e):
                    yield (e, a, b)


def in_arc(G, a, b, p):
    return 0 < (p + G - a) % G < (b + G - a) % G


def interleaved(G, a, b, c, d):
    return len({a, b, c, d}) == 4 and (in_arc(G, a, b, c) != in_arc(G, a, b, d))


# ---------------------------------------------------------------- I_s


def bridges_copy(G, L, R, e, t):
    pts = frozenset(((t + G - 1) % G, (t + e) % G))
    for r in R:
        if pts <= frozenset((r + d) % G for d in range(L)):
            return True
    return False


def information_feasible(S, L, R, tris, reps):
    G = len(S)
    covered = set()
    for r in R:
        covered |= {(r + d) % G for d in range(L)}
    if len(covered) < G:
        return False
    for (e, a, b, c) in tris:
        if not all(bridges_copy(G, L, R, e, t) for t in (a, b, c)):
            return False
    for (e1, a, b) in reps:
        for (e2, c, d) in reps:
            if interleaved(G, a, b, c, d) and not (
                    bridges_copy(G, L, R, e1, a) or bridges_copy(G, L, R, e1, b)
                    or bridges_copy(G, L, R, e2, c) or bridges_copy(G, L, R, e2, d)):
                return False
    return True


def feasible(S, L):
    """`Some R in I_s`, decided at the maximal start set by monotonicity."""
    G = len(S)
    tris = list(triples(S))
    reps = list(repeats(S))
    return information_feasible(S, L, set(range(G)), tris, reps)


# ---------------------------------------------------------------- search


def run(Gmax, alpha, census_Gmax):
    counts = Counter()
    culprits = []
    counterexamples = []
    escapes = 0
    for G in range(3, Gmax + 1):
        pool = list(itertools.product(range(alpha), repeat=G))
        for L in range(2, G + 1):
            groups = {}
            for D in pool:
                groups.setdefault(frozenset(spec(D, L)), []).append(D)
            for S in pool:
                sup = frozenset(spec(S, L))
                sp = spec(S, L)
                cands = groups.get(sup, [])
                beating = [D for D in cands
                           if any(spec(D, L)[w] > sp[w] for w in sup)]
                feas = feasible(S, L) if (beating or G <= census_Gmax) else None
                if feas:
                    counts['I_s_satisfiable'] += 1
                if not beating:
                    continue
                escapes += 1
                # Q2: the culprit statement, at *every* escape
                if any(L - 1 <= e < G - L for (e, _, _, _) in triples(S)):
                    counts['culprit_ok'] += 1
                else:
                    counts['culprit_VIOLATED'] += 1
                    culprits.append((''.join(map(str, S)), L,
                                     max_triple_ge(S, L), G - L))
                # Q4: an escape at an I_s-feasible instance
                if not feas:
                    counts['escape_without_I_s'] += 1
                    continue
                counterexamples.append((''.join(map(str, S)), L,
                                        ''.join(map(str, beating[0]))))
                counts['escape_with_I_s'] += 1
    return counts, escapes, culprits, counterexamples


if __name__ == '__main__':
    gmax = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    alpha = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    census = int(sys.argv[3]) if len(sys.argv) > 3 else 7
    counts, escapes, culprits, cex = run(gmax, alpha, census)
    print('alphabet size %d, G <= %d (I_s census for G <= %d)' % (alpha, gmax, census))
    print('(S, L) with I_s satisfiable :', counts['I_s_satisfiable'])
    print('escapes (same-support same-length beats truth) :', escapes)
    print('escapes at an I_s-feasible (S, L) :', counts['escape_with_I_s'])
    print('culprit statement holds at every escape :',
          counts['culprit_ok'], ' violated :', counts['culprit_VIOLATED'])
    if culprits:
        print('CULPRIT VIOLATIONS:', culprits[:20])
    if cex:
        print('COUNTEREXAMPLES to the #88 theorem:', cex[:20])
    else:
        print('counterexamples to the #88 theorem: none')
