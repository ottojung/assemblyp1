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
* bridging is the source's **single-lift span** condition: one realized read,
  one offset `d`, the copy at offset `d + 1`, with `d + e + 1 < L`
  (`SourceFaithfulIs.BridgesCopy`). This is a strict-extension clause on both
  sides and forces `e + 2 <= L`;
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
    python3 scripts/issue88-wraparound-search.py 9 2 7 --endpoint-only
        # the pre-migration endpoint-only bridging reading, for comparison only

**Status of the results.** Q2 and Q4 were the crux of the retired
`EscapeForcesMidRangeRepeat` programme, and they were asked against the
*endpoint-only* bridging reading. Under the canonical single-lift span semantics
of this version the crux is not open: `I_s` forbids every maximal triple repeat
of length `>= L - 1`
(`AssemblyP1.BridgingBridge.informationFeasible_no_long_triple_repeat`), so
Q2's conclusion holds for every escape for a structural reason rather than an
empirical one, and Q4 has no instances. The numbers this script prints are
therefore best read as a **consistency check on the transcription**, together
with the (still meaningful) non-vacuity census of escapes, and `--endpoint-only`
reproduces the historical figures of
`docs/issue88-wraparound-contrapositive.md` exactly.

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
    """Canonical `SourceFaithfulIs.BridgesCopy`: the source's single-lift span
    condition.

    One realized read `r`, one offset `d < L`, the copy's start at offset `d + 1`
    of that read, and the copy's successor still inside the read, i.e.
    `d + e + 1 < L`.  Equivalently `r < t'` and `t' + e < r + L` on a suitable
    integer lift, which is what Bresler et al. (Fig. 5) and Shomorony et al.
    (section 3 / Fig. 6) describe, and it forces `e + 2 <= L`.

    **This is a correction.** The version of this script that produced the
    results recorded in `docs/issue88-wraparound-contrapositive.md` used the
    *endpoint-only* reading, `the read at r covers (t - 1) % G and covers
    (t + e) % G`, which is strictly weaker: a read can reach both flanks of a long
    copy by travelling the complementary circular arc without containing the
    copy. That reading is what manufactured the "wraparound regime", and the
    recorded cruxes are consequences of the wrong predicate, not evidence about
    the source's `I_s`.  `bridges_copy_endpoint_only` below is kept only so the
    old figures can be reproduced verbatim for comparison.
    """
    return any((r + d + 1) % G == t and d + e + 1 < L for r in R for d in range(L))


def bridges_copy_endpoint_only(G, L, R, e, t):
    """The pre-migration endpoint-only reading.  **Not** the source's condition."""
    pts = frozenset(((t + G - 1) % G, (t + e) % G))
    for r in R:
        if pts <= frozenset((r + d) % G for d in range(L)):
            return True
    return False


def information_feasible(S, L, R, tris, reps, bridge=bridges_copy):
    G = len(S)
    covered = set()
    for r in R:
        covered |= {(r + d) % G for d in range(L)}
    if len(covered) < G:
        return False
    for (e, a, b, c) in tris:
        if not all(bridge(G, L, R, e, t) for t in (a, b, c)):
            return False
    for (e1, a, b) in reps:
        for (e2, c, d) in reps:
            if interleaved(G, a, b, c, d) and not (
                    bridge(G, L, R, e1, a) or bridge(G, L, R, e1, b)
                    or bridge(G, L, R, e2, c) or bridge(G, L, R, e2, d)):
                return False
    return True


def feasible(S, L, bridge=bridges_copy):
    """`Some R in I_s`, decided at the maximal start set by monotonicity."""
    G = len(S)
    tris = list(triples(S))
    reps = list(repeats(S))
    return information_feasible(S, L, set(range(G)), tris, reps, bridge)


# ---------------------------------------------------------------- search


def run(Gmax, alpha, census_Gmax, bridge=bridges_copy):
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
                feas = feasible(S, L, bridge) if (beating or G <= census_Gmax) else None
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
    bridge = bridges_copy
    tag = 'canonical'
    if '--endpoint-only' in sys.argv[1:]:
        bridge, tag = bridges_copy_endpoint_only, 'endpoint-only'
    counts, escapes, culprits, cex = run(gmax, alpha, census, bridge)
    print('bridging predicate: %s (single-lift span = the source\'s condition)'
          % tag)
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
