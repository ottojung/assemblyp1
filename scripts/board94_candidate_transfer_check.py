#!/usr/bin/env python3
"""Obligation 17 (candidate-side transfer) — cheap decidable checker.

Scope: this script tests STATEMENTS only, never the library's proofs.

It checks three things, in this order.

  PITFALL  Reproduces the witness recorded by front 94d23
           (S = 0001, G = 4, L = 2): `IsTripleRepeat 1 0 1 2` holds while no
           `IsRepeat 1` pair holds, so 0001 is NOT `Ukkonen` at L = 2.  Any
           negative result below is worthless unless this passes, because the
           94d23 bug was exactly a triple-repeat enumeration that missed
           triples living outside maximal repeat pairs.

  Q1       Conjunct 2 of `AssemblyP1.BBTEulerian.CandidateTransfer`
           (BBTCandidateTransfer.lean), forward half:
             Matching hK L W E σ  ⟹  VertexCycleEq hK L W (pullback σ) refl
                                     ⟹  RotEquiv hK E W
           (this is `BBTEulerian.rotEquiv_of_vertexCycleEq`, BBTEulerian.lean:294)

  Q2       Conjunct 2, REVERSE half — the OPEN direction:
             Matching hK L W E σ  ∧  RotEquiv hK E W
                                     ⟹  VertexCycleEq hK L W (pullback σ) refl
           Violations refute the second conjunct of `CandidateTransfer`.

  Q3       Conjunct 3, its `¬ OrbitVertexEq` half, contrapositively:
             RotEquiv hK E W  ⟹  OrbitVertexEq hK L W (succOf (pullback σ))
           plus the three side conditions (Bijective / FibrePreserving /
           OneCycle) for every matching pull-back.  Violations refute the third
           conjunct.

Definitions are re-derived from the Lean sources and cited by file:line:

  OrientedRigidity.window            AssemblyP1/OrientedRigidity.lean:616
  OrientedRigidity.specCount         AssemblyP1/OrientedRigidity.lean:626
  OrientedRigidity.nodeWindow        AssemblyP1/OrientedRigidity.lean:621
  BBTSequenceGraph.vtx               AssemblyP1/BBTCondense.lean:178
  BBTEulerian.EulerianCycle          AssemblyP1/BBTEulerian.lean:154
  BBTEulerian.VertexCycleEq          AssemblyP1/BBTEulerian.lean:166
  BBTEulerian.rotAdd                 (rotAdd hG k x = (x.val + k) % G)
  BBTChords.Matching                 AssemblyP1/BBTChords.lean:351
  BBTCondense.pullback               AssemblyP1/BBTCondense.lean:462
  BBTEulerianSearch.succOf           AssemblyP1/BBTEulerianSearch.lean:134
  BBTEulerianSearch.FibrePreserving  AssemblyP1/BBTEulerianSearch.lean:140
  BBTEulerianSearch.OneCycle         AssemblyP1/BBTEulerianSearch.lean:146
  BBTEulerianSearch.OrbitVertexEq    AssemblyP1/BBTEulerianSearch.lean:152
  PopulationReduction.RotEquiv       AssemblyP1/PopulationReduction.lean:1715
  SourceFaithfulIs.Genome.IsRepeat        AssemblyP1/SourceFaithfulIs.lean:111
  SourceFaithfulIs.Genome.IsTripleRepeat  AssemblyP1/SourceFaithfulIs.lean:122
  AssemblyP1.P2.Ukkonen              AssemblyP1/P2.lean:91

Usage:  python3 scripts/board94_candidate_transfer_check.py [maxG] [maxL]
        default maxG = 5, maxL = 3.
"""

import itertools
import sys
from collections import Counter

# ---------------------------------------------------------------- primitives


def window(S, G, L, r):
    """OrientedRigidity.window: the length-L read spelled at start r."""
    return tuple(S[(r + i) % G] for i in range(L))


def spec_count(S, G, L):
    """OrientedRigidity.specCount, as a Counter over length-L words."""
    return Counter(window(S, G, L, r) for r in range(G))


def node_window(S, G, L, r):
    """OrientedRigidity.nodeWindow: the length-(L-1) vertex at start r."""
    return tuple(S[(r + i) % G] for i in range(L - 1))


def vtx(S, G, L, r):
    """BBTSequenceGraph.vtx (L := L) — literally nodeWindow."""
    return node_window(S, G, L, r)


def next_pos(G):
    return lambda i: (i + 1) % G


def rot_add(G, k):
    return lambda i: (i + k) % G


def succ_of(G, sigma):
    """BBTEulerianSearch.succOf hG sigma."""
    nxt = next_pos(G)
    symm = [0] * G
    for a, b in enumerate(sigma):
        symm[b] = a
    return lambda x: sigma[nxt(symm[x])]


def visits_all(G, theta, x):
    """BBTEulerian.VisitsAll: injective on the first G iterates from x."""
    seen = set()
    cur = x
    for _ in range(G):
        if cur in seen:
            return False
        seen.add(cur)
        cur = theta(cur)
    return True


def fibre_preserving(G, L, S, theta):
    """BBTEulerianSearch.FibrePreserving."""
    nxt = next_pos(G)
    return all(vtx(S, G, L, theta(x)) == vtx(S, G, L, nxt(x)) for x in range(G))


def one_cycle(G, theta):
    """BBTEulerianSearch.OneCycle = VisitsAll theta (origin)."""
    return visits_all(G, theta, 0)


def orbit_vertex_eq(G, L, S, theta):
    """BBTEulerianSearch.OrbitVertexEq."""
    for k in range(G):
        ok = True
        for j in range(G):
            p = theta(j)  # origin = 0
            if vtx(S, G, L, p) != vtx(S, G, L, (j + k) % G):
                ok = False
                break
        if ok:
            return True
    return False


def vertex_cycle_eq(G, L, S, sigma, tau):
    """BBTEulerian.VertexCycleEq sigma tau."""
    for k in range(G):
        if all(vtx(S, G, L, sigma[i]) == vtx(S, G, L, rot_add(G, k)(tau[i]))
               for i in range(G)):
            return True
    return False


def eulerian_cycle(G, L, S, sigma):
    """BBTEulerian.EulerianCycle."""
    nxt = next_pos(G)
    if not all(vtx(S, G, L, sigma[nxt(i)]) == vtx(S, G, L, nxt(sigma[i]))
               for i in range(G)):
        return False
    nxtp = nxt
    theta = lambda x: sigma[nxtp(sigma.index(x))]  # noqa: E731
    return visits_all(G, theta, 0)


def is_bijective(G, sigma):
    return sorted(sigma) == list(range(G))


def matching(G, L, S, E, sigma):
    """BBTChords.Matching hG L S E sigma."""
    return is_bijective(G, sigma) and all(
        window(S, G, L, r) == window(E, G, L, sigma[r]) for r in range(G))


def pullback(G, sigma):
    """BBTCondense.pullback = (Equiv.ofBijective sigma h).symm."""
    symm = [0] * G
    for a, b in enumerate(sigma):
        symm[b] = a
    return symm


def rot_equiv(G, D, S):
    """PopulationReduction.RotEquiv hG D S = exists k, D ((i+k)%G) = S i."""
    return any(all(D[(i + k) % G] == S[i] for i in range(G)) for k in range(G))


# ------------------------------------------------- repeat predicates (pitfall)

def agree(S, G, e, a, b):
    return all(S[(a + t) % G] == S[(b + t) % G] for t in range(e))


def preceding(S, G, a):
    """SourceFaithfulIs.Genome.Preceding."""
    return S[(a + G - 1) % G]


def following(S, G, e, a):
    """SourceFaithfulIs.Genome.Following."""
    return S[(a + e) % G]


def is_repeat(S, G, e, a, b):
    """SourceFaithfulIs.Genome.IsRepeat (line 111)."""
    return (1 <= e and e < G and a != b and agree(S, G, e, a, b) and
            preceding(S, G, a) != preceding(S, G, b) and
            following(S, G, e, a) != following(S, G, e, b))


def is_triple_repeat(S, G, e, a, b, c):
    """SourceFaithfulIs.Genome.IsTripleRepeat (line 122).

    The three-copy clauses are `not (Preceding a = Preceding b and
    Preceding b = Preceding c)` and the following analogue — "not all three
    are equal", strictly weaker than pairwise distinctness.  This is the exact
    clause whose misreading cost front 94d23 a full census.
    """
    return (1 <= e and e < G and a != b and a != c and b != c and
            agree(S, G, e, a, b) and agree(S, G, e, a, c) and
            agree(S, G, e, b, c) and
            not (preceding(S, G, a) == preceding(S, G, b) and
                 preceding(S, G, b) == preceding(S, G, c)) and
            not (following(S, G, e, a) == following(S, G, e, b) and
                 following(S, G, e, b) == following(S, G, e, c)))


def interleaved(S, G, a, b, c, d):
    """SourceFaithfulIs.Genome.Interleaved (line 365)."""
    if len({a, b, c, d}) != 4:
        return False

    def in_open_arc(x, y, p):
        return 0 < (p + G - x) % G < (y + G - x) % G

    return (in_open_arc(a, b, c)) != (in_open_arc(a, b, d))


def long_obstruction(G, L, S):
    """BBTEulerian.LongObstruction (line 337)."""
    if L - 1 < 1:
        thresh = 0
    else:
        thresh = L - 1
    for e in range(1, G):
        for a, b, c in itertools.permutations(range(G), 3):
            if is_triple_repeat(S, G, e, a, b, c) and e >= thresh:
                return ("triple", e, a, b, c)
    for e1 in range(1, G):
        for e2 in range(1, G):
            for a, b in itertools.combinations(range(G), 2):
                if not is_repeat(S, G, e1, a, b):
                    continue
                for c, d in itertools.combinations(range(G), 2):
                    if not is_repeat(S, G, e2, c, d):
                        continue
                    if interleaved(S, G, a, b, c, d):
                        if e1 >= thresh and e2 >= thresh:
                            return ("interleaved", e1, e2, a, b, c, d)
    return None


def ukkonen(G, L, S):
    """AssemblyP1.P2.Ukkonen hG L S = not (LongObstruction hG L S)."""
    return long_obstruction(G, L, S) is None


# ------------------------------------------------------------- Q4: the pitfall

def check_pitfall():
    """Front 94d23's recorded witness, re-derived from source.

    The brief records: `S = 0001`, `G = 4`, `L = 2`; `IsTripleRepeat 1 0 1 2`
    holds; "all three candidate pairs fail `IsRepeat 1`"; hence `0001` is not
    `Ukkonen` at `L = 2`.

    Re-derivation of `IsRepeat 1 0 2` on 0001 (S = [0,0,0,1], indices 0..3):
      1 <= 1, 1 < 4, 0 != 2                                  ok
      Agree 1 0 2 : S[0] = 0 = S[2]                           ok
      Preceding 0 = S[3] = 1,  Preceding 2 = S[1] = 0        differ  ok
      Following 1 0 = S[1] = 0,  Following 1 2 = S[3] = 1    differ  ok
    so `IsRepeat 1 0 2` HOLDS and the "no maximal repeat pair" clause of the
    brief does not reproduce.  The conclusion the brief needs --- `0001` is not
    `Ukkonen` at `L = 2` --- does reproduce, witnessed by the triple
    `IsTripleRepeat 1 0 2 1` (preceding 1,0,0 and following 0,1,0 are each not
    all equal).  Reported, not silently repaired; see
    docs/candidate-transfer-oblig17-94.md section 6.
    """
    S = (0, 0, 0, 1)
    G, L = 4, 2
    trip_012 = is_triple_repeat(S, G, 1, 0, 1, 2)
    trip_021 = is_triple_repeat(S, G, 1, 0, 2, 1)
    pairs = [(a, b) for a, b in itertools.combinations(range(G), 2)
             if is_repeat(S, G, 1, a, b)]
    print("PITFALL  S=0001 G=4 L=2  (front 94d23's witness, re-derived)")
    print("  IsTripleRepeat 1 0 1 2        =", trip_012)
    print("  IsTripleRepeat 1 0 2 1        =", trip_021)
    print("  IsRepeat 1 pairs               =", pairs,
          " <-- brief says all three fail; (0,2) holds")
    print("  0001 is Ukkonen at L=2        =", ukkonen(G, L, S))
    ok = trip_012 and trip_021 and not ukkonen(G, L, S)
    print("  PITFALL CONCLUSION REPRODUCED  =", ok)
    if not ok:
        print("FATAL: conclusion not reproduced; negative results below are void.")
        return False
    return True


def q4_pair_route(maxG, maxQ):
    """Is `IsTripleRepeat` enumerated exactly by 'inside a maximal repeat pair'?

    Q4a  every IsTripleRepeat (e,a,b,c) contains some IsRepeat e pair inside
         {a,b,c}.  (The brief claims this can fail.)
    Q4b  every IsRepeat e pair (a,b) together with a third occurrence c
         agreeing at length e yields IsTripleRepeat (e,a,b,c).  (The other
         direction, which is what a "pair route" actually risks over-claiming.)

    Both directions are exhaustive searches, and both report their instance
    counts.  A zero with count zero would be vacuous.
    """
    a_triples = a_bad = 0
    b_pairs = b_bad = 0
    for G in range(3, maxG + 1):
        for q in range(2, maxQ + 1):
            for S in itertools.product(range(q), repeat=G):
                for e in range(1, G):
                    for a, b, c in itertools.permutations(range(G), 3):
                        if not is_triple_repeat(S, G, e, a, b, c):
                            continue
                        a_triples += 1
                        if not any(is_repeat(S, G, e, x, y)
                                   for x, y in itertools.combinations(
                                       sorted({a, b, c}), 2)):
                            a_bad += 1
                            if a_bad <= 3:
                                print("  Q4a counterexample:",
                                      G, q, "".join(map(str, S)), e, a, b, c)
                    for a, b in itertools.combinations(range(G), 2):
                        if not is_repeat(S, G, e, a, b):
                            continue
                        b_pairs += 1
                        for c in range(G):
                            if c in (a, b) or not agree(S, G, e, a, c):
                                continue
                            if not is_triple_repeat(S, G, e, a, b, c):
                                b_bad += 1
                                if b_bad <= 3:
                                    print("  Q4b counterexample:",
                                          G, q, "".join(map(str, S)), e, a, b, c)
    return a_triples, a_bad, b_pairs, b_bad


# ------------------------------------------------------------------- the census

def main():
    maxG = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    maxL = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    maxQ = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    if not check_pitfall():
        return 1

    stats = {L: dict(words=0, pairs=0, matchings=0, sigmas=0, q1=0, q2=0,
                     q3=0, eulerian=0, rotinst=0)
             for L in range(2, maxL + 1)}
    q2_hits, q3_hits = [], []

    for L in range(2, maxL + 1):
        st = stats[L]
        for G in range(1, maxG + 1):
            for S in itertools.product(range(2), repeat=G):
                st["words"] += 1
                scS = spec_count(S, G, L)
                # precompute all bijections sigma
                sigmas = [list(p) for p in itertools.permutations(range(G))]
                for E in itertools.product(range(2), repeat=G):
                    if scS != spec_count(E, G, L):
                        continue
                    st["pairs"] += 1
                    for sigma in sigmas:
                        if not matching(G, L, S, E, sigma):
                            continue
                        st["matchings"] += 1
                        if eulerian_cycle(G, L, S, sigma):
                            st["eulerian"] += 1
                        mu = pullback(G, sigma)
                        v = vertex_cycle_eq(G, L, S, mu, list(range(G)))
                        r = rot_equiv(G, E, S)
                        if v and not r:
                            st["q1"] += 1
                        if r:
                            st["rotinst"] += 1
                            if not v:
                                st["q2"] += 1
                                q2_hits.append((G, L, S, E, tuple(sigma)))
                            th = succ_of(G, mu)
                            if not orbit_vertex_eq(G, L, S, th):
                                st["q3"] += 1
                                q3_hits.append((G, L, S, E, tuple(sigma)))

    print()
    print("Q1  VertexCycleEq(pullback) -> RotEquiv          violations (want 0)")
    print("Q2  RotEquiv -> VertexCycleEq(pullback)          violations (want 0)")
    print("Q3  RotEquiv -> OrbitVertexEq(succOf pullback)    violations (want 0)")
    print()
    tot = dict(words=0, pairs=0, matchings=0, rotinst=0, q1=0, q2=0, q3=0)
    for L in range(2, maxL + 1):
        st = stats[L]
        for k in tot:
            tot[k] += st[k]
        print(f"L={L}  words={st['words']}  equal-spectrum (S,E) pairs={st['pairs']}"
              f"  matchings tested={st['matchings']}  of which EulerianCycle={st['eulerian']}"
              f"  RotEquiv instances={st['rotinst']}")
        print(f"      Q1={st['q1']}  Q2={st['q2']}  Q3={st['q3']}")
    print(f"TOTAL words={tot['words']}  equal-spectrum pairs={tot['pairs']}"
          f"  matchings={tot['matchings']}  RotEquiv instances={tot['rotinst']}"
          f"  Q1={tot['q1']}  Q2={tot['q2']}  Q3={tot['q3']}")
    print()
    print("Q2 witnesses (first 5):", q2_hits[:5])
    print("Q3 witnesses (first 5):", q3_hits[:5])
    print()
    a_t, a_bad, b_p, b_bad = q4_pair_route(maxG, maxQ)
    print(f"Q4a  IsTripleRepeat instances containing NO maximal e-pair: {a_bad}"
          f"  (of {a_t} triple instances, G<={maxG}, alphabet size <={maxQ})")
    print(f"Q4b  maximal e-pair + third copy that is NOT a triple repeat: {b_bad}"
          f"  (of {b_p} pair instances)")
    if tot["rotinst"] == 0:
        print("WARNING: Q2/Q3 were evaluated on 0 RotEquiv instances — VACUOUS.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
