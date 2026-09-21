#!/usr/bin/env python3
"""
Issue #48: finite repaired theorem with candidate-intrinsic admissibility.

Question attacked
-----------------
Suppose the true circular genome S satisfies the *source-faithful* sampled-read
information-feasibility condition I_s for a realized read placement R, and the
candidate universe is the set of circular genomes that satisfy a
*candidate-intrinsic* structural repeat/read-length admissibility predicate
(optionally primitive).  Is the truth then an exact maximum-likelihood
maximizer under the free-length Medvedev-Brudno read-count multinomial?

This script is a self-contained, exact-arithmetic verifier.  It re-implements
the source repeat / triple-repeat / interleaving / bridging semantics from
docs/bridging-source-semantics.md and the two candidate-intrinsic predicates
used in issue #48, and it searches small instances exhaustively.

Conventions (fixed here, stated explicitly)
-------------------------------------------
* Alphabet: finite; witnesses use {A, B} / {A, B, C}.
* Strand/read type: single-strand oriented reads of fixed length L (the
  Shomorony/Bresler panel).  No reverse-complement collapse.
* Truth: a circular word S of length G, read length L <= G, and a realized
  multiset R of latent start positions.  I_s(S, R) means (1) R covers S,
  (2) every Bresler triple repeat of S is all-bridged by R, (3) every
  interleaved pair of maximal repeat pairs of S is bridged by R.
* Bridging: strict two-sided extension on an integer lift of the circle:
  a length-ell copy at lifted start t is bridged by a read starting at lifted
  start r iff r < t and t + ell < r + L.
* Candidate universe: all circular words D over the same alphabet with any
  positive length.  The truth is a candidate.
* Intrinsic predicates on a candidate D (properties of D and L only):
    STRONG(D) : no (L-1)-mer of D occurs twice.
    WEAK(D)   : every triple repeat of D has length <= L-2 and every
                interleaved pair has a constituent repeat of length <= L-2
                (the full-read-set I_s shadow).
    primitive(D): D is not a nontrivial power w^m, m >= 2.
* Objective: exact Medvedev-Brudno read-count multinomial with
  candidate-intrinsic length N(D)=len(D).  For observed read-type counts x_w,
  L(D)/L(S) = prod_{w: x_w>0} ( G * d_D(w) / ( len(D) * d_S(w) ) )^{x_w},
  and 0 if some observed type is absent from D.  (The observation-only
  multinomial coefficient cancels.)  The fixed-length variant is the same with
  G*.../len(D) replaced by 1.
* Tie semantics: a *strict* competitor (ratio > 1) refutes both the
  "truth is a maximizer" schema and the "truth is the unique maximizer up to
  genome equivalence" schema for every equivalence relation and every tie rule.
  Equivalence is therefore not needed for the refutation; we record the
  intended panel equivalence (cyclic shift) only for completeness.

Usage:
    python3 scripts/verify_issue48_intrinsic_admissibility.py            # verify + search
    python3 scripts/verify_issue48_intrinsic_admissibility.py --search   # search only
"""
from __future__ import annotations

import argparse
import itertools
from collections import defaultdict
from fractions import Fraction

ALPHABETS = {
    2: "AB",
    3: "ABC",
}


# --------------------------------------------------------------------------
# Circular words and windows
# --------------------------------------------------------------------------
def windows(word, L):
    """Multiset (dict) of circular length-L windows of `word`."""
    n = len(word)
    d = defaultdict(int)
    for i in range(n):
        d[tuple(word[(i + j) % n] for j in range(L))] += 1
    return dict(d)


def observed(word, starts, L):
    d = defaultdict(int)
    n = len(word)
    for r in starts:
        d[tuple(word[(r + j) % n] for j in range(L))] += 1
    return dict(d)


def covered(word, starts, L):
    n = len(word)
    cov = set()
    for r in starts:
        for o in range(L):
            cov.add((r + o) % n)
    return len(cov) == n


# --------------------------------------------------------------------------
# Source repeat structures (Bresler et al.)
# --------------------------------------------------------------------------
def maximal_pairs(word):
    """All (ell, (t1,t2), word) maximal repeat pairs (both sides differ)."""
    n = len(word)
    out = []
    for ell in range(1, n):
        groups = defaultdict(list)
        for i in range(n):
            groups[tuple(word[(i + j) % n] for j in range(ell))].append(i)
        for w, ts in groups.items():
            for a, b in itertools.combinations(ts, 2):
                if word[(a - 1) % n] != word[(b - 1) % n] and \
                   word[(a + ell) % n] != word[(b + ell) % n]:
                    out.append((ell, (a, b), w))
    return out


def triple_repeats(word):
    """All (ell, (t1,t2,t3), word) with three-copy maximality."""
    n = len(word)
    out = []
    for ell in range(1, n):
        groups = defaultdict(list)
        for i in range(n):
            groups[tuple(word[(i + j) % n] for j in range(ell))].append(i)
        for w, ts in groups.items():
            for tri in itertools.combinations(ts, 3):
                pres = {word[(t - 1) % n] for t in tri}
                posts = {word[(t + ell) % n] for t in tri}
                if len(pres) > 1 and len(posts) > 1:
                    out.append((ell, tuple(sorted(tri)), w))
    return out


def interleaved_pairs(word):
    """Pairs of maximal repeat pairs with four starts alternating cyclically."""
    reps = maximal_pairs(word)
    out = []
    for i in range(len(reps)):
        for j in range(i + 1, len(reps)):
            e1, p1, w1 = reps[i]
            e2, p2, w2 = reps[j]
            four = sorted(set(p1) | set(p2))
            if len(four) != 4:
                continue
            labels = [0 if p in p1 else 1 for p in four]
            if labels in ([0, 1, 0, 1], [1, 0, 1, 0]):
                out.append((reps[i], reps[j]))
    return out


# --------------------------------------------------------------------------
# Bridging (strict two-sided extension on an integer lift)
# --------------------------------------------------------------------------
def copy_bridged(word, starts, t, ell, L):
    n = len(word)
    for r in starts:
        for m in range(-3, 4):
            rp = r + m * n
            if rp < t and t + ell < rp + L:
                return True
    return False


def check_I_s(word, starts, L, verbose=False):
    """Full source I_s: coverage, all-bridged triples, bridged interleaved."""
    n = len(word)
    if not covered(word, starts, L):
        if verbose:
            print("  coverage FAIL")
        return False
    for ell, tri, w in triple_repeats(word):
        for t in tri:
            if not copy_bridged(word, starts, t, ell, L):
                if verbose:
                    print(f"  triple {w}@{tri} copy {t} unbridged")
                return False
    for (e1, p1, w1), (e2, p2, w2) in interleaved_pairs(word):
        b1 = any(copy_bridged(word, starts, t, e1, L) for t in p1)
        b2 = any(copy_bridged(word, starts, t, e2, L) for t in p2)
        if not (b1 or b2):
            if verbose:
                print(f"  interleaved {w1}@{p1}||{w2}@{p2} unbridged")
            return False
    return True


# --------------------------------------------------------------------------
# Candidate-intrinsic predicates
# --------------------------------------------------------------------------
def strong_admissible(word, L):
    """No (L-1)-mer occurs twice."""
    return all(v <= 1 for v in windows(word, L - 1).values())


def weak_admissible(word, L):
    """Full-read-set I_s shadow (triple length <= L-2, some interleaved leg <= L-2)."""
    for ell, _tri, _w in triple_repeats(word):
        if ell > L - 2:
            return False
    for (e1, _p1, _w1), (e2, _p2, _w2) in interleaved_pairs(word):
        if min(e1, e2) > L - 2:
            return False
    return True


def primitive(word):
    n = len(word)
    for p in range(1, n):
        if n % p == 0 and word == word[:p] * (n // p):
            return False
    return True


# --------------------------------------------------------------------------
# Exact likelihood ratios
# --------------------------------------------------------------------------
def ratio_free(S, D, obs):
    """Free candidate length: candidate-intrinsic N(D)."""
    nS, nD = len(S), len(D)
    dS, dD = windows(S, len(next(iter(obs)))), windows(D, len(next(iter(obs))))
    r = Fraction(1)
    for w, x in obs.items():
        if dS.get(w, 0) == 0:
            raise ValueError("observed type absent from truth")
        if dD.get(w, 0) == 0:
            return Fraction(0)
        r *= Fraction(nS * dD[w], nD * dS[w]) ** x
    return r


def ratio_fixed(S, D, obs):
    """Fixed common candidate length: no length factor."""
    L = len(next(iter(obs)))
    dS, dD = windows(S, L), windows(D, L)
    r = Fraction(1)
    for w, x in obs.items():
        if dS.get(w, 0) == 0:
            raise ValueError("observed type absent from truth")
        if dD.get(w, 0) == 0:
            return Fraction(0)
        r *= Fraction(dD[w], dS[w]) ** x
    return r


# --------------------------------------------------------------------------
# Verification of named witnesses
# --------------------------------------------------------------------------
def verify(name, S, D, starts, L, intrinsic="STRONG", expect_free=None):
    """Verify one witness and return the coherent-refutation certificate.

    The certificate is the conjunction actually used by the negative theorem:
    truth realizes I_s, truth is primitive and WEAK-admissible (so it belongs
    to the source-shadow candidate class), the competitor is primitive and
    STRONG-admissible, and the free-length ratio is > 1.
    """
    S, D = list(S), list(D)
    obs = observed(S, starts, L)
    ok_Is = check_I_s(S, starts, L, verbose=True)
    print(f"=== {name} ===")
    print(f"S={''.join(S)} G={len(S)}  D={''.join(D)} n={len(D)}  L={L}  starts={starts}")
    print(f"observed = {obs}")
    print(f"truth primitive        = {primitive(S)}")
    print(f"truth STRONG           = {strong_admissible(S, L)}")
    print(f"truth WEAK             = {weak_admissible(S, L)}")
    print(f"truth I_s(S,starts)    = {ok_Is}")
    print(f"candidate primitive    = {primitive(D)}")
    print(f"candidate STRONG       = {strong_admissible(D, L)}")
    print(f"candidate WEAK         = {weak_admissible(D, L)}")
    rf = ratio_free(S, D, obs)
    print(f"free-length  ratio D/S = {rf}  (>1: {rf > 1})")
    if len(S) == len(D):
        print(f"fixed-length ratio D/S = {ratio_fixed(S, D, obs)}")
    if expect_free is not None:
        assert rf == expect_free, (rf, expect_free)
    print()
    return (ok_Is and primitive(S) and weak_admissible(S, L) and
            primitive(D) and strong_admissible(D, L) and rf > 1)


# --------------------------------------------------------------------------
# Exhaustive search
# --------------------------------------------------------------------------
def all_words(alpha, n):
    return [list(w) for w in itertools.product(alpha, repeat=n)]


def search(alpha, maxG, maxL, maxN, require_strong=True, require_primitive=True,
           require_truth_strong=False):
    """Search for coherent free-length counterexamples (bounded exhaustive).

    Returns list of (G, L, S, starts, D, ratio) with S I_s-feasible for
    `starts`, S primitive + WEAK-admissible (and STRONG-admissible if
    `require_truth_strong`), D primitive + STRONG-admissible, and
    ratio_free(S, D) > 1.
    """
    hits = []
    # Candidate pool: primitive STRONG-admissible words of every length, with
    # their L-spectra memoized per L.
    cand_cache = {}

    def candidates(L):
        if L in cand_cache:
            return cand_cache[L]
        pool = []
        for nD in range(L, maxG + 1):
            for D in all_words(alpha, nD):
                if require_primitive and not primitive(D):
                    continue
                if not strong_admissible(D, L):
                    continue
                pool.append((D, windows(D, L)))
        cand_cache[L] = pool
        return pool

    for L in range(2, maxL + 1):
        pool = candidates(L)
        for G in range(L, maxG + 1):
            for S in all_words(alpha, G):
                if require_primitive and not primitive(S):
                    continue
                if not weak_admissible(S, L):
                    continue
                if require_truth_strong and not strong_admissible(S, L):
                    continue
                dS = windows(S, L)
                for N in range(L, maxN + 1):
                    for starts in itertools.combinations_with_replacement(range(G), N):
                        if not check_I_s(S, starts, L):
                            continue
                        obs = observed(S, starts, L)
                        for D, dD in pool:
                            nD = len(D)
                            r = Fraction(1)
                            for w, x in obs.items():
                                if dD.get(w, 0) == 0:
                                    r = Fraction(0)
                                    break
                                r *= Fraction(G * dD[w], nD * dS[w]) ** x
                            if r > 1:
                                hits.append((G, L, ''.join(S), starts,
                                             ''.join(D), r))
    # de-duplicate on the essential tuple
    return list(dict.fromkeys(hits))


def smallest_report(hits, key):
    if not hits:
        print("  no hits")
        return
    hits = sorted(hits, key=key)
    G, L, S, starts, D, r = hits[0]
    print(f"  smallest by {key.__name__}: G={G} L={L} S={S} starts={starts} "
          f"D={D} ratio={r}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--search", action="store_true")
    ap.add_argument("--maxG", type=int, default=6)
    ap.add_argument("--maxL", type=int, default=3)
    ap.add_argument("--maxN", type=int, default=4)
    args = ap.parse_args()

    # Smallest possible coherent free-length witness under the WEAK (source
    # I_s shadow) universe: truth AAB is primitive + WEAK and realizes I_s;
    # competitor AB is primitive + STRONG and strictly more likely.
    ok = verify("minimal WEAK-universe witness (G=3, L=2)", "AAB", "AB",
                [1, 2], 2, "WEAK", Fraction(9, 4))
    # Minimal coherent witness with both truth and competitor primitive and
    # STRONG-admissible (the strongest intrinsic form), two reads.
    ok &= verify("minimal STRONG coherent witness", "AABB", "AAB", [0, 3], 3,
                 "STRONG", Fraction(16, 9))
    # Same minimal STRONG instance with three reads (larger margin 64/27).
    ok &= verify("minimal STRONG coherent witness (3 reads)", "AABB", "AAB",
                 [0, 0, 3], 3, "STRONG", Fraction(64, 27))
    # Issue #48 comment-1 headline witness.
    ok &= verify("issue #48 headline STRONG witness", "AABBC", "AABC", [0, 3], 3,
                 "STRONG", Fraction(25, 16))
    # Non-vacuous I_s truth (bridged triple + bridged interleaved pair).
    ok &= verify("non-vacuous I_s (ABACABC->ABAC)", "ABACABC", "ABAC",
                 [1, 1, 1, 3, 6], 3, "STRONG", None)

    if args.search:
        print("=" * 64)
        print("Exhaustive search (free length, exact arithmetic)")
        for alpha in ("AB", "ABC"):
            print(f"-- alphabet {alpha}, maxG={args.maxG}, maxL={args.maxL}, maxN={args.maxN}")
            hits = search(alpha, args.maxG, args.maxL, args.maxN)
            print(f"   coherent (truth WEAK) hits: {len(hits)}")
            smallest_report(hits, lambda h: (h[0], len(h[4]), h[1]))
            hits2 = search(alpha, args.maxG, args.maxL, args.maxN,
                           require_truth_strong=True)
            print(f"   coherent (truth STRONG) hits: {len(hits2)}")
            smallest_report(hits2, lambda h: (h[0], len(h[4]), h[1]))
    print("all checks passed:", ok)


if __name__ == "__main__":
    main()
