#!/usr/bin/env python3
"""
Self-contained independent verifier for fixed-length exact-ML counterexamples.

This deliberately re-implements the source repeat/bridging semantics from
docs/bridging-source-semantics.md instead of importing the reviewed search
script, so that agreement is independent evidence.

Checks, for a witness (truth S, read length L, latent starts, competitor D):
  1. coverage of S by the reads;
  2. every maximal triple repeat of S is all-bridged;
  3. every interleaved pair of maximal repeat pairs of S is bridged;
  4. every observed read type has positive occurrence in both S and D;
  5. len(S) == len(D) == fixed candidate length;
  6. exact rational likelihood ratio > 1.

Usage: python3 verify_interleaved_counterexample.py
"""
from fractions import Fraction
from itertools import combinations
from collections import defaultdict


def win(seq, t, ell, G):
    return tuple(seq[(t + j) % G] for j in range(ell))


def spectrum(seq, L):
    G = len(seq)
    d = defaultdict(int)
    for i in range(G):
        d[win(seq, i, L, G)] += 1
    return dict(d)


def covered(seq, starts, L):
    G = len(seq)
    cov = set()
    for r in starts:
        for o in range(L):
            cov.add((r + o) % G)
    return len(cov) == G, cov


def reads(seq, starts, L):
    """Observed read multiset as counts keyed by read string."""
    G = len(seq)
    obs = defaultdict(int)
    for r in starts:
        obs[win(seq, r, L, G)] += 1
    return dict(obs)


def maximal_pairs(seq):
    """All (ell, (t1,t2), word) maximal repeat pairs, one per unordered pair."""
    G = len(seq)
    out = []
    for ell in range(1, G):
        groups = defaultdict(list)
        for i in range(G):
            groups[win(seq, i, ell, G)].append(i)
        for w, ts in groups.items():
            for a, b in combinations(ts, 2):
                # maximal on both sides (source: preceding symbols differ,
                # following symbols differ)
                if seq[(a - 1) % G] != seq[(b - 1) % G] and \
                   seq[(a + ell) % G] != seq[(b + ell) % G]:
                    out.append((ell, (a, b), w))
    return out


def triple_repeats(seq):
    """All (ell, (t1,t2,t3), word) with three-copy maximality."""
    G = len(seq)
    out = []
    for ell in range(1, G):
        groups = defaultdict(list)
        for i in range(G):
            groups[win(seq, i, ell, G)].append(i)
        for w, ts in groups.items():
            for tri in combinations(ts, 3):
                pres = [seq[(t - 1) % G] for t in tri]
                posts = [seq[(t + ell) % G] for t in tri]
                if len(set(pres)) > 1 and len(set(posts)) > 1:
                    out.append((ell, tuple(sorted(tri)), w))
    return out


def copy_bridged(seq, starts, t, ell, L):
    """Source: read strictly extends beyond the copy on both sides."""
    G = len(seq)
    return any((t - 1) % G in {(r + o) % G for o in range(L)}
               and (t + ell) % G in {(r + o) % G for o in range(L)}
               for r in starts)


def interleaved_pairs(seq):
    reps = maximal_pairs(seq)
    out = []
    for i in range(len(reps)):
        for j in range(i + 1, len(reps)):
            e1, p1, w1 = reps[i]
            e2, p2, w2 = reps[j]
            four = sorted(set(p1) | set(p2))
            if len(four) != 4:
                continue
            labels = []
            for p in four:
                labels.append(0 if p in p1 else 1)
            if labels in ([0, 1, 0, 1], [1, 0, 1, 0]):
                out.append((reps[i], reps[j]))
    return out


def check_I_s(seq, starts, L, verbose=True):
    G = len(seq)
    ok_cov, cov = covered(seq, starts, L)
    if not ok_cov:
        if verbose:
            print(f"  FAIL coverage: {sorted(cov)} != all {G}")
        return False
    for ell, tri, w in triple_repeats(seq):
        for t in tri:
            if not copy_bridged(seq, starts, t, ell, L):
                if verbose:
                    print(f"  FAIL triple repeat {w}@{tri} copy {t} unbridged")
                return False
    for (e1, p1, w1), (e2, p2, w2) in interleaved_pairs(seq):
        b1 = any(copy_bridged(seq, starts, t, e1, L) for t in p1)
        b2 = any(copy_bridged(seq, starts, t, e2, L) for t in p2)
        if not (b1 or b2):
            if verbose:
                print(f"  FAIL interleaved {w1}@{p1} / {w2}@{p2} unbridged")
            return False
    return True


def ratio(S, D, obs):
    dS, dD = spectrum(S, len(next(iter(obs)))), spectrum(D, len(next(iter(obs))))
    r = Fraction(1)
    for w, x in obs.items():
        if dS.get(w, 0) == 0 or dD.get(w, 0) == 0:
            return Fraction(0), dS, dD
        r *= Fraction(dD[w], dS[w]) ** x
    return r, dS, dD


def verify(name, S, D, starts, L):
    print(f"=== {name} ===")
    print(f"S = {S}, D = {D}, L = {L}, starts = {starts}")
    obs = reads(S, starts, L)
    print(f"observed = {obs}")
    print(f"len(S)={len(S)} len(D)={len(D)} same-length={len(S)==len(D)}")
    ok = check_I_s(S, starts, L)
    print(f"I_s (coverage + all-bridged triples + bridged interleaved) = {ok}")
    if not ok:
        return
    r, dS, dD = ratio(S, D, obs)
    print(f"exact likelihood ratio D/S = {r}  (>1: {r > 1})")
    print(f"  dS(observed) = { {w: dS.get(w,0) for w in obs} }")
    print(f"  dD(observed) = { {w: dD.get(w,0) for w in obs} }")
    print(f"  interleaved pairs: ", end="")
    ilv = interleaved_pairs(S)
    print("none" if not ilv else "")
    for (e1, p1, w1), (e2, p2, w2) in ilv:
        b1 = [t for t in p1 if copy_bridged(S, starts, t, e1, L)]
        b2 = [t for t in p2 if copy_bridged(S, starts, t, e2, L)]
        print(f"    {w1}(ell={e1})@{p1} bridged_copies={b1} || "
              f"{w2}(ell={e2})@{p2} bridged_copies={b2}")
    print()


def main():
    # Existing kernel-checked witness (G=5), for cross-validation.
    verify("existing kernel-checked (no interleaved clause)",
           "AAABB", "AAAAB", [0, 1, 4], 3)

    # Minimal interleaved-clause counterexample (same repeated word).
    verify("minimal interleaved clause (same word, G=7, N=4)",
           "AAABACC", "AAAABAC", [0, 1, 3, 6], 3)

    # Minimal interleaved-clause counterexample with two distinct words.
    verify("interleaved clause, distinct words (G=7, N=5)",
           "ABACABC", "ACABACB", [1, 1, 1, 3, 6], 3)

    # Another distinct-word witness.
    verify("interleaved clause, distinct words (G=7, N=7)",
           "ABACABC", "ACABAAB", [0, 0, 0, 1, 1, 3, 6], 3)


if __name__ == "__main__":
    main()
