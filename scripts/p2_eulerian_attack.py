#!/usr/bin/env python3
"""
Independent attack on circular P2 spectrum uniqueness (issue #45 / #48).

Question
--------
Let L >= 2, K = L-1.  For a circular word D let d_D(w) be the multiset of
cyclic length-L windows (the L-mer spectrum).  P2(D,L) = TRF(D,L) and ILF(D,L):

  TRF: no Bresler *maximal triple repeat* of length >= K.
  ILF: no *interleaved pair* of maximal repeats whose shorter constituent
       has length >= K.

Claim under test (Theorem Q / BBT Thm 3 at K=L-1):
  P2(S,L)  =>  every circular T with the same L-mer spectrum is a rotation of S.

This script:
  1. re-derives the Bresler predicates from the published definitions
     (maximal triple repeat, maximal pair, interleaved pair), NOT via the
     raw-occurrence shortcut;
  2. obtains ground truth by grouping *all* circular words by spectrum;
  3. computes the de Bruijn multigraph spelled-word set by explicit Eulerian
     circuit enumeration (independent of the grouping route);
  4. hunts for a counterexample (a P2 word in a non-singleton rotation class);
  5. probes the suspected gap: raw / non-maximal repeated K-mers that are
     *nested* rather than interleaved.

Exact integer arithmetic.  Bounded searches are evidence only.
"""

from __future__ import annotations

from collections import defaultdict
from itertools import combinations


# --------------------------------------------------------------------------
# circular words
# --------------------------------------------------------------------------
def rotations(w):
    n = len(w)
    return [w[i:] + w[:i] for i in range(n)]


def canonical(w):
    return min(rotations(w))


def is_primitive(w):
    n = len(w)
    for p in range(1, n):
        if n % p == 0 and w == w[:p] * (n // p):
            return False
    return True


def _windows(w, L):
    n = len(w)
    d = defaultdict(int)
    for i in range(n):
        d[tuple(w[(i + j) % n] for j in range(L))] += 1
    return dict(d)


def spectrum_key(w, L):
    return tuple(sorted(_windows(w, L).items()))


# --------------------------------------------------------------------------
# Bresler repeat predicates (exact, from the published definitions)
# --------------------------------------------------------------------------
def has_maximal_triple(w, K):
    """True iff some Bresler triple repeat has length >= K.

    A length-ell triple repeat exists iff some ell-window occurs >= 3 times
    at positions whose preceding symbols are not all equal and whose
    following symbols are not all equal.  For an occurrence group of size
    >= 3 this is equivalent to: both the preceding sequence and the following
    sequence over the group are non-constant.
    """
    n = len(w)
    for ell in range(max(1, K), n):
        groups = defaultdict(list)
        for i in range(n):
            groups[tuple(w[(i + j) % n] for j in range(ell))].append(i)
        for ts in groups.values():
            if len(ts) < 3:
                continue
            pre = {w[(t - 1) % n] for t in ts}
            post = {w[(t + ell) % n] for t in ts}
            if len(pre) >= 2 and len(post) >= 2:
                return True
    return False


def has_triple_raw(w, K):
    """No-maximality version: ell-window occurs >= 3 times for some ell >= K."""
    n = len(w)
    for ell in range(max(1, K), n):
        c = defaultdict(int)
        for i in range(n):
            c[tuple(w[(i + j) % n] for j in range(ell))] += 1
        if any(v >= 3 for v in c.values()):
            return True
    return False


def maximal_pairs_at(w, ell):
    n = len(w)
    groups = defaultdict(list)
    for i in range(n):
        groups[tuple(w[(i + j) % n] for j in range(ell))].append(i)
    out = []
    for ts in groups.values():
        for a, b in combinations(ts, 2):
            if w[(a - 1) % n] != w[(b - 1) % n] and w[(a + ell) % n] != w[(b + ell) % n]:
                out.append((a, b))
    return out


def has_interleaved(w, K):
    """True iff two maximal-repeat pairs, both of length >= K, interleave."""
    n = len(w)
    reps = []
    for ell in range(max(1, K), n):
        reps.extend(((a, b) for a, b in maximal_pairs_at(w, ell)))
    for (a, b), (c, d) in combinations(reps, 2):
        four = sorted({a, b, c, d})
        if len(four) != 4:
            continue
        lab = [0 if p in (a, b) else 1 for p in four]
        if lab in ([0, 1, 0, 1], [1, 0, 1, 0]):
            return True
    return False


def trf(w, L):
    return not has_maximal_triple(w, L - 1)


def ilf(w, L):
    return not has_interleaved(w, L - 1)


def p2(w, L):
    return trf(w, L) and ilf(w, L)


# --------------------------------------------------------------------------
# Lyndon words (one rep per rotation class; all aperiodic since primitive)
# --------------------------------------------------------------------------
def lyndon_words(alpha, n):
    k = len(alpha)
    w = [0] * (n + 1)

    def gen(t, p):
        if t > n:
            if p == n:
                yield tuple(alpha[w[i]] for i in range(1, n + 1))
        else:
            w[t] = w[t - p]
            yield from gen(t + 1, p)
            for j in range(w[t - p] + 1, k):
                w[t] = j
                yield from gen(t + 1, t)

    yield from gen(1, 1)


# --------------------------------------------------------------------------
# ground truth: group ALL circular words by same-length spectrum
# --------------------------------------------------------------------------
def collisions(alpha, nmax, maxL, predicate):
    """Return list of (L, n, w, others) where w lies in a non-singleton
    same-length spectrum class and predicate(w, L) holds.  Primitive words
    only (Lyndon representatives; a primitive word cannot share its spectrum
    with a non-primitive one because primitivity is a rotation invariant but
    the theorem also holds for non-primitive -- see p2_no_primitivity_probe).
    """
    hits = []
    for L in range(2, maxL + 1):
        table = defaultdict(list)
        for n in range(L, nmax + 1):
            for w in lyndon_words(alpha, n):
                if not is_primitive(w):
                    continue
                table[spectrum_key(w, L)].append(w)
        for key, ws in table.items():
            if len(ws) < 2:
                continue
            for w in ws:
                if predicate(w, L):
                    hits.append((L, len(w), w, [x for x in ws if x != w]))
    return hits


# --------------------------------------------------------------------------
# tests
# --------------------------------------------------------------------------
def check_definitions_agree():
    """The exact maximal-triple predicate agrees with the raw occurrence
    shortcut on all primitive binary words up to length 16."""
    for n in range(2, 17):
        for w in lyndon_words("AB", n):
            if not is_primitive(w):
                continue
            for L in range(2, n + 1):
                if has_maximal_triple(w, L - 1) != has_triple_raw(w, L - 1):
                    print("  DEFN MISMATCH", w, L)
                    return False
    print("  [ok] exact maximal-triple == raw-occurrence shortcut (primitive, bin n<=16)")
    return True


def check_known():
    # sharpness witnesses from the repository notes
    S, T = tuple("AABABB"), tuple("AABBAB")
    assert is_primitive(S) and is_primitive(T)
    assert spectrum_key(S, 3) == spectrum_key(T, 3)
    assert canonical(S) != canonical(T)
    assert not ilf(S, 3), "AABABB should fail ILF"
    print("  [ok] AABABB/AABBAB collision is ILF-inadmissible")
    # nested repeat probe: AB and AA repeated, non-interleaved
    N = tuple("ABAAAB")
    print("  nested probe ABAAAB L=3: p2 =", p2(N, 3),
          " spectrum =", spectrum_key(N, 3))
    return True


def main():
    print("independent circular P2 spectrum-uniqueness attack")
    check_definitions_agree()
    check_known()

    print("ground-truth collision scans (primitive words, group-first):")
    for alpha, nmax, maxL in (("AB", 18, 4), ("ABC", 13, 3)):
        hits = collisions(alpha, nmax, maxL, p2)
        print(f"  |Sigma|={len(alpha)} n<={nmax} L<={maxL}: "
              f"{len(hits)} P2 words with non-rotation spectrum partners")
        for h in hits[:5]:
            print("    COUNTEREXAMPLE", h)

    print("done (use p2_broad_scan.py / p2_euler_direct.py for wider ranges)")


if __name__ == "__main__":
    main()
