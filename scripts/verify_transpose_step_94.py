#!/usr/bin/env python3
"""Breadth evidence for front 94transpose (Board 94, one-step transposition lemma).

Checks, over binary words, two claims that the Lean module
`AssemblyP1/Issue94TransposePreserve.lean` states:

  (1) the POSITIVE lemma: transposing two starts that spell the same
      `(L-1)`-mer preserves `VertexCycleEq` to the truth;
  (2) the REFUTED formulation: transposing two DISTINCT starts need not
      preserve `VertexCycleEq`.

The Lean statements are the evidence; this script is a search over a finite
slice (binary alphabets, `K <= 6`, `L <= 4`) and proves nothing about
minimality beyond that slice.  Definitions mirror
`BBTEulerian.VertexCycleEq` (`Ex`-rotation of the pointwise `(L-1)`-mer reading)
and `BBTChords.rotAdd`.
"""
import itertools
import sys


def rot(k, K, x):
    return (x + k) % K


def vtx(S, L, i):
    K = len(S)
    return tuple(S[(i + j) % K] for j in range(L - 1))


def VCE(S, L, perm, perm2):
    """`VertexCycleEq perm perm2`: some shift k makes the readings agree."""
    K = len(S)
    return any(all(vtx(S, L, perm[i]) == vtx(S, L, rot(k, K, perm2[i]))
                   for i in range(K))
               for k in range(K))


def swap(perm, a, b):
    out = list(perm)
    for i, v in enumerate(perm):
        if v == a:
            out[i] = b
        elif v == b:
            out[i] = a
    return out


def interlaces(a, b, K):
    """Do `a` and `b` alternate on the circle of `K` starts?"""
    if a == b:
        return False
    x = (a + 1) % K
    while x != a:
        if x == b:
            return True
        x = (x + 1) % K
    return False


def main():
    positive_failures = []
    negative_witnesses = []
    for K in range(2, 7):
        for L in range(2, min(K, 4) + 1):
            for S in itertools.product(range(2), repeat=K):
                for perm in itertools.permutations(range(K)):
                    if not VCE(S, L, list(perm), list(range(K))):
                        continue
                    for a, b in itertools.combinations(range(K), 2):
                        q = swap(perm, a, b)
                        same = vtx(S, L, a) == vtx(S, L, b)
                        holds = VCE(S, L, q, list(range(K)))
                        if same and not holds:
                            positive_failures.append((K, L, S, perm, a, b))
                        if (not same) and (not holds) and interlaces(a, b, K):
                            negative_witnesses.append((K, L, ''.join(map(str, S)),
                                                      perm, (a, b)))
    print("violations of the POSITIVE lemma (equal-mers transposition):",
          len(positive_failures))
    print("witnesses against the DISTINCT-points formulation:", len(negative_witnesses))
    for w in negative_witnesses[:5]:
        print("  ", w)
    return 1 if positive_failures else 0


if __name__ == "__main__":
    sys.exit(main())
