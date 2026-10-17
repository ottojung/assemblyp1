#!/usr/bin/env python3
"""Independent exact verifier for the corrected oriented-strand §6.2 source model (#261).

This is an implementation-independent re-derivation of the palindrome
representation defect and its repair, in exact integer arithmetic.  It does not
import Lean; it re-implements the historical `overlapEdges` / `bdEdge` /
`throughput` / `balCore` constructions and the corrected oriented-strand model
`AssemblyP1.Section62OrientedStrandFlow`, then checks the claims that the Lean
module kernel-checks.

Claim under audit: for an RC-palindromic molecule the historical model
(`strandsOf rc verts = verts ++ verts.map rc`, signs from `sgnRep`/`sgnTgt` on
the *word*) collapses both physical orientations to a single edge value with a
single sign pair, so a one-copy candidate is over-counted (throughput 4).  The
corrected model, which keeps an explicit orientation bit separate from the word
and derives signs from that bit, has four distinct edges with all four sign pairs
and counts a one-copy candidate once.  On non-palindromic classes the two models
agree.

Exit status is non-zero on any failed assertion.
"""

from __future__ import annotations

import sys
from itertools import product

# ---------------------------------------------------------------------------
# Words are tuples of booleans; Watson-Crick complement is `not`.
# ---------------------------------------------------------------------------


def rc(w: tuple) -> tuple:
    return tuple(not b for b in reversed(w))


def code(w: tuple) -> int:
    a = 0
    for b in w:
        a = a * 2 + (1 if b else 0)
    return a


def rep(w: tuple) -> tuple:
    return w if code(w) <= code(rc(w)) else rc(w)


def suf(w: tuple, l: int) -> tuple:
    return w[len(w) - l:] if l else ()


def pre(w: tuple, l: int) -> tuple:
    return w[:l]


# ---------------------------------------------------------------------------
# Historical model: strand = word; signs from word equality with the class rep.
# ---------------------------------------------------------------------------


def sgn_rep(s: tuple, mx: tuple) -> int:
    return 1 if s == mx else -1


def sgn_tgt(s: tuple, my: tuple) -> int:
    return -1 if s == my else 1


def strands_of(rcfun, verts):
    return list(verts) + [rcfun(v) for v in verts]


def historical_edges(rcfun, repfun, read_len: int, o_min: int, verts):
    edges = []
    for l in range(read_len):
        if l < o_min:
            continue
        for sx in strands_of(rcfun, verts):
            for sy in strands_of(rcfun, verts):
                if suf(sx, l) == pre(sy, l):
                    edges.append(
                        (sx, sy, l, sgn_rep(sx, repfun(sx)), sgn_tgt(sy, repfun(sy)))
                    )
    return edges


# ---------------------------------------------------------------------------
# Corrected model: strand = (class representative, orientation bit); the word is
# recovered from the bit; signs are derived from the bit.
# ---------------------------------------------------------------------------


def word(rcfun, s) -> tuple:
    cls, bit = s
    return rcfun(cls) if bit else cls


def dep_sign(s) -> int:
    return -1 if s[1] else 1


def arr_sign(s) -> int:
    return 1 if s[1] else -1


def oriented_strands(verts):
    return [(v, False) for v in verts] + [(v, True) for v in verts]


def corrected_edges(rcfun, read_len: int, o_min: int, verts):
    edges = []
    for l in range(read_len):
        if l < o_min:
            continue
        for sx in oriented_strands(verts):
            for sy in oriented_strands(verts):
                if suf(word(rcfun, sx), l) == pre(word(rcfun, sy), l):
                    edges.append((sx, sy, l, dep_sign(sx), arr_sign(sy)))
    return edges


# ---------------------------------------------------------------------------
# Throughput / balance over an edge list (foldr semantics), keyed by edge value.
# ---------------------------------------------------------------------------


def throughput(repfun, flow, edges, v) -> int:
    total = 0
    for (sx, sy, l, gx, gy) in edges:
        if repfun(sx) == v:
            total += flow((sx, sy, l, gx, gy))
    return total


def bal_core(repfun, flow, edges, v) -> int:
    total = 0
    for (sx, sy, l, gx, gy) in edges:
        if repfun(sx) == v:
            total += flow((sx, sy, l, gx, gy)) * gx
        if repfun(sy) == v:
            total += flow((sx, sy, l, gx, gy)) * gy
    return total


# ---------------------------------------------------------------------------
# Witnesses
# ---------------------------------------------------------------------------

PAL4 = (True, False, True, False)  # ATAT
NP3 = (True, False, False)  # ATT


def main() -> int:
    checks = 0

    def check(cond, msg):
        nonlocal checks
        checks += 1
        if not cond:
            print(f"FAIL: {msg}")
            sys.exit(1)
        print(f"ok: {msg}")

    # 0. The palindrome is an RC fixed point; the non-palindrome is not.
    check(rc(PAL4) == PAL4, "ATAT is an RC-palindrome (rc w = w)")
    check(rc(NP3) != NP3, "ATT is not an RC-palindrome")
    check(rep(PAL4) == PAL4, "rep(ATAT) = ATAT")

    # 1. Historical strand enumeration of a palindrome repeats the word.
    check(strands_of(rc, [PAL4]) == [PAL4, PAL4],
          "historical strandsOf on a palindrome repeats the single word")

    # 2. Historical graph on the palindrome: four identical edge values, one sign pair.
    hist_pal = historical_edges(rc, rep, 4, 2, [PAL4])
    check(len(hist_pal) == 4, "historical palindrome graph has 4 list entries")
    check(len(set(hist_pal)) == 1,
          "historical palindrome graph has exactly ONE distinct edge value")
    check({(e[3], e[4]) for e in hist_pal} == {(1, -1)},
          "historical palindrome sign pairs collapse to a single pair (+1,-1)")

    # 3. Corrected graph on the palindrome: four distinct edges, all four sign pairs.
    corr_pal = corrected_edges(rc, 4, 2, [PAL4])
    check(len(corr_pal) == 4, "corrected palindrome graph has 4 edges")
    check(len(set(corr_pal)) == 4,
          "corrected palindrome graph edges are pairwise distinct")
    check({(e[3], e[4]) for e in corr_pal} == {(1, -1), (1, 1), (-1, -1), (-1, 1)},
          "corrected palindrome sign pairs are all four combinations")
    check(all(word(rc, e[0]) == PAL4 and word(rc, e[1]) == PAL4 for e in corr_pal),
          "corrected palindrome edges all carry the palindrome word")

    # 4. Throughput of the one-copy candidate: 4 (historical) vs 1 (corrected).
    hist_edge = hist_pal[0]
    unit_hist = lambda e: 1 if e == hist_edge else 0
    check(throughput(rep, unit_hist, hist_pal, PAL4) == 4,
          "historical throughput of one unit of the shared edge value is 4")

    self_loop = ((PAL4, False), (PAL4, False), 2, 1, -1)
    unit_tag = lambda e: 1 if e == self_loop else 0
    check(throughput(lambda s: (s[0], False), unit_tag, corr_pal, (PAL4, False)) == 1,
          "corrected throughput of the one-copy palindrome self-loop is 1")
    check(bal_core(lambda s: (s[0], False), unit_tag, corr_pal, (PAL4, False)) == 0,
          "corrected one-copy palindrome self-loop is balanced")

    # 5. Non-palindrome: the two models agree, in count, signs, and words.
    hist_np = historical_edges(rc, rep, 3, 2, [NP3])
    corr_np = corrected_edges(rc, 3, 2, [NP3])
    check(len(hist_np) == len(corr_np),
          "non-palindrome: historical and corrected edge counts agree")
    check(sorted((e[3], e[4]) for e in hist_np)
          == sorted((e[3], e[4]) for e in corr_np),
          "non-palindrome: historical and corrected sign pairs agree")
    check([(e[0], e[1]) for e in hist_np]
          == [(word(rc, e[0]), word(rc, e[1])) for e in corr_np],
          "non-palindrome: historical edge words equal corrected edge words")
    check(len(set(hist_np)) == len(hist_np),
          "non-palindrome: historical graph is already duplicate-free")

    print(f"\nAll {checks} checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
