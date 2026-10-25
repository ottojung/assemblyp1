#!/usr/bin/env python3
"""Issue #257, section 22.5: AABAABB rigid repetitive cell (rank 2, non-cycle).

Self-contained, exact integer arithmetic, deterministic. Re-derives from
scratch (no repository imports):

1. Circular S = AABAABB, L = 3 has spectrum
   {AAB:2, ABA:1, BAA:2, ABB:1, BBA:1} (G = 7), support |V| = 4, |E| = 5,
   cycle rank |E|-|V|+c = 2 (zero-sum rank r = 1). It is NOT a single
   directed cycle, yet exact enumeration finds exactly ONE positive
   balanced circulation of total 7: (2,1,2,1,1) in spectrum order.
2. The support is over-constrained nearby: G = 6 and G = 8 admit ZERO
   positive balanced circulations, so the harness discriminates (unique
   rigid point, not a vacuous family).
3. Repeat note: (L-1)-mers AA/AB/BA each occur twice in S, so this rigid
   cell again refutes "no repeated (L-1)-mer" necessity beyond ATATAT/AABABAB.
4. Topology note: same cycle rank 2 as the AABABAB/AAAAAAB pair
   (|V|=3,|E|=4) but different (|V|,|E|) = (4,5) and rigid -- rigidity is
   not a function of rank alone.
"""

from __future__ import annotations

from itertools import product


def spectrum_circular(s: str, L: int) -> dict:
    n = len(s)
    t = s + s[: L - 1]
    d: dict = {}
    for i in range(n):
        w = t[i : i + L]
        d[w] = d.get(w, 0) + 1
    return d


def balanced(wit, eqs) -> bool:
    return all(
        sum(wit[i] for i in out) == sum(wit[i] for i in inn) for out, inn in eqs
    )


def main() -> int:
    fails = 0
    sp = spectrum_circular("AABAABB", 3)
    expected = {"AAB": 2, "ABA": 1, "BAA": 2, "ABB": 1, "BBA": 1}
    print(f"AABAABB L=3 spectrum: {sp}")
    if sp != expected:
        print("FAIL: AABAABB spectrum mismatch")
        fails += 1
    es = list(sp)
    vs = sorted({e[:-1] for e in es} | {e[1:] for e in es})
    outs = [[i for i, e in enumerate(es) if e[:-1] == v] for v in vs]
    ins = [[i for i, e in enumerate(es) if e[1:] == v] for v in vs]
    eqs = list(zip(outs, ins))
    print(f"support |V|={len(vs)} |E|={len(es)} rank={len(es)-len(vs)+1} vs={vs}")
    if (len(vs), len(es)) != (4, 5):
        print("FAIL: unexpected support shape")
        fails += 1
    counts = [sp[e] for e in es]
    for G in (6, 7, 8):
        wit = [
            vals
            for vals in product(range(1, G + 1), repeat=len(es))
            if sum(vals) == G and balanced(vals, eqs)
        ]
        print(f"G={G}: n={len(wit)} {wit[:4]}")
        if G == 7 and wit != [tuple(counts)]:
            print("FAIL: G=7 should have the unique genome witness")
            fails += 1
        if G in (6, 8) and wit:
            print(f"FAIL: G={G} should admit no positive circulation")
            fails += 1
    # repeat note: (L-1)-mer multiplicities in S
    lm = {}
    s = "AABAABB"
    for i in range(len(s)):
        w = (s + s[:1])[i : i + 2]
        lm[w] = lm.get(w, 0) + 1
    print(f"(L-1)-mer mults: {lm}")
    if not any(v >= 2 for v in lm.values()):
        print("FAIL: expected repeated (L-1)-mers")
        fails += 1
    if fails:
        print(f"RESULT: {fails} FAILURES")
        return 1
    print("RESULT: section-22.5 AABAABB checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
