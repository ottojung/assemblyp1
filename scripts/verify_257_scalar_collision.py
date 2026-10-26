#!/usr/bin/env python3
"""Issue #257: scalar topology summaries do not determine rigidity.

Self-contained, exact integer arithmetic, deterministic, no repository
imports. Narrow scope (three fixed genomes, no census sweep):

1. Two genuine circular-word read supports share the SAME scalar summary
   (L=3, G=7, |V|=3, |E|=4, cycle rank 2) but differ in rigidity:
     - S = AABABAB is RIGID;
     - S = AAAAAAB is NON-RIGID (explicit alternative circulation witness).
   So no function of (|V|, |E|, rank) at fixed (L, G) -- even with the
   alphabet fixed -- decides rigidity. This separates scalar topology
   summaries from the exact box criterion (Theorem 1), complementing the
   merged bouquet/bridge/multi-hub family criteria without re-running them.
2. Controls: S = ATATAT (L=3) is a rigid directed 2-cycle despite triple
   (L-1)-mer repeats; S = AATT (L=2, G=4) is rigid on a rank-2 support at
   all-ones multiplicities, and non-rigid at A=(2,1,1,1) -- so the same
   support flips with multiplicities (topology vs multiplicity split).

Exit 0 iff every expectation holds; nonzero otherwise.
"""

from __future__ import annotations


def positive_compositions(total: int, parts: int):
    if parts == 1:
        if total >= 1:
            yield (total,)
        return
    for first in range(1, total - parts + 2):
        for rest in positive_compositions(total - first, parts - 1):
            yield (first,) + rest


def spectrum_circular(word: str, ell: int) -> dict:
    n = len(word)
    ext = word + word[: ell - 1]
    counts: dict = {}
    for i in range(n):
        wmer = ext[i : i + ell]
        counts[wmer] = counts.get(wmer, 0) + 1
    return counts


def support_equations(edges: list):
    verts = sorted({e[:-1] for e in edges} | {e[1:] for e in edges})
    eqs = []
    for v in verts:
        out = [i for i, e in enumerate(edges) if e[:-1] == v]
        inn = [i for i, e in enumerate(edges) if e[1:] == v]
        eqs.append((out, inn))
    return verts, eqs


def all_positive_circulations(edges: list, eqs, total: int) -> list:
    good = []
    for vals in positive_compositions(total, len(edges)):
        if all(sum(vals[i] for i in out) == sum(vals[i] for i in inn)
               for out, inn in eqs):
            good.append(vals)
    return good


def analyze(word: str, ell: int):
    spec = spectrum_circular(word, ell)
    edges = sorted(spec)
    verts, eqs = support_equations(edges)
    counts = tuple(spec[e] for e in edges)
    cands = all_positive_circulations(edges, eqs, len(word))
    rank = len(edges) - len(verts) + 1  # connected circular-word support
    return {
        "word": word, "L": ell, "G": len(word),
        "V": len(verts), "E": len(edges), "rank": rank,
        "spectrum": spec, "A": counts,
        "rigid": cands == [counts], "candidates": cands,
    }


def main() -> int:
    fails = 0

    pair = [analyze("AABABAB", 3), analyze("AAAAAAB", 3)]
    for r in pair:
        print(f"{r['word']}: spectrum={r['spectrum']} "
              f"(L,G,|V|,|E|,rank)={(r['L'], r['G'], r['V'], r['E'], r['rank'])} "
              f"rigid={r['rigid']} candidates={r['candidates']}")
    keys = [(r["L"], r["G"], r["V"], r["E"], r["rank"]) for r in pair]
    if keys[0] != keys[1]:
        print(f"FAIL: expected identical scalar summaries, got {keys}")
        fails += 1
    if pair[0]["rigid"] is not True:
        print("FAIL: AABABAB should be rigid")
        fails += 1
    if pair[1]["rigid"] is not False:
        print("FAIL: AAAAAAB should be non-rigid")
        fails += 1
    alt = [c for c in pair[1]["candidates"] if c != pair[1]["A"]]
    if not alt:
        print("FAIL: non-rigid AAAAAAB has no alternative circulation")
        fails += 1
    else:
        print(f"AAAAAAB alternative witness: A={pair[1]['A']} B={alt[0]}")

    # A second, non-rotationally-equivalent pair at a different genome length.
    # This prevents the first scalar collision from being a one-off example.
    pair8 = [analyze("AABAABAB", 3), analyze("AAAAAAAB", 3)]
    for r in pair8:
        print(f"{r['word']}: spectrum={r['spectrum']} "
              f"(L,G,|V|,|E|,rank)={(r['L'], r['G'], r['V'], r['E'], r['rank'])} "
              f"rigid={r['rigid']} candidates={r['candidates']}")
    keys8 = [(r["L"], r["G"], r["V"], r["E"], r["rank"]) for r in pair8]
    if keys8[0] != keys8[1] or keys8[0] != (3, 8, 3, 4, 2):
        print(f"FAIL: expected second shared summary (3,8,3,4,2), got {keys8}")
        fails += 1
    if pair8[0]["rigid"] is not True or pair8[1]["rigid"] is not False:
        print("FAIL: AABAABAB / AAAAAAAB should be rigid / non-rigid")
        fails += 1
    alt8 = [c for c in pair8[1]["candidates"] if c != pair8[1]["A"]]
    if (2, 2, 2, 2) not in alt8:
        print("FAIL: expected AAAAAAAB alternative circulation (2,2,2,2)")
        fails += 1
    # Explicitly distinguish the circular genomes up to rotation.
    def rotations(word: str):
        return {word[i:] + word[:i] for i in range(len(word))}
    if rotations(pair8[0]["word"]) & rotations(pair8[1]["word"]):
        print("FAIL: second pair should not be rotations of the same genome")
        fails += 1

    atat = analyze("ATATAT", 3)
    print(f"ATATAT: spectrum={atat['spectrum']} rigid={atat['rigid']}")
    if atat["rigid"] is not True or atat["spectrum"] != {"ATA": 3, "TAT": 3}:
        print("FAIL: ATATAT control mismatch")
        fails += 1

    aatt = analyze("AATT", 2)
    print(f"AATT: spectrum={aatt['spectrum']} rank={aatt['rank']} "
          f"rigid={aatt['rigid']}")
    if aatt["rigid"] is not True or aatt["rank"] != 3:
        print("FAIL: AATT control mismatch (expect rigid, rank 3)")
        fails += 1
    # Multiplicity-flip control on the AATT support (not a circular spectrum).
    edges = ["AA", "AT", "TA", "TT"]
    _, eqs = support_equations(edges)
    cands = all_positive_circulations(edges, eqs, 5)
    mut_rigid = cands == [(2, 1, 1, 1)]
    print(f"AATT support A=(2,1,1,1) G=5: rigid={mut_rigid} "
          f"candidates={cands}")
    if mut_rigid or len(cands) < 2:
        print("FAIL: mutated AATT support should be non-rigid")
        fails += 1

    if fails:
        print(f"RESULT: {fails} FAILURES")
        return 1
    print("RESULT: all scalar-collision checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
