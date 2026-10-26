#!/usr/bin/env python3
"""Issue #257, section 22: directed-cycle sufficiency and the AATT boundary.

Self-contained, exact integer arithmetic, deterministic. Re-derives from
scratch (no repository imports):

1. Directed n-cycle supports (n = 2..6) with uniform multiplicity k = 1..4
   are rigid (balance forces constancy; the total pins the constant).
2. The S = AATT, L = 2 read graph (2 vertices, 4 edges, cycle rank 3, NOT a
   single directed cycle) is rigid at A = (1,1,1,1), G = 4 -- so "single
   directed cycle" is sufficient but NOT necessary (kernel-checked in
   AssemblyP1/RigiditySimpleCycle.lean as `aatt_rigid`).
3. Mutation-red control: the same AATT support at A = (2,1,1,1), G = 5 is
   NON-rigid (witnesses (1,1,2,1)/(1,1,1,2)-style splits), so the harness
   discriminates.
4. Complexity record: decider search space (G+1)^|E| tabulated against the
   zero-sum circulation rank r = |E| - |V| + c - 1.
5. Genome realization: circular S = AATT has L = 2 spectrum
   {AA:1, AT:1, TT:1, TA:1}.
6. A scalar topology summary plus L and G is insufficient: two circular
   L=3, G=7 genomes have |V|=3, |E|=4, cycle rank 2, but differ in rigidity.
7. Exhaustive enumeration of all binary circular genomes with G=1..8 and
   L=2..4, plus a new binary G=1..9, L=2..3 scope and all ternary circular
   genomes with G=1..6 and L=2..3:
   every scope contains scalar-summary groups with both rigid and
   non-rigid genomes, so no scalar summary (|V|,|E|,rank at fixed L,G,
   even with alphabet size fixed) determines rigidity.
"""

from __future__ import annotations

def positive_compositions(total: int, parts: int):
    """Yield positive integer vectors of fixed total without scanning a box."""
    if parts == 1:
        if total >= 1:
            yield (total,)
        return
    for first in range(1, total - parts + 2):
        for rest in positive_compositions(total - first, parts - 1):
            yield (first,) + rest


def spectrum_circular(s: str, L: int) -> dict:
    n = len(s)
    t = s + s[: L - 1]
    d: dict = {}
    for i in range(n):
        w = t[i : i + L]
        d[w] = d.get(w, 0) + 1
    return d


def brute_rigid(edges, balance_eqs, A, G):
    """Exact brute force: all B in [1..G]^m satisfying balance + total.

    edges: list of edge names; balance_eqs: list of (out_idx, in_idx) groups
    as (list_out, list_in) index lists; returns (rigid, witnesses).
    """
    m = len(edges)
    wit = []
    for vals in positive_compositions(G, m):
        ok = True
        for out, inn in balance_eqs:
            if sum(vals[i] for i in out) != sum(vals[i] for i in inn):
                ok = False
                break
        if ok:
            wit.append(vals)
    rigid = wit == [tuple(A)]
    return rigid, wit


def check_cycle(n, k):
    # directed n-cycle: vertex v has out {v}, in {(v-1) % n}
    eqs = [([v], [(v - 1) % n]) for v in range(n)]
    A = [k] * n
    return brute_rigid(list(range(n)), eqs, A, n * k)


def main() -> int:
    fails = 0

    # 1. directed n-cycles rigid at uniform multiplicity
    n_cycle_cases = 0
    for n in range(2, 7):
        for k in range(1, 5):
            rigid, wit = check_cycle(n, k)
            n_cycle_cases += 1
            if not rigid:
                print(f"FAIL: {n}-cycle k={k} not rigid: {wit}")
                fails += 1
    print(f"directed cycles n=2..6, k=1..4: {n_cycle_cases} cases, all rigid")

    # 2. AATT support: edges 0:AA (0->0), 1:AT (0->1), 2:TT (1->1), 3:TA (1->0)
    aatt_eqs = [([0, 1], [0, 3]), ([2, 3], [1, 2])]  # balance at A=0, T=1
    rigid, wit = brute_rigid([0, 1, 2, 3], aatt_eqs, [1, 1, 1, 1], 4)
    print(f"AATT A=(1,1,1,1) G=4: rigid={rigid} witnesses={wit}")
    if not rigid:
        print("FAIL: AATT should be rigid")
        fails += 1

    # rank check: |E|-|V|+c-1 = 4-2+1-1 = 2 > 0, so not a single cycle
    r = 4 - 2 + 1 - 1
    print(f"AATT cycle rank r={r} (single cycle would need r=0)")

    # 3. mutation-red control: A=(2,1,1,1), G=5 non-rigid
    rigid5, wit5 = brute_rigid([0, 1, 2, 3], aatt_eqs, [2, 1, 1, 1], 5)
    print(f"AATT A=(2,1,1,1) G=5: rigid={rigid5} witnesses={wit5}")
    if rigid5 or len(wit5) < 2:
        print("FAIL: mutated AATT should be non-rigid (control has no power)")
        fails += 1

    # 4. complexity record
    print("search-space table (G+1)^|E| vs rank r:")
    for name, E, V, c, G in [("cycle2 k=3", 2, 2, 1, 6), ("AATT", 4, 2, 1, 4),
                             ("AATT mut", 4, 2, 1, 5), ("cycle6 k=4", 6, 6, 1, 24)]:
        print(f"  {name}: |E|={E} G={G} space={(G + 1) ** E} r={E - V + c - 1}")

    # 5. genome realization
    spec = spectrum_circular("AATT", 2)
    print(f"circular AATT L=2 spectrum: {spec}")
    if spec != {"AA": 1, "AT": 1, "TT": 1, "TA": 1}:
        print("FAIL: AATT spectrum mismatch")
        fails += 1

    # 6. Same scalar topology summary (|V|, |E|, cycle rank) and same L,G,
    # but opposite rigidity statuses on two genuine circular-word supports.
    # Edges are 3-mers; vertices are their 2-mer prefix/suffix.
    rank_pair = []
    for word, expected_rigid in (("AABABAB", True), ("AAAAAAB", False)):
        sp = spectrum_circular(word, 3)
        es = list(sp)
        vs = {e[:-1] for e in es} | {e[1:] for e in es}
        outs = [[i for i, e in enumerate(es) if e[:-1] == v] for v in vs]
        ins = [[i for i, e in enumerate(es) if e[1:] == v] for v in vs]
        eqs = list(zip(outs, ins))
        counts = [sp[e] for e in es]
        is_rigid, candidates = brute_rigid(es, eqs, counts, 7)
        rank = len(es) - len(vs) + 1
        print(f"{word} L=3 spectrum={sp} |V|={len(vs)} |E|={len(es)} "
              f"rank={rank} rigid={is_rigid} candidates={candidates}")
        if is_rigid != expected_rigid or len(vs) != 3 or len(es) != 4 or rank != 2:
            print(f"FAIL: unexpected topology/rigidity for {word}")
            fails += 1
        if word == "AAAAAAB" and not any(tuple(c) != tuple(counts) for c in candidates):
            print("FAIL: non-rigid genome has no alternative candidate")
            fails += 1
        rank_pair.append((len(vs), len(es), 7, rank, is_rigid))
    if len(rank_pair) != 2 or rank_pair[0][:4] != rank_pair[1][:4] or rank_pair[0][4] == rank_pair[1][4]:
        print("FAIL: expected a rigidity split at fixed (L,G,|V|,|E|,rank)")
        fails += 1

    # 7. Exhaust all binary circular words in a bounded genome/read scope,
    # plus a ternary-alphabet scope (new cross-alphabet dimension).
    # Group by scalar summaries only, then require at least one group where
    # spectra have differing rigidity status. This verifies rank_pair as one
    # instance and also avoids selecting that pair as a hand-picked-only case.
    from itertools import product as cartesian_product

    def run_scope(alphabet, gmax, read_lengths):
        grouped = {}
        words_checked = 0
        for genome_length in range(1, gmax + 1):
            for letters in cartesian_product(alphabet, repeat=genome_length):
                word = "".join(letters)
                for read_length in read_lengths:
                    sp = spectrum_circular(word, read_length)
                    es = list(sp)
                    vs = {e[:-1] for e in es} | {e[1:] for e in es}
                    outs = [[i for i, e in enumerate(es) if e[:-1] == v] for v in vs]
                    ins = [[i for i, e in enumerate(es) if e[1:] == v] for v in vs]
                    eqs = list(zip(outs, ins))
                    counts = [sp[e] for e in es]
                    is_rigid, candidates = brute_rigid(es, eqs, counts, genome_length)
                    rank = len(es) - len(vs) + 1
                    key = (read_length, genome_length, len(vs), len(es), rank)
                    grouped.setdefault(key, []).append((word, is_rigid))
                    words_checked += 1
        return grouped, words_checked

    scopes = [
        ("AB", 7, (2, 3)),
        ("AB", 8, (2, 3, 4)),
        ("AB", 9, (2, 3)),
        ("ABC", 6, (2, 3)),
    ]
    for alphabet, gmax, read_lengths in scopes:
        grouped, words_checked = run_scope(alphabet, gmax, read_lengths)
        split_groups = {
            key: cases for key, cases in grouped.items()
            if {rigid for _, rigid in cases} == {False, True}
        }
        print(f"alphabet={alphabet} genome census G=1..{gmax}, L={read_lengths}: "
              f"{words_checked} cases, "
              f"{len(split_groups)} scalar-summary groups contain both rigid and non-rigid genomes")
        if not split_groups:
            print(f"FAIL: census {alphabet}/{gmax}/{read_lengths} found no scalar-summary collision")
            fails += 1
    grouped, _ = run_scope("AB", 7, (2, 3))
    split_groups = {
        key: cases for key, cases in grouped.items()
        if {rigid for _, rigid in cases} == {False, True}
    }
    if not any(key == (3, 7, 3, 4, 2) and
               {rigid for _, rigid in cases} == {False, True}
               for key, cases in split_groups.items()):
        print("FAIL: census did not independently recover the rank-pair key")
        fails += 1

    # ATATAT genome control (2-cycle, rigid despite triples)
    spec3 = spectrum_circular("ATATAT", 3)
    print(f"circular ATATAT L=3 spectrum: {spec3}")
    if spec3 != {"ATA": 3, "TAT": 3}:
        print("FAIL: ATATAT spectrum mismatch")
        fails += 1

    if fails:
        print(f"RESULT: {fails} FAILURES")
        return 1
    print("RESULT: all section-22 checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
