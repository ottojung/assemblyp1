#!/usr/bin/env python3
"""Independent exact validation of the #261 spelled-circuit -> §6.2 flow adapter.

Scope: the *spelled* half of the §6.2 feasible-flow adapter proved in
`AssemblyP1/Section62SpelledFlowAdapter.lean` (issue #261).  The Lean theorem
`spelling_flow_feasible` states that, for any `Nodup` graph `edges` containing all
steps of a circular bidirected-circuit spelling `sp` that visits every observed
vertex,

    Feasible62 ... (Spelling.flow sp) (noTerminals) (Spelling.visits sp)

holds, i.e. the walk flow is a zero-terminal §6.2 feasible flow whose count vector
is exactly the visit vector.

This script recomputes the adapter's four clauses from scratch, with exact
integer arithmetic and no trust in the Lean output, for several concrete circular
genomes.  It mirrors the Lean definitions of `AssemblyP1.Section62BidirectedFlow`:
`canon` is `rep`, `circular_window` is `Spelling.strand`, `bd_edge` records the
signed incidences `sgnRep`/`sgnTgt`, the step list is the cyclic walk, and the
flow is the multiplicity of each step.

Checked clauses for each instance, on the deduplicated step graph `edges`:

  * `BidirectedCircuit`: at every interior vertex the arriving and departing
    incidences are opposite (`sgnRep(s, canon s) == -sgnTgt(s, canon s)`);
  * `throughput(flow, edges, v) == visits(v)` for every molecule class;
  * `balCore(flow, edges, v) == 0` for every molecule class;
  * `Feasible62` with `edgeLB = 0`, `vertexLB = 1`, `t = noTerminals`, and
    `d = visits`, i.e. the four `Admissible` clauses plus zero terminal usage.

The script is deterministic, exits non-zero on any failed assertion, and shares
no code with the Lean module.
"""
from collections import Counter

COMP = {"A": "T", "T": "A", "C": "G", "G": "C"}


def rc(w):
    return "".join(COMP[c] for c in reversed(w))


def canon(w):
    return min(w, rc(w))


def circular_window(S, t, L):
    G = len(S)
    return "".join(S[(t + j) % G] for j in range(L))


def sgn_rep(s, mx):
    return 1 if s == mx else -1


def sgn_tgt(s, my):
    return -1 if s == my else 1


def bd_edge(sx, sy, length):
    """(sx, sy, len, sgnX, sgnY) with incidences from the molecule-class reps."""
    return (sx, sy, length, sgn_rep(sx, canon(sx)), sgn_tgt(sy, canon(sy)))


def strands(S, L):
    return [circular_window(S, t, L) for t in range(len(S))]


def steps(S, L):
    n = len(S)
    st = strands(S, L)
    return [bd_edge(st[i], st[(i + 1) % n], L - 1) for i in range(n)]


def dedup(seq):
    return list(dict.fromkeys(seq))


def flow(step_list, e):
    return step_list.count(e)


def throughput(step_list, edges, v):
    return sum(flow(step_list, e) for e in edges if canon(e[0]) == v)


def visits(S, L, v):
    return sum(1 for s in strands(S, L) if canon(s) == v)


def bal_core(step_list, edges, v):
    total = 0
    for e in edges:
        f = flow(step_list, e)
        if canon(e[0]) == v:
            total += f * e[3]
        if canon(e[1]) == v:
            total += f * e[4]
    return total


def check_instance(S, L, verbose=False):
    n = len(S)
    st = steps(S, L)
    edges = dedup(st)
    classes = sorted({canon(s) for s in strands(S, L)})

    # 1. BidirectedCircuit: sgnX(step i) == -sgnY(step (i-1)).
    for i in range(n):
        sgn_x = st[i][3]
        sgn_y_prev = st[(i - 1) % n][4]
        assert sgn_x == -sgn_y_prev, (S, L, i, sgn_x, sgn_y_prev)

    # 2. throughput == visits, 3. balCore == 0, 4. Feasible62 clauses.
    for v in classes:
        th = throughput(st, edges, v)
        vs = visits(S, L, v)
        assert th == vs, (S, L, v, th, vs)
        assert bal_core(st, edges, v) == 0, (S, L, v, bal_core(st, edges, v))
        assert 1 <= th, (S, L, v, th)  # vertex lower bound 1
    for e in edges:
        assert 0 <= flow(st, e)  # edge lower bound 0

    # The zero-terminal balance `balance = balCore + (0 - 0)` is `balCore`.
    for v in classes:
        assert bal_core(st, edges, v) + (0 - 0) == 0

    if verbose:
        print(f"[ok] S={S} L={L}: n={n} classes={classes} "
              f"visits={[visits(S, L, v) for v in classes]} "
              f"|edges|={len(edges)}")
    return True


def main():
    # Deterministic set of circular genomes exercising single-class, multi-class,
    # RC-collapsing, primitive and repeated molecules.
    instances = [
        ("AAA", 2),
        ("AATT", 2),
        ("AAATA", 3),
        ("ACGT", 2),
        ("ACGT", 3),
        ("AACCGGTT", 2),
        ("AACCGGTT", 3),
        ("AT", 1),
        ("ATAT", 2),
        ("AAATTT", 3),
    ]
    for S, L in instances:
        check_instance(S, L, verbose=True)

    # Also sweep all binary circular words up to length 8 at L=2 and L=3, which
    # is an exhaustive finite family (not a proof) corroborating the adapter.
    alphabet = "AT"
    swept = 0
    for length in range(1, 9):
        for tup in __import__("itertools").product(alphabet, repeat=length):
            S = "".join(tup)
            for L in (2, 3):
                if L <= length:
                    check_instance(S, L)
                    swept += 1
    print(f"[ok] exhaustive binary sweep: {swept} (S, L) instances checked")

    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
