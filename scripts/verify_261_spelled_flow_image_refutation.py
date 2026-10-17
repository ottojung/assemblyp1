#!/usr/bin/env python3
"""Independent exact validation of the #261 spelled-throughput image refutation.

Scope: `AssemblyP1/Section62SpelledFlowImageRefutation.lean` (issue #261).  That
Lean module refutes the identity

    Theta(feasibleFlowSet) = spelledVisitSet

(the open hypothesis `hEq` of `flow_maximal_iff_spelled_maximal_of_image_eq`) with
two genuine MB09 §6.2 `overlapEdges` instances at `o_min = 1`, `readLen = 3`:

  * instance A (`AAC`, `CCA`): the overlap graph has *no* maximal (length-`2`)
    edge, so `spelledVisitSet` is empty; a zero-terminal feasible flow still
    exists, so the image is nonempty.

  * instance B (`AAA`, `ACA`): the graph *does* contain maximal edges, but none
    of them *arrives* at the class `ACA`; a zero-terminal feasible flow routes
    through `ACA` on a length-`1` overlap, so its throughput is not spelled.

This script recomputes the §6.2 graph, the signed-incidence balance, the
feasibility of the flows, and the spelled visit set from scratch, with exact
integer arithmetic and no trust in the Lean output.  It is deterministic and
exits non-zero on any failed assertion.  It shares no code with the Lean module.
"""
from itertools import product
from pathlib import Path
import re

# --- the four-symbol alphabet {A,C,G,T}, A=0 C=1 G=2 T=3 -------------------
COMP = {0: 3, 3: 0, 1: 2, 2: 1}
SYM = {0: "A", 1: "C", 2: "G", 3: "T"}


def rc(w):
    return tuple(COMP[c] for c in reversed(w))


def code(w):
    r = 0
    for c in w:
        r = r * 4 + c
    return r


def rep(w):
    return w if code(w) <= code(rc(w)) else rc(w)


def show(w):
    return "".join(SYM[c] for c in w)


def pre_of(l, n):
    return tuple(l[:n])


def suf_of(l, n):
    return tuple(l[len(l) - n:]) if n <= len(l) else tuple(l)


def bd_edge(sx, sy, length):
    sgn_x = 1 if sx == rep(sx) else -1
    sgn_y = -1 if sy == rep(sy) else 1
    return (sx, sy, length, sgn_x, sgn_y)


def strands_of(verts):
    return list(verts) + [rc(w) for w in verts]


def overlap_edges(read_len, o_min, verts):
    out = []
    for length in range(read_len):
        if length < o_min:
            continue
        for sx in strands_of(verts):
            for sy in strands_of(verts):
                if suf_of(sx, length) == pre_of(sy, length):
                    out.append(bd_edge(sx, sy, length))
    return out


def cls(w):
    return rep(w)


def throughput(f, edges, v):
    return sum(f.get(e, 0) for e in edges if cls(e[0]) == v)


def balance(f, edges, v):
    b = 0
    for e in edges:
        if cls(e[0]) == v:
            b += f.get(e, 0) * e[3]
        if cls(e[1]) == v:
            b += f.get(e, 0) * e[4]
    return b


def feasible(f, edges, verts):
    """Zero-terminal §6.2 feasibility with the flow's own throughput vector."""
    for e in edges:
        assert f.get(e, 0) >= 0
    for v in verts:
        if throughput(f, edges, v) < 1:
            return False
    for v in verts:
        if balance(f, edges, v) != 0:
            return False
    return True


def spelled_visits(verts, read_len, edges, max_n=6):
    """All visit tuples realizable by a spelled circuit with steps in `edges`."""
    max_edges = {e for e in edges if e[2] == read_len - 1}
    strands = strands_of(verts)
    out = set()
    for n in range(1, max_n + 1):
        for sp in product(strands, repeat=n):
            steps = [bd_edge(sp[i], sp[(i + 1) % n], read_len - 1) for i in range(n)]
            if not all(s in max_edges for s in steps):
                continue
            out.add(tuple(sum(1 for s in sp if cls(s) == v) for v in verts))
    return out


def check_instance_a():
    read_len, o_min = 3, 1
    verts = [(0, 0, 1), (1, 1, 0)]  # AAC, CCA
    edges = overlap_edges(read_len, o_min, verts)

    # No maximal edge at all.
    assert not any(e[2] == read_len - 1 for e in edges), edges

    # A zero-terminal feasible flow.
    f = {}
    for e in edges:
        if e == bd_edge((2, 3, 3), (3, 2, 2), 1) or e == bd_edge((3, 2, 2), (2, 3, 3), 1):
            f[e] = 1
    assert feasible(f, edges, verts), (f, [balance(f, edges, v) for v in verts])
    assert [throughput(f, edges, v) for v in verts] == [1, 1]

    # No spelled circuit at all, so the throughput is not spelled.
    assert spelled_visits(verts, read_len, edges) == set()
    print("instance A (AAC,CCA): graph has no maximal edge; feasible throughput (1,1) not spelled: OK")


def check_instance_b():
    read_len, o_min = 3, 1
    verts = [(0, 0, 0), (0, 1, 0)]  # AAA, ACA
    edges = overlap_edges(read_len, o_min, verts)

    # The graph *does* contain maximal edges ...
    assert any(e[2] == read_len - 1 for e in edges), edges
    # ... but none of them arrives at the class ACA.
    aca = (0, 1, 0)
    assert all(not (e[2] == read_len - 1 and cls(e[1]) == aca) for e in edges), edges

    # A zero-terminal feasible flow using length-1 overlaps.
    f = {}
    for e in edges:
        if e in (bd_edge((0, 0, 0), (0, 1, 0), 1), bd_edge((0, 1, 0), (0, 0, 0), 1)):
            f[e] = 1
    assert feasible(f, edges, verts), (f, [balance(f, edges, v) for v in verts])
    assert [throughput(f, edges, v) for v in verts] == [1, 1]

    # No spelled circuit can visit ACA, so the throughput is not spelled.
    for d in spelled_visits(verts, read_len, edges):
        assert d[1] == 0, (d, "spelled circuit visited ACA without an arriving maximal edge")
    assert (1, 1) not in spelled_visits(verts, read_len, edges)
    print("instance B (AAA,ACA): maximal edges exist but none arrives at ACA; feasible (1,1) not spelled: OK")


def check_lean_dna_encodings():
    """Ensure the Python DNA graph tests exercise precisely the Lean DNA witnesses.

    Lean separately proves rc/toList compatibility with Watson-Crick complement.
    This text-level guard catches accidental divergence between the independent
    Python test's instance and the Lean instance (which happened in a review).
    """
    src = (Path(__file__).resolve().parents[1] /
           "AssemblyP1/Section62SpelledFlowImageRefutation.lean").read_text()
    compact = re.sub(r"\s+", "", src)
    for fragment in [
        "deftoList4:W4→ListA4:=![[0,0,1],[1,1,0],[2,3,3],[3,2,2]]",
        "deftoList4b:W4→ListA4:=![[0,0,0],[0,1,0],[3,3,3],[3,2,3]]",
    ]:
        assert fragment in compact, "Lean DNA encoding diverged from Python witness"


def main():
    check_lean_dna_encodings()
    check_instance_a()
    check_instance_b()
    print("verify_261_spelled_flow_image_refutation: PASS")


if __name__ == "__main__":
    main()
