#!/usr/bin/env python3
"""Independent check of the exact MB09 Section 6.2 overlap-edge and
transitive-reduction rules, and of the repository's two conflicting
implementations of them.

Reads are DNA molecules = unordered reverse-complement pairs (MB09 Section
3.1).  A bidirected overlap edge is one of the four strand cases of Section
3.3:

    (p(x),p(y)) -> (+x,-y)   (p(x),n(y)) -> (+x,+y)
    (n(x),p(y)) -> (-x,-y)   (n(x),n(y)) -> (-x,+y)

where "A overlaps B" means a nonempty proper suffix of A equals a prefix of B,
and the edge length is that suffix/prefix length.  Section 6.2 says edges are
"all possible bidirected overlaps of length at least o_min", then transitive
edge reduction removes "any overlap that is spelled by two shorter overlaps",
"identical to ... Myers (2005)".

This script builds the graph for the reads {AAA, AAT, TAA} (L = 3) directly
from Section 3.3 and tests:

  * edge counts at o_min = 1 and 2, with all proper overlap lengths, and with
    only the maximal overlap per (strand,strand) choice;
  * the exact transitive-reduction rule: an edge e is removed iff there is an
    intermediate observed read z and a two-step path x -> z -> y whose overlaps
    l1,l2 are proper (< L), whose composed length is l1 + l2 - L = len(e), whose
    interior incidences oppose, and whose boundary incidences equal e's;
  * that the condition "l1 < len(e) and l2 < len(e)" used by
    scripts/independent_se62_bidirected_model.py is unsatisfiable for proper
    overlaps, so that script's reduction is vacuous;
  * that the content predicate ("the middle window of the spelled molecule is
    an observed read") used by scripts/verify_se62_aaatt_flow_cone.py agrees
    with the incidence-based rule on every length-1 edge;
  * that for L = 3 only length-1 edges can be reduced (len <= L-2), so the
    length-2 witnesses are reduction-robust.

Exits non-zero on any failed assertion.  Exact integer arithmetic only.
"""

A, T = 0, 1


def rc(w):
    return tuple(1 - b for b in reversed(w))


def mol_class(w):
    return min(w, rc(w))


def sb(w):
    return "".join("A" if b == 0 else "T" for b in w)


# canonical positive strand p = min(w, rc(w)) for each observed read
MOLS = {"AAA": (A, A, A), "AAT": (A, A, T), "TAA": (T, A, A)}
OBS = set(MOLS.values())


def strands(name):
    p = MOLS[name]
    return {"P": p, "N": rc(p)}


def overlap_lengths(X, Y):
    """All proper overlap lengths l in [1, L-1] with suffix_l(X) == prefix_l(Y)."""
    L = len(X)
    return [l for l in range(1, L) if X[L - l:] == Y[:l]]


def section33_edges(o_min, maximal_only=False):
    """Ordered bidirected edges (x, sx, y, sy, l) as tuples.

    sx, sy in {+1,-1} are the incidences at x and y.  Each edge is directed
    x (left) -> y (right) in the sense of Section 3.3; its reverse traversal is
    represented separately by (y, sy, x, sx, l)."""
    out = []
    for x in MOLS:
        for y in MOLS:
            for ox in ("P", "N"):
                for oy in ("P", "N"):
                    A_ = strands(x)[ox]
                    B_ = strands(y)[oy]
                    ls = overlap_lengths(A_, B_)
                    if maximal_only and ls:
                        ls = [max(ls)]
                    for l in ls:
                        if l < o_min:
                            continue
                        sx = +1 if ox == "P" else -1
                        sy = +1 if oy == "N" else -1
                        out.append((x, sx, y, sy, l))
    return out


def reducible(edges, e):
    """Exact Myers composition reduction (returns a witness or None).

    Remove e = (x,sx,y,sy,l) if some observed read z and edges e1 (x->z) and
    e2 (z->y) satisfy: e1's tail incidence at x is sx; e1's head incidence at z
    is the negation of e2's tail incidence at z; e2's head incidence at y is
    sy; both overlap lengths are proper (< L); and l1 + l2 - L = l.
    """
    x, sx, y, sy, l = e
    L = len(MOLS[x])
    for z in MOLS:
        for e1 in edges:
            if e1[0] == x and e1[2] == z:
                tailx, headz, l1 = e1[1], e1[3], e1[4]
            elif e1[2] == x and e1[0] == z:
                tailx, headz, l1 = e1[3], e1[1], e1[4]
            else:
                continue
            if tailx != sx:
                continue
            for e2 in edges:
                if e2[0] == z and e2[2] == y:
                    tailz, heady, l2 = e2[1], e2[3], e2[4]
                elif e2[2] == z and e2[0] == y:
                    tailz, heady, l2 = e2[3], e2[1], e2[4]
                else:
                    continue
                if headz != -tailz or heady != sy:
                    continue
                if l1 < L and l2 < L and l1 + l2 - L == l:
                    return (z, e1, e2)
    return None


def repo_shorter_predicate(edges, e):
    """The condition in scripts/independent_se62_bidirected_model.py lines
    213-216: interior incidences oppose and l1<l and l2<l and l1+l2-L==l.
    (No boundary-incidence check, and the strict inequality is backwards.)"""
    x, sx, y, sy, l = e
    L = len(MOLS[x])
    # Explicit path enumeration, mirroring that script's structure.
    for z in MOLS:
        for e1 in edges:
            if e1[0] == x and e1[2] == z:
                sb1 = e1[3]
            elif e1[2] == x and e1[0] == z:
                sb1 = e1[1]
            else:
                continue
            for e2 in edges:
                if e2[0] == z and e2[2] == y:
                    sc2 = e2[1]
                elif e2[2] == z and e2[0] == y:
                    sc2 = e2[3]
                else:
                    continue
                if sb1 == -sc2 and e1[4] < l and e2[4] < l \
                        and e1[4] + e2[4] - L == l:
                    return True
    return False


def content_predicate(e):
    """The condition in scripts/verify_se62_aaatt_flow_cone.py: a length-1 edge
    is reducible iff the middle window of its spelled 5-mer is an observed read
    molecule."""
    x, sx, y, sy, l = e
    assert l == 1
    su = strands(x)["P"] if sx == +1 else strands(x)["N"]
    sv = strands(y)["N"] if sy == +1 else strands(y)["P"]
    assert su[-1] == sv[0]
    spelled = su + sv[1:]
    return mol_class(tuple(spelled[1:4])) in OBS


def main():
    # -- 1. edge counts ----------------------------------------------------
    all2 = section33_edges(2, maximal_only=False)
    all1 = section33_edges(1, maximal_only=False)
    max1 = section33_edges(1, maximal_only=True)
    assert len(all2) == 10, len(all2)
    assert len(all1) == 28, len(all1)
    assert len(max1) == 20, len(max1)
    assert sorted(set(all1)) == sorted(all1)  # no duplicate ordered edges

    # -- 2. no length-2 edge is reducible; only length-1 can be ------------
    assert all(reducible(all2, e) is None for e in all2)
    red1 = [e for e in all1 if reducible(all1, e) is not None]
    assert len(red1) == 16, len(red1)
    assert all(e[4] == 1 for e in red1)
    for e in red1:
        w = reducible(all1, e)
        assert w[1][4] < 3 and w[2][4] < 3
        assert w[1][4] + w[2][4] - 3 == e[4]
        assert w[1][4] > e[4] and w[2][4] > e[4]  # Myers: longer sub-overlaps

    survivors = [e for e in all1 if e[4] == 1 and reducible(all1, e) is None]
    assert survivors == [("AAT", +1, "TAA", -1, 1),
                         ("TAA", -1, "AAT", +1, 1)], survivors

    # -- 3. the repository's shorter-than predicate is unsatisfiable -------
    for e in all1 + all2:
        assert repo_shorter_predicate(all1, e) is False, e
    # and mathematically it is impossible for any proper overlaps:
    # l = l1 + l2 - L with l1,l2 < l forces l >= L + 2 > L - 1.

    # -- 4. the content predicate agrees on every length-1 edge -----------
    for e in [x for x in all1 if x[4] == 1]:
        assert content_predicate(e) == (reducible(all1, e) is not None), e

    # -- 5. maximal-only and all-length graphs give the same reduced graph --
    red_max = [e for e in max1 if reducible(max1, e) is None]
    red_all = survivors + [e for e in all1 if e[4] == 2]
    assert sorted(set(red_max)) == sorted(set(red_all)), (red_max, red_all)

    # -- report ------------------------------------------------------------
    print("PASS: exact MB09 Section 6.2 overlap-edge / transitive-reduction rules")
    print(f"  Section 3.3 ordered edges, L=3, o_min=2 : {len(all2)} (all length 2)")
    print(f"  Section 3.3 ordered edges, L=3, o_min=1 : {len(all1)} "
          f"({len([e for e in all1 if e[4] == 2])} length 2, "
          f"{len([e for e in all1 if e[4] == 1])} length 1)")
    print(f"  maximal-only edges, o_min=1             : {len(max1)}")
    print(f"  reducible at o_min=1                    : {len(red1)} "
          f"(all length 1; <= L-2 = 1)")
    print(f"  reducible at o_min=2                    : 0")
    print(f"  surviving length-1 edges (all-length)   : "
          f"{[(e[0], e[2]) for e in survivors]}  (the two directions of AAT--TAA)")
    print(f"  same reduced graph from maximal-only    : yes")
    print(f"  repo '< len' predicate hits             : 0 (unsatisfiable for"
          f" proper overlaps)")
    print(f"  content predicate == incidence rule     : yes (all 18 length-1 edges)")


if __name__ == "__main__":
    main()
