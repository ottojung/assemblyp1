#!/usr/bin/env python3
"""
Independent reconstruction of the Medvedev-Brudno (2009) Section 6.2
transitively reduced bidirected overlap graph and flow feasibility for the
`AAATT -> AAAATT` witness of PR #39.

This file was written from the primary-source text (PMC3154397) and the
Section 3.1/3.2/3.3/3.4, 5.2, 6.1, 6.2 definitions only.  It does not import
or reproduce any other repository script or predicate.

Source facts implemented (quotations are from PMC3154397, retrieved 2026-09-20):

  §3.1  A DNA molecule is an unordered pair of reverse-complement strings;
        a k-molecule is represented once.  On {A,T} the involution is A <-> T.
  §3.2  A bidirected edge carries a positive/negative incidence at each
        endpoint.  A link has I(x,e) in {+1,-1}; a loop has I(x,e) in
        {+2,-2,0}.  A walk has e_{i-1}, e_i of opposite orientation at every
        interior vertex.
  §3.3  A bidirected overlap is exactly one of the four cases
          (p,p) -> (+,-),  (p,n) -> (+,+),  (n,p) -> (-,-),  (n,n) -> (-,+)
        and its length is the length of the underlying string overlap.
  §3.4  A flow satisfies l(e) <= f(e) <= u(e) and sum_e I(v,e) f(e) = b(v).
  §5.2  Splitting v into v- -> v+ turns a vertex bound/cost into an edge
        bound/cost; the split-edge flow is the vertex throughput.
  §6.1  The objective is the product of per-type binomials with the external
        true genome length N: prod_w (d_w/N)^{x_w} (1 - d_w/N)^{n - x_w}.
  §6.2  Vertices are the reads; edges are all bidirected overlaps of length
        >= o_min; transitive edge reduction removes an overlap spelled by two
        shorter (proper) overlaps (Myers 2005); each vertex has lower bound 1,
        all other lower bounds 0, all upper bounds infinity; supersource/sink
        edges carry prohibitive cost.
  Obs.7 The number of times a walk visits a read equals the number of times
        that read occurs as a submolecule of the molecule the walk spells.

Exact integer / Fraction arithmetic.  Exits non-zero on any failed assertion.
"""

from __future__ import annotations

import sys
from collections import Counter
from fractions import Fraction

# ---------------------------------------------------------------------------
# §3.1 molecules on the binary alphabet
# ---------------------------------------------------------------------------

_A, _T = "A", "T"
_COMP = {"A": "T", "T": "A"}


def rc(w):
    return tuple(_COMP[b] for b in reversed(tuple(w)))


def molecule(w):
    """Canonical representative of the unordered reverse-complement pair."""
    w = tuple(w)
    return min(w, rc(w))


L = 3  # read length
N = 5  # external true genome length for the witness


# ---------------------------------------------------------------------------
# §3.2 / §3.3 bidirected overlap graph
# ---------------------------------------------------------------------------

_CASE = {
    ("p", "p"): (1, -1),
    ("p", "n"): (1, 1),
    ("n", "p"): (-1, -1),
    ("n", "n"): (-1, 1),
}


def build_graph(vertices, o_min):
    """All §3.3 bidirected overlap edges, length in [o_min, L-1].

    A vertex is a canonical molecule string.  Its positive strand is the
    canonical string and its negative strand is the reverse complement.  For
    every ordered pair (x, y) (possibly x == y) and every overlap length l we
    test the four strand cases.  An edge records the used strand at each end
    and the signed incidences of the (possibly loop) edge.
    """
    edges = []
    for x in vertices:
        strands_x = {"p": x, "n": rc(x)}
        for y in vertices:
            strands_y = {"p": y, "n": rc(y)}
            for l in range(o_min, L):
                for sx in ("p", "n"):
                    for sy in ("p", "n"):
                        if strands_x[sx][-l:] == strands_y[sy][:l]:
                            ix, iy = _CASE[(sx, sy)]
                            edges.append(
                                {
                                    "x": x,
                                    "y": y,
                                    "l": l,
                                    "sx": sx,
                                    "sy": sy,
                                    "ix": ix,
                                    "iy": iy,
                                }
                            )
    return edges


def transitive_reduction(edges):
    """Myers' transitive-edge reduction, §6.2.

    Edge e (x -> y, length l, boundary incidences ix,iy) is removed iff there
    is an observed molecule z with edges e1 (x -> z, length l1) and
    e2 (z -> y, length l2), both proper (l1, l2 < L), whose interior
    incidences at z oppose, whose boundary incidences equal e's, and whose
    lengths compose as l = l1 + l2 - L.
    """
    kept, removed = [], []
    for e in edges:
        witness = None
        for z in {f["y"] for f in edges} | {f["x"] for f in edges}:
            for e1 in edges:
                if e1["x"] != e["x"] or e1["y"] != z:
                    continue
                if e1["l"] >= L or e1["ix"] != e["ix"]:
                    continue
                for e2 in edges:
                    if e2["x"] != z or e2["y"] != e["y"]:
                        continue
                    if e2["l"] >= L or e2["iy"] != e["iy"]:
                        continue
                    if e1["l"] + e2["l"] - L != e["l"]:
                        continue
                    if e1["iy"] == e2["ix"]:  # interior incidences must oppose
                        continue
                    witness = (e1, e2, z)
                    break
                if witness:
                    break
            if witness:
                break
        (removed if witness else kept).append(e)
    return kept, removed


def edge_present(edges, x, y, l, sx, sy):
    return any(
        e["x"] == x and e["y"] == y and e["l"] == l and e["sx"] == sx and e["sy"] == sy
        for e in edges
    )


# ---------------------------------------------------------------------------
# walks induced by the length-L cyclic windows of a spelled molecule
# ---------------------------------------------------------------------------


def window_visits(seq):
    """(molecule, used-strand, representative window) for every cyclic window."""
    G = len(seq)
    visits = []
    for i in range(G):
        w = tuple(seq[(i + k) % G] for k in range(L))
        m = molecule(w)
        strand = "p" if w == m else "n"
        visits.append((m, strand, w))
    return visits


def certify_walk(seq, edges, label):
    """Check that the cyclic window walk is a valid §6.2 bidirected circuit."""
    visits = window_visits(seq)
    G = len(visits)
    steps = []
    for i in range(G):
        (mx, sx, wx) = visits[i]
        (my, sy, wy) = visits[(i + 1) % G]
        l = L - 1
        assert wx[1:] == wy[:-1], (label, i, "windows not consecutive")
        assert edge_present(edges, mx, my, l, sx, sy), (
            label,
            i,
            "missing edge",
            mx,
            my,
            l,
            sx,
            sy,
        )
        ix, iy = _CASE[(sx, sy)]
        steps.append((mx, my, l, sx, sy, ix, iy))

    # §3.2 walk condition: opposite incidences at every interior vertex.
    for i in range(G):
        arrive = steps[i][6]        # incidence at the end vertex of step i
        depart = steps[(i + 1) % G][5]  # incidence at the start vertex of next
        assert arrive == -depart, (label, "orientation", i, arrive, depart)

    # §3.4 / Observation 7: throughput = number of visits per molecule.
    throughput = Counter(m for (m, _, _) in visits)
    assert all(v >= 1 for v in throughput.values()), (label, "lower bound 1")

    # §3.4 balance sum_e I(v,e) f(e) = 0 at every vertex (b = 0, closed flow).
    balance = Counter()
    for (mx, my, l, sx, sy, ix, iy) in steps:
        balance[mx] += ix
        balance[my] += iy
    assert all(b == 0 for b in balance.values()), (label, "balance", dict(balance))

    return throughput, steps, visits


def induced_sequence(visits):
    """Reconstruct the spelled circular sequence from its window visits alone.

    Each visit is a length-L window; consecutive windows overlap in L-1 chars.
    Append the new last character of each window to the first window.  The
    result is a length-(G + L - 1) string that is (L-1)-circular; its length-G
    circular reduction is the spelled molecule.
    """
    G = len(visits)
    spelled = list(visits[0][2])
    for i in range(1, G):
        spelled.append(visits[i][2][-1])
    spelled = tuple(spelled)
    assert len(spelled) == G + L - 1
    assert spelled[: L - 1] == spelled[G : G + L - 1], "not (L-1)-circular"
    circular = spelled[:G]
    windows = Counter(
        molecule(tuple(circular[(i + k) % G] for k in range(L))) for i in range(G)
    )
    return "".join(spelled), "".join(circular), windows


# ---------------------------------------------------------------------------
# §6.1 separable-binomial objective
# ---------------------------------------------------------------------------


def log_lik_factor(d_w, x_w, n):
    return Fraction(d_w, N) ** x_w * (Fraction(N - d_w, N)) ** (n - x_w)


def likelihood_ratio(d1, d2, obs, n):
    r = Fraction(1)
    for w in set(d1) | set(d2):
        assert set(d1) == set(d2)
        r *= log_lik_factor(d1[w], obs[w], n) / log_lik_factor(d2[w], obs[w], n)
    return r


# ---------------------------------------------------------------------------
# checks
# ---------------------------------------------------------------------------


def main():
    truth = tuple("AAATT")
    competitor = tuple("AAAATT")
    vertices = sorted(
        {
            molecule(tuple(seq[(i + k) % len(seq)] for k in range(L)))
            for seq in (truth, competitor)
            for i in range(len(seq))
        }
    )

    report = {}
    for o_min in (1, 2):
        raw = build_graph(vertices, o_min)
        kept, removed = transitive_reduction(raw)

        d_S, steps_S, visits_S = certify_walk(truth, kept, f"S o_min={o_min}")
        d_D, steps_D, visits_D = certify_walk(competitor, kept, f"D o_min={o_min}")

        # observed reads x from the advertised distinct starts (0, 1, 4)
        starts = (0, 1, 4)
        G = len(truth)
        observed = Counter(
            molecule(tuple(truth[(s + k) % G] for k in range(L))) for s in starts
        )
        assert observed == Counter({molecule(tuple("AAA")): 1,
                                    molecule(tuple("AAT")): 1,
                                    molecule(tuple("TAA")): 1}), observed
        assert all(d_S[m] >= observed[m] for m in observed), (d_S, observed)

        n = sum(observed.values())
        ratio = likelihood_ratio(d_D, d_S, observed, n)
        assert ratio > 1, ratio

        # transitive reduction must not touch any edge used by either walk
        used = {(mx, my, l, sx, sy) for (mx, my, l, sx, sy, _, _) in steps_S}
        used |= {(mx, my, l, sx, sy) for (mx, my, l, sx, sy, _, _) in steps_D}
        removed_keys = {(e["x"], e["y"], e["l"], e["sx"], e["sy"]) for e in removed}
        assert not (used & removed_keys), (o_min, used & removed_keys)

        report[o_min] = {
            "raw_edges": len(raw),
            "kept_edges": len(kept),
            "removed_edges": len(removed),
            "d_S": dict(d_S),
            "d_D": dict(d_D),
            "ratio": ratio,
        }

    # ---- induced sequences ---------------------------------------------------
    for seq, name in ((truth, "S"), (competitor, "D")):
        spelled, circular, windows = induced_sequence(window_visits(seq))
        assert windows == Counter(report[2]["d_" + name]), (name, windows)
        report[name + "_induced"] = (spelled, circular)

    # ---- adversarial / falsification checks ---------------------------------
    G = len(truth)
    oriented_windows_truth = {
        tuple(truth[(i + k) % G] for k in range(L)) for i in range(G)
    }
    oriented_observed = {
        tuple(truth[(s + k) % G] for k in range(L)) for s in (0, 1, 4)
    }
    # Under MB09's literal §6.1 "4^k oriented k-mers" reading the truth's window
    # set is NOT contained in the observed oriented support: 011 (ATT) and 110
    # (TTA) are unobserved.  So the witness is a revcomp-molecule-class witness,
    # not an oriented-type witness.  This is a genuine scope dependency.
    oriented_fails = not oriented_windows_truth <= oriented_observed
    assert oriented_fails

    # Reduction detail at o_min=1: only length-1 edges are removable (L=3
    # forces l <= L-2 = 1), and the surviving length-1 edges are exactly the
    # two directions of the AAT--TAA link whose spelled 5-mer has middle window
    # ATA/TAT, which is not an observed read class.
    raw1 = build_graph(vertices, 1)
    kept1, removed1 = transitive_reduction(raw1)
    assert len(raw1) == 28 and len(kept1) == 12 and len(removed1) == 16
    assert all(e["l"] == 1 for e in removed1)
    surviving_len1 = [e for e in kept1 if e["l"] == 1]
    assert all(
        {e["x"], e["y"]} == {tuple("AAT"), tuple("TAA")} for e in surviving_len1
    ), surviving_len1
    assert len(surviving_len1) == 2

    # The per-occurrence strengthening d_w >= x_w also holds for this witness.
    for o_min in (1, 2):
        d_S = report[o_min]["d_S"]
        for m, c in ((tuple("AAA"), 1), (tuple("AAT"), 1), (tuple("TAA"), 1)):
            assert d_S[m] >= c, (o_min, m, d_S[m], c)

    # The PR #39 prose spectrum (2,2,1) is not produced by either molecule.
    report["prose_spectrum_is_wrong"] = (
        report[1]["d_S"] != {tuple("AAA"): 2, tuple("AAT"): 2, tuple("TAA"): 1}
    )
    assert report["prose_spectrum_is_wrong"]

    print("=== independent §6.2 certificate: AAATT -> AAAATT ===")
    for o_min in (1, 2):
        r = report[o_min]
        ds = {"".join(m): v for m, v in r["d_S"].items()}
        dd = {"".join(m): v for m, v in r["d_D"].items()}
        print(
            f"o_min={o_min}: raw={r['raw_edges']} kept={r['kept_edges']} "
            f"removed={r['removed_edges']} d_S={ds} d_D={dd} "
            f"L(D)/L(S)={r['ratio']}"
        )
    print(
        "induced S spelled/circular =", report["S_induced"],
        " D spelled/circular =", report["D_induced"],
    )
    print("oriented 4^k reading kills truth support containment:", oriented_fails)
    print("per-occurrence d_w >= x_w holds: True")
    print("PR39 prose spectrum (2,2,1) rejected:", report["prose_spectrum_is_wrong"])
    print("ALL ASSERTIONS PASSED")


if __name__ == "__main__":
    main()
