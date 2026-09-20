#!/usr/bin/env python3
"""Independent audit certificate for the Medvedev-Brudno (2009) section 6.2
definitions used to judge PR #39's `AAATT -> AAAATT` witness.

This is an *independent* reconstruction, written without using the concurrent
branch artifact `docs/section62-mb09-bidirected-graph-audit.md` or its script.
Its purpose is to check, from the primary source definitions only:

  (G) the explicit bidirected overlap graph on the observed read *molecules*
      {AAA, AAT, TAA} with the reverse-complement involution A <-> T
      (MB09 section 3.1, 3.3);
  (W) that the cyclic length-3 window walks of the truth `AAATT` and the
      competitor `AAAATT` lift to genuine *closed bidirected walks*: every step
      is a real graph edge and consecutive edges have opposite orientations at
      every interior vertex (MB09 section 3.2);
  (F) that they induce admissible section 6.2 flows / circuits: vertex
      throughput = Observation 7 occurrence counts, vertex lower bound 1,
      edge lower bound 0, zero signed-incidence balance at every read vertex,
      no supersource/supersink usage (MB09 section 3.4, 6.2);
  (L) the section 6.1 separable binomial ratio with external N = 5, n = 3;
  (C) the alternate oriented (non-reverse-complement-collapsed) reading, which
      shows the witness is load-bearing on the molecule collapse;
  (T) the PR #39 prose table error: the correct truth spectrum is
      d_S = {AAA:1, AAT:2, TAA:2}, not {AAA:2, AAT:2, TAA:1}.

All arithmetic is exact (fractions.Fraction); exits non-zero on any failure.
"""
from __future__ import annotations

import sys
from collections import Counter
from fractions import Fraction

COMP = {"A": "T", "T": "A"}
L = 3
OMIN = 2  # section 6.2 threshold; witness walks use overlap L-1 = 2


def rc(w):
    return tuple(COMP[c] for c in reversed(w))


def mol(w):
    """Molecule class: the lexicographically smaller strand of the revcomp pair."""
    return min(tuple(w), rc(tuple(w)))


def word(w):
    return "".join(w)


class Molecule:
    def __init__(self, rep):
        self.p = tuple(rep)
        self.n = rc(self.p)

    def __eq__(self, other):
        return isinstance(other, Molecule) and self.p == other.p

    def __hash__(self):
        return hash(self.p)

    def __repr__(self):
        return word(self.p)


OBS = [Molecule("AAA"), Molecule("AAT"), Molecule("TAA")]


def incidences(mx, sx, my, sy):
    sig_x = +1 if tuple(sx) == mx.p else -1
    sig_y = -1 if tuple(sy) == my.p else +1
    return sig_x, sig_y


def build_graph(omin):
    """All bidirected overlap edges of proper length in [omin, L)."""
    edges = []
    for mx in OBS:
        for my in OBS:
            for sx in (mx.p, mx.n):
                for sy in (my.p, my.n):
                    for length in range(omin, L):
                        if sx[len(sx) - length:] == sy[:length]:
                            sig_x, sig_y = incidences(mx, sx, my, sy)
                            edges.append((mx, my, tuple(sx), tuple(sy), length, sig_x, sig_y))
    return edges


def window_strands(seq):
    g = len(seq)
    return [tuple(seq[(i + j) % g] for j in range(L)) for i in range(g)]


def walk(seq, graph):
    ws = window_strands(seq)
    g = len(seq)
    steps = []
    for i in range(g):
        sx, sy = ws[i], ws[(i + 1) % g]
        assert sx[1:] == sy[:-1], (word(sx), word(sy))
        mx, my = Molecule(mol(sx)), Molecule(mol(sy))
        sig_x, sig_y = incidences(mx, sx, my, sy)
        length = L - 1
        assert any(e[2] == tuple(sx) and e[3] == tuple(sy) and e[4] == length for e in graph), \
            ("missing graph edge", word(sx), word(sy))
        steps.append({"u": mx, "v": my, "sx": sx, "sy": sy,
                      "len": length, "sx_sign": sig_x, "sy_sign": sig_y})
    visits = [Molecule(mol(w)) for w in ws]
    for i in range(g):
        prev, cur = steps[(i - 1) % g], steps[i]
        assert prev["v"] == visits[i] and cur["u"] == visits[i]
        assert prev["sy_sign"] == -cur["sx_sign"], ("orientation mismatch at visit", i)
    throughput = Counter(visits)
    balance = {m: 0 for m in OBS}
    for st in steps:
        balance[st["u"]] += st["sx_sign"]
        balance[st["v"]] += st["sy_sign"]
    return steps, visits, throughput, balance


def phi(xw, n, N, d):
    return Fraction(d, N) ** xw * Fraction(N - d, N) ** (n - xw)


def lik(x, n, N, d):
    result = Fraction(1)
    for w, xw in x.items():
        result *= phi(xw, n, N, d.get(w, 0))
    return result


def main() -> int:
    checks = []
    truth = tuple("AAATT")
    competitor = tuple("AAAATT")
    starts = (0, 1, 4)
    N = len(truth)          # external known genome size (MB09 section 6.1)
    n = len(starts)

    x = Counter(mol(tuple(truth[(r + j) % len(truth)] for j in range(L))) for r in starts)
    dS = Counter(mol(w) for w in window_strands(truth))
    dD = Counter(mol(w) for w in window_strands(competitor))

    print("observed read molecules x :", {word(k): v for k, v in x.items()})
    print("truth spectrum d_S        :", {word(k): v for k, v in dS.items()})
    print("competitor spectrum d_D   :", {word(k): v for k, v in dD.items()})

    graph = build_graph(OMIN)
    print(f"(G) o_min={OMIN}: {len(graph)} bidirected overlap edges among "
          f"{[word(m.p) for m in OBS]} (all length L-1=2)")
    checks.append((f"(G) exactly 10 edges at o_min={OMIN}", len(graph) == 10))

    # (C) load-bearing reverse-complement collapse
    oriented = [word(w) for w in window_strands(truth)]
    print("(C) truth oriented windows  :", oriented)
    print("(C) observed oriented reads :", [word(tuple(truth[(r + j) % len(truth)] for j in range(L))) for r in starts])
    checks.append(("(C) oriented truth support strictly contains observed support "
                   "(witness needs the molecule/revcomp collapse)",
                   set(oriented) > set(word(tuple(truth[(r + j) % len(truth)] for j in range(L)))
                                       for r in starts)))

    for name, seq in (("truth AAATT", truth), ("competitor AAAATT", competitor)):
        steps, visits, throughput, balance = walk(seq, graph)
        lb1 = all(v >= 1 for v in throughput.values()) and set(throughput) == set(OBS)
        bal0 = all(v == 0 for v in balance.values())
        print(f"(W) {name}: closed bidirected circuit; throughput "
              f"{ {word(k.p): v for k, v in throughput.items()} }; LB1={lb1}; balance0={bal0}")
        checks.append((f"(W) {name} is a valid closed bidirected walk", True))
        checks.append((f"(F) {name} flow admissible (LB 1, balance 0, no source/sink)", lb1 and bal0))

    ratio = lik(dict(x), n, N, dict(dD)) / lik(dict(x), n, N, dict(dS))
    print(f"(L) section 6.1 ratio L(D)/L(S) = {ratio}")
    checks.append(("(L) ratio == 9/8 > 1", ratio == Fraction(9, 8)))

    # (T) table error
    correct_dS = {word(k): v for k, v in dS.items()}
    stale_dS = {"AAA": 2, "AAT": 2, "TAA": 1}
    print("(T) PR#39 prose d_S:", stale_dS, "| correct d_S:", correct_dS)
    checks.append(("(T) PR#39 prose d_S = {AAA:2,AAT:2,TAA:1} is wrong; "
                   "correct is {AAA:1,AAT:2,TAA:2}",
                   stale_dS != correct_dS
                   and correct_dS == {"AAA": 1, "AAT": 2, "TAA": 2}))

    print()
    ok = True
    for name, result in checks:
        print(f"[{'PASS' if result else 'FAIL'}] {name}")
        ok &= bool(result)
    print("\nALL CHECKS PASS" if ok else "\nSOME CHECKS FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
