#!/usr/bin/env python3
"""Exact bounded census of literal §6.2 flows on the audited AAATT graph.

The graph construction, reverse-complement representatives, edge signs and
literal transitive reduction are reused from verify_se62_mb09_bidirected_graph.py.
For each candidate length N, this script enumerates *every* nonnegative integer
edge-flow vector of total N on that graph, then imposes signed-incidence balance
and the per-vertex throughput lower bound 1.  Since every edge has exactly one
departure endpoint, total edge flow N is equivalent to total throughput N.

The truth is the circular molecule AAATT, with its complete length-3 spectrum
as the read-count vector. Candidate scores are the exact variable-length
multinomial likelihood product_c (d_c/N)^x_c. This is a bounded diagnostic for
one literal graph, not a general maximality theorem. In particular the flow
set is not the set of spelled circuits, and a finite N cutoff cannot settle
unbounded candidates.
"""
from __future__ import annotations

from collections import Counter
from fractions import Fraction
from itertools import combinations

import verify_se62_mb09_bidirected_graph as mb


TRUTH = (mb.A, mb.A, mb.A, mb.T, mb.T)  # AAATT
MAX_N = 10


def compositions(total: int, parts: int):
    """Yield all weak compositions, without duplicates, in lexicographic order."""
    if parts == 1:
        yield (total,)
        return
    for cuts in combinations(range(total + parts - 1), parts - 1):
        points = (-1, *cuts, total + parts - 1)
        yield tuple(points[i + 1] - points[i] - 1 for i in range(parts))


def likelihood(counts: Counter, throughput: dict, n: int) -> Fraction:
    value = Fraction(1)
    for molecule, x in counts.items():
        value *= Fraction(throughput.get(molecule, 0), n) ** x
    return value


def main() -> None:
    graph = mb.build_graph()
    vertices = mb.OBSERVED
    # Confirm these are precisely the already-audited graph choices.
    assert len(graph) == 10
    assert not any(mb.reduce_literal(edge, vertices)[0] for edge in graph)
    assert not any(mb.reduce_myers_longer(edge, vertices)[0] for edge in graph)

    _, _, truth_d_objects = mb.validate_bidirected_walk(TRUTH, graph)
    truth_d = {molecule.rep: count for molecule, count in truth_d_objects.items()}
    truth_length = len(TRUTH)
    # Complete spectrum (all circular starts), not a subset of read starts.
    truth_windows = mb.window_strands(TRUTH)
    x = Counter(mb.mol(w) for w in truth_windows)
    assert x == truth_d
    truth_score = likelihood(x, truth_d, truth_length)
    print("graph: observed molecules AAA, AAT, TAA; readLen=3; oMin=2")
    print("truth: AAATT; complete spectrum:",
          {mb.word(k): v for k, v in x.items()})
    print("truth exact variable-length likelihood:", truth_score)
    print("N | feasible integral edge flows | best exact score | best throughput(s) | strict improvement")

    for n in range(1, MAX_N + 1):
        feasible = 0
        best_score = Fraction(-1)
        maximizers: set[tuple[int, ...]] = set()
        # Enumerating all compositions of N over all 10 edge variables is a
        # completeness certificate for the bounded integral flow universe.
        for edge_weights in compositions(n, len(graph)):
            balance = {v: 0 for v in vertices}
            throughput = {v: 0 for v in vertices}
            for edge, weight in zip(graph, edge_weights):
                balance[edge["x"]] += weight * edge["sign_x"]
                balance[edge["y"]] += weight * edge["sign_y"]
                throughput[edge["x"]] += weight
            if any(balance[v] != 0 for v in vertices):
                continue
            if any(throughput[v] < 1 for v in vertices):
                continue
            feasible += 1
            by_rep = {v.rep: throughput[v] for v in vertices}
            score = likelihood(x, by_rep, n)
            vector = tuple(by_rep[v.rep] for v in vertices)
            if score > best_score:
                best_score, maximizers = score, {vector}
            elif score == best_score:
                maximizers.add(vector)

        improved = feasible > 0 and best_score > truth_score
        print(f"{n} | {feasible} | {best_score if feasible else 'none'} | "
              f"{sorted(maximizers) if feasible else []} | {improved}")
        # Every candidate is separately checked against the fixed truth score;
        # at N=truth_length the truth itself must occur in the feasible image.
        if n == truth_length:
            truth_vec = tuple(truth_d[v.rep] for v in vertices)
            assert truth_vec in maximizers
            assert best_score == truth_score
        assert not improved

    print(f"PASS: complete edge-assignment census for 1 <= N <= {MAX_N}; "
          "no feasible flow strictly exceeds the AAATT truth score.")
    print("SCOPE: finite evidence for this graph only; no unbounded or general claim.")


if __name__ == "__main__":
    main()
