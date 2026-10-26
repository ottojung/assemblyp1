#!/usr/bin/env python3
"""Exact bounded check of conformal-minimal circulation witnesses for #257.

This deliberately checks only a small finite scope. It enumerates delta vectors
in the multiplicity box, filters the zero-sum circulation lattice, and checks
whether any feasible nonzero vector has no proper nonzero conformal lattice
vector below it. It is independent of the Lean implementation and Graver code.
"""

from itertools import product


def circulation_vectors(edges, slack):
    """Enumerate all integer vectors in [-slack, C] satisfying balance, sum=0."""
    C = sum(slack)
    for delta in product(*(range(-s, C + 1) for s in slack)):
        if not any(delta):
            continue
        if sum(delta) != 0:
            continue
        if any(sum(delta[i] for i, (u, v) in enumerate(edges) if u == node)
               != sum(delta[i] for i, (u, v) in enumerate(edges) if v == node)
               for node in {x for edge in edges for x in edge}):
            continue
        yield delta


def conformal_leq(g, d):
    """Coordinatewise containment of positive and negative parts."""
    return all(min(g_i, 0) >= min(d_i, 0) and
               max(g_i, 0) <= max(d_i, 0) for g_i, d_i in zip(g, d))


def is_conformal_minimal(g, lattice):
    return not any(h != g and conformal_leq(h, g) for h in lattice)


def check_instance(edges, multiplicities):
    assert len(edges) == len(multiplicities)
    assert all(m >= 1 for m in multiplicities)
    # The base must be a circulation, and G is its total.
    nodes = {x for edge in edges for x in edge}
    assert all(sum(multiplicities[i] for i, (u, _) in enumerate(edges) if u == v)
               == sum(multiplicities[i] for i, (_, w) in enumerate(edges) if w == v)
               for v in nodes)
    slack = tuple(m - 1 for m in multiplicities)
    lattice = list(circulation_vectors(edges, slack))
    # By construction every enumerated delta is box-feasible; compute statuses
    # both from full feasible deltas and from conformal-minimal feasible deltas.
    direct_nonrigid = bool(lattice)
    minimal = [g for g in lattice if is_conformal_minimal(g, lattice)]
    minimal_nonrigid = bool(minimal)
    assert direct_nonrigid == minimal_nonrigid
    assert all(sum(g) == 0 for g in lattice)
    assert all(not any(h != g and conformal_leq(h, g) for h in lattice)
               for g in minimal)
    return direct_nonrigid, len(lattice), len(minimal)


def main():
    cases = []

    # Directed cycles (including a rank-one support with slack).
    cycle = [(0, 1), (1, 0)]
    for m in (1, 2, 3):
        cases.append((cycle, (m, m)))

    # Figure-eight: rigid unit spectrum, and non-rigid A=(2,2,1,1).
    figure8 = [(0, 1), (1, 0), (0, 2), (2, 0)]
    cases.extend([
        (figure8, (1, 1, 1, 1)),
        (figure8, (2, 2, 1, 1)),
        (figure8, (3, 3, 1, 1)),
        (figure8, (1, 1, 2, 2)),
    ])

    # Circular genome AATT at L=3: AAT -> ATT -> TTA -> TAA -> AAT.
    aatt_cycle = [(0, 1), (1, 2), (2, 3), (3, 0)]
    cases.append((aatt_cycle, (1, 1, 1, 1)))

    # Double-theta support (4 vertices, 6 edges).
    double_theta = [(0, 1), (0, 2), (2, 1), (1, 0), (1, 3), (3, 0)]
    cases.extend([
        (double_theta, (1, 1, 1, 1, 1, 1)),
        (double_theta, (2, 1, 1, 2, 1, 1)),
        (double_theta, (1, 2, 2, 1, 2, 2)),
    ])

    total_lattice = 0
    for index, (edges, mult) in enumerate(cases, 1):
        nonrigid, count, minimal_count = check_instance(edges, mult)
        total_lattice += count
        print(f"case {index:02d}: m={mult} nonrigid={nonrigid} "
              f"feasible_deltas={count} conformal_minimal={minimal_count}")
    print(f"ALL CHECKS PASSED: {len(cases)} balanced instances; "
          f"{total_lattice} feasible nonzero deltas; direct iff conformal-minimal")


if __name__ == "__main__":
    main()
