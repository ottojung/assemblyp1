#!/usr/bin/env python3
"""A rigid/non-rigid genome pair with the same positive-slack support graph.

For S=AAAB, L=2, both genomes have support edges AA, AB, BA and the same
support topology, but A=(2,1,1) is rigid while A=(3,1,1) is not. Exact
criterion: a nonzero integer delta must satisfy incidence*delta=0,
sum(delta)=0, and delta >= 1-A edgewise. This script checks the claim by
enumerating positive integer circulations of the fixed total.
"""

from itertools import combinations


def spectrum(word, length):
    extended = word + word[: length - 1]
    counts = {}
    for i in range(len(word)):
        edge = extended[i : i + length]
        counts[edge] = counts.get(edge, 0) + 1
    return counts


def positive_compositions(total, parts):
    for cuts in combinations(range(1, total), parts - 1):
        points = (0,) + cuts + (total,)
        yield tuple(points[i + 1] - points[i] for i in range(parts))


def balanced(edges, values):
    vertices = {edge[:-1] for edge in edges} | {edge[1:] for edge in edges}
    return all(
        sum(values[i] for i, edge in enumerate(edges) if edge[:-1] == vertex)
        == sum(values[i] for i, edge in enumerate(edges) if edge[1:] == vertex)
        for vertex in vertices
    )


def candidates(spec, total):
    edges = sorted(spec)
    return [values for values in positive_compositions(total, len(edges))
            if balanced(edges, values)]


def main():
    rigid_spec = spectrum("AAAB", 2)
    nonrigid_spec = spectrum("AAAAB", 2)
    assert set(rigid_spec) == set(nonrigid_spec) == {"AA", "AB", "BA"}
    rigid_edges, nonrigid_edges = sorted(rigid_spec), sorted(nonrigid_spec)
    assert rigid_edges == nonrigid_edges
    rigid_a = tuple(rigid_spec[e] for e in rigid_edges)
    nonrigid_a = tuple(nonrigid_spec[e] for e in nonrigid_edges)
    rigid_candidates = candidates(rigid_spec, 4)
    nonrigid_candidates = candidates(nonrigid_spec, 5)
    assert rigid_candidates == [rigid_a], (rigid_a, rigid_candidates)
    assert nonrigid_candidates == [(1, 2, 2), nonrigid_a], nonrigid_candidates
    alternative = (1, 2, 2)
    delta = tuple(b - a for a, b in zip(nonrigid_a, alternative))
    assert sum(delta) == 0 and any(delta)
    assert balanced(nonrigid_edges, delta)
    assert all(d >= 1 - a for d, a in zip(delta, nonrigid_a))
    print(f"support={rigid_edges}; AAAB A={rigid_a}, candidates={rigid_candidates}")
    print(f"AAAAB A={nonrigid_a}, candidates={nonrigid_candidates}")
    print(f"alternative={alternative}, delta={delta}: exact box criterion verified")


if __name__ == "__main__":
    main()
