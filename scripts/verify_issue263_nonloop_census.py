#!/usr/bin/env python3
"""Exact bounded census for T-compatible conformal Graver decompositions.

All arithmetic is Python integer arithmetic. Graphs are directed multigraphs
specified by an ordered edge list; the census uses balance rows, one total row,
and source-oriented outflow T. It enumerates every displacement in the box,
every conformal kernel element in its coordinate box, the Graver elements
(conformal-minimal nonzero kernel elements), and every unordered decomposition.
"""

from itertools import permutations, product


def kernel(vs, edges, x):
    balances = [0] * vs
    for (u, v), a in zip(edges, x):
        balances[u] += a
        balances[v] -= a
    return not any(balances) and sum(x) == 0


def outflow(vs, edges, x):
    out = [0] * vs
    for (u, _), a in zip(edges, x):
        out[u] += a
    return tuple(out)


def conformal(a, b):
    return all(x == 0 or y == 0 or x * y > 0 for x, y in zip(a, b)) and all(
        abs(x) <= abs(y) for x, y in zip(a, b)
    )


def compatible(a, delta):
    return all(x == 0 or y == 0 or x * y > 0 for x, y in zip(a, delta))


def census(vs, edges, radius):
    displacements = [x for x in product(range(-radius, radius + 1), repeat=len(edges))
                     if any(x) and kernel(vs, edges, x)]
    tested_decompositions = 0
    for delta in displacements:
        box = [range(min(0, d), max(0, d) + 1) for d in delta]
        conformal_kernel = [g for g in product(*box)
                            if any(g) and kernel(vs, edges, g)]
        graver = [g for g in conformal_kernel
                  if not any(g != h and conformal(h, g) for h in conformal_kernel)]
        graver.sort()
        decompositions = []

        def visit(rem, start, parts):
            if not any(rem):
                decompositions.append(tuple(parts))
                return
            for i in range(start, len(graver)):
                g = graver[i]
                if conformal(g, rem):
                    visit(tuple(a - b for a, b in zip(rem, g)), i, parts + [g])

        visit(delta, 0, [])
        assert decompositions, (edges, delta, "no conformal Graver decomposition")
        tested_decompositions += len(decompositions)
        td = outflow(vs, edges, delta)
        good = [parts for parts in decompositions
                if all(compatible(outflow(vs, edges, g), td) for g in parts)]
        if not good:
            return {"counterexample": delta, "throughput": td,
                    "graver": graver, "decompositions": decompositions,
                    "tested": tested_decompositions}
    return {"counterexample": None, "displacements": len(displacements),
            "decompositions": tested_decompositions}


def main():
    # A two-vertex directed 2-cycle is the smallest loop-free circulation
    # graph, but its fixed-total kernel is zero; this is a deliberate control.
    assert census(2, [(0, 1), (1, 0)], 2)["displacements"] == 0

    # Three vertices with both orientations of a 2-cycle and a 3-cycle make a
    # nontrivial balance-plus-total kernel. Edges are all genuine non-loops.
    edges = [(0, 1), (1, 0), (1, 2), (2, 1), (2, 0), (0, 2)]
    result = census(3, edges, 2)
    assert result["counterexample"] is None, result
    assert result["displacements"] > 0 and result["decompositions"] > 0

    # Mutation/control: change the source of one edge while preserving a valid
    # endpoint pair; the census must be recomputed and remain internally valid.
    mutated = edges[:-1] + [(1, 2)]
    mutation = census(3, mutated, 2)
    assert mutation["counterexample"] is None, mutation

    # Complete graph-class census: every nonempty simple directed graph on
    # three labeled vertices, with any subset of the six non-loop arcs.
    arcs = list(permutations(range(3), 2))
    graph_results = [census(3, [e for i, e in enumerate(arcs) if mask >> i & 1], 2)
                     for mask in range(1, 1 << len(arcs))]
    assert all(x["counterexample"] is None for x in graph_results)
    nontrivial_graphs = sum(x["displacements"] > 0 for x in graph_results)
    print(f"two-vertex-loopfree-control: PASS (zero nonzero kernel displacements)")
    print(f"three-vertex-six-edge-census: PASS ({result['displacements']} displacements, "
          f"{result['decompositions']} decompositions, radius=2)")
    print(f"endpoint-mutation-control: PASS ({mutation['displacements']} displacements, "
          f"{mutation['decompositions']} decompositions, radius=2)")
    print(f"all-three-vertex-loopfree-simple-digraphs: PASS (63 graphs; "
          f"{nontrivial_graphs} nontrivial; radius=2)")


if __name__ == "__main__":
    main()
