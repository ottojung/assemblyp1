"""Issue #261: spelled-vs-flow separation transfers to the transitively reduced graph.

Parent cells (AGA/CTC and ACA/CAC, o_min=1, L=3, fixed-N binomial N=4,
x=(1,2), n=3) separate spelled-circuit maximality (truth (2,2), K=64) from
integer-flow maximality via a (1,2) defeater (K=72) that uses an overlap-1
self-loop edge. Transitive reduction (keeping only maximal overlaps L-1=2)
removes that edge, so transfer is NOT free: it must be re-proved.

This verifier certifies, for both RC supports, on the 4-edge reduced graph:
  T0. the reduced graph has exactly the 4 maximal-overlap edges;
  T1. every reduced edge crosses observed classes (repSrc != repDst), hence
      EVERY closed-walk (spelled circuit, any length) has a diagonal
      throughput image (k,k) -- reduction makes spelled images diagonal;
  T2. the original (1,2) defeater image is absent from reduced 0/1 flows;
  T3. an explicit multiplicity<=2 reduced-graph integer flow with image
      (1,3) is feasible (throughput >= 1, zero balance, no terminals);
  T4. K(1,3) = 81 > 64 = K(truth), and (1,3) is off-diagonal hence
      non-spelled at ANY length by T1.

Candidate class: integer edge-multiplicity flows on the reduced graph, edge
lower bound 0, vertex throughput lower bound 1, zero signed-incidence
balance, zero terminal usage. Likelihood: fixed-N product-binomial core on
the two observed coordinates; unobserved coordinates omitted/fixed at zero
by the same stated (non-adjudicated) convention as the parent cells.
"""
from itertools import product

CELLS = {
    "AGA/CTC": ((0, 2, 0), (1, 3, 1)),
    "ACA/CAC": ((0, 1, 0), (1, 0, 1)),
}
# Explicit reduced-graph (1,3) witnesses: edge-multiplicity tuples in the
# reduced edge order built below (verified, not searched, at cert time).
WITNESS = {"AGA/CTC": (0, 2, 1, 1), "ACA/CAC": (0, 1, 1, 2)}


def rc(w):
    return tuple(3 - b for b in reversed(w))


def K(d, N=4, x=(1, 2)):
    return (d[0] ** x[0] * d[1] ** x[1]
            * (N - d[0]) ** (sum(x) - x[0])
            * (N - d[1]) ** (sum(x) - x[1]))


def main():
    for name, (a, b) in CELLS.items():
        strands = list(dict.fromkeys((a, b, rc(a), rc(b))))
        assert len(strands) == 4 and all(rc(rc(w)) == w for w in strands)
        rep = {s: min(s, rc(s)) for s in strands}
        verts = (a, b)
        L = 3
        edges = [(x, y, 2, 1 if x == rep[x] else -1,
                  -1 if y == rep[y] else 1)
                 for x in strands for y in strands if x[L - 2:] == y[:2]]
        # T0: reduced graph = exactly the 4 maximal-overlap edges.
        assert len(edges) == 4, (name, edges)

        def throughput(f, v):
            return sum(f[i] for i, e in enumerate(edges)
                       if rep[e[0]] == v)

        def balance(f, v):
            return (sum(f[i] * e[3] for i, e in enumerate(edges)
                        if rep[e[0]] == v)
                    + sum(f[i] * e[4] for i, e in enumerate(edges)
                          if rep[e[1]] == v))

        def feasible(f):
            return all(throughput(f, v) >= 1 and balance(f, v) == 0
                       for v in verts)

        # T1: bipartition at class level => every closed walk is diagonal.
        assert all(rep[e[0]] != rep[e[1]] for e in edges), name

        # T2: original (1,2) defeater absent from reduced 0/1 flows.
        red01 = {tuple(throughput(f, v) for v in verts)
                 for f in product(range(2), repeat=len(edges))
                 if feasible(f)}
        assert (1, 2) not in red01, (name, sorted(red01))

        # T3: explicit multiplicity<=2 feasible flow with image (1,3).
        f = WITNESS[name]
        assert all(m <= 2 for m in f) and feasible(f), (name, f)
        img = tuple(throughput(f, v) for v in verts)
        assert img == (1, 3), (name, img)

        # T4: strict separation on the reduced graph; (1,3) off-diagonal
        # is non-spelled at any length by T1.
        assert K((2, 2)) == 64 and K((1, 3)) == 81, name
        assert K(img) > K((2, 2)) and img[0] != img[1]
        print(f"PASS {name}: reduced edges=4, 0/1 images={sorted(red01)}, "
              f"(1,2) absent, witness{list(f)}->(1,3) feasible, "
              f"K=81 > 64=truth, off-diagonal non-spelled at any length")


if __name__ == "__main__":
    main()
