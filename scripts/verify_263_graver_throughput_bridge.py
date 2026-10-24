#!/usr/bin/env python3
"""Independent exact-integer check of the #263 edge-flow Graver bridge.

Cross-checks the two unconditional claims of
``AssemblyP1/GraverThroughputBridge.lean`` (documented in
``docs/issue263-graver-throughput-bridge.md``) on a concrete tiny graph,
without re-proving anything:

* ``flowLin_eq_zero_iff``: on 2 vertices and 3 edges, ``flowLin f = 0``
  holds exactly for the balanced zero-sum flows (exhaustive over a box).
* ``hasGraverDecomposition_aug`` mechanism in the vanishing case: for the
  zero throughput map ``T = 0`` (trivially additive and annihilating every
  Graver move), the naive lift ``g |-> (g, T g) = (g, 0)`` of a conformal
  decomposition of a concrete displacement preserves full augmented
  sign-compatibility.

The genuine vertex-throughput map (``T_v f`` = out-flow at ``v``) does NOT
vanish on the edge lattice, so this script does not claim the general
``T``-sign-compatible lift; that remains OPEN per the bridge doc and the
separate ``verify_263_throughput_sign_clash.py`` witness.
"""

from itertools import product

# Tiny graph: vertices {0, 1}; edges e0 : 0 -> 1, e1 : 1 -> 0, e2 : 0 -> 0 (loop).
TAIL = (0, 1, 0)
HEAD = (1, 0, 0)
NEDGE = 3
NVERT = 2
BOX = range(-2, 3)


def balance(flow):
    return tuple(
        sum(flow[e] for e in range(NEDGE) if TAIL[e] == v)
        - sum(flow[e] for e in range(NEDGE) if HEAD[e] == v)
        for v in range(NVERT)
    )


def flow_lin(flow):
    """flowLin tail head f : balance rows ++ fixed-total row."""
    return balance(flow) + (sum(flow),)


def in_kernel(flow):
    return balance(flow) == (0,) * NVERT and sum(flow) == 0


def conformal(part, whole):
    return all(a == 0 or b == 0 or (a > 0) == (b > 0) for a, b in zip(part, whole))


def main():
    # 1. Kernel characterization: flowLin f = 0 iff balanced and zero-sum.
    checked = 0
    for flow in product(BOX, repeat=NEDGE):
        lhs = flow_lin(flow) == (0,) * (NVERT + 1)
        assert lhs == in_kernel(flow), f"kernel mismatch at {flow}"
        checked += 1
    print(f"flowLin_eq_zero_iff: {checked} flows checked, characterization holds")

    # 2. Concrete displacement and its conformal decomposition.
    # delta = g1 + g2 with both moves sign-compatible with delta.
    g1 = (1, 1, -2)  # kernel here is 1-dim: balanced iff f0 = f1, sum 0 iff f2 = -2*f0
    g2 = (2, 2, -4)
    delta = tuple(a + b for a, b in zip(g1, g2))
    assert in_kernel(g1) and in_kernel(g2) and in_kernel(delta), "moves must be in L0"
    assert conformal(g1, delta) and conformal(g2, delta), "moves must be conformal"
    print(f"conformal decomposition: delta={delta} = {g1} + {g2}")

    # 3. Zero-throughput lift: T = 0 vanishes on L0, lift is (g, 0, 0).
    def lift(g):
        return g + (0,) * NVERT

    w = lift(delta)
    parts = [lift(g1), lift(g2)]
    assert tuple(a + b for a, b in zip(*parts)) == w, "lift must preserve the sum"
    assert all(conformal(p, w) for p in parts), "lifted moves must stay conformal"
    print(f"zero-T lift: {w} = {parts[0]} + {parts[1]}, sign-compatibility holds")

    # 4. The lifted pieces lie in the augmented kernel: edge block balanced
    # and zero-sum, throughput block s - T(edge) = 0 - 0 = 0.
    for p in parts + [w]:
        edge, thru = p[:NEDGE], p[NEDGE:]
        assert in_kernel(edge) and thru == (0,) * NVERT, f"aug kernel failure at {p}"
    print("augLin kernel: lifted moves and total lie in the augmented kernel")

    print("verify_263_graver_throughput_bridge: all checks passed")


if __name__ == "__main__":
    main()
