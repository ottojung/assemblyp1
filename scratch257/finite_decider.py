"""Independent cross-check of the finite rigidity decider (issue #257).

The finite decider of `AssemblyP1/FiniteRigidityDecider.lean` says:

    A is rigid  <=>  every B : E -> {1,...,G} that is balanced and has
                     sum B = G equals A.

This script re-implements that decider *independently* (a full
`itertools.product(range(G+1), repeat=m)` sweep with a zero-coordinate
rejection) and cross-checks it against the backtracking brute force of
`rigidity.is_rigid` on exhaustive small cases.  It also checks the concrete
worked instances of the Lean module and the failed-hypothesis counterexamples.

Run:  python3 scratch257/finite_decider.py
"""
from itertools import product

from rigidity import out_in, is_rigid, enum_positive_circulations
from explore import is_strongly_connected, every_edge_on_cycle
from test_n4 import all_digraphs_n


def finite_decider_rigid(n, arcs, A):
    """The finite decider: enumerate the full product (G+1)^m, reject zeros.

    Returns (rigid, first_witness_or_None). Independent of the backtracking
    brute force: no pruning, pure product enumeration of the *bounded* box
    B_e in {0,...,G} (0 rejected) from the coordinate bound 1 <= B_e <= G.
    """
    G = sum(A)
    m = len(arcs)
    out, inn = out_in(n, arcs)
    A = tuple(A)
    for B in product(range(G + 1), repeat=m):
        if any(x == 0 for x in B):          # positivity: B_e >= 1
            continue
        if sum(B) != G:                     # fixed total mass
            continue
        if any(sum(B[e] for e in out[v]) != sum(B[e] for e in inn[v])
               for v in range(n)):          # vertex balance
            continue
        if B != A:
            return (False, B)
    return (True, None)


def cross_check(n, max_m, max_g_mult, label, size_cap=2_000_000):
    tested = 0
    skipped = 0
    rigid = 0
    nonrigid = 0
    mismatch = []
    for arcs in all_digraphs_n(n):
        if not is_strongly_connected(n, arcs):
            continue
        if not every_edge_on_cycle(n, arcs):
            continue
        m = len(arcs)
        if m > max_m:
            continue
        for G in range(m, max_g_mult * m + 1):
            if (G + 1) ** m > size_cap:
                skipped += 1
                continue
            for A in enum_positive_circulations(n, arcs, G):
                bf_rigid, _ = is_rigid(n, arcs, A)
                dec_rigid, _ = finite_decider_rigid(n, arcs, A)
                tested += 1
                rigid += bf_rigid
                nonrigid += (not bf_rigid)
                if bf_rigid != dec_rigid:
                    mismatch.append((arcs, A, bf_rigid, dec_rigid))
    print(f"{label}: tested={tested} rigid={rigid} nonrigid={nonrigid} "
          f"skipped_large={skipped} mismatch={len(mismatch)}")
    for mm in mismatch[:10]:
        print("  MISMATCH", mm)
    return len(mismatch)


def worked_instances():
    print("worked instances (finite decider):")
    cases = [
        ("ATATAT L=3 (rigid despite triples)", 2, [(0, 1), (1, 0)], [3, 3], True),
        ("AAAAB L=2 (non-rigid genome)", 2, [(0, 0), (0, 1), (1, 0)], [3, 1, 1], False),
        ("figure-eight A=(1,1,1,1) (rigid)", 3,
         [(0, 1), (1, 0), (0, 2), (2, 0)], [1, 1, 1, 1], True),
        ("figure-eight A=(2,2,1,1) (non-rigid)", 3,
         [(0, 1), (1, 0), (0, 2), (2, 0)], [2, 2, 1, 1], False),
    ]
    ok = True
    for name, n, arcs, A, expected in cases:
        got, wit = finite_decider_rigid(n, arcs, A)
        status = "OK" if got == expected else "FAIL"
        ok = ok and got == expected
        print(f"  [{status}] {name}: rigid={got} (expected {expected}) witness={wit}")
    return ok


def main():
    ok = worked_instances()
    m3 = cross_check(3, max_m=6, max_g_mult=3, label="n=3, m<=6, G<=3m")
    m4 = cross_check(4, max_m=5, max_g_mult=2, label="n=4, m<=5, G<=2m")
    total_mismatch = m3 + m4
    print(f"TOTAL mismatch = {total_mismatch}; worked instances ok = {ok}")
    assert ok, "worked instance mismatch"
    assert total_mismatch == 0, "decider/brute-force mismatch"


if __name__ == "__main__":
    main()
