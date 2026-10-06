#!/usr/bin/env python3
"""Exhaustive evidence for the generic #94 conjugacy adapter (board 94, front
`94conj`), companion to `AssemblyP1/Issue94ConjugacyAdapter.lean`.

Setup (exactly the objects of the Lean module):

  * circle of `K` positions, word `S : Fin K -> alpha`, window length `L`
    (so the vertex of the `(L-1)`-mer graph at a start `r` is
    `S r, ..., S (r + L - 2)`, i.e. `vtx hK L S r` of
    `AssemblyP1/BBTCondense.lean`);
  * `rho = nextPos hK`, the one-step rotation of the circle;
  * transition maps `f, f' : Fin K -> Fin K`;  `jump hK f = f o rho`;
  * `f` is **label preserving**: `vtx (f q) = vtx q` for every start;
  * `J = jump f` and `J' = jump f'` are both **single** `K`-cycles
    (`VisitsAll`), so `sigFun hK f i = J^[i] 0` and `sigFun hK f' i = (J')^[i] 0`
    are permutations (`Issue94Reconstruct.sigEquiv`);
  * a **vtx-preserving conjugacy** `h` between `J` and `J'`:
    `h (J q) = J' (h q)` and `vtx (h q) = vtx q`.  Conjugacies between two
    `K`-cycles are in bijection with the image of the base point, so the list of
    them is obtained by letting `h (0)` range over `Fin K` and forcing
    `h (J^[i] 0) = (J')^[i] (h 0)`.

The two readings of "rotation" that the module keeps apart:

  * **listing index** -- rotate the *position in the listing*: `i |-> i + k`.
    The conjugacy delivers this for free (`listingIndex_conj`);
  * **genomic coordinate** -- rotate the *start* that a listing position reads:
    `q |-> q + k`.  This is what `BBTEulerian.VertexCycleEq` quantifies over
    (`vtx hK L S (sig i) = vtx hK L S (rotAdd hK k (sig' i))`), and it is a
    strictly different statement.

Predicates checked at every instance:

  C1  a vtx-preserving conjugacy implies the **listing-index** version.
      (kernel: `Issue94ConjugacyAdapter.listingIndex_conj`)
  C2  `RotAligned` implies the **genomic** version.
      (kernel: `Issue94ConjugacyAdapter.vertexCycleEq_of_conjugacy`)
  C3  a vtx-preserving conjugacy does **not** imply the genomic version.
      (kernel refutation: `Issue94ConjugacyAdapter.not_vertexCycleEq_000001`)
  C4  if `jump f' = nextPos` then `RotAligned` holds at `k = h (0)` for every
      conjugacy, so C1 does imply the genomic version.
      (kernel: `Issue94ConjugacyAdapter.vertexCycleEq_of_conj_nextPos`)
  C5  `rotAdd k` centralises `jump f'` iff it centralises `f'`.
      (kernel: `Issue94ConjugacyAdapter.jump_commute_iff`)

Run:  `python3 scripts/verify_conjugacy_adapter_94.py [--maxk 7]`
"""

from __future__ import annotations

import argparse
import itertools
import sys


# ---------------------------------------------------------------- primitives


def rot(k: int, q: int, n: int) -> int:
    return (q + k) % n


def perms(n: int):
    return itertools.permutations(range(n))


def is_single_cycle(J, n: int) -> bool:
    """`VisitsAll J 0`: the `K` iterates of `J` at `0` are pairwise distinct."""
    seen = set()
    x = 0
    while x not in seen:
        seen.add(x)
        x = J[x]
    return len(seen) == n


def vtx(S, L: int):
    """`vtx hK L S r` for every start, as a list of tuples."""
    n = len(S)
    m = L - 1
    return [tuple(S[(r + d) % n] for d in range(m)) for r in range(n)]


def orbit(J, n: int):
    """`sigFun hK f i = J^[i] 0` for `i = 0 .. n-1`."""
    out = []
    x = 0
    for _ in range(n):
        out.append(x)
        x = J[x]
    return out


def conj_of_base(J, Jp, sig, n: int, h0: int):
    """The unique conjugacy `h` with `h 0 = h0`; `None` if not a permutation."""
    h = [None] * n
    x = h0
    for i in range(n):
        h[sig[i]] = x
        x = Jp[x]
    return h


# --------------------------------------------------------------- predicates


def listing_index_eq(V, sig, sigp, n) -> bool:
    """`ListingIndexEq`: rotation by `k` on the *listing index*, i.e. the
    position read by the prime listing is moved from `i` to `i + k`."""
    return any(
        all(V[sig[i]] == V[sigp[rot(k, i, n)]] for i in range(n))
        for k in range(n)
    )


def listing_vertex_eq(V, sig, sigp, n) -> bool:
    """`ListingVertexEq` = `VertexCycleEq`: rotation by `k` on *genomic starts*."""
    return any(
        all(V[sig[i]] == V[rot(k, sigp[i], n)] for i in range(n))
        for k in range(n)
    )


def rot_aligned(V, Jp, h, n) -> bool:
    """`RotAligned hK J' (h 0) h` for the forced witness `k = h (origin)`."""
    k = h[0]
    if h[0] != rot(k, 0, n):
        return False
    return all(Jp[rot(k, x, n)] == rot(k, Jp[x], n) for x in range(n))


# ------------------------------------------------------------------ the scan


def scan(n: int, L: int, alpha: int, counters: dict) -> None:
    rho = [rot(1, q, n) for q in range(n)]
    for S in itertools.product(range(alpha), repeat=n):
        V = vtx(list(S), L)

        # label-preserving permutations of the starts
        lp = [f for f in perms(n) if all(V[f[q]] == V[q] for q in range(n))]
        if not lp:
            continue
        # ... whose jump is a single K-cycle (a genuine alternative traversal)
        LP = [f for f in lp if is_single_cycle([f[rho[q]] for q in range(n)], n)]
        if not LP:
            continue

        for f in LP:
            J = [f[rho[q]] for q in range(n)]
            sig = orbit(J, n)
            for fp in LP:
                Jp = [fp[rho[q]] for q in range(n)]
                sigp = orbit(Jp, n)
                vce = listing_vertex_eq(V, sig, sigp, n)

                for h0 in range(n):
                    h = conj_of_base(J, Jp, sig, n, h0)
                    if sorted(h) != list(range(n)):
                        continue
                    if not all(V[h[q]] == V[q] for q in range(n)):
                        continue  # not vtx-preserving
                    counters["conjugacies"] += 1

                    # C1: listing-index rotation is free
                    if not listing_index_eq(V, sig, sigp, n):
                        counters["c1_violations"] += 1
                    # C3: genomic rotation need not follow
                    if not vce:
                        counters["c3_counterexamples"] += 1
                        if counters["c3_first"] is None:
                            counters["c3_first"] = (n, L, tuple(S), tuple(f),
                                                    tuple(fp), tuple(h))
                    # C2: RotAligned implies the genomic version
                    if rot_aligned(V, Jp, h, n) and not vce:
                        counters["c2_violations"] += 1
                    # C4: jump f' = nextPos  =>  RotAligned at k = h 0
                    if Jp == rho:
                        counters["c4_instances"] += 1
                        if not rot_aligned(V, Jp, h, n):
                            counters["c4_violations"] += 1
                        if not vce:
                            counters["c4_counterexamples"] += 1
                    # C5: centralising the jump iff centralising f'
                    for k in range(n):
                        a = all(Jp[rot(k, x, n)] == rot(k, Jp[x], n)
                                for x in range(n))
                        b = all(fp[rot(k, x, n)] == rot(k, fp[x], n)
                                for x in range(n))
                        if a != b:
                            counters["c5_violations"] += 1

                counters["instances"] += 1


def refuted_instance():
    """The Lean refutation instance, spelled out and re-checked here."""
    n, L = 5, 3
    S = [0, 0, 0, 0, 1]
    rho = [rot(1, q, n) for q in range(n)]
    f = [0, 1, 2, 3, 4]
    fp = [1, 2, 0, 3, 4]
    h = [1, 0, 2, 3, 4]
    V = vtx(S, L)
    J = [f[rho[q]] for q in range(n)]
    Jp = [fp[rho[q]] for q in range(n)]
    sig = orbit(J, n)
    sigp = orbit(Jp, n)
    out = {
        "vtx": V,
        "J": J,
        "Jprime": Jp,
        "J_single": is_single_cycle(J, n),
        "Jprime_single": is_single_cycle(Jp, n),
        "sigma": sig,
        "sigma_prime": sigp,
        "h": h,
        "h_is_conjugacy": all(h[J[q]] == Jp[h[q]] for q in range(n)),
        "h_is_vtx_preserving": all(V[h[q]] == V[q] for q in range(n)),
        "forced_witness_k_eq_h_origin": h[0],
        "orbit_index_k0_of_h_origin": sigp.index(h[0]),
        "listing_index_eq": listing_index_eq(V, sig, sigp, n),
        "listing_vertex_eq": listing_vertex_eq(V, sig, sigp, n),
        "rot_aligned_at_forced_k": rot_aligned(V, Jp, h, n),
    }
    assert out["J_single"] and out["Jprime_single"], "both jumps must be single"
    assert out["h_is_conjugacy"], "h must be a conjugacy"
    assert out["h_is_vtx_preserving"], "h must preserve the labelling"
    assert out["listing_index_eq"], "C1 must hold here"
    assert not out["listing_vertex_eq"], "C3: the refutation"
    assert not out["rot_aligned_at_forced_k"], "and the condition must fail"
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--maxk", type=int, default=7)
    args = ap.parse_args()

    print(refuted_instance())

    ranges = [(k, L, 2) for k in range(3, args.maxk + 1) for L in (3, 4)
              if L <= k]
    ranges += [(k, 3, 3) for k in range(3, min(args.maxk, 6) + 1)]

    total = dict(instances=0, conjugacies=0, c1_violations=0, c2_violations=0,
                 c3_counterexamples=0, c3_first=None, c4_instances=0,
                 c4_violations=0, c4_counterexamples=0, c5_violations=0)
    for (k, L, alpha) in ranges:
        scan(k, L, alpha, total)
        print(f"scanned K={k} L={L} alpha={alpha}", file=sys.stderr)

    print()
    print(f"(f, f') pairs with both jumps single : {total['instances']}")
    print(f"vtx-preserving conjugacies            : {total['conjugacies']}")
    print(f"C1 violations (listing index)         : {total['c1_violations']}")
    print(f"C2 violations (RotAligned)            : {total['c2_violations']}")
    print(f"C3 counterexamples (genomic)          : "
          f"{total['c3_counterexamples']}")
    print(f"C4 instances (jump f' = nextPos)      : {total['c4_instances']}")
    print(f"C4 violations of RotAligned           : {total['c4_violations']}")
    print(f"C4 counterexamples (conj -> genomic)  : "
          f"{total['c4_counterexamples']}")
    print(f"C5 violations (jump iff f')           : {total['c5_violations']}")
    print(f"smallest C3 counterexample            : {total['c3_first']}")

    bad = (total["c1_violations"] or total["c2_violations"]
           or total["c4_violations"] or total["c4_counterexamples"]
           or total["c5_violations"])
    if bad:
        print("\nFAIL: a positive prediction of the kernel lemmas was violated")
        return 1
    if total["c3_counterexamples"] == 0:
        print("\nINCONCLUSIVE: C3 found no counterexample; the refutation of the "
              "conjugacy => VertexCycleEq inference is not corroborated here")
        return 1
    print("\nOK: C1, C2, C4, C5 hold everywhere searched; C3 fails, as the "
          "kernel refutation requires")
    return 0


if __name__ == "__main__":
    sys.exit(main())