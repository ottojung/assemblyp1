#!/usr/bin/env python3
"""Independent exact validation for AssemblyP1 issue #261.

Scope: the extension of #260 (full-overlap, fixed-length, RC-molecule ML) to the
general MB09 section 6.2 bidirected overlap domain at arbitrary o_min <= L-1, at the
count-vector x length layer (exact multinomial, Variant E, variable length) and its
synthesis with the section 6.2 flow domain (separable binomial, Variant A, external
N = G).

This script recomputes from scratch, with exact integer/rational arithmetic and no
trust in the Lean output, the finite facts behind
`AssemblyP1/GeneralBidirectedFlowML.lean` and
`docs/issue261-general-bidirected-flow-ml.md`:

  * the variable-length exact-multinomial criterion (density bound) and its
    witnesses: the stretch failure `AATT -> AATATT` and the dilution failure;
  * the rescaling tie: at variable length the k-fold cover S^k of a truth S ties
    with S under the exact objective, so uniqueness of the normalized spectrum is
    impossible at variable length (a phenomenon with no full-overlap analogue);
  * the flow-domain (fixed-external-N multinomial-product) maximality criterion:
    the truth is sample-uniformly maximal over a class of throughput vectors iff
    no admissible throughput strictly dominates the truth spectrum on an observed
    class;
  * the refutation of the claim that the genuine section 6.1 separable binomial
    is coordinatewise: truth A=(1,2), candidate B=(1,1), N=3, x=(2,1) has B<=A
    coordinatewise but the binomial strictly prefers B (core 8 > 4);
  * the failure of that criterion at o_min < L-1: the AAATT instance at o_min = 1
    has non-spelling flow maximizers that beat the truth (ratio 256/81), recomputed
    independently here;
  * the half-integral relaxation gap: the half-integral flow h = (f2 + f3)/2
    beats the integral maximizers by 625/576.

The script is deterministic, exits non-zero on any failed assertion, and shares no
code with the Lean module.
"""
from collections import Counter
from fractions import Fraction
from itertools import product
from math import comb

COMP = {"A": "T", "T": "A", "C": "G", "G": "C"}


def rc(w):
    return "".join(COMP[c] for c in reversed(w))


def canon(w):
    return min(w, rc(w))


def circular_window(S, t, L):
    G = len(S)
    return "".join(S[(t + j) % G] for j in range(L))


def spectrum(S, L):
    """Molecule-class count vector of a circular word."""
    return Counter(canon(circular_window(S, t, L)) for t in range(len(S)))


def cross_lik(d, x, N):
    """Exact multinomial cross-likelihood: (prod_c d[c]**x[c]) * N**(sum x)."""
    p = 1
    n = sum(x.values())
    for c, e in x.items():
        p *= d.get(c, 0) ** e
    return p * N ** n


def exact_lik(d, x, N):
    """Exact multinomial likelihood up to the positive candidate-independent
    factor n! / prod x!:  prod_c (d[c]/N)**x[c]."""
    p = Fraction(1)
    for c, e in x.items():
        p *= Fraction(d.get(c, 0), N) ** e
    return p


def density_bound_holds(A, G, B, N):
    """The variable-length criterion: for all i in supp A, B[i]*G <= A[i]*N."""
    return all(B.get(c, 0) * G <= A[c] * N for c in A)


def check_variable_length_criterion():
    """The density criterion decides sample-uniform exact-E maximality.

    For a truth (A, G) and candidate (B, N), the candidate never beats the truth on
    any observed vector supported inside supp A iff B[i]*G <= A[i]*N for all i in
    supp A.  We verify the equivalence on a finite grid by brute force over all
    supported samples up to a bounded total.
    """
    checked = 0
    for alphabet in ("AT",):
        for G in range(3, 7):
            words = ["".join(t) for t in product(alphabet, repeat=G)]
            specs = {D: spectrum(D, 3) for D in words}
            for S in words:
                A = specs[S]
                for D in words:
                    B = specs[D]
                    for N in range(G, 2 * G + 1):
                        # candidate (B, N): compare against truth (A, G)
                        holds = density_bound_holds(A, G, B, N)
                        # brute-force the sample-uniform comparison
                        robust = True
                        supp = list(A)
                        for total in range(1, 5):
                            for counts in product(range(total + 1), repeat=len(supp)):
                                if sum(counts) != total:
                                    continue
                                x = {c: e for c, e in zip(supp, counts) if e > 0}
                                if not x:
                                    continue
                                if cross_lik(B, x, G) > cross_lik(A, x, N):
                                    robust = False
                                    break
                            if not robust:
                                break
                        assert robust == holds, (S, A, D, B, N, robust, holds)
                        checked += 1
    print(f"[ok] variable-length density criterion on {checked} (truth,candidate,length) triples")


def check_stretch():
    """AATATT (length 6) beats AATT (length 4) on the concentrated sample e_{AT}.

    Class space is the three length-2 submolecule classes over {A,T}:
    W1 = {AA,TT}, W2 = {AT}, W3 = {TA}.  Truth AATT has counts (2,1,1),
    candidate AATATT has counts (2,2,2).  The density bound is violated at W2:
    B[W2]*G = 2*4 = 8 > 1*6 = A[W2]*N.

    This is the variable-length failure with no full-overlap analogue: at full
    overlap the length is fixed by the throughput, so a longer candidate with the
    same read counts cannot exist.
    """
    S, D, L = "AATT", "AATATT", 2
    A, B = spectrum(S, L), spectrum(D, L)
    G, N = len(S), len(D)
    assert (G, N) == (4, 6)
    # Class space (W1={AA,TT}, W2={AT}, W3={TA}): map length-2 classes to W-basis
    def to_w_basis(spec):
        w1 = spec.get("AA", 0) + spec.get("TT", 0)
        w2 = spec.get("AT", 0)
        w3 = spec.get("TA", 0)
        return {"W1": w1, "W2": w2, "W3": w3}
    Aw, Bw = to_w_basis(A), to_w_basis(B)
    assert (Aw["W1"], Aw["W2"], Aw["W3"]) == (2, 1, 1), Aw
    assert (Bw["W1"], Bw["W2"], Bw["W3"]) == (2, 2, 2), Bw
    # density bound violated at W2 (AT): B[W2]*G = 2*4 = 8 > 1*6 = A[W2]*N
    assert Bw["W2"] * G > Aw["W2"] * N
    # concentrated sample x = e_{W2}
    x = {"W2": 1}
    assert cross_lik(Bw, x, G) > cross_lik(Aw, x, N)
    assert exact_lik(Bw, x, G) > exact_lik(Aw, x, N)
    print(f"[ok] stretch failure  S={S} A={Aw} D={D} B={Bw}  beats on e_W2")


def check_dilution():
    """A candidate with the truth's counts but a longer genome is strictly worse."""
    S, L = "AATT", 3
    A = spectrum(S, L)
    G = len(S)
    for N in range(G + 1, G + 4):
        x = dict(A)  # the full observed vector
        assert cross_lik(A, x, G) < cross_lik(A, x, N), (G, N)
    print(f"[ok] dilution  same counts, longer genome is strictly worse (G={G})")


def check_rescaling_tie():
    """At variable length the k-fold cover S^k ties with S under the exact objective.

    S^k is a circular word of length k*G with spectrum k*A, so its normalized
    spectrum equals the truth's and it ties on every sample.  Hence uniqueness of
    the normalized spectrum is impossible at variable length (for any truth and any
    k >= 2), a phenomenon with no full-overlap analogue.
    """
    for S in ("AATT", "AAATAT", "ATATACAC"):
        L = 3
        A = spectrum(S, L)
        G = len(S)
        for k in (2, 3):
            Sk = S * k
            B = spectrum(Sk, L)
            N = len(Sk)
            assert N == k * G
            assert B == {c: k * e for c, e in A.items()}, (S, k, A, B)
            # ties on every supported sample
            supp = list(A)
            for total in range(1, 5):
                for counts in product(range(total + 1), repeat=len(supp)):
                    if sum(counts) != total:
                        continue
                    x = {c: e for c, e in zip(supp, counts) if e > 0}
                    if not x:
                        continue
                    assert cross_lik(B, x, G) == cross_lik(A, x, N), (S, k, x)
            # and the density bound holds with equality
            assert density_bound_holds(A, G, B, N)
            assert all(B[c] * G == A[c] * N for c in A)
    print("[ok] rescaling tie  S^k ties with S for k=2,3 (uniqueness impossible at variable length)")


def binomial_lik(d, x, N):
    """Section 6.1 separable binomial with external N."""
    n = sum(x.values())
    p = Fraction(1)
    for c, e in x.items():
        p *= Fraction(comb(n, e)) * Fraction(d.get(c, 0), N) ** e \
            * Fraction(N - d.get(c, 0), N) ** (n - e)
    return p


def check_flow_domain_counterexample():
    """AAATT at o_min=1: non-spelling flow maximizers beat the truth (binomial).

    Truth S = AAATT (G=5), spectrum d_S = (AAA:1, AAT:2, TAA:2), external N=5,
    observed x = (AAA:2, AAT:1, TAA:1), n=4.  The section 6.1 binomial is
    separable, so the unconstrained integer maximizer over 1 <= d <= 5 is attained
    at the per-coordinate maxima:
      AAA: d^2 (5-d)^2 maximized at d=2,3 (value 36)
      AAT: d (5-d)^3 maximized at d=1 (value 128)
      TAA: same as AAT
    giving the maximizer set {(2,1,1),(3,1,1)} and ratio 256/81 over the truth.
    """
    dS = {"AAA": 1, "AAT": 2, "TAA": 2}
    x = {"AAA": 2, "AAT": 1, "TAA": 1}
    N = 5
    # per-coordinate maxima of the binomial factor d^e (5-d)^(n-e)
    def coord_max(c, e):
        best, arg = -1, []
        for d in range(1, N + 1):
            v = d ** e * (N - d) ** (sum(x.values()) - e)
            if v > best:
                best, arg = v, [d]
            elif v == best:
                arg.append(d)
        return arg
    m_AAA = coord_max("AAA", 2)
    m_AAT = coord_max("AAT", 1)
    m_TAA = coord_max("TAA", 1)
    assert m_AAA == [2, 3], m_AAA
    assert m_AAT == [1], m_AAT
    assert m_TAA == [1], m_TAA
    # the maximizer set
    maximizers = [{"AAA": a, "AAT": 1, "TAA": 1} for a in m_AAA]
    assert maximizers == [{"AAA": 2, "AAT": 1, "TAA": 1},
                          {"AAA": 3, "AAT": 1, "TAA": 1}]
    # the truth is beaten
    ratio = binomial_lik(maximizers[0], x, N) / binomial_lik(dS, x, N)
    assert ratio == Fraction(256, 81), ratio
    # the truth's throughputs are NOT the maximizer
    assert binomial_lik(dS, x, N) < binomial_lik(maximizers[0], x, N)
    # dominance criterion: the maximizer violates coordinatewise dominance
    assert maximizers[0]["AAA"] > dS["AAA"]
    print(f"[ok] flow-domain counterexample  AAATT o_min=1  "
          f"maxima {maximizers}  ratio 256/81 > 1")


def check_half_integral_gap():
    """The half-integral relaxation beats the integral maximizers.

    h = (f2 + f3)/2 has throughput (5/2, 1, 1).  The AAA binomial factor is
    proportional to d^2 (5-d)^2: 36 at d=2,3 but 625/16 at d=5/2.  So
    L(h)/L(f2) = 625/576 > 1.
    """
    x = {"AAA": 2, "AAT": 1, "TAA": 1}
    N = 5

    def aaa_factor(d):
        return Fraction(d) ** 2 * Fraction(N - d) ** 2

    f2, f3 = Fraction(2), Fraction(3)
    h = (f2 + f3) / 2
    assert h == Fraction(5, 2)
    assert aaa_factor(h) == Fraction(625, 16)
    assert aaa_factor(f2) == 36
    assert aaa_factor(f3) == 36
    gap = aaa_factor(h) / aaa_factor(f2)
    assert gap == Fraction(625, 576), gap
    print(f"[ok] half-integral gap  L(h)/L(f2) = 625/576 > 1")


def check_binomial_not_coordinatewise():
    """The genuine §6.1 separable binomial is NOT coordinatewise.

    Truth A=(1,2), candidate B=(1,1), external N=3, sample x=(2,1), n=3.  The
    binomial comparison core (dropping the candidate-independent C(n,x_i) and the
    common N^-n) is  prod_i d_i^{x_i} (N-d_i)^{n-x_i}:
      A: 1^2 (3-1)^1 * 2^1 (3-2)^2 = 2 * 2 = 4
      B: 1^2 (3-1)^1 * 1^1 (3-1)^2 = 2 * 4 = 8
    so B strictly beats A although B<=A coordinatewise on the truth's support.
    Hence coordinatewise dominance is not sufficient for the §6.1 binomial, and
    the Lean `flow_dominance_criterion` (a product-objective criterion) must not be
    cited as the §6.1 binomial criterion.
    """
    A = {0: 1, 1: 2}
    B = {0: 1, 1: 1}
    N = 3
    x = {0: 2, 1: 1}
    assert all(B[c] <= A[c] for c in A)  # coordinatewise dominance holds
    core_A = 1
    core_B = 1
    n = sum(x.values())
    for c, e in x.items():
        core_A *= A[c] ** e * (N - A[c]) ** (n - e)
        core_B *= B[c] ** e * (N - B[c]) ** (n - e)
    assert (core_A, core_B) == (4, 8), (core_A, core_B)
    assert core_B > core_A
    # same conclusion through the full binomial likelihood (coefficients common)
    assert binomial_lik(B, x, N) > binomial_lik(A, x, N)
    print("[ok] §6.1 binomial is not coordinatewise  "
          "A=(1,2) B=(1,1) N=3 x=(2,1)  core 8 > 4")


def check_flow_dominance_criterion():
    """Fixed-external-N multinomial-product maximality iff no flow dominates.

    For the product objective  prod_c B[c]**x[c]  (NOT the §6.1 binomial), with
    external N = G fixed, the comparison holds for every supported x iff no
    candidate throughput B has B[i] > A[i] for some i in supp A.  We verify the
    equivalence on a finite grid.  This is a criterion for the product objective,
    not for the §6.1 separable binomial (see check_binomial_not_coordinatewise).
    """
    checked = 0
    for alphabet in ("AT",):
        for G in range(3, 7):
            words = ["".join(t) for t in product(alphabet, repeat=G)]
            specs = {D: spectrum(D, 3) for D in words}
            for S in words:
                A = specs[S]
                supp = list(A)
                for D in words:
                    B = specs[D]
                    # dominance: B[i] <= A[i] for all i in supp A
                    dominates = any(B.get(c, 0) > A[c] for c in supp)
                    # brute-force sample-uniform comparison (external N = G)
                    robust = True
                    for total in range(1, 5):
                        for counts in product(range(total + 1), repeat=len(supp)):
                            if sum(counts) != total:
                                continue
                            x = {c: e for c, e in zip(supp, counts) if e > 0}
                            if not x:
                                continue
                            if cross_lik(B, x, G) > cross_lik(A, x, G):
                                robust = False
                                break
                        if not robust:
                            break
                    assert robust == (not dominates), (S, A, D, B, robust, dominates)
                    checked += 1
    print(f"[ok] flow-domain dominance criterion on {checked} (truth,flow) pairs")


def main():
    check_variable_length_criterion()
    check_stretch()
    check_dilution()
    check_rescaling_tie()
    check_flow_domain_counterexample()
    check_half_integral_gap()
    check_binomial_not_coordinatewise()
    check_flow_dominance_criterion()
    print("\nALL CHECKS PASSED")


if __name__ == "__main__":
    main()
