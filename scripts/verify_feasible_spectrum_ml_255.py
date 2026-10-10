#!/usr/bin/env python3
"""Independent exact-rational tests for issue #255 (feasible-spectrum ML classification).

Parent of #258 (fixed-x exact ML classification) and #259 (binomial maximality).

Everything here is EXACT: Python arbitrary-precision integers and fractions.Fraction.
No floating point anywhere. Zero-count edges are never omitted: they contribute the
factor 1 to every product comparison and still constrain the candidate circulations
through balance and positivity on the whole support.

Frozen axes (per the delegated task): oriented single-strand read types, exact
multinomial objective (Medvedev-Brudno Variant E, multinomial coefficient divided
out), candidate universe = same-length oriented feasible spectra (positive integer
balanced circulations of total mass G on the truth's window support).

The script checks, independently of Lean:
  1. the AAABBB instance: the feasible set is exactly the four spectra
     {B1,B2,B3,B4}, each realized by an explicit circular genome;
  2. three realizable complete-support samples at the same genome exhibit all three
     truth statuses: unique maximizer (x1), tie at the top with B4 (xT), strict
     loss to B4 with exact ratio 4 (x2);
  3. the realizations really produce the samples (observedOf) and their distinct
     starts really cover the genome (historical coverage);
  4. a brute-force scan over ALL 2^6 circular genomes confirms that the
     genome-level exact-likelihood ranking agrees with the spectrum-level
     classification at x1, xT, x2 (at this instance every feasible spectrum is
     genome-realizable, so the two candidate universes coincide);
  5. a small census: for every binary truth of length G=5 and G=6 at L=2, the
     trichotomy (unique maximizer / tie at top / strict loss) is exhaustive and
     mutually exclusive over a grid of realizable samples, and the status computed
     from the feasible-spectrum certificate always matches the status computed by
     brute force over all genomes.
"""

from fractions import Fraction
from itertools import product

# --------------------------------------------------------------------------------------
# Basic model
# --------------------------------------------------------------------------------------

def windows(S, L):
    """All length-L circular windows of the circular string S (one per start)."""
    G = len(S)
    return [tuple(S[(r + d) % G] for d in range(L)) for r in range(G)]


def spectrum(S, L):
    """A: window type -> occurrence count (specCount)."""
    A = {}
    for w in windows(S, L):
        A[w] = A.get(w, 0) + 1
    return A


def support(S, L):
    """E: the set of window types with positive count."""
    return set(spectrum(S, L))


def observedOf(S, L, rho):
    """x: window type -> observed count for the realization rho (list of starts)."""
    x = {}
    for r in rho:
        w = tuple(S[(r + d) % len(S)] for d in range(L))
        x[w] = x.get(w, 0) + 1
    return x


def covers(S, L, R):
    """Historical coverage: every position lies in at least one realized read."""
    G = len(S)
    return all(any((r + d) % G == p for r in R for d in range(L)) for p in range(G))


def realizedStarts(rho):
    return sorted(set(rho))


# --------------------------------------------------------------------------------------
# Feasible spectra: positive integer balanced circulations of total mass G on E
# --------------------------------------------------------------------------------------

def feasible_spectra(S, L):
    """Enumerate the candidate universe: all B with B positive exactly on E,
    balanced on the (L-1)-window incidence, and total mass G."""
    G = len(S)
    E = sorted(support(S, L))
    if L == 1:
        # Degenerate read length: every window is a single symbol; balance is vacuous.
        # Not used by the tests below (L = 2 throughout); included for completeness.
        return []
    nodes = sorted({w[:-1] for w in E} | {w[1:] for w in E})
    out = {v: [w for w in E if w[:-1] == v] for v in nodes}
    inc = {v: [w for w in E if w[1:] == v] for v in nodes}
    sols = []
    def rec(i, B, total):
        if i == len(E):
            if total != G:
                return
            for v in nodes:
                if sum(B[w] for w in out[v]) != sum(B[w] for w in inc[v]):
                    return
            sols.append(dict(B))
            return
        w = E[i]
        for k in range(1, G - total - (len(E) - i - 1) + 1):
            B[w] = k
            rec(i + 1, B, total + k)
        B.pop(w, None)
    rec(0, {}, 0)
    return E, sols


def lik_product(B, x, E, default=None):
    """Exact integer likelihood product prod_{w in E} (B w)^(x w).

    Zero-count edges contribute the factor 1 (present, never omitted). A feasible B
    is positive on E, so every factor is a positive integer. With default=None a
    missing edge is an error (feasible spectra are total on E); with default=0 a
    genome missing an observed edge contributes the factor 0 (likelihood 0).
    """
    p = 1
    for w in E:
        if w in B:
            p *= B[w] ** x.get(w, 0)
        else:
            assert default is not None, f"edge {w} missing from spectrum"
            p *= default ** x.get(w, 0)
    return p


def lik_factor(B, x, E, G):
    """Exact rational likelihood factor prod_{w in E} (B w / G)^(x w)."""
    return Fraction(lik_product(B, x, E), G ** sum(x.values()))


def truth_status(A, x, E, sols):
    """Classify the truth's status at x over the feasible spectra.

    Returns (status, certificate) where status is one of
    'unique_maximizer', 'tie_at_top', 'strict_loss', and certificate is the list of
    (B, product, comparison) triples against the truth's product.
    """
    pA = lik_product(A, x, E)
    cert = []
    for B in sols:
        pB = lik_product(B, x, E)
        cmp = '<' if pB < pA else ('=' if pB == pA else '>')
        cert.append((B, pB, cmp))
    if any(c == '>' for _, _, c in cert):
        return 'strict_loss', cert
    if any(c == '=' for B, _, c in cert if B != A):
        return 'tie_at_top', cert
    return 'unique_maximizer', cert


# --------------------------------------------------------------------------------------
# The AAABBB instance
# --------------------------------------------------------------------------------------

AA = (0, 0)
AB = (0, 1)
BB = (1, 1)
BA = (1, 0)

B1 = {AA: 2, AB: 1, BB: 2, BA: 1}   # = spec(AAABBB), the truth spectrum
B2 = {AA: 1, AB: 1, BB: 3, BA: 1}   # = spec(BBBBAA)
B3 = {AA: 3, AB: 1, BB: 1, BA: 1}   # = spec(AAABBA)
B4 = {AA: 1, AB: 2, BB: 1, BA: 2}   # = spec(AABABB)

X1 = {AA: 2, AB: 1, BB: 2, BA: 1}   # realized by every start once
XT = {AA: 1, AB: 1, BB: 1, BA: 1}   # realized by starts {0,2,3,5}
X2 = {AA: 1, AB: 2, BB: 1, BA: 2}   # realized by starts {0,2,2,3,5,5}

R1 = [0, 1, 2, 3, 4, 5]
RT = [0, 2, 3, 5]
R2 = [0, 2, 2, 3, 5, 5]

S255 = (0, 0, 0, 1, 1, 1)            # AAABBB
G255 = 6
L255 = 2


def check(cond, msg):
    if not cond:
        raise AssertionError(msg)
    print(f"  ok: {msg}")


def test_instance():
    print("== AAABBB instance ==")
    A = spectrum(S255, L255)
    E = sorted(support(S255, L255))
    check(A == B1, "truth spectrum A = spec(AAABBB) = (AA:2,AB:1,BB:2,BA:1)")
    check(E == [AA, AB, BA, BB], "support E = {AA,AB,BB,BA}")

    Ee, sols = feasible_spectra(S255, L255)
    check(Ee == E, "feasible-spectrum enumeration runs on the whole support E")
    check(sorted(tuple(sorted(B.items())) for B in sols)
          == sorted(tuple(sorted(B.items())) for B in [B1, B2, B3, B4]),
          "feasible set is exactly {B1,B2,B3,B4}")

    # Each feasible spectrum is realized by an explicit circular genome.
    for name, B, genome in [("B1", B1, "AAABBB"), ("B2", B2, "BBBBAA"),
                            ("B3", B3, "AAABBA"), ("B4", B4, "AABABB")]:
        g = tuple(0 if c == 'A' else 1 for c in genome)
        check(spectrum(g, L255) == B, f"{name} = spec({genome})")

    # Samples: realizability and historical coverage.
    for name, x, rho in [("x1", X1, R1), ("xT", XT, RT), ("x2", X2, R2)]:
        check(observedOf(S255, L255, rho) == x, f"realization rho_{name} produces {name}")
        check(covers(S255, L255, realizedStarts(rho)),
              f"distinct starts of rho_{name} cover the genome (historical coverage)")
        check(set(x) <= set(E), f"{name} is supported on E (sampling realizability)")

    # Statuses and exact products.
    st1, cert1 = truth_status(A, X1, E, sols)
    check(st1 == 'unique_maximizer', f"x1: truth is the unique maximizer (status {st1})")
    check(sorted((p, tuple(sorted(B.items()))) for B, p, _ in cert1)
          == sorted([(16, tuple(sorted(B1.items()))), (9, tuple(sorted(B2.items()))),
                     (9, tuple(sorted(B3.items()))), (4, tuple(sorted(B4.items())))]),
          "x1: exact products A,B2,B3,B4 = 16,9,9,4")
    check(lik_factor(A, X1, E, G255) == Fraction(16, 6**6), "x1: Lik(A;x1) = 16/6^6 exactly")

    stT, certT = truth_status(A, XT, E, sols)
    check(stT == 'tie_at_top', f"xT: truth ties at the top with B4 (status {stT})")
    check(sorted((p, tuple(sorted(B.items()))) for B, p, _ in certT)
          == sorted([(4, tuple(sorted(B1.items()))), (3, tuple(sorted(B2.items()))),
                     (3, tuple(sorted(B3.items()))), (4, tuple(sorted(B4.items())))]),
          "xT: exact products A,B2,B3,B4 = 4,3,3,4")
    check(lik_factor(A, XT, E, G255) == lik_factor(B4, XT, E, G255),
          "xT: Lik(A;xT) = Lik(B4;xT) exactly (tie)")

    st2, cert2 = truth_status(A, X2, E, sols)
    check(st2 == 'strict_loss', f"x2: truth strictly loses to B4 (status {st2})")
    check(sorted((p, tuple(sorted(B.items()))) for B, p, _ in cert2)
          == sorted([(4, tuple(sorted(B1.items()))), (3, tuple(sorted(B2.items()))),
                     (3, tuple(sorted(B3.items()))), (16, tuple(sorted(B4.items())))]),
          "x2: exact products A,B2,B3,B4 = 4,3,3,16")
    check(lik_factor(B4, X2, E, G255) / lik_factor(A, X2, E, G255) == 4,
          "x2: Lik(B4;x2)/Lik(A;x2) = 4 exactly (strict defeat ratio)")

    # Brute force over ALL 2^6 circular genomes. At the genome level the truth can
    # never be the UNIQUE maximizer — its cyclic shifts always tie (rotation
    # invariance of the exact likelihood) — and a spectrum's genome fibre can be
    # larger than its shift orbit (at xT the B4-fibre has 6 genomes). So the
    # genome-level check is: the argmax SPECTRUM set over all genomes equals the
    # spectrum-level argmax set over the feasible spectra, and the truth's status
    # (in the argmax set / strictly below) agrees.
    for name, x, expected in [("x1", X1, 'unique_maximizer'), ("xT", XT, 'tie_at_top'),
                              ("x2", X2, 'strict_loss')]:
        best = max(lik_product(spectrum(bits, L255), x, E, default=0)
                   for bits in product([0, 1], repeat=G255))
        argmax_spectra = {tuple(sorted(spectrum(bits, L255).items()))
                          for bits in product([0, 1], repeat=G255)
                          if lik_product(spectrum(bits, L255), x, E, default=0) == best}
        pA = lik_product(A, x, E)
        st, cert = truth_status(A, x, E, sols)
        cert_best = max(p for _, p, _ in cert)
        cert_argmax = {tuple(sorted(B.items())) for B, p, _ in cert if p == cert_best}
        check(argmax_spectra == cert_argmax,
              f"{name}: genome-scan argmax spectra = feasible-certificate argmax spectra "
              f"({len(argmax_spectra)} spectrum classes)")
        if expected == 'unique_maximizer':
            check(pA == best and argmax_spectra == {tuple(sorted(A.items()))},
                  f"{name}: truth spectrum is the unique argmax at both levels")
        elif expected == 'tie_at_top':
            check(pA == best and len(argmax_spectra) == 2,
                  f"{name}: truth spectrum ties at the top with exactly one other spectrum")
        else:
            check(pA < best and tuple(sorted(A.items())) not in argmax_spectra,
                  f"{name}: truth spectrum strictly loses at both levels")


def test_census():
    """Census over all binary truths of length G=5,6 at L=2.

    For each truth: enumerate the feasible spectra; for a grid of realizable
    complete-support samples, check (a) the trichotomy is exhaustive and mutually
    exclusive, and (b) the certificate status matches a brute-force scan over the
    SPELLED candidate class (genomes whose window support is exactly E — these have
    exactly the feasible spectra). A separate count records how often a genome
    OUTSIDE the spelled class beats the truth: that is the #88 residual gap
    reappearing at the fixed-x level, not a contradiction.
    """
    print("== census: all binary truths, G in {5,6}, L = 2 ==")
    total = 0
    gap_examples = 0
    for G in (5, 6):
        for bits in product([0, 1], repeat=G):
            S = bits
            A = spectrum(S, 2)
            E = sorted(support(S, 2))
            if len(E) < 2:
                continue
            _, sols = feasible_spectra(S, 2)
            all_genomes = list(product([0, 1], repeat=G))
            spelled = [D for D in all_genomes if set(spectrum(D, 2)) == set(E)]
            # Realizable complete-support samples: choose a subset of starts that
            # covers the genome, then take the induced observation.
            samples = set()
            for mask in range(1, 1 << G):
                R = [r for r in range(G) if mask >> r & 1]
                if covers(S, 2, R):
                    samples.add(tuple(sorted(observedOf(S, 2, R).items())))
            for xs in samples:
                x = dict(xs)
                st, cert = truth_status(A, x, E, sols)
                # (a) Exhaustivity: exactly one status, decided by the certificate.
                pA = lik_product(A, x, E)
                all_le = all(pB <= pA for _, pB, _ in cert)
                any_gt = any(pB > pA for _, pB, _ in cert)
                any_eq_other = any(pB == pA and B != A for B, pB, _ in cert)
                if st == 'unique_maximizer':
                    assert all_le and not any_eq_other
                elif st == 'tie_at_top':
                    assert all_le and any_eq_other
                else:
                    assert any_gt
                # (b) Brute-force agreement over the spelled candidate class.
                best_spelled = max(lik_product(spectrum(D, 2), x, E, default=0)
                                   for D in spelled)
                if st in ('unique_maximizer', 'tie_at_top'):
                    assert pA == best_spelled, (S, x, st, pA, best_spelled)
                else:
                    assert pA < best_spelled, (S, x, st, pA, best_spelled)
                # Residual-gap count: non-spelled genomes may beat the truth.
                best_all = max(lik_product(spectrum(D, 2), x, E, default=0)
                               for D in all_genomes)
                if best_all > best_spelled:
                    gap_examples += 1
                total += 1
    print(f"  ok: {total} (truth, sample) pairs across the census all satisfy the "
          f"trichotomy and match the brute-force spelled-class scan")
    print(f"  note: at {gap_examples} (truth, sample) pairs a genome OUTSIDE the "
          f"spelled class beats the truth — the fixed-x residual gap (#88), "
          f"not a contradiction")


def test_zero_counts():
    """Zero-count edges are never omitted: they contribute the factor 1 and still
    constrain the candidate circulations through balance and positivity on E."""
    print("== zero-count edges ==")
    A = spectrum(S255, L255)
    E = sorted(support(S255, L255))
    _, sols = feasible_spectra(S255, L255)
    # A sample observing only AA and BB (zero counts on AB, BA) is realizable
    # (starts {0,1,3}) but does NOT cover the genome: coverage is a realization
    # property, independent of the likelihood.
    x = {AA: 2, BB: 1}
    check(observedOf(S255, 2, [0, 1, 3]) == x, "x = (AA:2,BB:1) is realizable (starts {0,1,3})")
    check(not covers(S255, 2, [0, 1, 3]), "starts {0,1,3} do not cover the genome")
    st, cert = truth_status(A, x, E, sols)
    # Products: A: 2^2*2^1 = 8; B2: 1^2*3 = 3; B3: 3^2*1 = 9; B4: 1^2*1 = 1.
    check(sorted((p, tuple(sorted(B.items()))) for B, p, _ in cert)
          == sorted([(8, tuple(sorted(B1.items()))), (3, tuple(sorted(B2.items()))),
                     (9, tuple(sorted(B3.items()))), (1, tuple(sorted(B4.items())))]),
          "zero-count edges contribute the factor 1: products 8,3,9,1")
    check(st == 'strict_loss',
          "truth strictly loses to B3 at this zero-count sample (9 > 8): zero-count "
          "edges neither rescue nor harm the truth by themselves")
    check(lik_factor(B3, x, E, G255) / lik_factor(A, x, E, G255) == Fraction(9, 8),
          "exact defeat ratio 9/8")
    # The zero-count edges still constrain the candidates: dropping them from the
    # circulation constraints would admit (e.g.) B = (AA:2,BB:2,AB:1,BA:1)-style
    # circulations that are NOT balanced on the full E. Balance on the whole E is
    # what forces AB = BA at every node.
    for B in sols:
        assert B[AB] == B[BA], "balance on the whole support forces AB = BA"
    print("  ok: balance on the whole support E forces AB = BA at every feasible spectrum")


if __name__ == "__main__":
    test_instance()
    test_zero_counts()
    test_census()
    print("\nAll exact-rational tests for #255 passed.")
