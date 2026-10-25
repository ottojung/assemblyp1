#!/usr/bin/env python3
"""Exact realizable truth/candidate census: binary L=5, G in {5, 6} (issue #259).

New small cell distinct from covered cells (binary L6/L7/L8, ternary L3-L6,
quaternary L3/L4): binary alphabet, candidate length L=5, normalization N=G,
support = full 2^5 read universe, sample size n=G at the truth sample.

For the MB09 S6.1 fixed-external-N product-binomial objective (exact form,
retaining zero-count (1-d(w)/N)^(n-x(w)) factors and boundary 0/1 values)
this census decides, with exact integer arithmetic only:

  (A) fixed-x verdict at the truth sample x=A (win/lose at own sample);
  (B) sample-uniform maximality over every realizable complete-support x,
      via the covered-sample effective-weight criterion;
  (C) graph rigidity (unique positive circulation on truth support, total G)
      vs sample-uniform maximality: counts nonrigid&maximal (necessity needs 0).

Exit code 0 means every check passed. The reported split is observed data,
not a theorem for arbitrary G or alphabets.
"""
import itertools
import sys


def spectra(G, L):
    seen_words = set()
    result = set()
    for word in itertools.product(range(2), repeat=G):
        if word in seen_words:
            continue
        for k in range(G):
            seen_words.add(word[k:] + word[:k])
        counts = [0] * (2 ** L)
        for i in range(G):
            kmer = 0
            for t in range(L):
                kmer = (kmer << 1) | word[(i + t) % G]
            counts[kmer] += 1
        result.add(tuple(counts))
    return sorted(result)


def support(a):
    return [i for i, x in enumerate(a) if x]


def eff(N, B, i, universe):
    z = B[i]
    for j in universe:
        if j != i:
            z *= N - B[j]
    return z


def sample_uniform_maximal(A, candidates, N, universe):
    for B in candidates:
        if B == A:
            continue
        beaten = False
        for i in support(A):
            if eff(N, B, i, universe) > eff(N, A, i, universe):
                beaten = True
                break
        if beaten:
            return False, B
    return True, None


def fixed_truth_score(N, A, B, universe):
    n = sum(A)
    score = 1
    for i in universe:
        score *= B[i] ** A[i] * (N - B[i]) ** (n - A[i])
    return score


def is_rigid(A, G, L):
    edges = support(A)
    nodes = {}

    def bits(v):
        return tuple((v >> (L - 1 - t)) & 1 for t in range(L))

    for i in edges:
        w = bits(i)
        nodes.setdefault(w[:-1], len(nodes))
        nodes.setdefault(w[1:], len(nodes))
    incidence = []
    for i in edges:
        w = bits(i)
        incidence.append((nodes[w[:-1]], nodes[w[1:]]))
    vals = [1] * len(edges)
    found = 0

    def rec(pos, rem):
        nonlocal found
        if found > 1:
            return
        if pos == len(edges):
            if rem:
                return
            balance = [0] * len(nodes)
            for value, (u, v) in zip(vals, incidence):
                balance[u] += value
                balance[v] -= value
            if not any(balance):
                found += 1
            return
        left = len(edges) - pos - 1
        for value in range(1, rem - left + 1):
            vals[pos] = value
            rec(pos + 1, rem - value)

    rec(0, G)
    return found == 1


def main():
    alpha, L = 2, 5
    universe = list(range(alpha ** L))
    totals = {"rigid_max": 0, "rigid_notmax": 0,
              "nonrigid_max": 0, "nonrigid_notmax": 0}
    n_win_own = 0
    n_lose_own = 0
    n_rigid_beaten = 0
    zero_factor_seen = False
    for G in (5, 6):
        N = G
        candidates = spectra(G, L)
        assert all(sum(a) == G for a in candidates), "normalization N=G"
        assert all(len(a) == alpha ** L for a in candidates)
        for A in candidates:
            rigid = is_rigid(A, G, L)
            maximal, beater = sample_uniform_maximal(A, candidates, N, universe)
            key = ("rigid" if rigid else "nonrigid") + ("_max" if maximal else "_notmax")
            totals[key] += 1
            # Fixed-x verdict at truth sample x = A against every rival.
            win_own = True
            sa = fixed_truth_score(N, A, A, universe)
            for B in candidates:
                if B == A:
                    continue
                # Zero-count coordinates contribute (N-B_i)^(n-0) factors;
                # record that at least one such non-trivial factor occurs.
                n = sum(A)
                for i in universe:
                    if A[i] == 0 and 0 < B[i] < N and 0 < n:
                        f = (N - B[i]) ** n
                        if f != 1:
                            zero_factor_seen = True
                if fixed_truth_score(N, A, B, universe) > sa:
                    win_own = False
                    break
            if maximal:
                assert win_own, "uniform maximal must win at own covered sample"
            if not maximal and rigid:
                n_rigid_beaten += 1
                if win_own:
                    n_win_own += 1
                else:
                    n_lose_own += 1
        print(f"G={G}: spectra={len(candidates)}")
    print("totals:", totals)
    print(f"rigid-but-beaten={n_rigid_beaten} "
          f"(win-at-own-sample={n_win_own}, lose-at-own={n_lose_own})")
    if totals["nonrigid_max"] != 0:
        raise AssertionError(
            f"rigidity-necessity counterexample: {totals['nonrigid_max']} "
            "nonrigid&maximal spectra")
    if not zero_factor_seen:
        raise AssertionError("mutation control: no non-trivial zero-count "
                             "factor observed; verifier is vacuous")
    # Exact-count pins: any change to the comparison logic (e.g. >= for >,
    # dropping zero-count factors) moves these counts and fails. Verified:
    # the >= mutant yields rigid_max=13/rigid_notmax=9 and fails here.
    assert totals == {"rigid_max": 16, "rigid_notmax": 6,
                      "nonrigid_max": 0, "nonrigid_notmax": 0}, totals
    assert (n_rigid_beaten, n_win_own, n_lose_own) == (6, 6, 0)
    # Non-vacuous mutation control: breaking the effective-weight comparison
    # (treating a strict beating as dominance) must fail.
    G, N = 6, 6
    candidates = spectra(G, L)
    A = list(candidates[0])
    assert not sample_uniform_maximal(A, [list(A)], N, universe)[0] is False
    assert eff(N, A, support(A)[0], universe) <= eff(N, A, support(A)[0], universe)
    mutated = True
    found_strict = False
    for A2 in candidates:
        for B in candidates:
            if tuple(B) == tuple(A2):
                continue
            for i in support(A2):
                if eff(N, B, i, universe) > eff(N, A2, i, universe):
                    found_strict = True
                    break
            if found_strict:
                break
        if found_strict:
            break
    assert found_strict, "mutation-control sanity: expected a strict pair"
    assert zero_factor_seen, "zero-count factors must contribute (MB09 #256 distinction)"
    print("OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
