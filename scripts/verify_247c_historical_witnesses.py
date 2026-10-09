#!/usr/bin/env python3
"""Independent validation for Antonina #247 lane 247c.

Recomputes from scratch, against the exact Lean predicates:
  * observed read multiset from the sampled starts (strand level),
  * molecule-class observed counts x,
  * truth/competitor spectra d_S, d_D,
  * historical read-string coverage (strand level AND molecule-class level),
  * old sampled-base coverage (SourceFaithfulIs.Covers),
  * DenseSampledStarts certificate,
  * exact multinomial ratio and fixed-N binomial ratio,
  * support equality / per-occurrence feasibility,
for the two same-length Section 6.2 molecule-flow witnesses:

  W1: S=AAATAT, D=AAAAAT, G=6, L=3, starts [0,0,1,3,5]  (exact 3, binomial 5)
  W2: S=ATATACAC, D=ATACACAC, G=8, L=3, starts [1,3,4,5,6,7]
      (per-occurrence; exact 3/2, binomial 9/5)

No Lean output is trusted; everything is recomputed here.
"""
from fractions import Fraction
from math import comb

COMP = {'A': 'T', 'T': 'A', 'C': 'G', 'G': 'C'}


def rc(w):
    return ''.join(COMP[c] for c in reversed(w))


def window(S, G, L, t):
    return ''.join(S[(t + j) % G] for j in range(L))


def check(name, S, D, starts, L, N, exact_ratio, binomial_ratio):
    G = len(S)
    assert len(D) == G, "same-length witness required"
    print(f"=== {name}: S={S} D={D} G={G} L={L} starts={starts} ===")

    # observed strands and molecule classes
    obs_strands = [window(S, G, L, r) for r in starts]
    obs_classes = [min(w, rc(w)) for w in obs_strands]
    x = {}
    for c in obs_classes:
        x[c] = x.get(c, 0) + 1
    print(f"observed strands: {sorted(set(obs_strands))}")
    print(f"observed classes x: {dict(sorted(x.items()))}")

    # spectra
    dS = {}
    dD = {}
    for t in range(G):
        cs = min(window(S, G, L, t), rc(window(S, G, L, t)))
        cd = min(window(D, G, L, t), rc(window(D, G, L, t)))
        dS[cs] = dS.get(cs, 0) + 1
        dD[cd] = dD.get(cd, 0) + 1
    print(f"d_S: {dict(sorted(dS.items()))}")
    print(f"d_D: {dict(sorted(dD.items()))}")

    # historical coverage, strand level: forall t, exists observed strand w and
    # delta < L-1 with w = window((t+delta) % G)
    strand_fail = []
    for t in range(G):
        ok = any(window(S, G, L, (t + d) % G) in set(obs_strands)
                 for d in range(L - 1))
        if not ok:
            strand_fail.append(t)
    print(f"historical coverage (strand level): "
          f"{'PASS' if not strand_fail else f'FAIL at t={strand_fail}'}")

    # historical coverage, molecule-class level
    class_fail = []
    for t in range(G):
        ok = any(min(window(S, G, L, (t + d) % G), rc(window(S, G, L, (t + d) % G)))
                 in set(obs_classes) for d in range(L - 1))
        if not ok:
            class_fail.append(t)
    print(f"historical coverage (class level): "
          f"{'PASS' if not class_fail else f'FAIL at t={class_fail}'}")

    # old sampled-base coverage: every position p in some read [r, r+L)
    base_fail = []
    for p in range(G):
        if not any((p - r) % G < L for r in starts):
            base_fail.append(p)
    print(f"old Covers (sampled-base): "
          f"{'PASS' if not base_fail else f'FAIL at p={base_fail}'}")

    # DenseSampledStarts: distinct starts, cyclic gaps <= L-1
    distinct = sorted(set(starts))
    gaps = [distinct[i + 1] - distinct[i] for i in range(len(distinct) - 1)]
    gaps.append(distinct[0] + G - distinct[-1])
    dense = all(g <= L - 1 for g in gaps)
    print(f"DenseSampledStarts: distinct={distinct} gaps={gaps} -> {dense}")

    # exact multinomial ratio: prod_c d_c^{x_c}
    def exact(d):
        v = Fraction(1)
        for c, xc in x.items():
            v *= Fraction(d.get(c, 0)) ** xc
        return v
    eS, eD = exact(dS), exact(dD)
    print(f"exact: L(S)={eS} L(D)={eD} ratio={eD / eS} "
          f"(expected {exact_ratio}) {'OK' if eD / eS == exact_ratio else 'MISMATCH'}")

    # fixed-N binomial ratio with zero-count factors retained
    n = len(starts)
    def lik(d):
        v = Fraction(1)
        for c, xc in x.items():
            v *= comb(n, xc) * Fraction(d.get(c, 0), N) ** xc \
                * (1 - Fraction(d.get(c, 0), N)) ** (n - xc)
        return v
    lS, lD = lik(dS), lik(dD)
    print(f"binomial: L(S)={lS} L(D)={lD} ratio={lD / lS} "
          f"(expected {binomial_ratio}) {'OK' if lD / lS == binomial_ratio else 'MISMATCH'}")

    # support equality and per-occurrence feasibility
    sup = all((dS.get(c, 0) > 0) == (x.get(c, 0) > 0) and
              (dD.get(c, 0) > 0) == (x.get(c, 0) > 0) for c in set(x) | set(dS) | set(dD))
    per = all(x.get(c, 0) <= dS.get(c, 0) and x.get(c, 0) <= dD.get(c, 0)
              for c in set(x) | set(dS) | set(dD))
    print(f"support equality: {sup}; per-occurrence feasible: {per}")
    print()
    return not strand_fail and not class_fail and dense \
        and eD / eS == exact_ratio and lD / lS == binomial_ratio and sup


ok1 = check("W1 SameLengthSection62Counterexample", "AAATAT", "AAAAAT",
           [0, 0, 1, 3, 5], 3, 6, Fraction(3), Fraction(5))
ok2 = check("W2 PerOccurrenceSameLengthCounterexample", "ATATACAC", "ATACACAC",
           [1, 3, 4, 5, 6, 7], 3, 8, Fraction(3, 2), Fraction(9, 5))

# Incomparability regressions from the #247 source audit.
print("=== Regression A: S=AAAA G=4 L=3 starts [0] ===")
print("  historical (strand):", "PASS" if all(
    any(window("AAAA", 4, 3, (t + d) % 4) == "AAA" for d in range(2))
    for t in range(4)) else "FAIL")
print("  old Covers:", "PASS" if all((p - 0) % 4 < 3 for p in range(4)) else "FAIL")
print("=== Regression B: S=ACGT G=4 L=2 starts [0,2] ===")
print("  historical (strand):", "PASS" if all(
    any(window("ACGT", 4, 2, (t + d) % 4) in {"AC", "GT"} for d in range(1))
    for t in range(4)) else "FAIL")
print("  old Covers:", "PASS" if all(any((p - r) % 4 < 2 for r in [0, 2])
                                    for p in range(4)) else "FAIL")

print()
print(f"W1 fully validated: {ok1}")
print(f"W2 fully validated: {ok2}")
raise SystemExit(0 if (ok1 and ok2) else 1)
