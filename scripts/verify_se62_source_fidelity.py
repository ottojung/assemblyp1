#!/usr/bin/env python3
"""Independent exact check of Medvedev-Brudno section 6.2 source fidelity.

Self-contained, deterministic, exact `fractions.Fraction` arithmetic; exits
non-zero on any assertion failure.  See `docs/section62-source-fidelity-audit.md`.

Primary source: Paul Medvedev, Michael Brudno, "Maximum Likelihood Genome
Assembly", J. Comput. Biol. 16(8) (2009) 1101-1116 (PMC3154397), sections 3.1,
3.3, 4.1, 6.1, 6.2, 7; and Paul Medvedev, "Genome Graphs", PhD thesis,
University of Toronto, 2010, chapter 4, section 4.4 (the dissertation version of
section 6.2, which adds the supersink -> supersource return edge).

The script checks three things:

  (A) The kernel-checked witness of
      `AssemblyP1/Section62BridgingCounterexample.lean` (truth `AAATT`,
      competitor `AAAATT`, `L = 3`, molecule/revcomp reading) remains
      sequence-level section 6.2 feasible under the *source-faithful*
      per-type lower bound and the general containment + (L - o_min)-density
      spelling criterion, for `o_min` in {1, 2}; binomial ratio 9/8.

  (B) The support-equality criterion used in
      `docs/bridging-se62-flow-ml-counterexample.md` is only the
      `o_min = L - 1` special case: a molecule with an unobserved window can
      still be spelled when `o_min < L - 1` (containment + density).

  (C) Under the source-faithful molecule (revcomp) + per-type + containment
      reading with `o_min = 1`, there is a small sequence-level counterexample
      that the tracked support-equality/per-occurrence criterion *excludes*:
      truth `AAAT`, competitor `AAAAT`, binomial ratio 16/9 and exact
      (candidate-intrinsic-length) ratio 1024/625.  This shows the
      counterexample frontier is strictly larger than the tracked one.
"""
import sys
from fractions import Fraction
from collections import Counter, defaultdict
from itertools import combinations


def make_comp(table):
    return lambda c: table[c]


def rc(word, comp):
    return tuple(comp(c) for c in reversed(word))


def mol(word, comp, quotient_rc=True):
    t = tuple(word)
    if not quotient_rc:
        return t
    return min(t, rc(t, comp))


def windows(seq, L):
    G = len(seq)
    return [tuple(seq[(i + j) % G] for j in range(L)) for i in range(G)]


def spec(seq, L, comp, quotient_rc=True):
    return Counter(mol(w, comp, quotient_rc) for w in windows(seq, L))


def observed(seq, starts, L, comp, quotient_rc=True):
    x = Counter()
    for r in starts:
        x[mol(tuple(seq[(r + j) % len(seq)] for j in range(L)), comp, quotient_rc)] += 1
    return x


def covers_all(seq, starts, L):
    G = len(seq)
    cov = set()
    for r in starts:
        cov.update((r + o) % G for o in range(L))
    return len(cov) == G


def maximal_pairs(seq):
    G = len(seq)
    out, seen = [], set()
    for ell in range(1, G):
        grp = defaultdict(list)
        for i in range(G):
            grp[tuple(seq[(i + j) % G] for j in range(ell))].append(i)
        for _, pos in grp.items():
            for a, b in combinations(pos, 2):
                if seq[(a - 1) % G] != seq[(b - 1) % G] and seq[(a + ell) % G] != seq[(b + ell) % G]:
                    if (a, b) not in seen:
                        seen.add((a, b))
                        out.append((ell, (a, b)))
    return out


def triple_repeats(seq):
    G = len(seq)
    out, seen = [], set()
    for ell in range(1, G):
        grp = defaultdict(list)
        for i in range(G):
            grp[tuple(seq[(i + j) % G] for j in range(ell))].append(i)
        for _, pos in grp.items():
            for tri in combinations(pos, 3):
                if (len({seq[(t - 1) % G] for t in tri}) > 1
                        and len({seq[(t + ell) % G] for t in tri}) > 1):
                    key = tuple(sorted(tri))
                    if key not in seen:
                        seen.add(key)
                        out.append((ell, key))
    return out


def interleaved_pairs(seq):
    reps = maximal_pairs(seq)
    out = []
    for i in range(len(reps)):
        e1, p1 = reps[i]
        for j in range(i + 1, len(reps)):
            e2, p2 = reps[j]
            four = sorted(set(p1) | set(p2))
            if len(four) != 4:
                continue
            lab = {p: 0 for p in p1}
            lab.update({p: 1 for p in p2})
            if [lab[p] for p in four] in ([0, 1, 0, 1], [1, 0, 1, 0]):
                out.append(((e1, tuple(sorted(p1))), (e2, tuple(sorted(p2)))))
    return out


def copy_bridged(seq, t, ell, starts, L):
    G = len(seq)
    for r in starts:
        rp = {(r + o) % G for o in range(L)}
        if (t - 1) % G in rp and (t + ell) % G in rp:
            return True
    return False


def check_is(seq, starts, L):
    if not covers_all(seq, starts, L):
        return False
    for ell, pos in triple_repeats(seq):
        if not all(copy_bridged(seq, t, ell, starts, L) for t in pos):
            return False
    for (e1, p1), (e2, p2) in interleaved_pairs(seq):
        b1 = any(copy_bridged(seq, t, e1, starts, L) for t in p1)
        b2 = any(copy_bridged(seq, t, e2, starts, L) for t in p2)
        if not (b1 or b2):
            return False
    return True


def max_cyclic_gap(positions, G):
    if not positions:
        return G
    ps = sorted(positions)
    return max((ps[(k + 1) % len(ps)] - ps[k]) % G for k in range(len(ps)))


def containment_density(seq, L, comp, x, o_min, quotient_rc=True):
    supp = set(x)
    G = len(seq)
    cls = [mol(w, comp, quotient_rc) for w in windows(seq, L)]
    if not supp.issubset(set(cls)):
        return False, "support containment fails"
    allowed = [i for i, c in enumerate(cls) if c in supp]
    gap = max_cyclic_gap(allowed, G)
    if gap > L - o_min:
        return False, f"density fails (gap {gap} > {L - o_min})"
    return True, f"ok (max gap {gap})"


def support_equality(seq, L, comp, x, quotient_rc=True):
    return set(spec(seq, L, comp, quotient_rc)) == set(x)


def binom_product(x, n, N, d):
    r = Fraction(1)
    for w, xw in x.items():
        dw = d.get(w, 0)
        r *= Fraction(dw, N) ** xw * Fraction(N - dw, N) ** (n - xw)
    return r


def exact_product(x, d, G):
    r = Fraction(1)
    for w, xw in x.items():
        if xw:
            r *= Fraction(d.get(w, 0), G) ** xw
    return r


def main():
    ok = True
    comp = make_comp({"A": "T", "T": "A"})

    def check(name, cond, extra=""):
        nonlocal ok
        ok &= bool(cond)
        print(f"[{'PASS' if cond else 'FAIL'}] {name} {extra}")

    # (A) kernel witness survives the source-faithful reading
    S, D = ("A", "A", "A", "T", "T"), ("A", "A", "A", "A", "T", "T")
    L, starts = 3, (0, 1, 4)
    x = observed(S, starts, L, comp)
    dS, dD = spec(S, L, comp), spec(D, L, comp)
    check("A: I_s holds for AAATT", check_is(S, starts, L))
    for om in (1, 2):
        fS, mS = containment_density(S, L, comp, x, om)
        fD, mD = containment_density(D, L, comp, x, om)
        check(f"A: truth feasible (containment+density, o_min={om})", fS, mS)
        check(f"A: competitor feasible (containment+density, o_min={om})", fD, mD)
    check("A: per-type lower bound on truth", all(v >= 1 for v in dS.values()))
    check("A: per-type lower bound on competitor", all(v >= 1 for v in dD.values()))
    n, N = sum(x.values()), len(S)
    ratio = binom_product(x, n, N, dict(dD)) / binom_product(x, n, N, dict(dS))
    check("A: binomial ratio = 9/8", ratio == Fraction(9, 8), f"ratio={ratio}")

    # (B) support equality is the o_min = L-1 special case
    idc = make_comp({"A": "A", "B": "B"})
    S2, D2, L2, starts2 = ("A", "A", "A", "B", "B"), ("A", "A", "A", "A", "B", "B"), 3, (0, 0, 1, 2, 4)
    x2 = observed(S2, starts2, L2, idc, quotient_rc=False)
    check("B: I_s holds for AAABB", check_is(S2, starts2, L2))
    check("B: support equality excludes truth AAABB",
          not support_equality(S2, L2, idc, x2, quotient_rc=False))
    fS2, mS2 = containment_density(S2, L2, idc, x2, 1, quotient_rc=False)
    fD2, mD2 = containment_density(D2, L2, idc, x2, 1, quotient_rc=False)
    check("B: truth feasible under containment+density (o_min=1)", fS2, mS2)
    check("B: competitor feasible under containment+density (o_min=1)", fD2, mD2)
    dS2 = spec(S2, L2, idc, quotient_rc=False)
    dD2 = spec(D2, L2, idc, quotient_rc=False)
    check("B: per-type lower bound on truth", all(v >= 1 for v in dS2.values()))
    n2 = sum(x2.values())
    br2 = binom_product(x2, n2, len(S2), dict(dD2)) / binom_product(x2, n2, len(S2), dict(dS2))
    er2 = exact_product(x2, dict(dD2), len(D2)) / exact_product(x2, dict(dS2), len(S2))
    check("B: binomial ratio = 27/16 > 1", br2 == Fraction(27, 16), f"ratio={br2}")
    check("B: exact ratio = 3125/1944 > 1", er2 == Fraction(3125, 1944), f"ratio={er2}")

    # (C) molecule (revcomp) + per-type containment-only witness at o_min = 1
    S3, D3, L3, starts3 = ("A", "A", "A", "T"), ("A", "A", "A", "A", "T"), 3, (0, 0, 1, 2)
    x3 = observed(S3, starts3, L3, comp)
    dS3, dD3 = spec(S3, L3, comp), spec(D3, L3, comp)
    check("C: I_s holds for AAAT", check_is(S3, starts3, L3))
    check("C: support equality excludes truth AAAT",
          not support_equality(S3, L3, comp, x3))
    fS3, mS3 = containment_density(S3, L3, comp, x3, 1)
    fD3, mD3 = containment_density(D3, L3, comp, x3, 1)
    check("C: truth feasible under containment+density (o_min=1)", fS3, mS3)
    check("C: competitor feasible under containment+density (o_min=1)", fD3, mD3)
    check("C: per-type lower bound on truth", all(v >= 1 for v in dS3.values()))
    n3 = sum(x3.values())
    br3 = binom_product(x3, n3, len(S3), dict(dD3)) / binom_product(x3, n3, len(S3), dict(dS3))
    er3 = exact_product(x3, dict(dD3), len(D3)) / exact_product(x3, dict(dS3), len(S3))
    check("C: binomial ratio = 16/9 > 1", br3 == Fraction(16, 9), f"ratio={br3}")
    check("C: exact ratio = 1024/625 > 1", er3 == Fraction(1024, 625), f"ratio={er3}")

    print()
    print("(A) x =", dict(x), "dS =", dict(dS), "dD =", dict(dD))
    print("(C) x =", dict(x3), "dS =", dict(dS3), "dD =", dict(dD3))
    print("\nALL CHECKS PASS" if ok else "\nSOME CHECKS FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
