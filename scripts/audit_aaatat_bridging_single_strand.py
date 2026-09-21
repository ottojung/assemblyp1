#!/usr/bin/env python3
"""
Adversarial audit of the integrated `AAATAT -> AAAAAT` counterexample against
the published Shomorony et al. (2016) Eq. (1) / Bresler-Bresler-Tse (2013)
Theorem 6 bridging condition, under source-faithful SINGLE-STRAND semantics.

Primary-source definitions (Bresler et al. 2013, PMC3706340, exact wording
re-retrieved 2026-09-21):

  * repeat of length l: two starts t1,t2 with equal length-l windows, maximal:
    s(t1-1) != s(t2-1) and s(t1+l) != s(t2+l).
  * triple repeat of length l: three starts with equal windows and NOT all of
    s(ti-1) equal and NOT all of s(ti+l) equal.
  * pair of repeats interleaved iff t1 < t2 < t3 < t4 or t2 < t1 < t4 < t3.
  * a copy at t of length l is bridged iff some read start lies in the
    preceding interval of length L-l-1: r = t-d, 1 <= d <= L-l-1.
    If L-l-1 <= 0 the copy is UNBRIDGEABLE.
  * Theorem 6 / I_s: all interleaved repeats bridged; all triple repeats
    all-bridged; sequence covered.

Recomputes the whole single-strand inventory of AAATAT, checks I_s with the
STRICT source predicate, and compares it with the repository flank-coverage
predicate that is implemented by
`AssemblyP1/SameLengthSection62Counterexample.lean` (`bridgedCopy`).  Also
evaluates exact same-length likelihoods under (a) source-faithful single-strand
oriented read types and (b) the reverse-complement-collapsed molecule reading
used by the integrated artifact.

Exact integer/Fraction arithmetic; exits non-zero on any failed assertion.
Usage: python3 scripts/audit_aaatat_bridging_single_strand.py
"""
from __future__ import annotations

from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations

A, T = 0, 1
COMP = {A: T, T: A}
SYM = {0: "A", 1: "T"}


def word(s):
    return "".join(SYM[c] for c in s)


def rc(s):
    return tuple(COMP[c] for c in reversed(s))


def circ(seq, i, l):
    G = len(seq)
    return tuple(seq[(i + j) % G] for j in range(l))


def maximal_pairs(seq):
    G = len(seq)
    out = []
    for l in range(1, G):
        grp = defaultdict(list)
        for i in range(G):
            grp[circ(seq, i, l)].append(i)
        for _, pos in grp.items():
            for a, b in combinations(pos, 2):
                if seq[(a - 1) % G] != seq[(b - 1) % G] and \
                   seq[(a + l) % G] != seq[(b + l) % G]:
                    out.append((l, (a, b)))
    return out


def triple_repeats(seq):
    G = len(seq)
    out = []
    for l in range(1, G):
        grp = defaultdict(list)
        for i in range(G):
            grp[circ(seq, i, l)].append(i)
        for _, pos in grp.items():
            for tri in combinations(pos, 3):
                if len({seq[(t - 1) % G] for t in tri}) > 1 and \
                   len({seq[(t + l) % G] for t in tri}) > 1:
                    out.append((l, tri))
    return out


def interleaved_pairs(seq):
    reps = maximal_pairs(seq)
    out = []
    for i in range(len(reps)):
        for j in range(i + 1, len(reps)):
            l1, p1 = reps[i]
            l2, p2 = reps[j]
            four = sorted(set(p1) | set(p2))
            if len(four) != 4:
                continue
            lab = {p: 0 for p in p1}
            lab.update({p: 1 for p in p2})
            if [lab[p] for p in four] in ([0, 1, 0, 1], [1, 0, 1, 0]):
                out.append(((l1, p1), (l2, p2)))
    return out


# ------------------------------------------------------------------ bridging
def strict_bridge_starts(G, L, t, l):
    """Source BridgeStarts: preceding interval of length L-l-1."""
    return {(t - d) % G for d in range(1, L - l)} if L - l - 1 >= 1 else set()


def repo_flank_starts(G, L, t, l):
    """Repository predicate: starts whose read covers both flanking positions
    (t-1) and (t+l) modulo G."""
    out = set()
    for r in range(G):
        cells = {(r + o) % G for o in range(L)}
        if (t - 1) % G in cells and (t + l) % G in cells:
            out.add(r)
    return out


def strict_bridged(G, L, t, l, starts):
    return bool(strict_bridge_starts(G, L, t, l) & set(starts))


def repo_bridged(G, L, t, l, starts):
    return bool(repo_flank_starts(G, L, t, l) & set(starts))


def covers(G, starts, L):
    cov = set()
    for r in starts:
        for o in range(L):
            cov.add((r + o) % G)
    return cov == set(range(G))


def check_I_s(seq, starts, L, bridged):
    G = len(seq)
    if not covers(G, starts, L):
        return False, "coverage"
    for l, tri in triple_repeats(seq):
        for t in tri:
            if not bridged(G, L, t, l, starts):
                return False, f"triple len {l} @ {tri} copy {t}"
    for (l1, p1), (l2, p2) in interleaved_pairs(seq):
        if not (any(bridged(G, L, t, l1, starts) for t in p1) or
                any(bridged(G, L, t, l2, starts) for t in p2)):
            return False, f"interleaved {l1}@{p1} / {l2}@{p2}"
    return True, "ok"


# ------------------------------------------------------------------ likelihood
def oriented_reads(seq, starts, L):
    x = Counter()
    for r in starts:
        x[circ(seq, r, L)] += 1
    return x


def class_reads(seq, starts, L):
    x = Counter()
    for r in starts:
        w = circ(seq, r, L)
        x[min(w, rc(w))] += 1
    return x


def oriented_spectrum(seq, L):
    return Counter(circ(seq, i, L) for i in range(len(seq)))


def class_spectrum(seq, L):
    return Counter(min(circ(seq, i, L), rc(circ(seq, i, L)))
                   for i in range(len(seq)))


def exact_product(sp, x):
    r = Fraction(1)
    for w, xw in x.items():
        r *= Fraction(sp.get(w, 0)) ** xw
    return r


def binom_product(x, n, N, d):
    r = Fraction(1)
    for w, xw in x.items():
        dw = d.get(w, 0)
        r *= Fraction(dw, N) ** xw * Fraction(N - dw, N) ** (n - xw)
    return r


def show(c):
    return "{" + ", ".join(f"{word(w)}:{v}" for w, v in sorted(c.items())) + "}"


def main():
    L = 3
    S = (A, A, A, T, A, T)              # AAATAT (circular)
    D = (A, A, A, A, A, T)              # AAAAAT (same length)
    starts = (0, 0, 1, 3, 5)
    G = len(S)
    n = len(starts)
    N = G
    failed = []

    def chk(name, cond):
        print(f"[{'PASS' if cond else 'FAIL'}] {name}")
        if not cond:
            failed.append(name)

    print(f"truth S = {word(S)} (G={G}, L={L}); competitor D = {word(D)} "
          f"(|D|={len(D)}); starts={starts} n={n} N={N}\n")

    reps = sorted(maximal_pairs(S))
    trips = sorted(triple_repeats(S))
    inter = interleaved_pairs(S)

    print("== single-strand maximal repeats (Bresler) ==")
    for l, (a, b) in reps:
        print(f"  l={l}: {word(circ(S,a,l))}@{a} == {word(circ(S,b,l))}@{b}")
    print("== triple repeats ==")
    for l, tri in trips:
        print(f"  l={l}: {word(circ(S,tri[0],l))}@{tri}")
    print("== interleaved pairs ==")
    for (l1, p1), (l2, p2) in inter:
        print(f"  l={l1}@{p1} x l={l2}@{p2}")
    print()

    chk("maximal pairs = {A@(0,2), A@(1,4), AA@(0,1), ATA@(2,4)}",
        reps == [(1, (0, 2)), (1, (1, 4)), (2, (0, 1)), (3, (2, 4))])
    chk("triple repeats = four length-1 A-triples",
        trips == [(1, (0, 1, 2)), (1, (0, 1, 4)),
                  (1, (0, 2, 4)), (1, (1, 2, 4))])
    chk("exactly one interleaved pair A@(0,2) x A@(1,4)",
        inter == [((1, (0, 2)), (1, (1, 4)))])

    print("\n== bridge status of every maximal-repeat copy (strict source) ==")
    for l, (a, b) in reps:
        for t in (a, b):
            ss = sorted(strict_bridge_starts(G, L, t, l))
            rr = sorted(repo_flank_starts(G, L, t, l))
            print(f"  l={l} t={t}: strict={ss} repo={rr} "
                  f"strict_bridged={strict_bridged(G,L,t,l,starts)} "
                  f"repo_bridged={repo_bridged(G,L,t,l,starts)}")
    print()

    chk("length-2/3 copies are UNBRIDGEABLE under the source predicate",
        all(strict_bridge_starts(G, L, t, l) == set()
            for l, (a, b) in reps if l >= 2 for t in (a, b)))
    diff = [(l, t) for l, (a, b) in reps for t in (a, b)
            if strict_bridge_starts(G, L, t, l) != repo_flank_starts(G, L, t, l)]
    chk("repo flank predicate OVER-REPORTS bridging on the length-3 copies",
        diff == [(3, 2), (3, 4)])
    chk("repo over-report is exactly via the complementary arc (L>=G-l)",
        all(repo_bridged(G, L, t, l, starts) and
            not strict_bridged(G, L, t, l, starts) for l, t in diff))
    print(f"  strict/repo disagreements: {diff}\n")

    sok, sw = check_I_s(S, starts, L, strict_bridged)
    rok, rw = check_I_s(S, starts, L, repo_bridged)
    chk(f"I_s HOLDS under the STRICT source predicate ({sw})", sok)
    chk(f"I_s holds under the repo flank predicate ({rw})", rok)
    constrained = [(l, t) for l, tri in triple_repeats(S) for t in tri]
    constrained += [(l1, t) for (l1, p1), _ in interleaved_pairs(S) for t in p1]
    constrained += [(l2, t) for _, (l2, p2) in interleaved_pairs(S) for t in p2]
    chk("every I_s-constrained copy is length-1 (repo==strict there)",
        all(l == 1 for l, _ in constrained))

    # ---------------------------------------------------------- likelihoods
    print("\n== likelihoods ==")
    xs = oriented_reads(S, starts, L)
    ds = oriented_spectrum(S, L)
    dDs = oriented_spectrum(D, L)
    xc = class_reads(S, starts, L)
    dSc = class_spectrum(S, L)
    dDc = class_spectrum(D, L)
    print(f"  oriented x      = {show(xs)}")
    print(f"  oriented d_S    = {show(ds)}")
    print(f"  oriented d_D    = {show(dDs)}")
    print(f"  class    x      = {show(xc)}")
    print(f"  class    d_S    = {show(dSc)}")
    print(f"  class    d_D    = {show(dDc)}")
    ess, eds = exact_product(ds, xs), exact_product(dDs, xs)
    bss = binom_product(xs, n, N, dict(ds))
    bds = binom_product(xs, n, N, dict(dDs))
    ecs, ecd = exact_product(dSc, xc), exact_product(dDc, xc)
    bcs = binom_product(xc, n, N, dict(dSc))
    bcd = binom_product(xc, n, N, dict(dDc))
    print(f"  SINGLE-STRAND oriented: D exact = {eds} (ratio {eds}/"
          f"{ess}); D 6.1 = {bds}")
    print(f"  REVCOMP-CLASS molecule: exact D/S = {ecd/ecs}; 6.1 D/S = {bcd/bcs}")
    chk("SINGLE-STRAND: competitor D has ZERO exact same-length likelihood",
        eds == 0)
    chk("SINGLE-STRAND: competitor D has ZERO literal 6.1 likelihood", bds == 0)
    chk("REVCOMP-CLASS: exact D/S = 3 and 6.1 D/S = 5",
        ecd / ecs == Fraction(3) and bcd / bcs == Fraction(5))
    print()

    print()
    if failed:
        print("SOME CHECKS FAILED:", failed)
        return 1
    print("ALL CHECKS PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
