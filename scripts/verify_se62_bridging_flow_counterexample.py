#!/usr/bin/env python3
"""
Self-contained exact verification of a Section 6.2 counterexample to
"bridging conditions force the truth-induced flow to be maximum-likelihood".

Instance (2026-09-20):

    alphabet          {A, T} with the DNA reverse-complement involution A <-> T
    truth             S = AAATT          (G = 5)
    read length       L = 3
    realized starts   (0, 1, 4)          (n = 3 reads)
    external size     N = |S| = 5        (Medvedev-Brudno known genome size)
    observed          x = { AAA:1, AAT:1, TAA:1 }   (read *molecule* classes)
    truth spectrum    d_S = { AAA:1, AAT:2, TAA:2 }
    competitor        D = AAAATT         (|D| = 6)
    competitor spec   d_D = { AAA:2, AAT:2, TAA:2 }

Claims checked (all exact, fractions.Fraction):

  (1) The realized reads cover S.
  (2) Every maximal triple repeat of S is all-bridged by the reads,
      and the interleaved-repeat condition is vacuous: R in I_s.
  (3) Both S and D satisfy the *sequence-level support/lower-bound certificate*
      w.r.t. R: supp(spec_L(.)) == supp(x) and d_w >= x_w for every observed w.
      This is a stronger finite sufficient condition; it is NOT the Medvedev-
      Brudno section 6.2 feasibility definition (see the audit note below).
  (4) Each of S and D is spelled by a cyclic walk in the read-overlap graph
      (consecutive L-windows overlap in L-1 symbols), so the flow is a circuit
      and uses every observed read molecule at least once.
  (5) The literal Section 6.1 product-of-binomial-marginals objective with the
      fixed external N = 5 and n = 3 reads (zero-count factors retained) is
      strictly larger for D than for S: ratio = 9/8 > 1.

Consequently, under the source-faithful Section 6.2 reading in which the
truth-induced flow is an admissible candidate, the truth-induced flow is not a
maximum-likelihood maximizer.  Bridging (I_s) does not force it to be one.

The exact section 6.2 bidirected-graph and flow admissibility certificate is a
separate script: `verify_se62_mb09_bidirected_graph.py` (see
`docs/section62-mb09-bidirected-graph-audit.md`).  The `d_S` printed here is the
corrected value; an earlier prose table in the note printed `{AAA:2, AAT:2,
TAA:1}`, which was a start-3 indexing error (the window is TTA, class TAA).

Scope / caveats (see docs/bridging-se62-flow-ml-counterexample.md):
  * The candidate D has length 6 != N = 5.  Section 6.2 does not constrain the
    candidate-flow length; N is the binomial denominator only.
  * The reading is the bidirected (reverse-complement) one, under which reads
    are DNA molecules.  Single-strand per-occurrence witnesses with
    non-constant truth were not found in the bounded scope (see the note).
  * All arithmetic is exact rational arithmetic.
"""
import sys
from fractions import Fraction
from collections import Counter, defaultdict
from itertools import combinations


A, T = 0, 1
COMP = {A: T, T: A}


def rc(s):
    return tuple(COMP[c] for c in reversed(s))


def mol(s):
    """Molecule class: the lexicographically smaller of a word and its revcomp."""
    return min(tuple(s), rc(tuple(s)))


def windows(seq, L):
    G = len(seq)
    return [tuple(seq[(i + j) % G] for j in range(L)) for i in range(G)]


def spec(seq, L):
    return Counter(mol(w) for w in windows(seq, L))


def observed(S, starts, L):
    x = Counter()
    for r in starts:
        x[mol(tuple(S[(r + j) % len(S)] for j in range(L)))] += 1
    return x


def covers_all(S, starts, L):
    G = len(S)
    cov = set()
    for r in starts:
        for o in range(L):
            cov.add((r + o) % G)
    return len(cov) == G


def maximal_pairs(S):
    G = len(S)
    out, seen = [], set()
    for ell in range(1, G):
        grp = defaultdict(list)
        for i in range(G):
            grp[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for _, pos in grp.items():
            if len(pos) < 2:
                continue
            for a, b in combinations(pos, 2):
                if S[(a - 1) % G] != S[(b - 1) % G] and S[(a + ell) % G] != S[(b + ell) % G]:
                    if (a, b) not in seen:
                        seen.add((a, b))
                        out.append((ell, (a, b)))
    return out


def triple_repeats(S):
    G = len(S)
    out, seen = [], set()
    for ell in range(1, G):
        grp = defaultdict(list)
        for i in range(G):
            grp[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for _, pos in grp.items():
            if len(pos) < 3:
                continue
            for tri in combinations(pos, 3):
                if (len({S[(t - 1) % G] for t in tri}) > 1
                        and len({S[(t + ell) % G] for t in tri}) > 1):
                    key = tuple(sorted(tri))
                    if key not in seen:
                        seen.add(key)
                        out.append((ell, key))
    return out


def interleaved_pairs(S):
    reps = maximal_pairs(S)
    out, seen = [], set()
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
                key = (e1, tuple(sorted(p1)), e2, tuple(sorted(p2)))
                if key not in seen:
                    seen.add(key)
                    out.append(((e1, tuple(sorted(p1))), (e2, tuple(sorted(p2)))))
    return out


def copy_bridged(S, t, ell, starts, L):
    G = len(S)
    for r in starts:
        rp = {(r + o) % G for o in range(L)}
        if (t - 1) % G in rp and (t + ell) % G in rp:
            return True
    return False


def check_I_s(S, starts, L):
    if not covers_all(S, starts, L):
        return False
    for ell, pos in triple_repeats(S):
        for t in pos:
            if not copy_bridged(S, t, ell, starts, L):
                return False
    for (e1, p1), (e2, p2) in interleaved_pairs(S):
        b1 = any(copy_bridged(S, t, e1, starts, L) for t in p1)
        b2 = any(copy_bridged(S, t, e2, starts, L) for t in p2)
        if not (b1 or b2):
            return False
    return True


def feasible(x, sp):
    """Sequence-level support/lower-bound certificate (a sufficient, not the source section 6.2, condition)."""
    return set(sp) == set(x) and all(sp[w] >= c for w, c in x.items())


def spelled_by_circuit(seq, L):
    """Consecutive L-windows overlap in L-1 symbols: a cyclic overlap walk."""
    ws = windows(seq, L)
    G = len(seq)
    return all(ws[i][1:] == ws[(i + 1) % G][:-1] for i in range(G))


def phi(x, n, N, d):
    """Section 6.1 binomial factor (d/N)^x (1-d/N)^(n-x)."""
    return Fraction(d, N) ** x * Fraction(N - d, N) ** (n - x)


def binom_product(x, n, N, d):
    """Literal Section 6.1 product over the observed read-molecule types."""
    r = Fraction(1)
    for w, xw in x.items():
        r *= phi(xw, n, N, d.get(w, 0))
    return r


def main():
    S = (A, A, A, T, T)                 # AAATT
    D = (A, A, A, A, T, T)              # AAAATT
    L = 3
    starts = (0, 1, 4)
    N = len(S)                          # external known genome size = 5
    x = observed(S, starts, L)
    dS = spec(S, L)
    dD = spec(D, L)
    n = sum(x.values())
    checks = []

    checks.append((f"(1) coverage of S by starts {starts}", covers_all(S, starts, L)))

    trips = triple_repeats(S)
    all_bridged = all(all(copy_bridged(S, t, e, starts, L) for t in pos)
                      for e, pos in trips)
    checks.append((f"(2) I_s: all {len(trips)} triple repeat(s) all-bridged",
                   all_bridged and len(trips) > 0))
    checks.append((f"(2) I_s: interleaved pairs = {interleaved_pairs(S)} (vacuous)",
                   interleaved_pairs(S) == []))
    checks.append(("(2) I_s holds", check_I_s(S, starts, L)))

    checks.append((f"(3) supp(spec(S)) == supp(x); supp(S)={sorted(dS)}",
                   set(dS) == set(x)))
    checks.append((f"(3) d_S >= x; d_S={dict(dS)}", all(dS[w] >= c for w, c in x.items())))
    checks.append(("(3) S satisfies the support/lower-bound certificate", feasible(x, dS)))
    checks.append((f"(3) supp(spec(D)) == supp(x); supp(D)={sorted(dD)}",
                   set(dD) == set(x)))
    checks.append((f"(3) d_D >= x; d_D={dict(dD)}", all(dD[w] >= c for w, c in x.items())))
    checks.append(("(3) D satisfies the support/lower-bound certificate", feasible(x, dD)))

    checks.append(("(4) S spelled by a cyclic overlap walk", spelled_by_circuit(S, L)))
    checks.append(("(4) D spelled by a cyclic overlap walk", spelled_by_circuit(D, L)))

    prod_S = binom_product(x, n, N, dict(dS))
    prod_D = binom_product(x, n, N, dict(dD))
    ratio = prod_D / prod_S
    checks.append((f"(5) literal Section 6.1 ratio L(D)/L(S) = {ratio} = 9/8 > 1",
                   ratio == Fraction(9, 8) and ratio > 1))

    print("observed x      :", dict(x))
    print("truth spectrum  :", dict(dS), " |S| =", len(S))
    print("competitor spec :", dict(dD), " |D| =", len(D))
    print()
    ok = True
    for name, res in checks:
        print(f"[{'PASS' if res else 'FAIL'}] {name}")
        ok &= bool(res)
    print("\nALL CHECKS PASS" if ok else "\nSOME CHECKS FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
