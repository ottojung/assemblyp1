#!/usr/bin/env python3
"""Independent exact audit of the normalized-spectrum identifiability theorem
for circular genomes, with emphasis on the divisibility and Eulerian-spelling
steps (issue #45).

Claim under test (minimal hypotheses):

    Let Sigma be a finite alphabet and L >= 2.  Let S, T be circular words such
    that
        (i)  S is primitive and WEAK(S,L) = TRF(S,L) and ILF(S,L);
        (ii) T is primitive and TRF(T,L);
    and let p_D(w) = d_D(w)/|D| be the normalized L-mer spectrum.  Then
        p_T = p_S   ==>   T is a cyclic shift of S.

The script independently re-derives/checks:

  [A] Bresler triple-repeat detection vs. the (L-1)-multiplicity criterion
      (Lemma L* / Lemma 2.2), for primitive words.
  [B] Lemma L*: primitive + TRF  ==>  every (L-1)-mer multiplicity <= 2.
  [C] gcd lemma: primitive + TRF  ==>  gcd of the positive L-mer multiplicities
      is 1.
  [D] Theorem P by pure divisibility: primitive + TRF on both sides and
      d_T = c*d_S with c rational > 0  ==>  c = 1.
  [E] The scaling/divisibility step: from p_T = p_S with |T|/|S| = a/b in
      lowest terms, b | d_S; the reduced vector e = d_S/b is an integral
      balanced vector with the same support and is spelled by a circular word
      T0 with d_{T0} = e, d_{T0^b} = d_S, |T0^b| = |S|.
  [F] Ordinary circular P2 uniqueness, one-sided: grouping primitive words by
      same-length spectrum, no group containing a WEAK word has a
      non-rotation member.
  [G] Sharpness witnesses and the L=1 / panel / parallel-edge edge cases.

Exact integer / Fraction arithmetic.  Deterministic.  Exits non-zero on any
failed assertion.

Usage:
    python3 scripts/verify_normalized_spectrum_divisibility.py          # default
    python3 scripts/verify_normalized_spectrum_divisibility.py --full    # wider
"""
import argparse
import itertools
from collections import Counter, defaultdict
from fractions import Fraction
from functools import reduce
from math import gcd


# ---------------------------------------------------------------- basic words

def rots(s):
    return [s[i:] + s[:i] for i in range(len(s))]


def canon(s):
    return min(rots(s))


def primitive(s):
    n = len(s)
    return not any(n % d == 0 and s == s[:d] * (n // d) for d in range(1, n))


def windows(s, L):
    n = len(s)
    return ["".join(s[(i + j) % n] for j in range(L)) for i in range(n)]


def spec(s, L):
    return Counter(windows(s, L))


def mult_lminus1(s, L):
    n = len(s)
    return Counter("".join(s[(i + j) % n] for j in range(L - 1))
                   for i in range(n))


def gcd_spec(s, L):
    vals = [v for v in spec(s, L).values() if v > 0]
    return reduce(gcd, vals) if vals else 0


def necklaces(sigma, n):
    seen = set()
    for t in itertools.product(sigma, repeat=n):
        s = "".join(t)
        if s in seen:
            continue
        for r in rots(s):
            seen.add(r)
        yield s


# ------------------------------------------------- direct Bresler predicates

def triple_run_best(s, L=None):
    """Maximal length of a Bresler triple repeat in the circular word s.

    A triple repeat of length l: three distinct starts with equal length-l
    windows, the three preceding symbols not all equal and the three following
    symbols not all equal.  For a triple with a non-degenerate left flank the
    maximal possible l is the maximal common right run, so the best length is
    that run whenever the preceding symbols are not all equal.  A full-period
    run is only possible for non-primitive words and is reported as len(s).
    """
    n = len(s)
    if n < 3:
        return 0
    best = 0
    for t1, t2, t3 in itertools.combinations(range(n), 3):
        run = 0
        while run < n and s[(t1 + run) % n] == s[(t2 + run) % n] == s[(t3 + run) % n]:
            run += 1
        if run >= n:
            best = max(best, n)
            continue
        pre = (s[(t1 - 1) % n], s[(t2 - 1) % n], s[(t3 - 1) % n])
        if len(set(pre)) == 1:
            continue
        best = max(best, run)
    return best


def TRF_direct(s, L):
    return triple_run_best(s) < L - 1


def maximal_repeats(s):
    """Maximal repeat pairs (t1<t2, run length), non-wrapping, circular."""
    n = len(s)
    out = []
    for t1 in range(n):
        for t2 in range(t1 + 1, n):
            run = 0
            while run < n and s[(t1 + run) % n] == s[(t2 + run) % n]:
                run += 1
            if run >= n:
                continue
            if s[(t1 - 1) % n] == s[(t2 - 1) % n]:
                continue
            out.append((t1, t2, run))
    return out


def ILF_direct(s, L):
    reps = maximal_repeats(s)
    for a, b, l1 in reps:
        for c, d, l2 in reps:
            if len({a, b, c, d}) < 4:
                continue
            if ((a < c < b < d) or (c < a < d < b)) and min(l1, l2) >= L - 1:
                return False
    return True


def TRF_mult(s, L):
    """Multiplicity criterion (valid for primitive words; checked in [A])."""
    return all(m <= 2 for m in mult_lminus1(s, L).values())


def WEAK_direct(s, L):
    return TRF_direct(s, L) and ILF_direct(s, L)


# --------------------------------------------------------- Eulerian spelling

def spell(e):
    """Spell a circular word from an integral L-mer vector e via an Eulerian
    circuit of the de Bruijn multigraph (iterative Hierholzer).  Returns a word
    with d_word = e, or None if e is not connected/balanced."""
    edges = []
    for w, k in e.items():
        for _ in range(k):
            edges.append((w[:-1], w[1:], w))
    if not edges:
        return ""
    adj = defaultdict(list)
    for i, (u, v, w) in enumerate(edges):
        adj[u].append(i)
    start = edges[0][0]
    it = defaultdict(int)
    stack = [start]
    path = []
    circuit = []
    while stack:
        v = stack[-1]
        if it[v] < len(adj[v]):
            i = adj[v][it[v]]
            it[v] += 1
            stack.append(edges[i][1])
            path.append(i)
        else:
            stack.pop()
            if path:
                circuit.append(path.pop())
    if len(circuit) != len(edges):
        return None
    circuit = circuit[::-1]
    return "".join(edges[i][2][0] for i in circuit)


# ------------------------------------------------------------------- checks

def check_A(args, out):
    """Direct Bresler TRF <=> primitive multiplicity <= 2."""
    bad = 0
    checked = 0
    for sigma, nmax in args.small:
        for n in range(1, nmax + 1):
            for s in necklaces(sigma, n):
                if not primitive(s):
                    continue
                for L in range(2, min(n + 3, 6) + 1):
                    checked += 1
                    if TRF_direct(s, L) != TRF_mult(s, L):
                        bad += 1
                        out.append(("A", sigma, n, s, L))
    out.append(("A-summary", checked, bad))
    return bad == 0


def check_B(args, out):
    """Lemma L*: primitive + TRF => (L-1)-multiplicity <= 2."""
    bad = []
    mx = 0
    for sigma, nmax, Lmax in args.ranges:
        for L in range(2, Lmax + 1):
            for n in range(1, nmax + 1):
                for s in necklaces(sigma, n):
                    if not primitive(s) or not TRF_mult(s, L):
                        continue
                    for v, m in mult_lminus1(s, L).items():
                        mx = max(mx, m)
                        if m > 2:
                            bad.append((sigma, L, s, v, m))
    out.append(("B", "max (L-1)-mult=", mx, "violations=", len(bad)))
    return not bad


def check_C(args, out):
    """gcd lemma: primitive + TRF => gcd(d_S) = 1."""
    bad = []
    cnt = 0
    for sigma, nmax, Lmax in args.ranges:
        for L in range(2, Lmax + 1):
            for n in range(1, nmax + 1):
                for s in necklaces(sigma, n):
                    if not primitive(s) or not TRF_mult(s, L):
                        continue
                    cnt += 1
                    if gcd_spec(s, L) != 1:
                        bad.append((sigma, L, s, gcd_spec(s, L)))
    out.append(("C", "primitive-TRF instances=", cnt, "gcd!=1:", len(bad)))
    return not bad


def check_D(args, out):
    """Theorem P by divisibility: primitive TRF both sides, d_T=c d_S => c=1."""
    collisions = []
    # group by normalized spectrum (Fraction of the count relative to length)
    for sigma, nmax, Lmax in args.ranges:
        for L in range(2, Lmax + 1):
            by = defaultdict(list)
            for n in range(1, nmax + 1):
                for s in necklaces(sigma, n):
                    if not primitive(s) or not TRF_mult(s, L):
                        continue
                    c = spec(s, L)
                    key = tuple(sorted((w, Fraction(k, n)) for w, k in c.items()))
                    by[key].append(s)
            for key, words in by.items():
                cls = set(canon(w) for w in words)
                lens = set(len(w) for w in words)
                if len(cls) > 1 and len(lens) > 1:
                    collisions.append((sigma, L, sorted(cls)))
    out.append(("D", "cross-length proportional collisions:", len(collisions)))
    for c in collisions[:10]:
        out.append(("D-hit", c))
    return not collisions


def check_E(args, out):
    """Scaling/divisibility step: b|d_S, e=d_S/b spellable, T0^b matches."""
    failures = []
    examples = []
    tested = 0
    for sigma, nmax, Lmax in args.ranges:
        for L in range(2, Lmax + 1):
            for n in range(1, nmax + 1):
                for s in necklaces(sigma, n):
                    if not primitive(s):
                        continue
                    g = gcd_spec(s, L)
                    if g <= 1:
                        continue
                    # reduce by every divisor b>=2 (g is the maximal one)
                    for b in range(2, g + 1):
                        if g % b:
                            continue
                        d = spec(s, L)
                        if any(k % b for k in d.values()):
                            continue
                        e = {w: k // b for w, k in d.items()}
                        T0 = spell(e)
                        tested += 1
                        if T0 is None or spec(T0, L) != Counter(e):
                            failures.append((sigma, L, s, b, "not spellable"))
                            continue
                        Tg = T0 * b
                        if spec(Tg, L) != d or len(Tg) != len(s):
                            failures.append((sigma, L, s, b, "T0^b mismatch"))
                        elif len(examples) < 6:
                            examples.append((L, s, b, T0, primitive(T0)))
    out.append(("E", "reduced vectors tested=", tested, "failures:", len(failures)))
    for ex in examples:
        out.append(("E-example", ex))
    for f in failures[:10]:
        out.append(("E-hit", f))
    return not failures


def check_F(args, out):
    """One-sided ordinary circular P2 uniqueness for same-length words."""
    hits = []
    pairs = 0
    for sigma, nmax, Lmax in args.ranges:
        for L in range(2, Lmax + 1):
            for n in range(1, nmax + 1):
                by = defaultdict(list)
                for s in necklaces(sigma, n):
                    if not primitive(s):
                        continue
                    by[tuple(sorted(spec(s, L).items()))].append(s)
                for key, words in by.items():
                    if len(set(canon(w) for w in words)) < 2:
                        continue
                    weak = [w for w in words if WEAK_direct(w, L)]
                    if weak:
                        pairs += 1
                        hits.append((sigma, L, sorted(set(canon(w) for w in words))))
    out.append(("F", "same-length equal-spectrum non-rotation groups, any WEAK:",
                pairs))
    for h in hits[:10]:
        out.append(("F-hit", h))
    return not hits


# --------------------------------------------------------------- witnesses

def witness_checks(out):
    res = {}

    # (1) primitivity is required (tandem scale ambiguity).  The non-primitive
    # mate T = S^2 is itself WEAK, so this is not an admissibility failure.
    res["prim_S_primitive_weak"] = primitive("AAB") and WEAK_direct("AAB", 3)
    res["prim_T_not_primitive"] = not primitive("AABAAB")
    res["prim_T_weak"] = WEAK_direct("AABAAB", 3)
    res["prim_T_not_rotation"] = canon("AABAAB") != canon("AAB")
    res["prim_same_norm"] = all(
        Fraction(spec("AAB", 3).get(w, 0), 3) ==
        Fraction(spec("AABAAB", 3).get(w, 0), 6)
        for w in set(spec("AAB", 3)) | set(spec("AABAAB", 3)))

    # (2) candidate-side TRF is required
    res["cand_T_primitive"] = primitive("AAAABAAB")
    res["cand_T_not_TRF"] = not TRF_direct("AAAABAAB", 3)
    res["cand_same_norm"] = all(
        Fraction(spec("AAAB", 3).get(w, 0), 4) ==
        Fraction(spec("AAAABAAB", 3).get(w, 0), 8)
        for w in set(spec("AAAB", 3)) | set(spec("AAAABAAB", 3)))

    # (3) ILF is required at equal length
    res["AB_eq_spectrum"] = spec("AABABB", 3) == spec("AABBAB", 3)
    res["AB_both_prim_TRF"] = (primitive("AABABB") and primitive("AABBAB")
                               and TRF_direct("AABABB", 3) and TRF_direct("AABBAB", 3))
    res["AB_not_both_ILF"] = not (ILF_direct("AABABB", 3) and ILF_direct("AABBAB", 3))

    # (4) L = 1 fails: anagram not rotation
    res["L1_counterexample"] = (primitive("ABC") and primitive("ACB")
                                and spec("ABC", 1) == spec("ACB", 1)
                                and canon("ABC") != canon("ACB"))

    # (5) molecule panel boundary
    def rc(w):
        return w.translate(str.maketrans("ACGT", "TGCA"))[::-1]
    def molspec(s):
        c = Counter(min(w, rc(w)) for w in windows(s, 3))
        return c
    res["molecule_same_law"] = molspec("AACAGT") == molspec("AACTGT")
    res["molecule_not_rotation"] = canon("AACAGT") != canon("AACTGT")
    res["molecule_not_rc"] = (canon("AACAGT") != canon(rc("AACTGT")) and
                              canon("AACAGT") != canon(rc("AACAGT")))

    for k, v in res.items():
        out.append(("G", k, v))
    return all(bool(v) for v in res.values())


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--full", action="store_true")
    args = ap.parse_args()
    if args.full:
        args.small = [("AB", 10), ("ABC", 8)]
        args.ranges = [("AB", 16, 5), ("ABC", 11, 4)]
    else:
        args.small = [("AB", 8), ("ABC", 7)]
        args.ranges = [("AB", 12, 4), ("ABC", 9, 4)]

    out = []
    ok = True
    ok &= check_A(args, out)
    ok &= check_B(args, out)
    ok &= check_C(args, out)
    ok &= check_D(args, out)
    ok &= check_E(args, out)
    ok &= check_F(args, out)
    ok &= witness_checks(out)

    for row in out:
        print(row)
    print("\nRESULT:", "PASS" if ok else "FAIL")
    raise SystemExit(0 if ok else 1)


if __name__ == "__main__":
    main()
