#!/usr/bin/env python3
"""Independent re-verification of the AssemblyP1 exact-multinomial (Variant E)
and fixed-`N` product-of-binomial-marginals (Variant A) negative results, for
issue #209.

This script deliberately shares **no code** with the Lean library.  It
re-implements, from the source definitions:

  * the circular genome / read-window substrate;
  * the full source-faithful hypothesis `I_s` (coverage, all-bridged triple
    repeats, bridged interleaved repeat pairs) of Shomorony et al. (2016) Eq. (1)
    with the Bresler-Bresler-Tse (2013) repeat semantics, i.e. the predicate that
    `AssemblyP1/SourceFaithfulIs.lean` claims to transcribe;
  * the exact Medvedev-Brudno (2009) §6.1 multinomial likelihood with
    candidate-intrinsic `N(D)`;
  * the literal §6.1 product-of-binomial-marginals approximation with the
    *fixed external* length `N`, keeping the `(1 - d_i/N)^(n-x_i)` factors of
    unobserved read types.

and then checks, for each witness in `docs/`:

  1. the `I_s` certificate (agreement with the Lean `decide`);
  2. the exact likelihood values and the strict ratio;
  3. the domain condition `0 <= d_i <= N` that makes the binomial marginal a
     probability;
  4. duplicate-read (parametric) families;
  5. bounded searches over the relevant candidate universe;
  6. the parameters needed by the unparameterized "read-tiled" witness row in
     `docs/source-notes/same-length-witnesses-candidate-set-inclusion.md`.

Everything here is *evidence* (exact rational arithmetic and exhaustive finite
computation).  Nothing in this script is a proof.  The proof obligations are
discharged in Lean; this script checks that the Lean instances are the instances
the notes claim, and that the arithmetic is right.
"""

from fractions import Fraction
from itertools import product as iproduct

# The read-type alphabet.  The Lean witness modules use `Base = A | B | C | G`,
# a four-letter DNA alphabet in which the witnesses themselves use only `A, B`
# (or `A, C`).  The fixed-length binomial objective is a product over the whole
# read-type space, so the alphabet must be the module's, not the witness's.
ALPHABET = "ABCG"

_RL = {"L": None}


def set_read_length(L):
    _RL["L"] = L


def read_length():
    if _RL["L"] is None:
        raise RuntimeError("set read length first")
    return _RL["L"]


# --------------------------------------------------------------------------
# Circular genome substrate
# --------------------------------------------------------------------------
class Circ:
    """A circular genome: `syms` cyclically repeated."""

    __slots__ = ("syms",)

    def __init__(self, syms):
        self.syms = tuple(syms)
        assert len(self.syms) > 0

    @property
    def G(self):
        return len(self.syms)

    def at(self, i):
        """Symbol at arbitrary integer position (circular)."""
        return self.syms[i % self.G]

    def window(self, e, r):
        """Length-`e` circular window at start `r` (0-based, lifted)."""
        return tuple(self.at(r + d) for d in range(e))

    def windows(self, e):
        """All `G` length-`e` windows, indexed by start."""
        return [self.window(e, r) for r in range(self.G)]

    def __str__(self):
        return "".join(self.syms)


def counts(circ, e):
    """`d_i`: number of starts whose length-`e` window equals read type `i`."""
    c = {}
    for w in circ.windows(e):
        c[w] = c.get(w, 0) + 1
    return c


def type_space(L):
    return [tuple(w) for w in iproduct(ALPHABET, repeat=L)]


# --------------------------------------------------------------------------
# Source-faithful `I_s` (independent transcription of the Lean predicate
# `SourceFaithfulIs.InformationFeasible`)
# --------------------------------------------------------------------------
def preceding(circ, t):
    return circ.at(t - 1)


def following(circ, e, t):
    return circ.at(t + e)


def is_repeat(circ, e, a, b):
    """Two selected starts, equal length-`e` windows, maximal on both sides."""
    return (
        1 <= e
        and e < circ.G
        and a != b
        and circ.window(e, a) == circ.window(e, b)
        and preceding(circ, a) != preceding(circ, b)
        and following(circ, e, a) != following(circ, e, b)
    )


def is_triple_repeat(circ, e, a, b, c):
    """Three pairwise distinct selected starts, three-copy maximality."""
    return (
        1 <= e
        and e < circ.G
        and a != b
        and a != c
        and b != c
        and circ.window(e, a) == circ.window(e, b)
        and circ.window(e, a) == circ.window(e, c)
        and circ.window(e, b) == circ.window(e, c)
        and not (preceding(circ, a) == preceding(circ, b) == preceding(circ, c))
        and not (following(circ, e, a) == following(circ, e, b) == following(circ, e, c))
    )


def bridges_copy(circ, L, starts, e, t):
    """Some realized read covers one base strictly on both sides of the copy.

    Source convention: a read interval `[r, r+L)` bridges a lifted copy interval
    `[t', t'+e)` iff `r < t'` and `t' + e < r + L`.  Equivalently the copy's
    start sits at offset `d+1` of the read and `d + e + 1 < L`.
    """
    for r in starts:
        for d in range(L):
            if d + e + 1 < L and (r + d + 1) % circ.G == t:
                return True
    return False


def in_open_arc(circ, a, b, p):
    """`p` strictly on the open clockwise arc from `a` to `b`."""
    d1 = (p + circ.G - a) % circ.G
    d2 = (b + circ.G - a) % circ.G
    return 0 < d1 < d2


def four_distinct(a, b, c, d):
    return len({a, b, c, d}) == 4 and a != b and c != d


def interleaved(circ, a, b, c, d):
    """Cyclic alternation of the two repeats' four selected starts."""
    if not four_distinct(a, b, c, d):
        return False
    return in_open_arc(circ, a, b, c) != in_open_arc(circ, a, b, d)


def covers(circ, L, starts):
    for p in range(circ.G):
        if not any(any((r + dd) % circ.G == p for dd in range(L)) for r in starts):
            return False
    return True


def information_feasible(circ, L, starts):
    """Full `I_s`: coverage, all-bridged triple repeats, bridged interleavings."""
    if not covers(circ, L, starts):
        return False, "coverage fails"
    G = circ.G
    for e in range(1, G):
        for a, b, c in iproduct(range(G), repeat=3):
            if is_triple_repeat(circ, e, a, b, c):
                if not all(bridges_copy(circ, L, starts, e, t) for t in (a, b, c)):
                    return False, "triple repeat e=%d starts=%s not all-bridged" % (
                        e,
                        (a, b, c),
                    )
    for e1 in range(1, G):
        for e2 in range(1, G):
            for a, b, c, d in iproduct(range(G), repeat=4):
                if not (
                    is_repeat(circ, e1, a, b)
                    and is_repeat(circ, e2, c, d)
                    and interleaved(circ, a, b, c, d)
                ):
                    continue
                if not (
                    bridges_copy(circ, L, starts, e1, a)
                    or bridges_copy(circ, L, starts, e1, b)
                    or bridges_copy(circ, L, starts, e2, c)
                    or bridges_copy(circ, L, starts, e2, d)
                ):
                    return False, "interleaved pair e1=%d(%d,%d) e2=%d(%d,%d) failed" % (
                        e1,
                        a,
                        b,
                        e2,
                        c,
                        d,
                    )
    return True, "ok"


def repeat_census(circ):
    """Enumerate maximal repeats / triple repeats / interleaved pairs."""
    G = circ.G
    reps, triples, inter = [], [], []
    for e in range(1, G):
        for a, b in iproduct(range(G), repeat=2):
            if is_repeat(circ, e, a, b):
                reps.append((e, a, b))
    for e in range(1, G):
        for a, b, c in iproduct(range(G), repeat=3):
            if is_triple_repeat(circ, e, a, b, c):
                triples.append((e, a, b, c))
    for e1 in range(1, G):
        for e2 in range(1, G):
            for a, b, c, d in iproduct(range(G), repeat=4):
                if (
                    is_repeat(circ, e1, a, b)
                    and is_repeat(circ, e2, c, d)
                    and interleaved(circ, a, b, c, d)
                ):
                    inter.append((e1, a, b, e2, c, d))
    return reps, triples, inter


# --------------------------------------------------------------------------
# Objectives
# --------------------------------------------------------------------------
def multinom_coeff(obs):
    """`n! / prod_i x_i!` for a read-type count dict."""
    from math import factorial

    n = sum(obs.values())
    acc = factorial(n)
    for x in obs.values():
        acc //= factorial(x)
    return acc


def exact_likelihood(cand, obs):
    """Medvedev-Brudno §6.1 exact multinomial likelihood, candidate-intrinsic
    `N(D)`:  `n!/prod x_i! * prod_i (d_i / N(D))^x_i`."""
    N = cand.G
    L = read_length()
    cnt = counts(cand, L)
    acc = Fraction(multinom_coeff(obs))
    for w, x in obs.items():
        acc *= Fraction(cnt.get(w, 0), N) ** x
    return acc


def binomial_likelihood(cand, obs, N, drop_zero_count=False):
    """Literal §6.1 product-of-binomial-marginals approximation with the
    *fixed external* length `N`, over the whole length-`L` read-type space:

        `prod_w C(n, x_w) (d_w/N)^x_w (1 - d_w/N)^(n - x_w)`.

    With `drop_zero_count=True` the factors of unobserved types are dropped,
    which defines a *different* objective; used only to exhibit the effect of
    the retained `(1 - d_w/N)^n` factors.  Returns `(value, note)`.
    """
    L = read_length()
    n = sum(obs.values())
    cnt = counts(cand, L)
    acc = Fraction(1)
    for w in type_space(L):
        x = obs.get(w, 0)
        d = cnt.get(w, 0)
        if drop_zero_count and x == 0:
            continue
        # Domain: the binomial marginal is a probability mass function only for
        # 0 <= d/N <= 1.  Record the violation instead of silently producing
        # a negative or complex "likelihood".
        if d > N:
            return None, "domain violation: d=%d > N=%d for type %s" % (
                d,
                N,
                "".join(w),
            )
        acc *= comb(n, x) * Fraction(d, N) ** x * (1 - Fraction(d, N)) ** (n - x)
    return acc, "ok"


def comb(n, k):
    from math import comb as _c

    return _c(n, k)


# --------------------------------------------------------------------------
# Reporting helpers
# --------------------------------------------------------------------------
FAILURES = []


def check(label, cond, detail=""):
    status = "PASS" if cond else "FAIL"
    if not cond:
        FAILURES.append(label)
    print("  [%s] %-68s %s" % (status, label, detail))


def section(title):
    print()
    print("=" * 78)
    print(title)
    print("=" * 78)


def report_witness(name, truth, cand, L, starts, obs, N_external=None):
    print()
    print("--- %s" % name)
    print(
        "  truth=%s (G=%d)  competitor=%s (|D|=%d)  L=%d  starts=%s  N_external=%s"
        % (truth, truth.G, cand, cand.G, L, sorted(set(starts)), N_external)
    )
    print("  observation: %s (n=%d)" % (obs, sum(obs.values())))

    set_read_length(L)

    # --- I_s certificate
    ok, why = information_feasible(truth, L, sorted(set(starts)))
    check("I_s membership (full predicate)", ok, why)
    realized = {}
    for r in starts:
        w = truth.window(L, r)
        realized[w] = realized.get(w, 0) + 1
    check("realization reproduces observation", realized == obs, str(realized))

    reps, triples, inter = repeat_census(truth)
    print(
        "  repeats: %d maximal pairs, %d maximal triples, %d interleaved pairs"
        % (len(reps), len(triples), len(inter))
    )
    if triples:
        print("    distinct triples: %s" % (sorted(set(triples)),))
    if inter:
        print("    interleaved: %s" % (sorted(set(inter)),))

    # --- exact multinomial (Variant E)
    lt = exact_likelihood(truth, obs)
    ld = exact_likelihood(cand, obs)
    ratio_e = ld / lt if lt != 0 else None
    check(
        "exact E: D strictly more likely than truth",
        ratio_e is not None and ratio_e > 1,
        "L(S)=%s L(D)=%s ratio=%s" % (lt, ld, ratio_e),
    )

    # --- fixed-N binomial marginals (Variant A)
    if N_external is not None:
        la, why1 = binomial_likelihood(truth, obs, N_external)
        lb, why2 = binomial_likelihood(cand, obs, N_external)
        if la is None or lb is None:
            check("binomial A: defined on both candidates", False, why1 + " / " + why2)
        else:
            ratio_a = lb / la
            check(
                "binomial A: D more likely than truth",
                ratio_a > 1,
                "L_A(S)=%s L_A(D)=%s ratio=%s" % (la, lb, ratio_a),
            )
            la2, _ = binomial_likelihood(truth, obs, N_external, drop_zero_count=True)
            lb2, _ = binomial_likelihood(cand, obs, N_external, drop_zero_count=True)
            print(
                "    zero-count factors retained:   ratio=%s  (%s / %s)"
                % (ratio_a, lb, la)
            )
            print(
                "    zero-count factors dropped:    ratio=%s  (%s / %s)"
                % ((lb2 / la2) if la2 else None, lb2, la2)
            )
            ct, cc = counts(truth, L), counts(cand, L)
            for w in type_space(L):
                x = obs.get(w, 0)
                if ct.get(w, 0) != cc.get(w, 0):
                    print(
                        "    type %s: x=%d  d_S=%d  d_D=%d   %s"
                        % (
                            "".join(w),
                            x,
                            ct.get(w, 0),
                            cc.get(w, 0),
                            "zero-count factor retained"
                            if x == 0
                            else "observed",
                        )
                    )
    return lt, ld


# ==========================================================================
def main():
    # ----------------------------------------------------------------------
    section("A. Exact multinomial (Variant E) - unrestricted-length witness")
    # The ACGT witness lives in the full DNA alphabet; ALPHABET must be ACGT.
    global ALPHABET
    ALPHABET = "ACGT"
    truth = Circ("ACGT")
    cand = Circ("ACACGT")
    obs = {("A", "C"): 2, ("G", "T"): 1}
    report_witness(
        "ACGT -> ACACGT (issue #24 / docs/exact-variant-e-counterexample.md)",
        truth, cand, 2, [0, 0, 2], obs,
    )

    # ----------------------------------------------------------------------
    section("B. Exact multinomial (Variant E) and Variant A - same-length AAABB")
    ALPHABET = "ABCG"
    truth = Circ("AAABB")
    cand = Circ("AAAAB")
    obs = {("A", "A", "A"): 1, ("A", "A", "B"): 1, ("B", "A", "A"): 1}
    report_witness(
        "AAABB -> AAAAB (issue #31 / docs/fixed-length-exact-counterexample.md)",
        truth, cand, 3, [0, 1, 4], obs, N_external=5,
    )
    print()
    print("  duplicate-read families (extra copies of the start-0 read AAA):")
    for k in range(1, 7):
        ob = {
            ("A", "A", "A"): k,
            ("A", "A", "B"): 1,
            ("B", "A", "A"): 1,
        }
        re = exact_likelihood(cand, ob) / exact_likelihood(truth, ob)
        la, _ = binomial_likelihood(truth, ob, 5)
        lb, _ = binomial_likelihood(cand, ob, 5)
        check(
            "exact E with AAA x%d: ratio 2^%d" % (k, k),
            re == Fraction(2) ** k,
            "ratio=%s" % re,
        )
        print(
            "      binomial A (N=5) with AAA x%d: L_A(S)=%s L_A(D)=%s ratio=%s"
            % (k, la, lb, (lb / la if la else None))
        )

    # ----------------------------------------------------------------------
    section("C. Variant A and Variant E - same-length AAACC -> AAAAC (B->C)")
    truth = Circ("AAACC")
    cand = Circ("AAAAC")
    obs = {("A", "A", "A"): 1, ("A", "A", "C"): 1, ("C", "A", "A"): 1}
    report_witness(
        "AAACC -> AAAAC (issue #32 / docs/fixed-length-binomial-counterexample.md)",
        truth, cand, 3, [0, 1, 4], obs, N_external=5,
    )

    # ----------------------------------------------------------------------
    section("D. Domain of the binomial marginal: `0 <= d_i <= N`")
    truth = Circ("AAACC")
    obs = {("A", "A", "A"): 1, ("A", "A", "C"): 1, ("C", "A", "A"): 1}
    for cand_s in ["AAA", "AAAA", "AAAAA", "AAAAAA"]:
        c = Circ(cand_s)
        val, why = binomial_likelihood(c, obs, 5)
        print(
            "  candidate %-8s |D|=%d  d_AAA=%2d  L_A(cand | N=5) = %s %s"
            % (
                cand_s,
                c.G,
                counts(c, 3).get(("A", "A", "A"), 0),
                "UNDEFINED (domain)" if val is None else val,
                why if val is None else "",
            )
        )
    print(
        "  => three regions: |D| <= N (objective automatically a product of"
        " probabilities), {D : forall w, d_w <= N} (happens to be well-defined),"
        " and the unrestricted circular class (negative values occur)."
    )
    worst = max(
        max(counts(Circ("".join(p)), 3).values())
        for p in iproduct(ALPHABET, repeat=5)
    )
    check(
        "for |D| = N = 5, max d_i <= N always",
        worst <= 5,
        "max d over all 4^5 length-5 genomes = %d" % worst,
    )

    # ----------------------------------------------------------------------
    section("E. Bounded searches over the candidate universe")
    # E1: exact E, unrestricted length, ACGT instance
    ALPHABET = "ACGT"
    set_read_length(2)
    truth = Circ("ACGT")
    obs = {("A", "C"): 2, ("G", "T"): 1}
    best = (-1, None)
    tv = exact_likelihood(truth, obs)
    for L in range(1, 9):
        for tup in iproduct(ALPHABET, repeat=L):
            v = exact_likelihood(Circ(tup), obs)
            if v > best[0]:
                best = (v, "".join(tup))
    check(
        "exact E (ACGT): truth not maximizer over |D|<=8, {A,C,G,T}",
        best[0] > tv,
        "best=%s L=%s  truth L=%s" % (best[0], best[1], tv),
    )

    # E2/E3/E4: length-5 universe, 4-letter alphabet ABCG
    ALPHABET = "ABCG"
    set_read_length(3)
    court = [
        ("exact E", lambda c, ob: exact_likelihood(c, ob)),
        ("binomial A", lambda c, ob: binomial_likelihood(c, ob, 5)[0]),
        (
            "binomial A, zero-count dropped",
            lambda c, ob: binomial_likelihood(c, ob, 5, drop_zero_count=True)[0],
        ),
    ]
    instances = [
        ("AAABB -> AAAAB", Circ("AAABB"),
         {("A", "A", "A"): 1, ("A", "A", "B"): 1, ("B", "A", "A"): 1}),
        ("AAACC -> AAAAC", Circ("AAACC"),
         {("A", "A", "A"): 1, ("A", "A", "C"): 1, ("C", "A", "A"): 1}),
    ]
    for iname, truth, obs in instances:
        for oname, obj in court:
            tv = obj(truth, obs)
            best = (-1, None)
            for tup in iproduct(ALPHABET, repeat=5):
                v = obj(Circ("".join(tup)), obs)
                if v > best[0]:
                    best = (v, "".join(tup))
            check(
                "%s (%s): truth not maximizer over 4^5 length-5 genomes"
                % (iname, oname),
                best[0] > tv,
                "best=%s (cand %s)  truth=%s" % (best[0], best[1], tv),
            )

    # ----------------------------------------------------------------------
    section("E2. Variant A on the other E witnesses")

    # (a) ACGT -> ACACGT evaluated with the external length N = 4 (the truth's
    #     length).  The competitor has |D| = 6 > N = 4, i.e. it lies outside the
    #     class where the literal binomial marginal is a probability.
    ALPHABET = "ACGT"
    set_read_length(2)
    truth = Circ("ACGT")
    cand = Circ("ACACGT")
    obs = {("A", "C"): 2, ("G", "T"): 1}
    la, _ = binomial_likelihood(truth, obs, 4)
    lb, why = binomial_likelihood(cand, obs, 4)
    print("  ACGT/ACACGT with external N = 4: L_A(S)=%s  L_A(D)=%s  ratio D/S=%s"
          % (la, lb, lb / la if lb else why))
    print("  |D| of competitor = %d > N = 4: outside the domain in which the"
          % cand.G)
    print("  literal marginal is a product of binomial probabilities.")

    # (b) AABB -> ABAB, the oriented same-length witness of issue #88 / #211.
    ALPHABET = "AB"
    set_read_length(2)
    truth = Circ("AABB")
    cand = Circ("ABAB")
    obs = {("A", "B"): 1, ("B", "A"): 1}
    report_witness("AABB -> ABAB (oriented same-length witness, issues #88/#211)",
                   truth, cand, 2, [1, 3], obs, N_external=4)

    # ----------------------------------------------------------------------
    section("F. The unparameterized 'read-tiled' row: AAABCBC -> AAAAABC, ratio 27")
    # The previous section leaves the module-global read length at 2; the
    # read-tiled row uses length-3 reads, so it must be reset explicitly
    # (it used to be inherited, which silently zeroed every likelihood here).
    set_read_length(3)
    truth = Circ("AAABCBC")
    cand = Circ("AAAAABC")
    print("  truth windows: %s" % (truth.windows(3),))
    print("  cand   windows: %s" % (cand.windows(3),))
    types = sorted(set(truth.windows(3)))
    candidates = []
    for combo in iproduct(range(5), repeat=len(types)):
        ob = {t: c for t, c in zip(types, combo) if c > 0}
        if not ob:
            continue
        lt = exact_likelihood(truth, ob)
        ld = exact_likelihood(cand, ob)
        if lt == 0 or ld == 0:
            continue
        if ld / lt == 27:
            # The distinct realized starts that can produce `ob` are exactly the
            # starts whose window is observed; coverage/I_s use that set.
            R = [r for r in range(truth.G) if truth.window(3, r) in ob]
            cov = covers(truth, 3, R)
            okis, why = information_feasible(truth, 3, R)
            candidates.append((ob, sorted(R), cov, okis, why))
    print("  observations (multisets of truth windows, counts 0..4) with ratio 27: %d"
          % len(candidates))
    feas = [c for c in candidates if c[3]]
    print("  ... of which fully I_s-feasible: %d" % len(feas))
    for ob, R, cov, okis, why in candidates[:8]:
        print(
            "    obs=%s  R=%s  coverage=%s  I_s=%s %s"
            % ({"".join(k): v for k, v in ob.items()}, R, cov, okis, "")
        )
    for ob, R, cov, okis, why in feas[:4]:
        print(
            "    FEASIBLE obs=%s  R=%s  (%s)"
            % ({"".join(k): v for k, v in ob.items()}, R, why)
        )
    # also record the minimal ratio-27 family with coverage and positive D
    if candidates:
        best_cov = [c for c in candidates if c[2]]
        print("  ... of these, %d give coverage of the truth" % len(best_cov))

    # ----------------------------------------------------------------------
    section("G. Maximizer census (bounded: exhaustive over the candidate class)")

    def shifts(g):
        return {"".join(g.syms[i:] + g.syms[:i]) for i in range(g.G)}

    def census(name, truth, obs, obj, klass, alphabet):
        global ALPHABET
        ALPHABET = alphabet
        set_read_length(2 if len(list(obs)[0]) == 2 else 3)
        vals = {}
        for tup in klass:
            c = Circ(tup)
            v = obj(c, obs)
            vals["".join(tup)] = v
        mx = max(vals.values())
        best = [k for k, v in vals.items() if v == mx]
        non_shift = [b for b in best if b not in shifts(truth)]
        print("  %s (class size %d)" % (name, len(klass)))
        print("    maximum value %s attained by %d candidates; %d are NOT cyclic"
              " shifts of the truth" % (mx, len(best), len(non_shift)))
        print("    maximizers: %s" % (best[:12],))
        print("    truth value %s (%s)" % (vals[str(truth)],
              "maximizer" if vals[str(truth)] == mx else "NOT a maximizer"))
        return mx, best, non_shift

    def objAN(N):
        # Variance-A objective for an explicit external length `N`.  The census
        # rows below pass `N` explicitly; an earlier version hardcoded `5`, so
        # the row labelled "N=4" actually reported the N=5 numbers.
        return lambda c, ob: binomial_likelihood(c, ob, N)[0]

    ALPHABET = "ABCG"
    set_read_length(3)
    classes = ["".join(p) for p in iproduct(ALPHABET, repeat=5)]
    objE = lambda c, ob: exact_likelihood(c, ob)
    objA5 = objAN(5)
    for nm, t, ob in [
        ("exact E, AAABB obs", Circ("AAABB"),
         {("A", "A", "A"): 1, ("A", "A", "B"): 1, ("B", "A", "A"): 1}),
        ("exact E, AAACC obs", Circ("AAACC"),
         {("A", "A", "A"): 1, ("A", "A", "C"): 1, ("C", "A", "A"): 1}),
        ("binomial A (N=5), AAABB obs", Circ("AAABB"),
         {("A", "A", "A"): 1, ("A", "A", "B"): 1, ("B", "A", "A"): 1}),
        ("binomial A (N=5), AAACC obs", Circ("AAACC"),
         {("A", "A", "A"): 1, ("A", "A", "C"): 1, ("C", "A", "A"): 1}),
    ]:
        census(nm, t, ob, objE if nm.startswith("exact") else objA5,
               classes, ALPHABET)

    ALPHABET = "AB"
    set_read_length(2)
    classes2 = ["".join(p) for p in iproduct(ALPHABET, repeat=4)]
    census("exact E, AB/BA obs", Circ("AABB"),
           {("A", "B"): 1, ("B", "A"): 1}, objE, classes2, ALPHABET)
    census("binomial A (N=4), AB/BA obs", Circ("AABB"),
           {("A", "B"): 1, ("B", "A"): 1}, objAN(4), classes2, ALPHABET)
    census("binomial A (N=5), AB/BA obs", Circ("AABB"),
           {("A", "B"): 1, ("B", "A"): 1}, objAN(5), classes2, ALPHABET)

    # ----------------------------------------------------------------------
    section("G. Summary")
    if FAILURES:
        print("  FAILED CHECKS:")
        for f in FAILURES:
            print("   - %s" % f)
    else:
        print("  All checks passed.")


if __name__ == "__main__":
    main()
