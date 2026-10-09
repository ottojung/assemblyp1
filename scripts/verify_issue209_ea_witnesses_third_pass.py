#!/usr/bin/env python3
"""Independent (third) re-verification of the AssemblyP1 issue #209 E/A
negative results under the *full* source-faithful hypothesis `I_s`.

Written for issue #209 (front `agent/board-209-6cf9bd`) as a check that shares
**no code** with either
  * `scripts/verify_issue209_ea_witnesses.py` (the first audit script), or
  * `scratch-209/independent_recheck.py` (the second-pass script).

Everything below is re-derived from the source definitions:

  substrate   circular genome, length-`L` windows at integer starts (`% len`);
  `I_s`       Shomorony et al. (2016) Eq. (1), with the Bresler-Bresler-Tse
              (2013) repeat semantics:
                clause 1  R covers S;
                clause 2  every maximal triple repeat is all-bridged;
                clause 3  every interleaved pair of maximal repeats is bridged;
  bridges     a read interval `[r, r+L)` bridges a copy `[t', t'+e)` iff
              `r < t'` and `t' + e < r + L` on a suitable integer lift
              (`e + 2 <= L`);
  Variant E   exact Medvedev-Brudno (2009) Sec. 6.1 multinomial with
              candidate-intrinsic `N(D) = |D|`:
              `n! / prod_i x_i! * prod_i (d_i / |D|)^x_i`;
  Variant A   the literal Sec. 6.1 approximation: the product of binomial
              marginals over the WHOLE read-type space with the fixed external
              length `N`:
              `prod_w C(n, x_w) (d_w/N)^x_w (1 - d_w/N)^(n - x_w)`,
              zero-count factors `(1 - d_w/N)^n` retained.

The read-type space is always the *model* alphabet `Fin L -> Base` (4 symbols),
never the candidate's own symbol set: dropping the types a candidate does not
contain silently deletes observed factors and inflates relabelled candidates.

Epistemic class of this script: **exact arithmetic** (rational values) and
**bounded evidence** (exhaustive computation over a finite class).  It is not a
proof.  The kernel-checked obligations live in Lean; the expected values below
are transcribed from the Lean theorems named in each check, so agreement between
this script and those numbers is an independent check that the instances the
notes claim are the instances Lean proved.
"""

from fractions import Fraction
from itertools import product as iproduct
from math import factorial

# The four-symbol DNA alphabet of the witness modules (Base = A | B | C | G).
ALPHABET = ("A", "B", "C", "G")

FAIL = []


def ck(name, ok, detail=""):
    tag = "PASS" if ok else "FAIL"
    print("  [%s] %-58s %s" % (tag, name, detail))
    if not ok:
        FAIL.append(name)
    return ok


def section(title):
    print("\n" + "=" * 78)
    print(title)
    print("=" * 78)


# --------------------------------------------------------------------------
# Substrate: a circular genome
# --------------------------------------------------------------------------
class Circ:
    def __init__(self, syms):
        self.syms = tuple(syms)
        self.G = len(self.syms)
        assert self.G > 0

    def at(self, i):
        return self.syms[i % self.G]

    def win(self, e, r):
        return tuple(self.at(r + d) for d in range(e))

    def wins(self, e):
        return [self.win(e, r) for r in range(self.G)]

    def __str__(self):
        return "".join(self.syms)


def counts(g, e):
    c = {}
    for w in g.wins(e):
        c[w] = c.get(w, 0) + 1
    return c


def types(L, alphabet=ALPHABET):
    return [tuple(t) for t in iproduct(alphabet, repeat=L)]


# --------------------------------------------------------------------------
# `I_s`: coverage, maximal repeats, bridging
# --------------------------------------------------------------------------
def covers(g, L, R):
    """Clause 1: every position lies in some realized read of length `L`."""
    return all(
        any((r + d) % g.G == p for r in R for d in range(L))
        for p in range(g.G)
    )


def maximal_repeats(g, e):
    """Maximal length-`e` repeats (Bresler: equal windows, preceding symbols
    differ, following symbols differ), as unordered pairs of starts."""
    out = []
    for a in range(g.G):
        for b in range(a + 1, g.G):
            if g.win(e, a) == g.win(e, b) and g.at(a - 1) != g.at(b - 1) and \
               g.at(a + e) != g.at(b + e):
                out.append((a, b))
    return out


def maximal_triple_repeats(g, e):
    """Maximal length-`e` triple repeats: three pairwise distinct starts whose
    windows agree, with the preceding symbols (resp. following symbols) not all
    equal.  Returned as unordered triples."""
    out = []
    for a in range(g.G):
        for b in range(a + 1, g.G):
            for c in range(b + 1, g.G):
                if not (g.win(e, a) == g.win(e, b) == g.win(e, c)):
                    continue
                pre = (g.at(a - 1), g.at(b - 1), g.at(c - 1))
                fol = (g.at(a + e), g.at(b + e), g.at(c + e))
                if pre[0] == pre[1] == pre[2]:
                    continue
                if fol[0] == fol[1] == fol[2]:
                    continue
                out.append((a, b, c))
    return out


def bridges_copy(g, L, R, e, t):
    """A single realized read straddles the copy of length `e` at `t`: strictly
    before and strictly after (Bresler Fig. 5 / Shomorony Sec. 3)."""
    for r in R:
        for d in range(L):
            # copy starts at lifted position r + d + 1
            if (r + d + 1) % g.G == t % g.G and d + e + 1 < L:
                return True
    return False


def alternates(g, a, b, c, d):
    """Four distinct starts that alternate around the circle: exactly one of
    `c`, `d` lies on the open clockwise arc from `a` to `b`."""
    def arc_len(x, y):
        return (y - x) % g.G

    ab = arc_len(a, b)
    ac = arc_len(a, c)
    ad = arc_len(a, d)
    if not (0 < ab < g.G):
        return False  # a and b are not two distinct positions on the circle
    return (0 < ac < ab) != (0 < ad < ab)


def interleaved_pairs(g, e1, e2):
    """Pairs of maximal repeats (one of length e1, one of length e2) that
    interleave, with pairwise distinct starts."""
    out = []
    for (a, b) in maximal_repeats(g, e1):
        for (c, d) in maximal_repeats(g, e2):
            if len({a, b, c, d}) < 4:
                continue
            if alternates(g, a, b, c, d) or alternates(g, a, b, d, c):
                out.append(((a, b), (c, d)))
    return out


def information_feasible(g, L, R):
    """Full source-faithful `I_s`.  Returns (ok, diagnostics)."""
    if not covers(g, L, R):
        return False, "coverage"
    for e in range(1, g.G):
        for (a, b, c) in maximal_triple_repeats(g, e):
            if not all(bridges_copy(g, L, R, e, t) for t in (a, b, c)):
                return False, "triple repeat (%d,%d,%d) not all bridged" % (a, b, c)
    for e1 in range(1, g.G):
        for e2 in range(1, g.G):
            for ((a, b), (c, d)) in interleaved_pairs(g, e1, e2):
                if not any(bridges_copy(g, L, R, e1, t) for t in (a, b)) and \
                   not any(bridges_copy(g, L, R, e2, t) for t in (c, d)):
                    return False, "interleaved pair unbridged"
    return True, "ok"


def clause2_nonvacuous(g, e):
    return len(maximal_triple_repeats(g, e)) > 0


def clause3_nonvacuous(g):
    for e1 in range(1, g.G):
        for e2 in range(1, g.G):
            if interleaved_pairs(g, e1, e2):
                return True
    return False


# --------------------------------------------------------------------------
# Objectives
# --------------------------------------------------------------------------
def exact_multinomial(g, obs):
    """Variant E: exact multinomial, candidate-intrinsic `N(D) = |D|`."""
    d = counts(g, len(next(iter(obs))))
    n = sum(obs.values())
    coeff = Fraction(factorial(n))
    for x in obs.values():
        coeff /= factorial(x)
    val = coeff
    for w, x in obs.items():
        val *= Fraction(d.get(w, 0), g.G) ** x
    return val


def binomial_marginals(g, obs, N, drop_zero=False, alphabet=ALPHABET):
    """Variant A: product of binomial marginals over the WHOLE read-type space
    (zero-count factors retained unless `drop_zero`).  Returns None if some
    multiplicity exceeds `N`, i.e. the objective is not a product of
    probabilities for this candidate."""
    L = len(next(iter(obs)))
    d = counts(g, L)
    n = sum(obs.values())
    val = Fraction(1)
    for w in types(L, alphabet):
        x = obs.get(w, 0)
        dw = d.get(w, 0)
        if dw > N:
            return None  # (1 - d/N) is negative: outside the domain
        p = Fraction(dw, N)
        if x == 0 and drop_zero:
            continue
        val *= Fraction(factorial(n), factorial(x) * factorial(n - x)) * \
            p ** x * (1 - p) ** (n - x)
    return val


# --------------------------------------------------------------------------
# Witness table (instances transcribed from the docs; the Lean theorem that
# proves each row is named in the expected-value oracle below)
# --------------------------------------------------------------------------
WITNESSES = [
    dict(id="E-1", S=Circ("ACGT"), L=2, starts=[0, 2],
         obs={("A", "C"): 2, ("G", "T"): 1}, D=Circ("ACACGT"),
         # ExactVariantECounterexample uses `DNA = A | C | G | T`.
         alpha="ACGT"),
    dict(id="E-2", S=Circ("AAABB"), L=3, starts=[0, 1, 4],
         obs={("A", "A", "A"): 1, ("A", "A", "B"): 1, ("B", "A", "A"): 1},
         D=Circ("AAAAB"),
         # FixedLength*Counterexample / Issue209EAudit use
         # `Base = A | B | C | G`, so `Fin 3 -> Base` is the type space.
         alpha="ABCG"),
    dict(id="E-3", S=Circ("AAACC"), L=3, starts=[0, 1, 4],
         obs={("A", "A", "A"): 1, ("A", "A", "C"): 1, ("C", "A", "A"): 1},
         D=Circ("AAAAC"), alpha="ABCG"),
    dict(id="E-4", S=Circ("AABB"), L=2, starts=[1, 3],
         obs={("A", "B"): 1, ("B", "A"): 1}, D=Circ("ABAB"),
         # SameLengthExactMLCounterexample uses the two-letter alphabet.
         alpha="AB"),
]

# Expected values transcribed from the Lean theorems (kernel-checked rows).
LEAN_E = {
    "E-1": (Fraction(3, 64), Fraction(1, 18), Fraction(32, 27)),
    "E-2": (Fraction(6, 125), Fraction(12, 125), Fraction(2)),
    "E-3": (Fraction(6, 125), Fraction(12, 125), Fraction(2)),
    "E-4": (Fraction(1, 8), Fraction(1, 2), Fraction(4)),
}
# Fixed-N binomial rows: (N, L(S), L(D), ratio) as proved in Lean for A-1/A-2
# and reproduced by exact arithmetic for A-3/A-4.
LEAN_A = {
    "E-1": (4, Fraction(177147, 16777216), Fraction(1594323, 134217728),
            Fraction(9, 8)),
    "E-2": (5, Fraction(452984832, 30517578125), Fraction(7962624, 244140625),
            Fraction(1125, 512)),
    "E-3": (5, Fraction(452984832, 30517578125), Fraction(7962624, 244140625),
            Fraction(1125, 512)),
    "E-4": (4, Fraction(729, 16384), Fraction(1, 4), Fraction(4096, 729)),
}


def check_witnesses():
    section("1. WITNESSES: full I_s, realization, exact values, strict ratios")
    for w in WITNESSES:
        g, D, L, R, obs = w["S"], w["D"], w["L"], w["starts"], w["obs"]
        print("\n--- %s  %s -> %s   L=%d  starts=%s" % (w["id"], g, D, L, R))
        ok, why = information_feasible(g, L, R)
        ck("I_s (full source-faithful predicate)", ok, why)
        # the realization is consistent with i.i.d. sampling from the starts:
        # every observed type must be producible by some start of S, and the
        # realized start set must be a set of starts producing observed types.
        dS = counts(g, L)
        ck("every observed type is a window of S",
           all(dS.get(t, 0) >= 1 for t in obs),
           "counts in S: %s" % {"".join(t): v for t, v in sorted(
               dS.items())})
        ck("R is exactly the set of starts producing an observed type",
           sorted(R) == sorted(r for r in range(g.G) if g.win(L, r) in obs),
           "R=%s" % sorted(R))
        ls = exact_multinomial(g, obs)
        ld = exact_multinomial(D, obs)
        eS, eD, eR = LEAN_E[w["id"]]
        ck("Variant E L(S) matches Lean", ls == eS, "%s (Lean %s)" % (ls, eS))
        ck("Variant E L(D) matches Lean", ld == eD, "%s (Lean %s)" % (ld, eD))
        ck("Variant E ratio strict, matches Lean", ld / ls == eR and eR > 1,
           "%s (Lean %s)" % (Fraction(ld, ls), eR))
        N, aS, aD, aR = LEAN_A[w["id"]]
        al = w["alpha"]
        bs = binomial_marginals(g, obs, N, alphabet=al)
        bd = binomial_marginals(D, obs, N, alphabet=al)
        ck("Variant A (N=%d) defined for S and D" % N,
           bs is not None and bd is not None, "L(S)=%s L(D)=%s" % (bs, bd))
        if bs is not None and bd is not None:
            ck("Variant A L(S) matches", bs == aS, "%s (Lean %s)" % (bs, aS))
            ck("Variant A L(D) matches", bd == aD, "%s (Lean %s)" % (bd, aD))
            ck("Variant A ratio strict, matches", bd / bs == aR and aR > 1,
               "%s (Lean %s)" % (Fraction(bd, bs), aR))
            # the zero-count-dropped reading (a *different* objective)
            ck("zero-count-dropped reading still refutes",
               binomial_marginals(D, obs, N, True, al) /
               binomial_marginals(g, obs, N, True, al) > 1)
            # Regression guard for the defect this pass found.  If the
            # read-type space omits a symbol that the model alphabet
            # contains, the factors of the types that use it are silently
            # dropped; the ratio then survives while the values change.  So a
            # script that checks only ratios cannot see the error, and every
            # value in the ledger must be reproduced over the module's own
            # alphabet.  Exhibit the sensitivity.
            sens = []
            for s in al:
                if s in str(g) or s in str(D):
                    v = binomial_marginals(g, obs, N, alphabet=al.replace(s, ""))
                    vD = binomial_marginals(D, obs, N, alphabet=al.replace(s, ""))
                    if v is not None and vD is not None and (v != bs or
                                                             vD != bd):
                        sens.append((s, v, vD, vD / v))
            ck("type space sensitivity: dropping a symbol used by the genomes"
               " changes the likelihood values",
               bool(sens),
               "; ".join("drop %s -> L(S)=%s L(D)=%s ratio=%s%s"
                         % (s, v, vD, r, " (ratio unchanged!)"
                            if r == aR else "")
                         for (s, v, vD, r) in sens[:3]))
        ck("I_s clause 2 non-vacuous" if clause2_nonvacuous(g, L)
           else "I_s clause 2 vacuous (no triple repeat)", True,
           "clause3 non-vacuous=%s" % clause3_nonvacuous(g))


def check_domains():
    section("2. DOMAIN d_w <= N and the three candidate regions")
    # the explicit boundary: a length-6 all-A candidate with N = 5
    neg = binomial_marginals(Circ("AAAAAA"), {("A", "A", "A"): 1}, 5)
    ck("length-6 all-A candidate, N=5: objective undefined (d_AAA=6 > 5)",
       neg is None)
    d = counts(Circ("AAAAAA"), 3)
    ck("... d_AAA = 6 there", d[("A", "A", "A")] == 6)
    ck("... the unobserved-type marginal is (1-6/5)^3 = -1/125 < 0",
       (Fraction(1) - Fraction(6, 5)) ** 3 < 0)
    # |D| <= N makes every literal marginal a probability
    bad = 0
    for tup in iproduct("AB", repeat=5):
        g = Circ(tup)
        if any(v > 5 for v in counts(g, 3).values()):
            bad += 1
    ck("|D| = N = 5: no length-5 word has d_w > 5", bad == 0)
    # the intermediate region is nonempty: |D| > N with all d_w <= N
    acacgt = Circ("ACACGT")
    ck("intermediate region nonempty: ACACGT, |D|=6 > N=4, all d_w <= 4",
       len(acacgt) if False else acacgt.G == 6 and
       all(v <= 4 for v in counts(acacgt, 2).values()))


def check_duplicates():
    section("3. DUPLICATE-READ FAMILIES (extra copies of the start-0 read AAA)")
    S, D = Circ("AAABB"), Circ("AAAAB")
    for k in range(1, 7):
        obs = {("A", "A", "A"): k, ("A", "A", "B"): 1, ("B", "A", "A"): 1}
        ls, ld = exact_multinomial(S, obs), exact_multinomial(D, obs)
        bs = binomial_marginals(S, obs, 5)
        bd = binomial_marginals(D, obs, 5)
        ck("k=%d exact E ratio 2^k" % k, ld / ls == Fraction(2) ** k,
           "%s (2^%d=%s)" % (Fraction(ld, ls), k, Fraction(2) ** k))
        ck("k=%d binomial ratio (1125/512)(5/2)^(k-1)" % k,
           bd / bs == Fraction(1125, 512) * Fraction(5, 2) ** (k - 1),
           "%s" % Fraction(bd, bs))


def check_census():
    section("4. EXHAUSTIVE MAXIMIZER CENSUSES (bounded evidence)")

    def shifts(g):
        return {str(Circ(g.syms[i:] + g.syms[:i])) for i in range(g.G)}

    def census(name, truth, obs, obj, alphabet, L):
        mx, best = None, []
        vals = {}
        for tup in iproduct(alphabet, repeat=L):
            v = obj(Circ(tup), obs)
            if v is None:
                continue
            vals["".join(tup)] = v
            if mx is None or v > mx:
                mx, best = v, ["".join(tup)]
            elif v == mx:
                best.append("".join(tup))
        non_shift = [b for b in best if b not in shifts(truth)]
        print("  %s (class %d)" % (name, len(vals)))
        print("    max %s at %d candidates, %d not cyclic shifts of the truth;"
              " maximizers=%s" % (mx, len(best), len(non_shift), sorted(best)[:6]))
        print("    truth value %s -> %s" % (vals[str(truth)],
              "MAXIMIZER" if vals[str(truth)] == mx else "NOT a maximizer"))
        return vals[str(truth)] < mx and len(non_shift) > 0

    ok = True
    for nm, truth, obs, obj, alpha, L in [
        ("exact E, AAABB obs", Circ("AAABB"),
         {("A", "A", "A"): 1, ("A", "A", "B"): 1, ("B", "A", "A"): 1},
         exact_multinomial, "ABCG", 5),
        ("exact E, AAACC obs", Circ("AAACC"),
         {("A", "A", "A"): 1, ("A", "A", "C"): 1, ("C", "A", "A"): 1},
         exact_multinomial, "ABCG", 5),
        ("binomial A (N=5), AAABB obs", Circ("AAABB"),
         {("A", "A", "A"): 1, ("A", "A", "B"): 1, ("B", "A", "A"): 1},
         lambda c, o: binomial_marginals(c, o, 5), "ABCG", 5),
        ("binomial A (N=5), AAACC obs", Circ("AAACC"),
         {("A", "A", "A"): 1, ("A", "A", "C"): 1, ("C", "A", "A"): 1},
         lambda c, o: binomial_marginals(c, o, 5), "ABCG", 5),
        ("binomial A (N=5, zero dropped), AAABB obs", Circ("AAABB"),
         {("A", "A", "A"): 1, ("A", "A", "B"): 1, ("B", "A", "A"): 1},
         lambda c, o: binomial_marginals(c, o, 5, True), "ABCG", 5),
        ("exact E, AB/BA obs", Circ("AABB"),
         {("A", "B"): 1, ("B", "A"): 1}, exact_multinomial, "AB", 4),
        ("binomial A (N=4), AB/BA obs", Circ("AABB"),
         {("A", "B"): 1, ("B", "A"): 1},
         lambda c, o: binomial_marginals(c, o, 4), "AB", 4),
        ("binomial A (N=5), AB/BA obs", Circ("AABB"),
         {("A", "B"): 1, ("B", "A"): 1},
         lambda c, o: binomial_marginals(c, o, 5), "AB", 4),
    ]:
        ok = census(nm, truth, obs, obj, alpha, L) and ok
    ck("truth never a maximizer, maximizers never the truth's shift class", ok)

    section("4b. ACGT OBSERVATION OVER EVERY CIRCULAR CANDIDATE OF LENGTH <= 8")
    truth = Circ("ACGT")
    obs = {("A", "C"): 2, ("G", "T"): 1}
    total = 0
    mx = None
    best = []
    for G in range(1, 9):
        for tup in iproduct("ACGT", repeat=G):
            total += 1
            v = exact_multinomial(Circ(tup), obs)
            if mx is None or v > mx:
                mx, best = v, [tup]
            elif v == mx:
                best.append(tup)
    ck("class size is sum_{G<=8} 4^G = 87380", total == 87380, str(total))
    ck("best value 1/18", mx == Fraction(1, 18), str(mx))
    ck("attained by exactly the six cyclic shifts of ACACGT",
       sorted("".join(t) for t in best) ==
       sorted("ACACGT"[i:] + "ACACGT"[:i] for i in range(6)),
       sorted("".join(t) for t in best))
    ck("truth value 3/64 is not the max",
       exact_multinomial(truth, obs) < mx)


def check_read_tiled():
    section("5. READ-TILED ROW  AAABCBC -> AAAAABC, claimed ratio 27")
    S, D = Circ("AAABCBC"), Circ("AAAAABC")
    L = 3
    obs = {("A", "A", "A"): 3, ("A", "A", "B"): 1, ("A", "B", "C"): 1,
           ("B", "C", "A"): 1, ("C", "A", "A"): 1}
    R = [0, 1, 2, 5, 6]
    ck("the claimed realization is realizable on the truth",
       all(any(S.win(L, r) == w for r in R) for w in obs))
    ck("R is exactly the set of starts producing an observed type",
       sorted(R) == sorted(r for r in range(S.G) if S.win(L, r) in obs))
    ok, why = information_feasible(S, L, R)
    ck("full I_s holds for the claimed realization", ok, why)
    ls, ld = exact_multinomial(S, obs), exact_multinomial(D, obs)
    ck("ratio 27 exactly", ld / ls == 27, "%s / %s = %s" % (ld, ls,
                                                            Fraction(ld, ls)))
    ck("L_E(D) = 3240/117649 and L_E(S) = 120/117649",
       ld == Fraction(3240, 117649) and ls == Fraction(120, 117649),
       "%s %s" % (ls, ld))
    # the families over S's window types, enumerating with the same rules as
    # the audit script: counts 0..4, R forced to the starts whose window is
    # observed (the most permissive choice).
    win_types = sorted(set(S.wins(L)))
    n_ratio27 = n_feasible = n_cover = 0
    minimal = None
    for combo in iproduct(range(5), repeat=len(win_types)):
        ob = {t: c for t, c in zip(win_types, combo) if c > 0}
        if not ob:
            continue
        lt, ld_ = exact_multinomial(S, ob), exact_multinomial(D, ob)
        if lt == 0 or ld_ == 0 or ld_ / lt != 27:
            continue
        n_ratio27 += 1
        RR = [r for r in range(S.G) if S.win(L, r) in ob]
        if covers(S, L, RR):
            n_cover += 1
        okk, _ = information_feasible(S, L, RR)
        if okk:
            n_feasible += 1
            if minimal is None:
                minimal = (ob, RR)
    ck("625 ratio-27 observations (counts 0..4)", n_ratio27 == 625,
       str(n_ratio27))
    ck("256 of them fully I_s-feasible", n_feasible == 256, str(n_feasible))
    ck("400 of them give coverage", n_cover == 400, str(n_cover))
    ck("the ledger's minimal feasible realization is among them",
       minimal is not None and minimal[0] == obs and minimal[1] == R,
       str({"".join(k): v for k, v in (minimal[0] if minimal else {}).items()}))


def check_inheritance():
    section("6. WHICH CANDIDATE UNIVERSES INHERIT THE REFUTATION")
    for w in WITNESSES:
        S, D, L, obs = w["S"], w["D"], w["L"], w["obs"]
        dS, dD = counts(S, L), counts(D, L)
        ck("%s: all d_w <= |D| for both objects (so inside {D: d_w<=N} and"
           " {|D|<=N})" % w["id"],
           max(dS.values()) <= S.G and max(dD.values()) <= D.G,
           "max d_S=%d, max d_D=%d" % (max(dS.values()), max(dD.values())))
        # An object is a sequence-level Section 6.2 candidate only if every
        # length-L window it produces was observed.  A witness refutes the
        # maximizer claim on that class only when BOTH objects are feasible.
        spellS = all(t in obs for t in set(S.wins(L)))
        spellD = all(t in obs for t in set(D.wins(L)))
        ck("%s: at least one of truth/competitor has an unobserved length-%d"
           " window, so the pair is not inside the Sec 6.2 sequence-level"
           " feasible set" % (w["id"], L),
           not (spellS and spellD),
           "truth feasible=%s (unobserved %s), competitor feasible=%s"
           " (unobserved %s)"
           % (spellS, sorted("".join(t) for t in set(S.wins(L)) if t not in obs),
              spellD,
              sorted("".join(t) for t in set(D.wins(L)) if t not in obs)))


def main():
    print("issue #209 independent re-verification (third implementation)")
    print("alphabet %s; all arithmetic exact (Fraction)" % ("".join(ALPHABET),))
    check_witnesses()
    check_domains()
    check_duplicates()
    check_census()
    check_read_tiled()
    check_inheritance()
    print("\n" + "=" * 78)
    if FAIL:
        print("FAILED CHECKS (%d):" % len(FAIL))
        for f in FAIL:
            print("  - %s" % f)
        raise SystemExit(1)
    print("All checks passed.")


if __name__ == "__main__":
    main()
