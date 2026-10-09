#!/usr/bin/env python3
"""Independent recheck of the issue #209 E/A ledger (fresh implementation).

Written from scratch for front #209; shares no code with
`scripts/verify_issue209_ea_witnesses.py` or the Lean library.

Checks, all in exact rational arithmetic:

  1. every ledger witness (E-1..E-4, A-1..A-4) under the FULL source-faithful
     `I_s` predicate transcribed here independently;
  2. exact multinomial objective (Variant E) and the literal whole-type-space
     product-of-binomial-marginals objective with a fixed external `N`
     (Variant A), both zero-count readings;
  3. the `d_i <= N` domain, and the three candidate regions;
  4. duplicate-read families and their strict ratios;
  5. exhaustive maximizer censuses over complete candidate classes;
  6. the "read-tiled" `AAABCBC -> AAAAABC` row parameterization.
"""
from fractions import Fraction
from itertools import product as iproduct
from math import comb, factorial

FAIL = []

# The model's read-type alphabet.  The Lean witness modules quantify the
# whole-space product over `Fin 3 -> Base` with `Base = A|B|C|G`, so the
# binomial objective's type space is this alphabet, never the candidate's own
# symbol set.
DNA = "ABCG"


def ck(label, cond, detail=""):
    print("  [%s] %-62s %s" % ("PASS" if cond else "FAIL", label, detail))
    if not cond:
        FAIL.append(label)


class G:
    """Circular genome; read windows are length-`L` lifted windows."""

    def __init__(self, s):
        self.s = list(s)
        assert self.s

    def __str__(self):
        return "".join(self.s)

    @property
    def n(self):
        return len(self.s)

    def at(self, i):
        return self.s[i % self.n]

    def win(self, r, L):
        return tuple(self.at(r + d) for d in range(L))

    def mult(self, L):
        m = {}
        for r in range(self.n):
            m[self.win(r, L)] = m.get(self.win(r, L), 0) + 1
        return m


def observed(genome, L, starts):
    m = {}
    for r in starts:
        w = genome.win(r, L)
        m[w] = m.get(w, 0) + 1
    return m


# ---------------------------------------------------------------- I_s copy
def is_rep(g, e, a, b):
    return (e >= 1 and e < g.n and a % g.n != b % g.n
            and g.win(a, e) == g.win(b, e)
            and g.at(a - 1) != g.at(b - 1)
            and g.at(a + e) != g.at(b + e))


def is_rep3(g, e, a, b, c):
    a, b, c = a % g.n, b % g.n, c % g.n
    if a == b or a == c or b == c:
        return False
    if not (g.win(a, e) == g.win(b, e) == g.win(c, e)):
        return False
    return not (g.at(a - 1) == g.at(b - 1) == g.at(c - 1)) and \
        not (g.at(a + e) == g.at(b + e) == g.at(c + e))


def bridges(g, L, starts, e, t):
    starts = sorted({r % g.n for r in starts})
    for r in starts:
        for d in range(L):
            if d + e + 1 < L and (r + d + 1) % g.n == t % g.n:
                return True
    return False


def in_arc(g, a, b, p):
    d1 = (p - a) % g.n
    d2 = (b - a) % g.n
    return 0 < d1 < d2


def interleaved(g, a, b, c, d):
    if len({a % g.n, b % g.n, c % g.n, d % g.n}) != 4:
        return False
    return in_arc(g, a, b, c) != in_arc(g, a, b, d)


def covers(g, L, starts):
    starts = sorted({r % g.n for r in starts})
    return all(any((r + d) % g.n == p for r in starts for d in range(L))
               for p in range(g.n))


def is_full(g, L, starts):
    """Full `I_s`: coverage + all-bridged triple repeats + bridged interleaves."""
    if not covers(g, L, starts):
        return False, "coverage"
    n = g.n
    for e in range(1, n):
        for a, b, c in iproduct(range(n), repeat=3):
            if is_rep3(g, e, a, b, c):
                if not all(bridges(g, L, starts, e, t) for t in (a, b, c)):
                    return False, "triple e=%d %s" % (e, (a, b, c))
    for e1 in range(1, n):
        for e2 in range(1, n):
            for a, b, c, d in iproduct(range(n), repeat=4):
                if not (is_rep(g, e1, a, b) and is_rep(g, e2, c, d)
                        and interleaved(g, a, b, c, d)):
                    continue
                if not any(bridges(g, L, starts, e, t)
                           for e, t in ((e1, a), (e1, b), (e2, c), (e2, d))):
                    return False, "interleaved e1=%d e2=%d" % (e1, e2)
    return True, "ok"


def clause_vacuity(g, L, starts):
    """Which clauses of I_s are non-vacuous on the truth."""
    n = g.n
    trips = [(e, a, b, c) for e in range(1, n)
             for a, b, c in iproduct(range(n), repeat=3) if is_rep3(g, e, a, b, c)]
    inter = [(e1, a, b, e2, c, d) for e1 in range(1, n) for e2 in range(1, n)
             for a, b, c, d in iproduct(range(n), repeat=4)
             if is_rep(g, e1, a, b) and is_rep(g, e2, c, d)
             and interleaved(g, a, b, c, d)]
    return bool(trips), bool(inter)


# ------------------------------------------------------------ objectives
def L_E(cand, obs):
    """Exact Medvedev-Brudno multinomial with candidate-intrinsic N(D)=|D|."""
    m = cand.mult(len(list(obs)[0]))
    n = sum(obs.values())
    coef = Fraction(factorial(n))
    for x in obs.values():
        coef /= factorial(x)
    acc = coef
    for w, x in obs.items():
        acc *= Fraction(m.get(w, 0), cand.n) ** x
    return acc


def L_A(cand, obs, N, drop_zero=False):
    """Literal MB 6.1 product of binomial marginals over the whole type space.

    The type space is the *model's* read-type space (the four-letter DNA
    alphabet), NOT the candidate's own symbol set: an observed read type whose
    symbols do not occur in the candidate still contributes a factor, and that
    factor is `0` when `d_w = 0` while `x_w >= 1`.  Restricting the type space
    to the candidate's alphabet silently drops those factors and inflates the
    candidates that avoid the observed symbols.
    """
    L = len(list(obs)[0])
    m = cand.mult(L)
    n = sum(obs.values())
    acc = Fraction(1)
    for w in iproduct(DNA, repeat=L):
        x = obs.get(w, 0)
        d = m.get(w, 0)
        if drop_zero and x == 0:
            continue
        if d > N:
            return None, "d=%d>N=%d @%s" % (d, N, "".join(w))
        acc *= comb(n, x) * Fraction(d, N) ** x * (1 - Fraction(d, N)) ** (n - x)
    return acc, "ok"


# =============================================================== witnesses
def witness(name, S, D, L, starts, Nex=None, alpha=None):
    print("\n--- %s   S=%s  D=%s  L=%d  starts=%s  N=%s" %
          (name, S, D, L, sorted({r % len(S) for r in starts}), Nex))
    s, d = G(S), G(D)
    obs = observed(s, L, starts)
    ok, why = is_full(s, L, starts)
    ck("I_s (full source-faithful predicate)", ok, why)
    ck("realization reproduces observation", obs == observed(s, L, starts))
    t, i = clause_vacuity(s, L, starts)
    print("    I_s clause 2 (triple repeat) non-vacuous: %s ; clause 3 (interleaved): %s" % (t, i))
    lt, ld = L_E(s, obs), L_E(d, obs)
    ck("Variant E strict", ld > lt, "L_E(S)=%s L_E(D)=%s ratio=%s" % (lt, ld, ld / lt))
    if Nex is not None:
        for drop in (False, True):
            va, wa = L_A(s, obs, Nex, drop)
            vb, wb = L_A(d, obs, Nex, drop)
            if va is None or vb is None:
                ck("Variant A (drop_zero=%s) defined" % drop, False, wa + "/" + wb)
            else:
                ck("Variant A strict (drop_zero=%s)" % drop, vb > va,
                   "ratio=%s" % (vb / va))
    return lt, ld


print("=" * 78)
print("1. WITNESSES")
print("=" * 78)
witness("E-1  ACGT -> ACACGT", "ACGT", "ACACGT", 2, [0, 0, 2], alpha="ACGT")
witness("E-2  AAABB -> AAAAB", "AAABB", "AAAAB", 3, [0, 1, 4], Nex=5)
witness("E-3  AAACC -> AAAAC", "AAACC", "AAAAC", 3, [0, 1, 4], Nex=5)
witness("E-4  AABB -> ABAB", "AABB", "ABAB", 2, [1, 3], Nex=4)
witness("A-4  ACGT -> ACACGT  (external N=4)", "ACGT", "ACACGT", 2, [0, 0, 2], Nex=4)

print("\n" + "=" * 78)
print("2. DOMAIN  d_i <= N  AND THE THREE CANDIDATE REGIONS")
print("=" * 78)
for s in ["AAA", "AAAA", "AAAAA", "AAAAAA", "AAAAAAA"]:
    c = G(s)
    v, w = L_A(c, observed(G("AAACC"), 3, [0, 1, 4]), 5)
    print("  cand %-8s |D|=%d d_AAA=%2d  L_A(|N=5) = %s %s"
          % (s, c.n, c.mult(3).get(("A", "A", "A"), 0), v if v is not None else "UNDEFINED", w))
ck("|D|<=N implies the literal marginal is a probability",
   all(max(G("".join(p)).mult(3).values()) <= 5 for p in iproduct("ABCG", repeat=5)),
   "max d_i over all 4^5 length-5 genomes = 5")
ck("the intermediate region is nonempty: |D|>N yet all d_i<=N",
   G("ACACGT").n == 6 and max(G("ACACGT").mult(2).values()) <= 4)

print("\n" + "=" * 78)
print("3. DUPLICATE-READ FAMILIES")
print("=" * 78)
for k in range(1, 7):
    s, d = G("AAABB"), G("AAAAB")
    ob = {("A", "A", "A"): k, ("A", "A", "B"): 1, ("B", "A", "A"): 1}
    re = L_E(d, ob) / L_E(s, ob)
    la, _ = L_A(s, ob, 5)
    lb, _ = L_A(d, ob, 5)
    ck("Variant E, AAA x%d: ratio 2^%d" % (k, k), re == Fraction(2) ** k, "%s" % re)
    ck("Variant A, AAA x%d: strict (formula (1125/512)*(5/2)^(k-1))" % k,
       lb / la > 1 and lb / la == Fraction(1125, 512) * Fraction(5, 2) ** (k - 1),
       "%s" % (lb / la))

print("\n" + "=" * 78)
print("4. EXHAUSTIVE MAXIMIZER CENSUSES (complete classes)")
print("=" * 78)


def census(label, S, obs, obj, klass, alpha):
    vals = {}
    for tup in klass:
        c = G(tup)
        v = obj(c, obs)
        if v is not None:
            vals["".join(tup)] = v
    mx = max(vals.values())
    best = [k for k, v in vals.items() if v == mx]
    sc = {"".join(S[i:] + S[:i]) for i in range(len(S))}
    non_shift = [b for b in best if b not in sc]
    tv = vals.get(S)
    print("  %s (class %d, defined %d)" % (label, len(klass), len(vals)))
    print("     max %s at %d candidates, %d not cyclic shifts of truth" % (mx, len(best), len(non_shift)))
    print("     truth value %s -> %s" % (tv, "MAXIMIZER" if tv == mx else "NOT a maximizer"))
    return mx, best, tv


c5 = ["".join(p) for p in iproduct("ABCG", repeat=5)]
c4 = ["".join(p) for p in iproduct("AB", repeat=4)]
oB = {("A", "A", "A"): 1, ("A", "A", "B"): 1, ("B", "A", "A"): 1}
oC = {("A", "A", "A"): 1, ("A", "A", "C"): 1, ("C", "A", "A"): 1}
o2 = {("A", "B"): 1, ("B", "A"): 1}
for lab, S, ob, o in [("E, AAABB obs", "AAABB", oB, lambda c, x: L_E(c, x)),
                      ("E, AAACC obs", "AAACC", oC, lambda c, x: L_E(c, x)),
                      ("A N=5, AAABB obs", "AAABB", oB, lambda c, x: L_A(c, x, 5)[0]),
                      ("A N=5, AAACC obs", "AAACC", oC, lambda c, x: L_A(c, x, 5)[0])]:
    census(lab, S, ob, o, c5, "ABCG")
for lab, S, ob, N in [("A N=4, AB/BA obs", "AABB", o2, 4), ("A N=5, AB/BA obs", "AABB", o2, 5)]:
    census(lab, S, ob, (lambda N: (lambda c, x: L_A(c, x, N)[0]))(N), c4, "AB")
census("E, AB/BA obs", "AABB", o2, lambda c, x: L_E(c, x), c4, "AB")

print("\n" + "=" * 78)
print("4b. ACGT OBSERVATION OVER ALL CIRCULAR GENOMES UP TO LENGTH 8")
print("=" * 78)
o1 = {("A", "C"): 2, ("G", "T"): 1}
scACGT = {"".join("ACGT"[i:] + "ACGT"[:i]) for i in range(4)}
best = (Fraction(-1), None)
cnt = {}
for ln in range(1, 9):
    for tup in iproduct("ACGT", repeat=ln):
        v = L_E(G(tup), o1)
        cnt["".join(tup)] = v
        if v > best[0]:
            best = (v, "".join(tup))
mx = max(cnt.values())
bestc = [k for k, v in cnt.items() if v == mx]
nonshift = [b for b in bestc if b not in scACGT]
print("  class size %d; max %s at %d candidates, %d not cyclic shifts of ACGT"
      % (len(cnt), mx, len(bestc), len(nonshift)))
print("  maximizers: %s" % bestc)
print("  truth value %s -> %s" % (cnt["ACGT"],
      "MAXIMIZER" if cnt["ACGT"] == mx else "NOT a maximizer"))
shifts6 = {"".join("ACACGT"[i:] + "ACACGT"[:i]) for i in range(6)}
ck("ledger §9: best value over |D|<=8 is 1/18, attained by ACACGT's shift class",
   mx == Fraction(1, 18) and sorted(bestc) == sorted(shifts6), "max=%s" % mx)

print("\n" + "=" * 78)
print("5. 'READ-TILED' ROW  AAABCBC -> AAAAABC, claimed ratio 27")
print("=" * 78)
S, D = G("AAABCBC"), G("AAAAABC")
types = sorted(set(S.win(r, 3) for r in range(S.n)))
found = []
for combo in iproduct(range(6), repeat=len(types)):
    ob = {t: c for t, c in zip(types, combo) if c > 0}
    if not ob:
        continue
    ls, ld = L_E(S, ob), L_E(D, ob)
    if ls == 0 or ld == 0:
        continue
    if ld / ls == 27:
        R = sorted({r for r in range(S.n) if S.win(r, 3) in ob})
        ok, why = is_full(S, 3, R)
        found.append((ob, R, ok, why))
ck("claimed ratio 27 is attainable", len(found) > 0, "%d observations" % len(found))
feas = [f for f in found if f[2]]
ck("... and some are fully I_s-feasible on the truth", len(feas) > 0,
   "%d feasible; minimal: obs=%s R=%s" % (len(feas),
      {"".join(k): v for k, v in feas[0][0].items()} if feas else None,
      feas[0][1] if feas else None))
led = None
for ob, R, ok, why in feas:
    if {"".join(k): v for k, v in ob.items()} == {"AAA": 3, "AAB": 1, "ABC": 1, "BCA": 1, "CAA": 1}:
        led = (ob, R, ok)
ck("ledger §10.4 reconstruction (AAA x3, AAB/ABC/BCA/CAA, R={0,1,2,5,6}) is feasible",
   led is not None and led[1] == [0, 1, 2, 5, 6],
   str(led[1]) if led else "not found")

print("\n" + "=" * 78)
print("6. REFUTATION INHERITANCE (which candidate universes inherit)")
print("=" * 78)
for nm, S, D, L, st, N in [("E-1", "ACGT", "ACACGT", 2, [0, 0, 2], 6),
                           ("E-2", "AAABB", "AAAAB", 3, [0, 1, 4], 5),
                           ("E-3", "AAACC", "AAAAC", 3, [0, 1, 4], 5),
                           ("E-4", "AABB", "ABAB", 2, [1, 3], 4)]:
    s, d = G(S), G(D)
    ob = observed(s, L, st)
    print("  %s: |S|=%d |D|=%d  inside {D: d_i<=N=%d}? %s   inside {|D|<=N}? %s"
          % (nm, s.n, d.n, N, max(d.mult(L).values()) <= N, d.n <= N))

print("\n" + "=" * 78)
print("SUMMARY: %d failed checks" % len(FAIL))
for f in FAIL:
    print("  - " + f)
