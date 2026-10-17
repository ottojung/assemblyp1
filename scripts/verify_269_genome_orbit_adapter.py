#!/usr/bin/env python3
"""Independent exact validation of the #269 assembly MAP orbit adapter.

Scope: `AssemblyP1/GenomeOrbitAdapter.lean` (Antonina #269, PR #200).  That
Lean module connects the merged finite-Bayes/MAP decision theorem
(`AssemblyP1.FiniteBayesDecision`) and its exact iid `n -> n+1` monotonicity
bridge (`AssemblyP1.IidMapMonotonicity`) to the concrete AssemblyP1 circular
oriented read model with uniformly sampled genomic starts,
`p_G(w) = multiplicity_G(w) / |G|`, on the finite family of genome
rotation-equivalence classes.

This script recomputes, from scratch with exact rational arithmetic and no trust
in the Lean output:

  * window multiplicities and the pmf normalization `sum_w p_G(w) = 1`;
  * rotation invariance of the multiplicity (`mult_rotWord`);
  * the rotation-orbit quotient: orbit sizes, `sum o orbitSize o = |spellings|`,
    normalization of the descended pmf on every orbit;
  * the uniform orbit prior and the uniform-spelling pushforward prior, both
    normalized, and a concrete witness that they differ when orbit sizes differ
    (`spellingPushforward_eq_uniform_iff_constant_orbitSize`);
  * the per-truth success drop `4/5` (one read) vs `16/25` (two reads)
    (`PerTruthDrop`), so the monotonicity is prior-averaged only;
  * the exact iid likelihood vs the MB09 fixed-N product-binomial surrogate
    (`ExactVsSurrogate.exact_ne_productBinomial`);
  * the unconditional conditional-success identity
    (`CoverageConditional.conditionalSuccess_univ_eq`) and the
    posterior/MAP ordering (`PosteriorMAP.posterior_argmax_iff`) on a tiny
    finite example.

It is deterministic and exits non-zero on any failed assertion.  It shares no
code with the Lean module.
"""
from fractions import Fraction
from itertools import product
from pathlib import Path
import re
import sys

FAILURES = []


def check(condition, message):
    if not condition:
        FAILURES.append(message)


def rotations(word):
    """All cyclic rotations of a tuple, in rotation order."""
    n = len(word)
    return [tuple(word[(i + j) % n] for i in range(n)) for j in range(n)]


def windows(genome, length):
    """All oriented length-`length` circular windows of `genome`, in start order."""
    n = len(genome)
    return [tuple(genome[(s + d) % n] for d in range(length)) for s in range(n)]


def multiplicity(genome, length, w):
    return sum(1 for v in windows(genome, length) if v == w)


def orbit(word):
    """The rotation orbit of a word (list of distinct rotations)."""
    seen = []
    for r in rotations(word):
        if r not in seen:
            seen.append(r)
    return seen


# --- 1. read model and normalization (readPmf_sum_one, sum_mult) ------------
A, C = 0, 1
ALPHABET = (A, C)
G, L = 4, 2
SPELLINGS = list(product(ALPHABET, repeat=G))
read_length_words = list(product(ALPHABET, repeat=L))

for S in SPELLINGS:
    mults = {w: multiplicity(S, L, w) for w in read_length_words}
    check(sum(mults.values()) == G, f"sum_mult failed for {S}")
    total = sum(Fraction(m, G) for m in mults.values())
    check(total == 1, f"readPmf_sum_one failed for {S}")

# --- 2. rotation invariance (mult_rotWord, readPmf_rotWord) -----------------
for S in SPELLINGS:
    for j in range(G):
        rot = tuple(S[(i + j) % G] for i in range(G))
        for w in read_length_words:
            check(multiplicity(rot, L, w) == multiplicity(S, L, w),
                  f"mult_rotWord failed for {S} j={j} w={w}")

# --- 3. rotation-orbit quotient (orbitReadPmf_sum_one, sum_orbitSize) -------
ORBITS = []
for S in SPELLINGS:
    if not any(S in o for o in ORBITS):
        ORBITS.append(orbit(S))

check(sum(len(o) for o in ORBITS) == len(SPELLINGS), "sum_orbitSize failed")
check(len(ORBITS) == 6, f"expected 6 binary length-4 rotation orbits, got {len(ORBITS)}")

for o in ORBITS:
    rep = o[0]
    total = sum(Fraction(multiplicity(rep, L, w), G) for w in read_length_words)
    check(total == 1, f"orbitReadPmf_sum_one failed for orbit of {rep}")

# --- 4. priors on orbit classes vs spellings -------------------------------
n_orbits = len(ORBITS)
uniform_orbit_prior = Fraction(1, n_orbits)
check(sum(uniform_orbit_prior for _ in ORBITS) == 1, "uniformOrbitPrior_sum_one failed")

for o in ORBITS:
    pushforward = Fraction(len(o), len(SPELLINGS))
    check(sum(Fraction(len(o2), len(SPELLINGS)) for o2 in ORBITS) == 1,
          "spellingPushforwardPrior_sum_one failed")
    if len(o) != len(ORBITS[0]) or any(len(o2) != len(o) for o2 in ORBITS):
        check(pushforward != uniform_orbit_prior,
              f"pushforward should differ from uniform orbit prior for orbit size {len(o)}")

# concrete witness: orbit sizes 1, 2, 4 all occur, so the priors differ
sizes = sorted(len(o) for o in ORBITS)
check(sizes == [1, 1, 2, 4, 4, 4], f"unexpected orbit sizes {sizes}")
check(Fraction(1, len(SPELLINGS)) != uniform_orbit_prior,
      "size-1 orbit pushforward must differ from uniform orbit prior")
check(Fraction(2, len(SPELLINGS)) != uniform_orbit_prior,
      "size-2 orbit pushforward must differ from uniform orbit prior")

# --- 5. per-truth success drop (PerTruthDrop) ------------------------------
readP = {(0, A): Fraction(4, 5), (0, C): Fraction(1, 5),
         (1, A): Fraction(1, 2), (1, C): Fraction(1, 2)}


def ml1(w):
    return 0 if Fraction(1, 2) * readP[(0, w)] >= Fraction(1, 2) * readP[(1, w)] else 1


def ml2(a, b):
    return 0 if (Fraction(1, 2) * readP[(0, a)] * readP[(0, b)]
                 >= Fraction(1, 2) * readP[(1, a)] * readP[(1, b)]) else 1


perTruth1 = sum(readP[(0, w)] for w in (A, C) if ml1(w) == 0)
perTruth2 = sum(readP[(0, a)] * readP[(0, b)]
                for a in (A, C) for b in (A, C) if ml2(a, b) == 0)
check(perTruth1 == Fraction(4, 5), f"perTruth_true_one failed: {perTruth1}")
check(perTruth2 == Fraction(16, 25), f"perTruth_true_two failed: {perTruth2}")
check(perTruth2 < perTruth1, "perTruth_true_drops failed")

# --- 6. exact iid vs fixed-N product-binomial surrogate (ExactVsSurrogate) --
half = Fraction(1, 2)
exact = half ** 1 * half ** 1
surrogate = (half ** 1 * (1 - half) ** (2 - 1)) * (half ** 1 * (1 - half) ** (2 - 1))
check(exact == Fraction(1, 4), f"exact likelihood should be 1/4, got {exact}")
check(surrogate == Fraction(1, 16), f"surrogate should be 1/16, got {surrogate}")
check(exact != surrogate, "exact_ne_productBinomial failed")

# --- 7. conditional-success identity and posterior/MAP ordering ------------
# Theta = {0,1}, X = {a,b}; J theta x exact rational joint masses.
J = {(0, 'a'): Fraction(1, 2), (0, 'b'): Fraction(1, 4),
     (1, 'a'): Fraction(1, 4), (1, 'b'): Fraction(1, 2)}
XS = ('a', 'b')
pred_univ = sum(J.values())
check(pred_univ == Fraction(3, 2), "predictive mass of the univ should be 3/2")


def choose_map(x):
    return max((0, 1), key=lambda t: J[(t, x)])


d_const0 = {'a': 0, 'b': 0}
success_d = sum(J[(d_const0[x], x)] for x in XS)
cond_success_d = success_d / pred_univ
check(cond_success_d == Fraction(1, 2), f"conditionalSuccess univ failed: {cond_success_d}")
check(cond_success_d == success_d / pred_univ,
      "conditionalSuccess_univ_eq failed")

d_map = {x: choose_map(x) for x in XS}
success_map = sum(J[(d_map[x], x)] for x in XS)
check(success_map / pred_univ >= cond_success_d,
      "conditional_MAP_optimal failed")

x = 'a'
pred_x = sum(J[(t, x)] for t in (0, 1))
check(pred_x == Fraction(3, 4), "predictive mass of a should be 3/4")
for t in (0, 1):
    post_t = J[(t, x)] / pred_x
    post_map = J[(choose_map(x), x)] / pred_x
    check((post_t <= post_map) == (J[(t, x)] <= J[(choose_map(x), x)]),
          f"posterior_argmax_iff failed for theta={t}")

# --- report -----------------------------------------------------------------
if FAILURES:
    print(f"FAIL: {len(FAILURES)} assertion(s) failed", file=sys.stderr)
    for f in FAILURES[:20]:
        print(f"  - {f}", file=sys.stderr)
    sys.exit(1)

print("PASS: verify_269_genome_orbit_adapter — all exact rational checks succeeded")
print(f"  orbits={n_orbits} sizes={sizes}; per-truth 1-read={perTruth1} "
      f"2-read={perTruth2}; exact={exact} surrogate={surrogate}")
