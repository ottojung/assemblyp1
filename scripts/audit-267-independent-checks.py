#!/usr/bin/env python3
"""
Independent rational checks for issue #267 audit.

Verifies, without Lean, every arithmetic claim of the finite exact-ML and
approximate-binomial witnesses, and checks I_s membership for each competitor.

Labels: standard statistics, mathematical proof, kernel-checked, source fact, open.
"""

from fractions import Fraction
from itertools import product
from math import comb

PASS = 0
FAIL = 0

def check(name, actual, expected):
    global PASS, FAIL
    if actual == expected:
        PASS += 1
        print(f"  PASS  {name}: {actual}")
    else:
        FAIL += 1
        print(f"  FAIL  {name}: got {actual}, expected {expected}")

def circular_windows(genome, L):
    """Return dict mapping read-type -> count of circular starts producing it."""
    G = len(genome)
    counts = {}
    for start in range(G):
        w = tuple(genome[(start + d) % G] for d in range(L))
        counts[w] = counts.get(w, 0) + 1
    return counts

def covers(genome, L, read_starts):
    """Check that reads at read_starts cover all positions."""
    G = len(genome)
    covered = set()
    for r in read_starts:
        for d in range(L):
            covered.add((r + d) % G)
    return len(covered) == G

# ============================================================
# Witness 1: FixedLengthExactCounterexample (AAABB vs AAAAB)
# ============================================================
print("=== Witness 1: FixedLengthExact (AAABB -> AAAAB) ===")

truth1 = "AAABB"
comp1 = "AAAAB"
L1 = 3
starts1 = [0, 1, 4]

tw1 = circular_windows(truth1, L1)
cw1 = circular_windows(comp1, L1)
print(f"  Truth windows: {tw1}")
print(f"  Competitor windows: {cw1}")

check("truth covers", covers(truth1, L1, starts1), True)
check("comp covers", covers(comp1, L1, starts1), True)

# Observed reads
obs1 = {}
for s in starts1:
    w = tuple(truth1[(s + d) % len(truth1)] for d in range(L1))
    obs1[w] = obs1.get(w, 0) + 1
print(f"  Observed: {obs1}")

# Exact multinomial: n! / prod(x_i!) * prod((d_i/N)^x_i)
# n=3, all x_i=1, multinomial coeff = 3! = 6
n1 = 3
exact_coeff1 = 6  # 3!
N1 = 5

def exact_lik(windows, obs, N, coeff):
    lik = Fraction(coeff, 1)
    for w, x in obs.items():
        d = windows.get(w, 0)
        lik *= Fraction(d, N) ** x
    return lik

lik_t1 = exact_lik(tw1, obs1, N1, exact_coeff1)
lik_c1 = exact_lik(cw1, obs1, N1, exact_coeff1)
print(f"  L(truth) = {lik_t1} = {float(lik_t1)}")
print(f"  L(comp)  = {lik_c1} = {float(lik_c1)}")
check("W1 ratio", lik_c1 / lik_t1, Fraction(2))

# ============================================================
# Witness 2: FixedLengthBinomialCounterexample (AAACC vs AAAAC)
# ============================================================
print("\n=== Witness 2: FixedLengthBinomial (AAACC -> AAAAC) ===")

truth2 = "AAACC"
comp2 = "AAAAC"
L2 = 3
starts2 = [0, 1, 4]

tw2 = circular_windows(truth2, L2)
cw2 = circular_windows(comp2, L2)
print(f"  Truth windows: {tw2}")
print(f"  Competitor windows: {cw2}")

check("truth covers", covers(truth2, L2, starts2), True)
check("comp covers", covers(comp2, L2, starts2), True)

obs2 = {}
for s in starts2:
    w = tuple(truth2[(s + d) % len(truth2)] for d in range(L2))
    obs2[w] = obs2.get(w, 0) + 1
print(f"  Observed: {obs2}")

n2 = 3
N2 = 5
from math import comb

def binom_lik(windows, obs, N, n):
    lik = Fraction(1, 1)
    all_types = set(windows.keys()) | set(obs.keys())
    for w in all_types:
        x = obs.get(w, 0)
        d = windows.get(w, 0)
        coeff = comb(n, x)
        lik *= Fraction(coeff, 1) * Fraction(d, N) ** x * (1 - Fraction(d, N)) ** (n - x)
    return lik

lik_t2 = binom_lik(tw2, obs2, N2, n2)
lik_c2 = binom_lik(cw2, obs2, N2, n2)
print(f"  L_A(truth) = {lik_t2} = {float(lik_t2)}")
print(f"  L_A(comp)  = {lik_c2} = {float(lik_c2)}")
check("W2 ratio", lik_c2 / lik_t2, Fraction(1125, 512))

# ============================================================
# Witness 3: SameLengthExactMLCounterexample (AABB vs ABAB)
# ============================================================
print("\n=== Witness 3: SameLengthExactML (AABB -> ABAB) ===")

truth3 = "AABB"
comp3 = "ABAB"
L3 = 2
starts3 = [1, 3]

tw3 = circular_windows(truth3, L3)
cw3 = circular_windows(comp3, L3)
print(f"  Truth windows: {tw3}")
print(f"  Competitor windows: {cw3}")

check("truth covers", covers(truth3, L3, starts3), True)
check("comp covers", covers(comp3, L3, starts3), True)

obs3 = {}
for s in starts3:
    w = tuple(truth3[(s + d) % len(truth3)] for d in range(L3))
    obs3[w] = obs3.get(w, 0) + 1
print(f"  Observed: {obs3}")

n3 = 2
N3 = 4

def exact_lik_per_read(windows, obs_list, N):
    """Variant E: product over reads of (d_g(w) / N), no multinomial coeff."""
    lik = Fraction(1, 1)
    for w in obs_list:
        d = windows.get(w, 0)
        lik *= Fraction(d, N)
    return lik

obs_list3 = []
for s in starts3:
    w = tuple(truth3[(s + d) % len(truth3)] for d in range(L3))
    obs_list3.append(w)

lik_t3 = exact_lik_per_read(tw3, obs_list3, N3)
lik_c3 = exact_lik_per_read(cw3, obs_list3, N3)
print(f"  L(truth) = {lik_t3} = {float(lik_t3)}")
print(f"  L(comp)  = {lik_c3} = {float(lik_c3)}")
check("W3 ratio", lik_c3 / lik_t3, Fraction(4))

# ============================================================
# Witness 4: ExactVariantECounterexample (ACGT vs ACACGT)
# ============================================================
print("\n=== Witness 4: ExactVariantE (ACGT -> ACACGT) ===")

truth4 = "ACGT"
comp4 = "ACACGT"
L4 = 2
starts4 = [0, 0, 2]

tw4 = circular_windows(truth4, L4)
cw4 = circular_windows(comp4, L4)
print(f"  Truth windows: {tw4}")
print(f"  Competitor windows: {cw4}")

check("truth covers", covers(truth4, L4, set(starts4)), True)
# The competitor has a different length (6 vs 4), so the truth's realized
# starts {0,0,2} do not cover the competitor's circle.  This is the coverage
# clause failing, which is exactly why the W4 competitor is not I_s-feasible.
check("comp covers (truth starts)", covers(comp4, L4, set(starts4)), False)

obs4 = {}
for s in starts4:
    w = tuple(truth4[(s + d) % len(truth4)] for d in range(L4))
    obs4[w] = obs4.get(w, 0) + 1
print(f"  Observed: {obs4}")

# Variant E: uses dinucleotideCount (count of x->y pairs), not all windows
# Truth ACGT: A->C at pos 0, G->T at pos 2 => d_AC=1, d_GT=1
# Competitor ACACGT: A->C at pos 0,2; G->T at pos 4 => d_AC=2, d_GT=1
def dinuc_count(genome, x, y):
    G = len(genome)
    return sum(1 for i in range(G) if genome[i] == x and genome[(i+1) % G] == y)

d_AC_t = dinuc_count(truth4, 'A', 'C')
d_GT_t = dinuc_count(truth4, 'G', 'T')
d_AC_c = dinuc_count(comp4, 'A', 'C')
d_GT_c = dinuc_count(comp4, 'G', 'T')
print(f"  dinucleotide counts: truth AC={d_AC_t}, GT={d_GT_t}; comp AC={d_AC_c}, GT={d_GT_c}")

# sampleLikelihood = 3 * (d_AC/len)^2 * (d_GT/len)^1
coeff4 = 3
lik_t4 = Fraction(coeff4, 1) * Fraction(d_AC_t, len(truth4))**2 * Fraction(d_GT_t, len(truth4))
lik_c4 = Fraction(coeff4, 1) * Fraction(d_AC_c, len(comp4))**2 * Fraction(d_GT_c, len(comp4))

print(f"  L(truth) = {lik_t4} = {float(lik_t4)}")
print(f"  L(comp)  = {lik_c4} = {float(lik_c4)}")
check("W4 truth lik", lik_t4, Fraction(3, 64))
check("W4 comp lik", lik_c4, Fraction(1, 18))
check("W4 ratio", lik_c4 / lik_t4, Fraction(32, 27))

# ============================================================
# Witness 5: SameLengthSection62Counterexample (AAATAT vs AAAAAT)
# §6.2 molecule model: reads are unoriented molecule classes (RC-collapsed)
# ============================================================
print("\n=== Witness 5: SameLengthSection62 (AAATAT -> AAAAAT, molecule model) ===")

truth5 = "AAATAT"
comp5 = "AAAAAT"
L5 = 3
starts5 = [0, 0, 1, 3, 5]

comp_map5 = {'A': 'T', 'T': 'A', 'C': 'G', 'G': 'C'}

def rc5(w):
    return ''.join(comp_map5[c] for c in reversed(w))

def mol_class5(w):
    r = rc5(w)
    return min(w, r)

def mol_windows(genome, L):
    G = len(genome)
    counts = {}
    for start in range(G):
        w = ''.join(genome[(start + d) % G] for d in range(L))
        mc = mol_class5(w)
        counts[mc] = counts.get(mc, 0) + 1
    return counts

tw5 = mol_windows(truth5, L5)
cw5 = mol_windows(comp5, L5)
print(f"  Truth molecule windows: {tw5}")
print(f"  Competitor molecule windows: {cw5}")

check("truth covers", covers(truth5, L5, set(starts5)), True)
check("comp covers", covers(comp5, L5, set(starts5)), True)

obs5 = {}
for s in starts5:
    w = ''.join(truth5[(s + d) % len(truth5)] for d in range(L5))
    mc = mol_class5(w)
    obs5[mc] = obs5.get(mc, 0) + 1
print(f"  Observed (molecule): {obs5}")

n5 = 5
N5 = 6

# Exact multinomial (candidate-intrinsic length, molecule model)
exact_coeff5 = 120  # 5!
lik_t5 = Fraction(exact_coeff5, 1)
lik_c5 = Fraction(exact_coeff5, 1)
for mc, x in obs5.items():
    d_t = tw5.get(mc, 0)
    d_c = cw5.get(mc, 0)
    lik_t5 *= Fraction(d_t, len(truth5)) ** x
    lik_c5 *= Fraction(d_c, len(comp5)) ** x

print(f"  L_exact(truth) = {lik_t5} = {float(lik_t5)}")
print(f"  L_exact(comp)  = {lik_c5} = {float(lik_c5)}")
check("W5 exact ratio", lik_c5 / lik_t5, Fraction(3))

# Binomial approximation (molecule model)
lik_t5b = Fraction(1, 1)
lik_c5b = Fraction(1, 1)
all_types5 = set(tw5.keys()) | set(cw5.keys()) | set(obs5.keys())
for mc in all_types5:
    x = obs5.get(mc, 0)
    d_t = tw5.get(mc, 0)
    d_c = cw5.get(mc, 0)
    coeff = comb(n5, x)
    lik_t5b *= Fraction(coeff, 1) * Fraction(d_t, N5) ** x * (1 - Fraction(d_t, N5)) ** (n5 - x)
    lik_c5b *= Fraction(coeff, 1) * Fraction(d_c, N5) ** x * (1 - Fraction(d_c, N5)) ** (n5 - x)

print(f"  L_binom(truth) = {lik_t5b} = {float(lik_t5b)}")
print(f"  L_binom(comp)  = {lik_c5b} = {float(lik_c5b)}")
check("W5 binomial ratio", lik_c5b / lik_t5b, Fraction(5))

# ============================================================
# Witness 6: P1 finite case (AABBC -> AABC), variable length
# Both candidates primitive and P1; shorter wrong candidate wins
# ============================================================
print("\n=== Witness 6: P1 finite case (AABBC -> AABC) ===")

truth6 = "AABBC"
comp6 = "AABC"
L6 = 3
starts6 = [0, 3]

tw6 = circular_windows(truth6, L6)
cw6 = circular_windows(comp6, L6)
print(f"  Truth windows: {tw6}")
print(f"  Competitor windows: {cw6}")

check("truth covers", covers(truth6, L6, set(starts6)), True)

obs6 = {}
for s in starts6:
    w = tuple(truth6[(s + d) % len(truth6)] for d in range(L6))
    obs6[w] = obs6.get(w, 0) + 1
print(f"  Observed: {obs6}")

n6 = 2

# Exact multinomial with candidate-intrinsic length
exact_coeff6 = 2  # 2!
lik_t6 = Fraction(exact_coeff6, 1)
lik_c6 = Fraction(exact_coeff6, 1)
for w, x in obs6.items():
    d_t = tw6.get(w, 0)
    d_c = cw6.get(w, 0)
    lik_t6 *= Fraction(d_t, len(truth6)) ** x
    lik_c6 *= Fraction(d_c, len(comp6)) ** x

print(f"  L(truth) = {lik_t6} = {float(lik_t6)}")
print(f"  L(comp)  = {lik_c6} = {float(lik_c6)}")
check("W6 truth lik", lik_t6, Fraction(2, 25))
check("W6 comp lik", lik_c6, Fraction(1, 8))
check("W6 ratio", lik_c6 / lik_t6, Fraction(25, 16))
check("W6 comp strictly better", lik_c6 > lik_t6, True)

# P1 check: circular (L-1)-mers are pairwise distinct
def p1_check(genome, L):
    G = len(genome)
    kmers = set()
    for start in range(G):
        kmer = tuple(genome[(start + d) % G] for d in range(L - 1))
        if kmer in kmers:
            return False
        kmers.add(kmer)
    return True

check("W6 truth P1", p1_check(truth6, L6), True)
check("W6 comp P1", p1_check(comp6, L6), True)

# ============================================================
# 2x2 Bayes example (kernel-checked in AssemblyP1.MapDecisionExamples)
# ============================================================
print("\n=== 2x2 Bayes example ===")

pi = [Fraction(1, 2), Fraction(1, 2)]
P = [[Fraction(1, 4), Fraction(3, 4)],
     [Fraction(3, 4), Fraction(1, 4)]]

joint = [[pi[g] * P[g][r] for r in range(2)] for g in range(2)]
print(f"  Joint law:")
for g in range(2):
    print(f"    g{g}: {joint[g]}")

# E = {(0,0), (1,1)}
P_E = joint[0][0] + joint[1][1]
print(f"  P(E) = {P_E}")

# deltaE: a->g1, b->g2 (infallible on E)
acc_deltaE = joint[0][0] + joint[1][1]
print(f"  accuracy(deltaE) = {acc_deltaE}")

# deltaMap: a->g2, b->g1 (unconstrained MAP)
acc_deltaMap = joint[1][0] + joint[0][1]
print(f"  accuracy(deltaMap) = {acc_deltaMap}")

check("P(E)", P_E, Fraction(1, 4))
check("acc(deltaE)", acc_deltaE, Fraction(1, 4))
check("acc(deltaMap)", acc_deltaMap, Fraction(3, 4))
check("MAP beats infallible", acc_deltaE < acc_deltaMap, True)

# ============================================================
# Nonuniform prior example
# ============================================================
print("\n=== Nonuniform prior example ===")

pi_nu = [Fraction(9, 10), Fraction(1, 10)]
P_ml = [[Fraction(1, 2), Fraction(0)], [Fraction(1), Fraction(0)]]

# At observation a (index 0):
joint_g1 = pi_nu[0] * P_ml[0][0]
joint_g2 = pi_nu[1] * P_ml[1][0]
print(f"  joint(g1, a) = {joint_g1}")
print(f"  joint(g2, a) = {joint_g2}")
check("MAP selects g1", joint_g1 > joint_g2, True)
check("ML selects g2 (lik)", P_ml[1][0] > P_ml[0][0], True)

# ============================================================
# Delegated two-hypothesis toy:
# p_g(x) = 1/10, p_h(x) = 1/5, uniform prior, E(g,x) = true, E(h,x) = false.
# Ordinary ML picks h; conditioning on E leaves the posterior supported on g.
# ============================================================
print("\n=== Delegated toy: ML picks nonfeasible h, E-posterior certain on g ===")

toy_P = {  # rows g, h; columns x, y
    "g": [Fraction(1, 10), Fraction(9, 10)],
    "h": [Fraction(1, 5), Fraction(4, 5)],
}
toy_prior = Fraction(1, 2)
toy_joint = {k: [toy_prior * v for v in row] for k, row in toy_P.items()}
toy_feasible = {"g": [True, False], "h": [False, False]}  # E only at (g, x)
toy_cond = {k: [toy_joint[k][i] if toy_feasible[k][i] else Fraction(0)
                for i in range(2)] for k in ("g", "h")}

print(f"  ML at x: p_g(x)={toy_P['g'][0]}, p_h(x)={toy_P['h'][0]}")
check("toy ML picks h", toy_P["h"][0] > toy_P["g"][0], True)
check("toy unconstrained MAP picks h", toy_joint["h"][0] > toy_joint["g"][0], True)
print(f"  Conditional joint at x: g={toy_cond['g'][0]}, h={toy_cond['h'][0]}")
check("toy conditional support only on g", toy_cond["h"][0] == 0, True)
denom = toy_cond["g"][0] + toy_cond["h"][0]
check("toy conditional posterior(g|x,E)", toy_cond["g"][0] / denom, Fraction(1))

# ============================================================
# I_s membership check for competitors
# ============================================================
print("\n=== I_s membership for competitors ===")

def is_repeat(genome, e, a, b):
    """Check if a,b form a maximal length-e repeat."""
    G = len(genome)
    if not (1 <= e < G):
        return False
    if a == b:
        return False
    # Equal windows
    for d in range(e):
        if genome[(a + d) % G] != genome[(b + d) % G]:
            return False
    # Preceding symbols differ
    prec_a = genome[(a - 1) % G]
    prec_b = genome[(b - 1) % G]
    if prec_a == prec_b:
        return False
    # Following symbols differ
    foll_a = genome[(a + e) % G]
    foll_b = genome[(b + e) % G]
    if foll_a == foll_b:
        return False
    return True

def is_triple_repeat(genome, e, a, b, c):
    """Check if a,b,c form a maximal triple repeat."""
    G = len(genome)
    if not (1 <= e < G):
        return False
    if a == b or a == c or b == c:
        return False
    for d in range(e):
        wa = genome[(a + d) % G]
        wb = genome[(b + d) % G]
        wc = genome[(c + d) % G]
        if wa != wb or wb != wc:
            return False
    precs = {genome[(a - 1) % G], genome[(b - 1) % G], genome[(c - 1) % G]}
    if len(precs) == 1:
        return False
    folls = {genome[(a + e) % G], genome[(b + e) % G], genome[(c + e) % G]}
    if len(folls) == 1:
        return False
    return True

def bridges_copy(genome, L, read_starts, e, t):
    """Source-faithful `BridgesCopy`: some realized read interval strictly
    contains the copy of length `e` starting at `t` (a base before and a base
    after the copy lie in the same read), i.e.

        exists r in read_starts, d < L with d + e + 1 < L and (r+d+1) % G == t.

    This is the strict-extension condition of `SourceFaithfulIs.BridgesCopy`;
    the weaker endpoint-only condition (read covers (t-1)%G and (t+e)%G but may
    travel the complementary arc) is deliberately *not* used here.
    """
    G = len(genome)
    for r in read_starts:
        for d in range(L):
            if d + e + 1 < L and (r + d + 1) % G == t:
                return True
    return False

def in_open_arc(genome, a, b, p):
    """`p` lies strictly on the open clockwise arc from `a` to `b`."""
    G = len(genome)
    return 0 < (p + G - a) % G < (b + G - a) % G

def interleaved(genome, a, b, c, d):
    """Cyclic alternation of the two repeats' selected starts
    (`SourceFaithfulIs.Interleaved`)."""
    if len({a, b, c, d}) != 4:
        return False
    return in_open_arc(genome, a, b, c) != in_open_arc(genome, a, b, d)

def info_feasible(genome, L, read_starts):
    """Check full `I_s` membership for `genome` against the read starts.

    Implements all three clauses of `SourceFaithfulIs.InformationFeasible`:
    coverage, all-bridged triple repeats, and bridged interleaved repeat pairs.
    """
    G = len(genome)
    rs = sorted(set(read_starts))

    # Clause 1: coverage
    if not covers(genome, L, rs):
        return False, "coverage fails"

    # Clause 2: every triple repeat is all-bridged
    for e in range(1, G):
        for a in range(G):
            for b in range(G):
                for c in range(G):
                    if is_triple_repeat(genome, e, a, b, c):
                        if not (bridges_copy(genome, L, rs, e, a) and
                                bridges_copy(genome, L, rs, e, b) and
                                bridges_copy(genome, L, rs, e, c)):
                            return False, f"triple repeat at e={e}, starts={a},{b},{c} not all-bridged"

    # Clause 3: every interleaved pair of maximal repeats is bridged
    for e1 in range(1, G):
        for a in range(G):
            for b in range(G):
                if not is_repeat(genome, e1, a, b):
                    continue
                for e2 in range(1, G):
                    for c in range(G):
                        for d in range(G):
                            if not is_repeat(genome, e2, c, d):
                                continue
                            if not interleaved(genome, a, b, c, d):
                                continue
                            if not (bridges_copy(genome, L, rs, e1, a) or
                                    bridges_copy(genome, L, rs, e1, b) or
                                    bridges_copy(genome, L, rs, e2, c) or
                                    bridges_copy(genome, L, rs, e2, d)):
                                return False, (f"interleaved pair (e1={e1},{a},{b}) "
                                               f"(e2={e2},{c},{d}) not bridged")

    return True, "all clauses hold"

# Check I_s for each competitor
print("\n  Competitor I_s checks:")
for name, genome, L, starts in [
    ("AAAAB (W1 comp)", comp1, L1, starts1),
    ("AAAAC (W2 comp)", comp2, L2, starts2),
    ("ABAB (W3 comp)", comp3, L3, starts3),
    ("ACACGT (W4 comp)", comp4, L4, starts4),
    ("AAAAAT (W5 comp)", comp5, L5, starts5),
]:
    result, reason = info_feasible(genome, L, starts)
    print(f"    {name}: I_s = {result} ({reason})")

# P1 competitor (AABC): check I_s with reads placed on competitor's own circle
# Observed reads {AAB, BCA} placed at starts {0, 2} on AABC (len 4)
print("\n  P1 competitor I_s check (AABC, reads at starts {0,2}):")
result_p1, reason_p1 = info_feasible(comp6, L6, {0, 2})
print(f"    AABC (W6 comp): I_s = {result_p1} ({reason_p1})")

# Also check truth I_s
print("\n  Truth I_s checks:")
for name, genome, L, starts in [
    ("AAABB (W1 truth)", truth1, L1, starts1),
    ("AAACC (W2 truth)", truth2, L2, starts2),
    ("AABB (W3 truth)", truth3, L3, starts3),
    ("ACGT (W4 truth)", truth4, L4, starts4),
    ("AAATAT (W5 truth)", truth5, L5, starts5),
    ("AABBC (W6 truth)", truth6, L6, starts6),
]:
    result, reason = info_feasible(genome, L, starts)
    print(f"    {name}: I_s = {result} ({reason})")

# ============================================================
# Summary
# ============================================================
print(f"\n{'='*60}")
print(f"SUMMARY: {PASS} passed, {FAIL} failed out of {PASS+FAIL} checks")
if FAIL == 0:
    print("All independent rational checks PASSED.")
else:
    print("SOME CHECKS FAILED - investigate!")
