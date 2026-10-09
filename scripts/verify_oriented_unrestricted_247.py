#!/usr/bin/env python3
"""Independent exact-rational verification of the board-#247 oriented
unrestricted finite ML counterexample (lane 247b).

Truth     S = AAABBABB  (circular, G = 8, alphabet {A, B})
Competitor D = AAAABABB  (circular, same length 8)
Read length L = 3, oriented.

Sample: each of the 8 starts of S once, plus FOUR extra copies of start 0
(AAA), total n = 12.  Observed oriented type counts
    x = {AAA:5, AAB:1, ABB:2, BBA:2, BAB:1, BAA:1}.
Truth spectrum      d_S = {AAA:1, AAB:1, ABB:2, BBA:2, BAB:1, BAA:1}.
Competitor spectrum d_D = {AAA:2, AAB:1, ABA:1, ABB:1, BBA:1, BAB:1, BAA:1}.

Checked here, with exact `fractions.Fraction` arithmetic:

  E1  exact intrinsic multinomial ratio  Lik(D)/Lik(S) = 2
  E2  fixed-N = 8 binomial ratio (zero-count factors over all 8 oriented
      types, including the unobserved ABA of D) =
      1341068619663964900807/448762029294263205888 = 2.9883736415332867...
  E3  the same 4-letter DNA binomial over {A,C,G,T} (64 oriented types,
      zero-count factors) has the SAME ratio, because every type containing
      G or T has x = d_S = d_D = 0 and hence contributes factor 1
  E4  S is information-feasible (old base-coverage `Covers`, all triple
      repeats all-bridged, all interleaved pairs bridged) under the
      repository SourceFaithfulIs definitions
  E5  historical read-string coverage holds for S (every length-(L-1)=2 start
      interval contains a match of an observed word)
  E6  D contains the unobserved window ABA, so D is NOT a §6.2
      support-equality / spelled / flow candidate, while it DOES satisfy the
      weak per-vertex lower bound (every observed type occurs in D)

This script is independent of the Lean formalisation; the two must agree.
"""

from fractions import Fraction
from math import comb, factorial

S = "AAABBABB"
D = "AAAABABB"
G = 8
L = 3
N = 8          # external known genome size for the binomial
K_EXTRA = 4    # extra copies of start 0

# ---------------------------------------------------------------- spectra --

def windows(word, L):
    n = len(word)
    return [''.join(word[(i + d) % n] for d in range(L)) for i in range(n)]

def spectrum(word, L):
    spec = {}
    for w in windows(word, L):
        spec[w] = spec.get(w, 0) + 1
    return spec

specS = spectrum(S, L)
specD = spectrum(D, L)
print("d_S =", specS, " sum", sum(specS.values()))
print("d_D =", specD, " sum", sum(specD.values()))
assert sum(specS.values()) == G and sum(specD.values()) == G

# ----------------------------------------------------------- observation --
# all 8 starts once plus K_EXTRA extra copies of start 0 (AAA)
obs = dict(specS)
obs["AAA"] = obs.get("AAA", 0) + K_EXTRA
n = sum(obs.values())
print("x  =", obs, " n =", n)
assert n == G + K_EXTRA == 12

# ------------------------------------------------------- exact objective --
def exactLik(x, d, t):
    """Candidate-intrinsic multinomial: n! / prod x_c! * prod (d_c/t)^x_c."""
    total = sum(x.values())
    r = Fraction(factorial(total), 1)
    for c in x:
        r /= factorial(x[c])
    for c in x:
        r *= Fraction(d.get(c, 0), t) ** x[c]
    return r

likS = exactLik(obs, specS, G)
likD = exactLik(obs, specD, G)
exact_ratio = likD / likS
print("Lik(S) =", likS)
print("Lik(D) =", likD)
print("E1 exact ratio D/S =", exact_ratio, "=", float(exact_ratio))
assert exact_ratio == 2

# ------------------------------------------------------ binomial objective --
AB_TYPES = ["AAA", "AAB", "ABA", "ABB", "BAA", "BAB", "BBA", "BBB"]
DNA_TYPES = [a + b + c for a in "ACGT" for b in "ACGT" for c in "ACGT"]

def binomLik(types, N, n, x, d):
    """Product over `types` of C(n,x_c) (d_c/N)^x_c (1-d_c/N)^(n-x_c),
    zero-count factors retained."""
    r = Fraction(1, 1)
    for c in types:
        dc = d.get(c, 0)
        xc = x.get(c, 0)
        r *= comb(n, xc) * Fraction(dc, N) ** xc * Fraction(N - dc, N) ** (n - xc)
    return r

binomS = binomLik(AB_TYPES, N, n, obs, specS)
binomD = binomLik(AB_TYPES, N, n, obs, specD)
binom_ratio = binomD / binomS
print("Binom(S) =", binomS)
print("Binom(D) =", binomD)
print("E2 binomial ratio D/S =", binom_ratio)
print("   num =", binom_ratio.numerator)
print("   den =", binom_ratio.denominator)
print("   float =", float(binom_ratio))
TARGET = Fraction(1341068619663964900807, 448762029294263205888)
assert binom_ratio == TARGET
assert abs(float(binom_ratio) - 2.9883736415332867) < 1e-12

# E3: 4-letter DNA binomial (rename B -> C).  Types with G or T contribute 1.
obs_dna = {k.replace("B", "C"): v for k, v in obs.items()}
specS_dna = {k.replace("B", "C"): v for k, v in specS.items()}
specD_dna = {k.replace("B", "C"): v for k, v in specD.items()}
binomS_dna = binomLik(DNA_TYPES, N, n, obs_dna, specS_dna)
binomD_dna = binomLik(DNA_TYPES, N, n, obs_dna, specD_dna)
dna_ratio = binomD_dna / binomS_dna
print("E3 4-letter DNA binomial ratio D/S =", dna_ratio)
assert dna_ratio == TARGET
# every type containing G or T has x = d_S = d_D = 0  =>  factor 1
for c in DNA_TYPES:
    if "G" in c or "T" in c:
        assert obs_dna.get(c, 0) == 0 and specS_dna.get(c, 0) == 0 and specD_dna.get(c, 0) == 0

# -------------------------------------------- E4: information feasibility --
def cyc(word, i):
    return word[i % len(word)]

def agree(word, e, a, b):
    return all(cyc(word, a + d) == cyc(word, b + d) for d in range(e))

def prec(word, t):
    return cyc(word, t + len(word) - 1)

def foll(word, e, t):
    return cyc(word, t + e)

def is_repeat(word, e, a, b):
    G_ = len(word)
    return (1 <= e < G_ and a != b and agree(word, e, a, b)
            and prec(word, a) != prec(word, b) and foll(word, e, a) != foll(word, e, b))

def is_triple(word, e, a, b, c):
    G_ = len(word)
    return (1 <= e < G_ and len({a, b, c}) == 3
            and agree(word, e, a, b) and agree(word, e, a, c) and agree(word, e, b, c)
            and not (prec(word, a) == prec(word, b) == prec(word, c))
            and not (foll(word, e, a) == foll(word, e, b) == foll(word, e, c)))

R = set(range(G))

def bridges_copy(word, e, t):
    """Repository BridgesCopy: exists r in R, d < L with d+e+1 < L and
    (r+d+1) % G == t  (strict bridging)."""
    return any((r + d + 1) % G == t and d + e + 1 < L
               for r in R for d in range(L))

def in_open_arc(word, a, b, p):
    G_ = len(word)
    return 0 < (p + G_ - a) % G_ < (b + G_ - a) % G_

def interleaved(word, a, b, c, d):
    if len({a, b, c, d}) < 4:
        return False
    return in_open_arc(word, a, b, c) != in_open_arc(word, a, b, d)

def covers(word, L, R):
    return all(any((r + d) % G == p for r in R for d in range(L)) for p in range(G))

triples = [(e, a, b, c) for e in range(1, G) for a in range(G)
           for b in range(G) for c in range(G) if is_triple(S, e, a, b, c)]
reps = [(e, a, b) for e in range(1, G) for a in range(G)
        for b in range(G) if is_repeat(S, e, a, b)]
all_triples_bridged = all(bridges_copy(S, e, t)
                          for (e, a, b, c) in triples for t in (a, b, c))
inter = [(e1, e2, a, b, c, d) for (e1, a, b) in reps for (e2, c, d) in reps
         if interleaved(S, a, b, c, d)]
all_inter_bridged = all(
    any(bridges_copy(S, e, t) for e, t in ((e1, a), (e1, b), (e2, c), (e2, d)))
    for (e1, e2, a, b, c, d) in inter)
print("E4 I_s for S: covers =", covers(S, L, R),
      " #triples =", len(triples), " all-bridged =", all_triples_bridged,
      " #interleaved =", len(inter), " all-bridged =", all_inter_bridged)
assert covers(S, L, R) and all_triples_bridged and all_inter_bridged

# --------------------------------------- E5: historical read-string coverage --
observed_types = set(obs.keys())
def hist_covers(genome, L, observed):
    G_ = len(genome)
    for t in range(G_):
        if not any(''.join(genome[(t + delta + d) % G_] for d in range(L)) in observed
                   for delta in range(L - 1)):
            return False, t
    return True, None

hcS, _ = hist_covers(S, L, observed_types)
hcD, _ = hist_covers(D, L, observed_types)
print("E5 historical coverage: S =", hcS, " D =", hcD)
assert hcS

# ------------------------------------------------- E6: D is not §6.2 ------
unobserved = set(specD) - set(obs)
print("E6 windows of D not observed:", unobserved)
assert "ABA" in unobserved
per_vertex_ok = all(specD.get(c, 0) >= 1 for c in obs)
print("   D satisfies weak per-vertex lower bound (every observed type in D):",
      per_vertex_ok)
assert per_vertex_ok
support_eq = all((specD.get(c, 0) > 0) == (obs.get(c, 0) > 0)
                 for c in set(list(specD) + list(obs)))
print("   D satisfies §6.2 support equality:", support_eq)
assert not support_eq

print("\nALL CHECKS PASSED")
