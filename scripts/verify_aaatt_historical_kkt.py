#!/usr/bin/env python3
"""Independent exact-rational checks for the paper's oriented AAATT example.

This is finite computation, not a substitute for Lean/source correspondence.
"""
from collections import Counter
from fractions import Fraction
from math import exp, lgamma, log


def spectrum(word, L):
    return Counter("".join(word[(i + j) % len(word)] for j in range(L))
                   for i in range(len(word)))


S, D, L = "AAATT", "AAAATT", 3
spec_s, spec_d = spectrum(S, L), spectrum(D, L)
assert spec_s == Counter({"AAA": 1, "AAT": 1, "ATT": 1, "TTA": 1, "TAA": 1})
assert spec_d == Counter({"AAA": 2, "AAT": 1, "ATT": 1, "TTA": 1, "TAA": 1})
observed = spec_s + Counter({"AAA": 1})
starts = list(range(len(S)))
reads = [S[i:] + S[:i] for i in starts]
reads = [x[:L] for x in reads]
assert set(reads) == set(spec_s)
# Historical H1: each t has at least one matched read in its L-1 start window.
assert all(any("".join(S[(t + delta + j) % len(S)] for j in range(L))
                   in set(reads) for delta in range(L-1))
           for t in starts)
# The three length-one A copies are all straddled by their previous read.
for pos in [0, 1, 2]:
    previous = (pos - 1) % 5
    assert "".join(S[(previous + j) % 5] for j in range(3)) in reads
    assert S[(previous + 1) % 5] == "A"
# Exhaustive finite check of the historical maximal-repeat clauses.
# Match starts are ALL genome starts because every distinct truth read is observed.
G = len(S)
match_starts = set(starts)
window = lambda t, size: "".join(S[(t + j) % G] for j in range(size))
bridged = lambda t, size: any(
    r % G in match_starts and r < t and t + size < r + L
    for r in range(t - L, t)
)
repeat_pairs = []
repeat_triples = []
for size in range(1, G):
    for a in range(G):
        for b in range(a + 1, G):
            if (window(a, size) == window(b, size)
                and S[(a - 1) % G] != S[(b - 1) % G]
                and S[(a + size) % G] != S[(b + size) % G]):
                repeat_pairs.append((size, a, b))
            for c in range(b + 1, G):
                if (window(a, size) == window(b, size) == window(c, size)
                    and len({S[(i - 1) % G] for i in (a, b, c)}) > 1
                    and len({S[(i + size) % G] for i in (a, b, c)}) > 1):
                    repeat_triples.append((size, a, b, c))

assert repeat_triples == [(1, 0, 1, 2)], repeat_triples
assert all(all(bridged(t, sz) for t in (a, b, c))
           for sz, a, b, c in repeat_triples)
for sz, a, b in repeat_pairs:
    for sz2, c, d in repeat_pairs:
        if len({a, b, c, d}) != 4:
            continue
        labels = ["p" if t in (a, b) else "q" for t in sorted([a, b, c, d])]
        alternating = labels in (["p", "q", "p", "q"], ["q", "p", "q", "p"])
        if alternating:
            assert (bridged(a, sz) or bridged(b, sz)
                    or bridged(c, sz2) or bridged(d, sz2))

lik = lambda sp, counts, G: __import__("math").prod(
    (Fraction(sp[w], G) ** n) for w, n in counts.items()
)
ratio = lik(spec_d, observed, 6) / lik(spec_s, observed, 5)
assert ratio == Fraction(15625, 11664), ratio

# Alternative: truth AAA once, every other truth type twice.
obs2 = Counter({"AAA": 1, "AAT": 2, "ATT": 2, "TTA": 2, "TAA": 2})
D2 = "AAATTAATT"
sp2 = spectrum(D2, 3)
assert sp2 == obs2
ratio2 = lik(sp2, obs2, len(D2)) / lik(spec_s, obs2, 5)
assert ratio2 == Fraction(500000000, 387420489)

# For any integers j>=0,k>=1, the explicit circular genome
# A^(j+2)TT(AATT)^(k-1) has AAA:j and AAT,ATT,TTA,TAA:k.
for j in range(9):
    for k in range(1, 9):
        g = "A" * (j + 2) + "TT" + "AATT" * (k - 1)
        assert spectrum(g, 3) == Counter(
            {"AAA": j, "AAT": k, "ATT": k, "TTA": k, "TAA": k}
        )

def mass_at_mean(n):
    x = n // 5
    return exp(lgamma(n+1)-lgamma(x+1)-lgamma(n-x+1)
               + x*log(.2)+(n-x)*log(.8))

print("historical full read-string H1 + all triple A copies bridged: PASS")
print("exact ratio for complete spectrum + one AAA:", ratio, float(ratio))
print("example with AAA once and four others twice:", ratio2, float(ratio2))
print("two-parameter circulation spelling family: PASS")
print("probability of necessary equality X_AAA=n/5:",
      mass_at_mean(100), mass_at_mean(1600))
