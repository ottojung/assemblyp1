#!/usr/bin/env python3
"""Exact multinomial comparison on an o_min=2 observed-panel flow cell.

Alphabet {A,T}, RC A<->T, read length 3, observed molecule classes
{AAA,AAT,TAA}, truth AAATT, observations x={AAA:2,AAT:1,TAA:1}.
Candidates are spelled closed walks/circular genomes on the observed-vertex
o_min=2 graph, with edge multiplicity allowed. The candidate universe is
fixed length N=5 and truth is admitted. Score is the exact multinomial
probability (including its common coefficient); exact Fraction arithmetic.
This is a bounded explicit rule-out for this cell, distinct from the prior
variable-length exact-iid and fixed-N binomial certificates.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import product
from math import factorial

L = 3
O_MIN = 2
TRUTH = "AAATT"
X = Counter({"AAA": 2, "AAT": 1, "TAA": 1})
OBSERVED = frozenset(X)
N = len(TRUTH)
REALIZED_STARTS = (0, 0, 1, 4)


def rc(word):
    return "".join("T" if c == "A" else "A" for c in reversed(word))


def molecule(word):
    return min(word, rc(word))


def graph():
    strands = sorted({w for v in OBSERVED for w in (v, rc(v))})
    return [(u, v) for u in strands for v in strands
            if u[L - O_MIN:] == v[:O_MIN]]


EDGES = graph()


def windows(circle):
    return ["".join(circle[(i + j) % len(circle)] for j in range(L))
            for i in range(len(circle))]


def spectrum(circle):
    return Counter(molecule(w) for w in windows(circle))


def score(d):
    n = sum(X.values())
    result = Q(factorial(n), 1)
    for count in X.values():
        result /= factorial(count)
    for read in OBSERVED:
        result *= Q(d.get(read, 0), N) ** X[read]
    return result


def allowed_walk(circle):
    ws = windows(circle)
    return all(molecule(w) in OBSERVED for w in ws) and all(
        (ws[i], ws[(i + 1) % len(ws)]) in EDGES for i in range(len(ws)))


def enumerate_spelled(length):
    return ["".join(chars) for chars in product("AT", repeat=length)
            if allowed_walk("".join(chars))]


def main():
    truth_d = spectrum(TRUTH)
    assert truth_d == Counter({"AAA": 1, "AAT": 2, "TAA": 2})
    assert allowed_walk(TRUTH)
    assert len(EDGES) == 10
    assert len(REALIZED_STARTS) == sum(X.values())
    assert Counter(molecule("".join(TRUTH[(start + j) % N] for j in range(L)))
                   for start in REALIZED_STARTS) == X

    candidates = enumerate_spelled(N)
    assert TRUTH in candidates
    truth_score = score(truth_d)
    scored = [(score(spectrum(g)), g, spectrum(g)) for g in candidates]
    best_score = max(value for value, _, _ in scored)
    beaters = [(value, genome, d) for value, genome, d in scored
               if value > truth_score]

    assert truth_score == Q(48, 625)
    assert best_score == truth_score
    assert not beaters
    print(f"o_min={O_MIN}, L={L}, observed-panel genomes length N={N}: {len(candidates)}")
    print(f"truth AAATT spectrum={dict(truth_d)}, exact multinomial={truth_score}")
    print(f"best exact multinomial={best_score}; strict beaters={len(beaters)}")
    print("BOUNDED RULE-OUT: no strict spelled-genome beater in this fixed-length cell")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
