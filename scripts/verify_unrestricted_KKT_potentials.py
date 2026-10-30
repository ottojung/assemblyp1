#!/usr/bin/env python3
"""Exact unrestricted-ML maximality certificates via rational difference constraints.

Mathematical theorem in the manuscript; independent executable verifier,
not a Lean theorem. No floating point arithmetic or optimization package.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import product


def spectrum(word, length):
    return Counter(
        "".join(word[(i+j) % len(word)] for j in range(length))
        for i in range(len(word))
    )


def likelihood(word, length, sample):
    sp = spectrum(word, length)
    return __import__("math").prod(
        Q(sp[e], len(word)) ** count for e, count in sample.items()
    )


def maximality_certificate(word, length, sample, alphabet):
    # Return exact rational potentials, or None if the KKT system is infeasible.
    vertices = ["".join(t) for t in product(alphabet, repeat=length-1)]
    edges = ["".join(t) for t in product(alphabet, repeat=length)]
    counts = spectrum(word, length)
    assert sample and sum(sample.values()) > 0
    assert all(e in edges for e in sample)
    if any(count > 0 and counts[e] == 0 for e, count in sample.items()):
        return None
    n = sum(sample.values())
    constraints = []  # h(v) <= h(u) + bound, i.e. u -> v
    for e in edges:
        tail, head = e[:-1], e[1:]
        if counts[e]:
            p = Q(counts[e], len(word))
            bound = Q(n) - Q(sample[e], 1) / p
            constraints.append((tail, head, bound))
            constraints.append((head, tail, -bound))
        else:
            constraints.append((tail, head, Q(n)))

    # Implicit zero-weight super-source to every vertex.
    distance = {v: Q(0) for v in vertices}
    for _ in range(len(vertices)):
        changed = False
        for u, v, bound in constraints:
            if distance[v] > distance[u] + bound:
                distance[v] = distance[u] + bound
                changed = True
        if not changed:
            break
    else:
        return None  # A negative directed cycle exists.

    assert all(distance[v] - distance[u] <= b
               for u, v, b in constraints)
    assert all(distance[e[1:]] - distance[e[:-1]]
               == Q(n) - Q(sample[e] * len(word), counts[e])
               for e in edges if counts[e])
    return distance


def test(word, length, sample, alphabet, expected):
    cert = maximality_certificate(word, length, sample, alphabet)
    assert (cert is not None) == expected, (word, length, sample, cert)


test("AAATT", 3, spectrum("AAATT", 3), "AT", True)
test("AAATT", 3, spectrum("AAATT", 3) + Counter({"AAA": 1}), "AT", False)
test("AAACAC", 3, spectrum("AAACAC", 3) + Counter({"AAC": 1}), "AC", False)
test("AC", 2, Counter({"AC": 1}), "AC", True)
test("A", 3, Counter({"AAA": 1}), "AC", True)
test("AACAG", 2, spectrum("AACAG", 2), "ACG", True)

# Known finite witness to failed unrestricted maximality.
sample = spectrum("AAATT", 3) + Counter({"AAA": 1})
assert likelihood("AAAATT", 3, sample) > likelihood("AAATT", 3, sample)

# Every KKT certificate is sufficient, so finite brute-force candidates
# must never beat the truth. Check all binary genomes to length 5, and all
# (ordered) truth-supported samples of length one or two.
alphabet = "AC"
all_genomes = [
    "".join(seq)
    for length in range(1, 9)
    for seq in product(alphabet, repeat=length)
]
candidate_laws = {}
for g in all_genomes:
    sp = spectrum(g, 2)
    key = tuple(Q(sp[e], len(g)) for e in ["AA", "AC", "CA", "CC"])
    candidate_laws[key] = g
distinct_candidates = list(candidate_laws.values())
checked = 0
certified = 0
for length in range(1, 6):
    for letters in product(alphabet, repeat=length):
        truth = "".join(letters)
        read_types = list(spectrum(truth, 2))
        for size in (1, 2):
            for selected in product(read_types, repeat=size):
                sample = Counter(selected)
                checked += 1
                cert = maximality_certificate(truth, 2, sample, alphabet)
                if cert is None:
                    continue
                certified += 1
                truth_likelihood = likelihood(truth, 2, sample)
                for competitor in distinct_candidates:
                    assert likelihood(competitor, 2, sample) <= truth_likelihood, (
                        truth, sample, competitor, cert
                    )

assert certified > 0
print("All named rational KKT certificate examples: PASS")
print(f"Brute force cross-check: {checked} cases, "
      f"{certified} certificates; no false-positive maximality")
print("Finite-sample decision is exact difference-constraint feasibility")
