#!/usr/bin/env python3
"""Finite exact tests for unrestricted balanced-circulation spelling and attainment.

This verifies representative finite cases of the mathematical criterion. It is
not a Lean formalization or a replacement for the general proof in the paper.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import product

ALPHABET = "AC"
L = 3
EDGES = ["".join(e) for e in product(ALPHABET, repeat=L)]
VERTICES = ["".join(v) for v in product(ALPHABET, repeat=L-1)]


def spectrum(word):
    return Counter("".join(word[(i+j) % len(word)] for j in range(L))
                   for i in range(len(word)))


def balanced(counts):
    return all(
        sum(n for e, n in counts.items() if e[:-1] == v)
        == sum(n for e, n in counts.items() if e[1:] == v)
        for v in VERTICES
    )


def connected(counts):
    active = {e[:-1] for e, n in counts.items() if n} | {
        e[1:] for e, n in counts.items() if n
    }
    if not active:
        return False
    seen, frontier = set(), [next(iter(active))]
    while frontier:
        v = frontier.pop()
        if v in seen:
            continue
        seen.add(v)
        for e, n in counts.items():
            if not n:
                continue
            if e[:-1] == v and e[1:] not in seen:
                frontier.append(e[1:])
            if e[1:] == v and e[:-1] not in seen:
                frontier.append(e[:-1])
    return seen == active


def spell(counts):
    assert sum(counts.values()) > 0
    assert balanced(counts)
    assert connected(counts)
    adj = defaultdict(list)
    for e, n in counts.items():
        adj[e[:-1]].extend([e[1:]] * n)
    start = next(e[:-1] for e, n in counts.items() if n)
    stack, circuit = [start], []
    while stack:
        v = stack[-1]
        if adj[v]:
            stack.append(adj[v].pop())
        else:
            circuit.append(stack.pop())
    circuit.reverse()
    assert circuit[0] == circuit[-1]
    assert len(circuit)-1 == sum(counts.values())
    word = "".join(v[-1] for v in circuit[:-1])
    assert spectrum(word) == counts, (word, counts, spectrum(word))
    return word


checked, connected_checked, disconnected_checked = 0, 0, 0
for values in product(range(3), repeat=len(EDGES)):
    counts = Counter({e: n for e, n in zip(EDGES, values) if n})
    if not counts or not balanced(counts):
        continue
    checked += 1
    if connected(counts):
        connected_checked += 1
        spell(counts)
    else:
        disconnected_checked += 1

assert connected_checked and disconnected_checked
print(f"All {checked} small balanced 3-mer multisets classified: "
      f"{connected_checked} connected Eulerian spellings, "
      f"{disconnected_checked} disconnected")

# A rational balanced flow can fail to admit any single-circle spelling.
counts = Counter({"AAA": 1, "CCC": 1})
assert balanced(counts) and not connected(counts)

previous_likelihood = Fraction(-1)
for n in [3, 4, 8, 20, 100, 1000]:
    word = "A"*n + "C"*n
    spec = spectrum(word)
    assert spec["AAA"] == spec["CCC"] == n - 2
    assert spec == Counter({"AAA": n-2, "CCC": n-2,
                            "AAC": 1, "ACC": 1, "CCA": 1, "CAA": 1})
    likelihood = Fraction(n-2, 2*n) ** 2
    assert likelihood < Fraction(1, 4)
    assert likelihood > previous_likelihood
    previous_likelihood = likelihood
assert Fraction(1000-2, 2*1000)**2 > Fraction(249, 1000)

# Every small circular candidate is strictly below the rational disconnected
# supremum of 1/4 for the two observed reads, including periodic candidates.
for length in range(1, 14):
    for letters in product(ALPHABET, repeat=length):
        word = "".join(letters)
        sp = spectrum(word)
        probability = (Fraction(sp["AAA"], length)
                       * Fraction(sp["CCC"], length))
        assert probability < Fraction(1, 4)

# Mixing the disconnected flow with positive rational uniform flow ensures a
# full-support connected rational circulation, hence actual spellings approach.
for m in [2, 20, 200]:
    mixed = Counter({e: 1 for e in EDGES}) + Counter({"AAA": m, "CCC": m})
    assert balanced(mixed) and connected(mixed)
    genome = spell(mixed)
    assert Fraction(spectrum(genome)["AAA"], len(genome)) == Fraction(m+1, 2*m+8)

print("Disconnected rational optimum and single-circle non-attainment: PASS")
print("Full-support rational approximation by explicit genomes: PASS")
