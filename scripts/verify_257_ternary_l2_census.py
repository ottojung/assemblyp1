#!/usr/bin/env python3
"""Independent finite census of ternary circular L=2 read graphs.

Universe: circular words over {A,B,C}, lengths 2..7, modulo rotation.
For each spectrum, enumerate every positive integer circulation of the same
total on its observed directed-edge support. Independently validate every
nonzero alternative by checking incidence, zero total delta, and A+delta >= 1.
This is bounded evidence only, not a general rigidity theorem.
"""

from collections import Counter
from itertools import product

ALPHABET = "ABC"
MAX_G = 7


def rotations(word):
    return [word[i:] + word[:i] for i in range(len(word))]


def compositions(total, slots):
    if slots == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in compositions(total - first, slots - 1):
            yield (first,) + rest


def spectrum(word):
    n = len(word)
    return Counter(word[i] + word[(i + 1) % n] for i in range(n))


def incidence(edges, values):
    balance = Counter()
    for (u, v), value in zip(edges, values):
        balance[u] += value
        balance[v] -= value
    return balance


def check_delta(edges, truth, alternative):
    delta = tuple(b - a for a, b in zip(truth, alternative))
    assert any(delta)
    assert not any(incidence(edges, delta).values())
    assert sum(delta) == 0
    assert all(a + d >= 1 for a, d in zip(truth, delta))
    return delta


def positive_circulations(edges, total):
    slack_total = total - len(edges)
    if slack_total < 0:
        return
    for slack in compositions(slack_total, len(edges)):
        values = tuple(x + 1 for x in slack)
        if not any(incidence(edges, values).values()):
            yield values


def main():
    genomes = 0
    spectrum_classes = {}
    for g in range(2, MAX_G + 1):
        for letters in product(ALPHABET, repeat=g):
            word = "".join(letters)
            if word != min(rotations(word)):
                continue
            genomes += 1
            spec = spectrum(word)
            key = tuple(sorted(spec.items()))
            spectrum_classes.setdefault(key, (word, spec))

    rigid = nonrigid = alternative_pairs = 0
    rigid_triples = []
    witnesses = []
    for _, (word, spec) in sorted(spectrum_classes.items()):
        edges = sorted(spec)
        truth = tuple(spec[e] for e in edges)
        alternatives = [b for b in positive_circulations(edges, len(word)) if b != truth]
        if alternatives:
            nonrigid += 1
            for alternative in alternatives:
                delta = check_delta(edges, truth, alternative)
                alternative_pairs += 1
                if not witnesses:
                    witnesses.append((word, edges, truth, alternative, delta))
        else:
            rigid += 1
            if max(spec.values()) >= 3 and len(spec) > 1:
                rigid_triples.append((word, dict(spec)))

    assert rigid + nonrigid == len(spectrum_classes)
    print(f"universe: ternary circular words, 2 <= G <= {MAX_G}, L=2, modulo rotation")
    print(f"rotation classes enumerated: {genomes}")
    print(f"distinct spectra: {len(spectrum_classes)}")
    print(f"rigid spectra: {rigid}; non-rigid spectra: {nonrigid}")
    print(f"directly validated alternative circulations: {alternative_pairs}")
    print(f"rigid spectra with support size > 1 and an edge multiplicity >= 3: {len(rigid_triples)}")
    print(f"first nontrivial rigid triple example: {rigid_triples[0] if rigid_triples else 'none'}")
    if witnesses:
        word, edges, truth, alternative, delta = witnesses[0]
        print(f"first non-rigid example: {word}, edges={edges}, A={truth}, B={alternative}, delta={delta}")
    print("ALL TERNARY L2 CENSUS CHECKS PASSED")


if __name__ == "__main__":
    main()
