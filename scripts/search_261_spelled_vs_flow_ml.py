#!/usr/bin/env python3
"""Exact bounded search for a spelled-maximal / flow-nonmaximal separation.

This is a deliberately small diagnostic, not a model of the full MB09 §6.2
bidirected-flow feasible set. It uses DNA reverse-complement molecule classes,
circular genome spectra, and the exact variable-length multinomial likelihood.
The comparison flow universe is the *larger unconstrained count-vector universe*:
all nonnegative vectors on the binary-alphabet molecule-class universe whose
total is N, for every 1 <= N <= MAX_LENGTH. Such vectors need not be graph-flow
feasible; consequently this search can exclude a genuine counterexample only
for this larger surrogate universe, not establish a general maximality theorem.

For each truth S of length <= MAX_LENGTH, the sample is the truth's complete
count vector x=A. We check all circular binary-alphabet candidates of lengths
L..MAX_LENGTH for spelled maximality, then all surrogate flow count vectors.
All comparisons use Fraction arithmetic.
"""
from collections import Counter
from fractions import Fraction
from itertools import product

ALPHABET = "AT"
COMPLEMENT = {"A": "T", "T": "A"}
MAX_LENGTH = 8


def reverse_complement(word):
    return "".join(COMPLEMENT[c] for c in reversed(word))


def molecule(word):
    return min(word, reverse_complement(word))


def spectrum(genome, read_length):
    n = len(genome)
    return Counter(
        molecule("".join(genome[(i + j) % n] for j in range(read_length)))
        for i in range(n)
    )


def exact_likelihood(counts, sample, length):
    """Candidate-dependent part prod_i (counts_i / length)^sample_i."""
    score = Fraction(1)
    for cls, exponent in sample.items():
        score *= Fraction(counts.get(cls, 0), length) ** exponent
    return score


def genomes(read_length):
    for n in range(read_length, MAX_LENGTH + 1):
        for letters in product(ALPHABET, repeat=n):
            genome = "".join(letters)
            yield genome, spectrum(genome, read_length)


def count_vectors(classes, total):
    """Every weak composition of total over classes (unconstrained surrogate)."""
    if len(classes) == 1:
        yield {classes[0]: total}
        return
    for values in product(range(total + 1), repeat=len(classes) - 1):
        used = sum(values)
        if used <= total:
            yield dict(zip(classes, (*values, total - used)))


def search(read_length):
    candidates = list(genomes(read_length))
    classes = sorted(
        {molecule("".join(word)) for word in product(ALPHABET, repeat=read_length)}
    )
    checked_truths = 0
    for truth, observed in candidates:
        truth_length = len(truth)
        truth_score = exact_likelihood(observed, observed, truth_length)
        spelled_dominators = [
            (genome, counts)
            for genome, counts in candidates
            if exact_likelihood(counts, observed, len(genome)) > truth_score
        ]
        if spelled_dominators:
            continue
        checked_truths += 1
        for length in range(1, MAX_LENGTH + 1):
            for flow_counts in count_vectors(classes, length):
                score = exact_likelihood(flow_counts, observed, length)
                if score > truth_score:
                    return {
                        "read_length": read_length,
                        "truth": truth,
                        "observed": dict(observed),
                        "truth_score": truth_score,
                        "flow_length": length,
                        "flow_counts": flow_counts,
                        "flow_score": score,
                        "spelled_maximal_truths_checked_before_witness": checked_truths,
                    }
    return {"read_length": read_length, "spelled_maximal_truths": checked_truths}


def main():
    total = 0
    for read_length in (2, 3):
        result = search(read_length)
        if "flow_counts" in result:
            raise AssertionError(f"bounded separation witness found: {result}")
        print(
            f"[ok] L={read_length}: no separation among "
            f"{result['spelled_maximal_truths']} spelled-maximal truths; "
            "all surrogate weak compositions and N=1..8 checked"
        )
        total += result["spelled_maximal_truths"]
    print(f"PASS: {total} spelled-maximal truth instances; no surrogate witness")


if __name__ == "__main__":
    main()
