#!/usr/bin/env python3
"""Exact RC/orientation class check for the AAATT reduced-graph witness (#261).

The graph candidate here is a spelled circular genome, not an arbitrary flow.
The script compares oriented words and reverse-complement molecule classes.
"""
from collections import Counter
from fractions import Fraction

L = 3
TRUTH = "AAATT"
COMPETITOR = "AAATA"
STARTS = (0, 0, 1, 2)


def rc(word: str) -> str:
    return word.translate(str.maketrans("AT", "TA"))[::-1]


def cls(word: str) -> str:
    return min(word, rc(word))


def windows(genome: str) -> list[str]:
    return ["".join(genome[(i + j) % len(genome)] for j in range(L))
            for i in range(len(genome))]


def spectrum(genome: str, quotient: bool) -> Counter[str]:
    ws = windows(genome)
    return Counter(map(cls, ws) if quotient else ws)


def exact_score(sample: Counter[str], d: Counter[str], n: int) -> Fraction:
    return Fraction(1) if not sample else _score(sample, d, n)


def _score(sample: Counter[str], d: Counter[str], n: int) -> Fraction:
    value = Fraction(1)
    for word, count in sample.items():
        value *= Fraction(d[word], n) ** count
    return value


def run() -> None:
    truth_words = windows(TRUTH)
    sample_oriented = Counter(truth_words[i] for i in STARTS)
    sample_class = Counter(map(cls, sample_oriented.elements()))
    assert sample_oriented == Counter({"AAA": 2, "AAT": 1, "ATT": 1})
    # In molecule-class semantics AAT and ATT are one RC class.
    assert sample_class == Counter({"AAA": 2, "AAT": 2})

    ts_o, ds_o = spectrum(TRUTH, False), spectrum(COMPETITOR, False)
    ts_c, ds_c = spectrum(TRUTH, True), spectrum(COMPETITOR, True)
    assert ts_o == Counter({"AAA": 1, "AAT": 1, "ATT": 1, "TTA": 1, "TAA": 1})
    assert ds_o == Counter({"AAA": 2, "AAT": 1, "ATA": 1, "TAA": 1})
    assert ts_c == Counter({"AAA": 1, "AAT": 2, "TAA": 2})
    assert ds_c == Counter({"AAA": 2, "AAT": 1, "ATA": 1, "TAA": 1})

    # Candidate classes: circular genomes modulo rotation (oriented), versus
    # circular genomes modulo rotation and reverse-complement. Neither changes
    # the likelihood within its own sample alphabet. Truth is admitted; N=5.
    ratio_oriented = exact_score(sample_oriented, ds_o, 5) / exact_score(sample_oriented, ts_o, 5)
    assert ratio_oriented == 0  # observed ATT is absent from competitor
    ratio_molecule = exact_score(sample_class, ds_c, 5) / exact_score(sample_class, ts_c, 5)
    assert ratio_molecule == Fraction(1)
    print(f"oriented exact iid competitor/truth = {ratio_oriented}")
    print(f"RC-class exact iid competitor/truth = {ratio_molecule}")
    print("PASS: class change alters the maximality verdict for this candidate pair")


if __name__ == "__main__":
    run()
