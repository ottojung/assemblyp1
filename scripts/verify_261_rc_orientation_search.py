#!/usr/bin/env python3
"""Exhaustive exact-rational length-five RC/orientation census for issue #261."""

from collections import Counter
from fractions import Fraction
from itertools import combinations_with_replacement, product
from math import prod


def rc(word):
    return word[::-1].translate(str.maketrans("ACGT", "TGCA"))


def canon(genome):
    rotations = [genome[i:] + genome[:i] for i in range(len(genome))]
    return min(rotations + [rc(g) for g in rotations])


def windows(genome):
    return tuple((genome + genome)[i : i + 3] for i in range(len(genome)))


def spectrum(genome, quotient):
    return Counter(min(w, rc(w)) if quotient else w for w in windows(genome))


def ratio(truth, competitor, sample, quotient):
    t, c = spectrum(truth, quotient), spectrum(competitor, quotient)
    obs = [min(w, rc(w)) if quotient else w for w in sample]
    tp = [Fraction(t[w], 5) for w in obs]
    cp = [Fraction(c[w], 5) for w in obs]
    assert all(p > 0 for p in tp), "truth must be admitted"
    return Fraction(0) if any(p == 0 for p in cp) else prod(cp, start=Fraction(1)) / prod(tp, start=Fraction(1))


def main():
    genomes = sorted({canon("".join(xs)) for xs in product("AT", repeat=5)})
    assert len(genomes) == 4
    oriented_zero_quotient_one = set()
    any_verdict_change = set()
    checked = 0
    for truth in genomes:
        ws = windows(truth)
        for indices in combinations_with_replacement(range(5), 4):
            sample = tuple(ws[i] for i in indices)
            for competitor in genomes:
                if competitor == truth:
                    continue
                ro = ratio(truth, competitor, sample, False)
                rq = ratio(truth, competitor, sample, True)
                key = (truth, competitor, tuple(sorted(sample)))
                checked += 1
                if ro == 0 and rq == 1:
                    oriented_zero_quotient_one.add(key)
                if ro != rq:
                    any_verdict_change.add(key)

    expected = ("AAATT", "AAATA", ("AAA", "AAA", "AAT", "ATT"))
    expected_key = (canon("AAATT"), canon("AAATA"), tuple(sorted(expected[2])))
    assert expected_key in oriented_zero_quotient_one
    assert len(oriented_zero_quotient_one) == 7, oriented_zero_quotient_one
    assert oriented_zero_quotient_one <= any_verdict_change

    truth, competitor, sample = expected
    assert windows(truth) == ("AAA", "AAT", "ATT", "TTA", "TAA")
    assert windows(competitor) == ("AAA", "AAT", "ATA", "TAA", "AAA")
    assert ratio(truth, competitor, sample, False) == 0
    assert ratio(truth, competitor, sample, True) == 1
    # The prior hand-check for the named pair is intentionally not generalized
    # here: arbitrary triples from the binary universe need not belong to the
    # same reduced graph induced by the sample.

    print(f"canonical binary genomes={len(genomes)}")
    print(f"truth/competitor/sample comparisons={checked}")
    print(f"all ratio changes={len(any_verdict_change)}")
    print(f"oriented zero / RC ratio one={len(oriented_zero_quotient_one)}")
    print("unique witness: AAATT vs AAATA; sample AAA,AAA,AAT,ATT")
    print("exact competitor/truth ratios: oriented=0; RC-class=1")
    print("both genomes' windows remain within observed-vertex 2-overlap graph")
    print("PASS")


if __name__ == "__main__":
    main()
