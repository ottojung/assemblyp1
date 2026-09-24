#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from collections import defaultdict
from itertools import product


def spectrum(word: str, length: int) -> dict[str, int]:
    size = len(word)
    result: dict[str, int] = defaultdict(int)
    for start in range(size):
        fragment = "".join(word[(start + offset) % size] for offset in range(length))
        result[fragment] += 1
    return dict(sorted(result.items()))


def rotations(word: str):
    return sorted({word[offset:] + word[:offset] for offset in range(len(word))})


def canonical(word: str) -> str:
    return rotations(word)[0]


def primitive(word: str) -> bool:
    return len(set(rotations(word))) == len(word)


def maximal_pair(word: str, length: int, first: int, second: int) -> bool:
    size = len(word)
    return (word[(first - 1) % size] != word[(second - 1) % size]
            and word[(first + length) % size] != word[(second + length) % size])


def maximal_triple(word: str, length: int, starts: tuple[int, int, int]) -> bool:
    size = len(word)
    return (len({word[(start - 1) % size] for start in starts}) > 1
            and len({word[(start + length) % size] for start in starts}) > 1)


def violates_p2(word: str, read_length: int) -> bool:
    size = len(word)
    threshold = read_length - 1
    for length in range(1, threshold + 1):
        groups: dict[str, list[int]] = defaultdict(list)
        for start in range(size):
            fragment = "".join(word[(start + offset) % size] for offset in range(length))
            groups[fragment].append(start)
        positions = [tuple(values) for values in groups.values() if len(values) >= 3]
        for first in range(size):
            for second in range(first + 1, size):
                for third in range(second + 1, size):
                    triple = (first, second, third)
                    if triple in positions and maximal_triple(word, length, triple):
                        return True
        for values in groups.values():
            for first in values:
                for second in values:
                    if not maximal_pair(word, length, first, second):
                        continue
                    for third in values:
                        if third == first or third == second:
                            continue
                        for fourth in values:
                            if fourth in (first, second, third):
                                continue
                            pair_one, pair_two = {first, second}, {third, fourth}
                            if len(pair_one | pair_two) != 4:
                                continue
                            four = sorted(pair_one | pair_two)
                            labels = ["A" if position in pair_one else "B" for position in four]
                            if labels in (["A", "B", "A", "B"], ["B", "A", "B", "A"]):
                                return True
    return False


def search(max_length: int, max_size: int) -> dict:
    checked = 0
    first_hit = None
    rejected_by_p2 = 0
    for read_length in range(1, max_length + 1):
        for size in range(1, max_size + 1):
            by_spectrum: dict[tuple[tuple[str, int], ...], set[str]] = defaultdict(set)
            for letters in product("AB", repeat=size):
                word = "".join(letters)
                if not primitive(word):
                    continue
                representative = canonical(word)
                by_spectrum[tuple(spectrum(representative, read_length).items())].add(representative)
            for letters in product("AB", repeat=size):
                word = "".join(letters)
                if not primitive(word) or canonical(word) != word:
                    continue
                checked += 1
                key = tuple(spectrum(word, read_length).items())
                if len(by_spectrum[key]) != 1:
                    continue
                if violates_p2(word, read_length):
                    candidate = {
                        "word": word,
                        "read_length": read_length,
                        "genome_size": size,
                        "spectrum": dict(key),
                        "unique_canonical_rotations": sorted(by_spectrum[key]),
                        "primitive": True,
                    }
                    if first_hit is None:
                        first_hit = candidate
                else:
                    rejected_by_p2 += 1
    return {
        "model": {
            "alphabet": ["A", "B"],
            "orientation": "fixed",
            "equivalence": "rotation only",
            "observation": "complete integer multiplicity spectrum",
            "candidate_length": "same as genome",
            "quantifier": "for every same-length binary circular candidate in the bounded scope",
        },
        "bounds": {"maximum_read_length": max_length, "maximum_genome_size": max_size},
        "checked_primitive_canonical_genomes": checked,
        "unique_but_p2_satisfying_before_hit": rejected_by_p2,
        "first_hit": first_hit,
        "evidence": "exhaustive only within the stated finite binary scope",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-length", type=int, default=2)
    parser.add_argument("--max-size", type=int, default=4)
    args = parser.parse_args()
    result = search(args.max_length, args.max_size)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
