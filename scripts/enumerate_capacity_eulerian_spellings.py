#!/usr/bin/env python3
"""Enumerate small capacitated edge-type cyclic Eulerian spellings modulo rotation."""

import argparse
import hashlib
import itertools
import json
from collections import Counter, defaultdict


def start(edge):
    return edge[0]


def end(edge):
    return edge[-1]


def canonical(rotation):
    return min(rotation[i:] + rotation[:i] for i in range(len(rotation)))


def enumerate_spellings(capacities, alphabet):
    total = sum(capacities.values())
    words = set()
    counts = Counter()

    def visit(prefix):
        if len(prefix) == total:
            if prefix and start(prefix[-1]) == start(prefix[0]):
                words.add(canonical(prefix))
            return
        for edge in alphabet:
            if counts[edge] == capacities[edge]:
                continue
            if prefix and end(prefix[-1]) != start(edge):
                continue
            counts[edge] += 1
            visit(prefix + (edge,))
            counts[edge] -= 1

    visit(())
    return sorted(words, key=lambda word: (len(word), word))


def incoming(word):
    return tuple(edge[-1] for edge in word)


def outgoing(word):
    return tuple(edge[0] for edge in word)


def forced_at_vertices(word):
    outgoing_by = defaultdict(list)
    incoming_by = defaultdict(list)
    for source, edge in zip(outgoing(word), word):
        outgoing_by[source].append(edge)
    for edge, target in zip(word, incoming(word)):
        incoming_by[target].append(edge)
    for vertex in set(outgoing_by) | set(incoming_by):
        if len(set(outgoing_by[vertex])) != 1 or len(set(incoming_by[vertex])) != 1:
            return False
    return True


def max_vertex_degree(word):
    vertices = set(outgoing(word))
    return max(Counter(outgoing(word))[v] + Counter(incoming(word))[v] for v in vertices)


def encode_capacities(capacities):
    encoded = {}
    for edge, count in capacities.items():
        if count:
            encoded["".join(edge)] = count
    return encoded



def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-length", type=int, default=8)
    parser.add_argument("--output")
    args = parser.parse_args()
    if args.max_length < 1:
        raise SystemExit("--max-length must be positive")

    alphabet = tuple((a, b) for a in "AB" for b in "AB")
    lengths = range(1, args.max_length + 1)
    results = []
    examples = {}
    for total in lengths:
        for positive in itertools.product(range(total + 1), repeat=len(alphabet) - 1):
            if sum(positive) >= total:
                continue
            capacities = dict(zip(alphabet[1:], positive))
            capacities[alphabet[0]] = total - sum(positive)
            words = enumerate_spellings(capacities, alphabet)
            if not words:
                continue
            unique = len(words) == 1
            forced = all(forced_at_vertices(word) for word in words)
            max_degree = min(max_vertex_degree(word) for word in words)
            key = "unique" if unique else "multiple"
            examples.setdefault(key, {
                "capacities": encode_capacities(capacities),
                "spellings": [list(map(list, word)) for word in words],
                "min_max_vertex_degree": max_degree,
            })
            results.append({
                "capacities": encode_capacities(capacities),
                "number_modulo_rotation": len(words),
                "forced_at_every_vertex_for_every_spelling": forced,
                "all_spellings_have_max_vertex_degree_2": all(max_vertex_degree(word) == 2 for word in words),
            })

    data = {
        "scope": "edge alphabet AA, AB, BA, BB; exact enumeration; at least one AA copy anchors the DFS",
        "max_length": args.max_length,
        "records": len(results),
        "unique_records": sum(row["number_modulo_rotation"] == 1 for row in results),
        "multiple_records": sum(row["number_modulo_rotation"] > 1 for row in results),
        "forced_implies_unique_records": sum(
            row["forced_at_every_vertex_for_every_spelling"] and row["number_modulo_rotation"] == 1
            for row in results
        ),
        "nonunique_forced_records": sum(
            row["forced_at_every_vertex_for_every_spelling"] and row["number_modulo_rotation"] > 1
            for row in results
        ),
        "examples": examples,
        "results": results,
    }
    payload = json.dumps(data, indent=2, sort_keys=True) + "\n"
    if args.output:
        with open(args.output, "w", encoding="utf-8") as handle:
            handle.write(payload)
    else:
        print(payload, end="")
    print("sha256", hashlib.sha256(payload.encode()).hexdigest(), file=__import__("sys").stderr)


if __name__ == "__main__":
    main()
