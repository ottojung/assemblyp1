#!/usr/bin/env python3
"""Independent exact-integer check of the bounded #263 throughput clash."""

from itertools import product

# Edge order: a0,a1,b0,b1. Each edge is a distinct directed loop.
tail = (0, 0, 1, 1)
head = (0, 0, 1, 1)
g1 = (1, 0, -1, 0)
g2 = (0, -1, 0, 1)
delta = tuple(a + b for a, b in zip(g1, g2))
z = (1, 1, 1, 1)
y = tuple(a + b for a, b in zip(z, delta))


def balance(flow):
    return tuple(
        sum(flow[e] for e in range(4) if tail[e] == v)
        - sum(flow[e] for e in range(4) if head[e] == v)
        for v in range(2)
    )


def throughput(flow):
    return tuple(sum(flow[e] for e in range(4) if tail[e] == v) for v in range(2))


def conformal(part, whole):
    return all(a == 0 or b == 0 or (a > 0) == (b > 0) for a, b in zip(part, whole))


def in_kernel(flow):
    return balance(flow) == (0, 0) and sum(flow) == 0


def is_graver(w):
    if not any(w) or not in_kernel(w):
        return False
    # Exhaustively check every integer conformal subvector; bounds follow from
    # coordinatewise sign-conformality to this fixed finite vector.
    ranges = [range(min(0, c), max(0, c) + 1) for c in w]
    for part in product(*ranges):
        if part == (0, 0, 0, 0) or part == w:
            continue
        other = tuple(a - b for a, b in zip(w, part))
        if conformal(part, w) and conformal(other, w) and in_kernel(part) and in_kernel(other):
            return False
    return True


assert all(t == h for t, h in zip(tail, head))  # all four edges are loops
assert is_graver(g1) and is_graver(g2)
assert tuple(a + b for a, b in zip(g1, g2)) == delta
assert conformal(g1, delta) and conformal(g2, delta)
assert in_kernel(g1) and in_kernel(g2) and in_kernel(delta)
assert balance(z) == balance(y) == (0, 0)
assert sum(z) == sum(y) == 4
assert all(0 <= x <= 2 for x in z + y)
assert throughput(z) == throughput(y) == (2, 2)
assert throughput(g1) == (1, -1)
assert throughput(g2) == (-1, 1)
assert throughput(delta) == (0, 0)
assert throughput(g1)[0] * throughput(g2)[0] < 0

# Mutation-negative-control: a witness with the wrong claimed g2 sign is rejected.
mutated_g2 = (0, 1, 0, -1)  # flip both nonzero edge signs
assert throughput(mutated_g2) == (1, -1)
assert throughput(mutated_g2) != throughput(g2)
assert not (throughput(g1)[0] * throughput(mutated_g2)[0] < 0)
print("#263 throughput sign-clash witness: PASS")
