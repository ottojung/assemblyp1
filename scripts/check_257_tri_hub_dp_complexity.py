#!/usr/bin/env python3
"""Independent exact census for the triangular-hub DP recurrence.

This deliberately does not import the repository verifier. It compares a
fresh dictionary DP (count saturated at two) with direct enumeration of every
shifted nonnegative vector in the bounded mass simplex. A control dropping
both hub-balance coordinates must disagree on the known rigid p3/m3 instance.
"""
from itertools import product


def dp_count(length_groups, slack_groups, enforce_balance=True):
    lengths = sum((list(g) for g in length_groups), [])
    slacks = sum((list(g) for g in slack_groups), [])
    a, b, c = map(len, length_groups)
    K = sum(L * s for L, s in zip(lengths, slacks))
    # State = (sum_A-sum_B, sum_B-sum_C, weighted mass).
    states = {(0, 0, 0): 1}
    for i, (L, group) in enumerate(zip(lengths,
                                       [0] * a + [1] * b + [2] * c)):
        nxt = {}
        for (x, y, mass), ways in states.items():
            for t in range((K - mass) // L + 1):
                dx = t if group == 0 else (-t if group == 1 else 0)
                dy = t if group == 1 else (-t if group == 2 else 0)
                if not enforce_balance:
                    dx = dy = 0
                key = (x + dx, y + dy, mass + t * L)
                nxt[key] = min(2, nxt.get(key, 0) + ways)
        states = nxt
    target = (sum(slacks[:a]) - sum(slacks[a:a + b]),
              sum(slacks[a:a + b]) - sum(slacks[a + b:]), K)
    if not enforce_balance:
        target = (0, 0, K)
    return states.get(target, 0), K


def direct_count(length_groups, slack_groups, enforce_balance=True):
    lengths = sum((list(g) for g in length_groups), [])
    slacks = sum((list(g) for g in slack_groups), [])
    a, b, c = map(len, length_groups)
    K = sum(L * s for L, s in zip(lengths, slacks))
    count = 0
    for u in product(*(range(K // L + 1) for L in lengths)):
        if sum(L * t for L, t in zip(lengths, u)) != K:
            continue
        if enforce_balance and not (
            sum(u[:a]) - sum(u[a:a + b]) ==
            sum(slacks[:a]) - sum(slacks[a:a + b]) and
            sum(u[a:a + b]) - sum(u[a + b:]) ==
            sum(slacks[a:a + b]) - sum(slacks[a + b:])
        ):
            continue
        count = min(2, count + 1)
    return count


def main():
    length_patterns = [
        ((1,), (1,), (1,)),
        ((1, 2), (1, 2), (1, 2)),
        ((1, 2), (1, 1), (2, 2)),
    ]
    checked = 0
    for groups in length_patterns:
        sizes = tuple(map(len, groups))
        for flat in product(range(3), repeat=sum(sizes)):
            at = 0
            slacks = []
            for size in sizes:
                slacks.append(flat[at:at + size])
                at += size
            if not (sum(slacks[0]) == sum(slacks[1]) == sum(slacks[2])):
                continue
            got, _ = dp_count(groups, slacks)
            want = direct_count(groups, slacks)
            assert got == want, (groups, slacks, got, want)
            checked += 1
    # Mutation-negative-control: removing coupling must call this rigid
    # instance non-rigid, while the exact equations give exactly the base.
    lengths = ((1, 3), (1, 3), (1, 3))
    slacks = ((1, 0), (1, 0), (1, 0))
    exact, _ = dp_count(lengths, slacks)
    relaxed, _ = dp_count(lengths, slacks, enforce_balance=False)
    assert exact == direct_count(lengths, slacks) == 1
    assert relaxed == 2
    print(f"exact DP vs direct enumeration: {checked} balanced instances, 0 mismatches")
    print(f"mutation control: exact count={exact}, balance-dropped count={relaxed} (red)")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
