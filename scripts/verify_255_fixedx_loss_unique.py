#!/usr/bin/env python3
"""Exact integer check: at x_lose=B4, rival B4 uniquely maximizes likelihood.

Oriented same-length model, S=AAABBB (G=6, L=2), E255 order (AA,AB,BB,BA).
Mirrors kernel-checked fixedX_unique_at_xLose258 (decide-closed).
"""
from math import prod

B1 = (2, 1, 2, 1)
B2 = (1, 1, 3, 1)
B3 = (3, 1, 1, 1)
B4 = (1, 2, 1, 2)
x_lose = B4

def lik(B, x):
    return prod(m ** c for m, c in zip(B, x, strict=True))

v1, v2, v3, v4 = lik(B1, x_lose), lik(B2, x_lose), lik(B3, x_lose), lik(B4, x_lose)
assert (v1, v2, v3, v4) == (4, 3, 3, 16), (v1, v2, v3, v4)
assert v4 > v1 and v4 > v2 and v4 > v3
print(f"PASS: loss chamber unique max at x_lose=B4: B1:{v1} B2:{v2} B3:{v3} B4:{v4}")
