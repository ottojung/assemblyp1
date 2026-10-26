#!/usr/bin/env python3
"""Exact finite regression check for the binary L=2 parameterization."""


def main() -> None:
    for m in range(1, 101):
        got = set()
        for t in range(2 * m + 1):
            lo = max(0, 2 * t - 2 * m)
            for a in range(lo, t + 1):
                b = t - a
                c = t - a
                d = 2 * m - 2 * t + a
                vector = (a, b, c, d)
                assert min(vector) >= 0
                assert sum(vector) == 2 * m
                # With fixed total, circulation is equivalent to AB=BA.
                assert b == c
                got.add(vector)

        # Independently enumerate all nonnegative compositions and retain
        # exactly those satisfying total and flow balance.
        brute = {
            (a, b, c, d)
            for a in range(2 * m + 1)
            for b in range(2 * m + 1 - a)
            for c in range(2 * m + 1 - a - b)
            for d in [2 * m - a - b - c]
            if b == c
        }
        assert got == brute, (m, got ^ brute)
        assert len(got) == (m + 1) ** 2, (m, len(got))

    print("PASS: m=1..100; parameterization is bijective with balanced vectors")
    print("PASS: balanced-vector count is (m+1)^2 for every checked m")


if __name__ == "__main__":
    main()
