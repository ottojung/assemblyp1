#!/usr/bin/env python3
"""Exact small checks for the scalar edge-type spelling claim."""

from itertools import product


def windows(word, k):
    n = len(word)
    return [((word + word)[i:i + k]) for i in range(n)]


def spectrum(word, k):
    out = {}
    for w in windows(word, k):
        out[w] = out.get(w, 0) + 1
    return tuple(sorted(out.items()))


def primitive_cycle(word):
    n = len(word)
    return not any(n % d == 0 and word == word[:d] * (n // d) for d in range(1, n))


def main():
    assert primitive_cycle("AAABAB")
    assert spectrum("AAB", 2) == (('AA', 1), ('AB', 1), ('BA', 1))
    assert spectrum("AAABAB", 2) == (('AA', 2), ('AB', 2), ('BA', 2))

    # Exhaustive binary check for L=2, lengths through 8: the only obstruction
    # found is the forced-cycle case (one outgoing edge type at every vertex).
    for n in range(1, 9):
        for bits in product("AB", repeat=n):
            s = "".join(bits)
            if not primitive_cycle(s):
                continue
            c = spectrum(s, 2)
            out = {}
            for w, _ in c:
                out[w[0]] = out.get(w[0], 0) + 1
            forced = all(k == 1 for k in out.values())
            doubled = any(primitive_cycle("".join(x)) for x in product("AB", repeat=2 * n)
                          if spectrum("".join(x), 2) == tuple((w, 2 * k) for w, k in c))
            assert doubled != forced, (s, c, out, doubled)
    print("checks passed: AAB/AAABAB and exhaustive binary L=2 n<=8")


if __name__ == "__main__":
    main()
