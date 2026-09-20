#!/usr/bin/env python3
"""Independent check of the candidate-universe reconciliation note.

This script recomputes, from scratch and with exact arithmetic, the finite facts
the note `docs/source-notes/candidate-universe-reconciliation.md` classifies:

* the four kernel-checked witness pairs on `main` and their strict ratios;
* whether each witness pair is a *spelled section 6.2 circuit* (its cyclic
  window spectrum has support exactly the observed read support), or carries an
  unobserved read window and is therefore not graph-representable;
* the lower-bound convention split: whether the per-occurrence strengthening
  `d_w >= x_w` holds for the truth, which is what distinguishes the
  variable-length from the same-length section 6.2 witness;
* the strict-oriented index inversion of the same-length witness.

No repository predicate or module is imported.  Exact `fractions.Fraction`
arithmetic only; deterministic; exits non-zero on any failed assertion.

Primary sources are cited in the note.
"""

from __future__ import annotations

from fractions import Fraction

DNA = {"A": "T", "T": "A", "C": "G", "G": "C"}


def windows(word: str, length: int) -> list[tuple[str, ...]]:
    n = len(word)
    return [tuple(word[(i + j) % n] for j in range(length)) for i in range(n)]


def rc(word: tuple[str, ...]) -> tuple[str, ...]:
    return tuple(DNA[c] for c in reversed(word))


def molecule_class(word: tuple[str, ...]) -> tuple[str, ...]:
    return min(word, rc(word))


def spectrum(word: str, length: int, collapse: bool) -> dict[tuple[str, ...], int]:
    d: dict[tuple[str, ...], int] = {}
    for w in windows(word, length):
        key = molecule_class(w) if collapse else w
        d[key] = d.get(key, 0) + 1
    return d


def observed(truth: str, length: int, starts: list[int], collapse: bool) -> dict[tuple[str, ...], int]:
    x: dict[tuple[str, ...], int] = {}
    ws = windows(truth, length)
    for s in starts:
        key = molecule_class(ws[s]) if collapse else ws[s]
        x[key] = x.get(key, 0) + 1
    return x


def support(d: dict[tuple[str, ...], int]) -> set[tuple[str, ...]]:
    return {k for k, v in d.items() if v > 0}


def is_spelled_circuit(d: dict[tuple[str, ...], int], x: dict[tuple[str, ...], int]) -> bool:
    """Support equality = spelled-circuit feasibility under per-vertex LB 1."""
    return support(d) == support(x)


def per_occurrence_lb(d: dict[tuple[str, ...], int], x: dict[tuple[str, ...], int]) -> bool:
    return all(d.get(k, 0) >= v for k, v in x.items())


def binom_full(d: dict[tuple[str, ...], int], x: dict[tuple[str, ...], int], N: int, n: int) -> Fraction:
    """Literal product of binomial marginals, retaining x_i = 0 factors."""
    value = Fraction(1)
    for t in set(d) | set(x):
        xi, di = x.get(t, 0), d.get(t, 0)
        if di == 0 and xi == 0:
            continue
        if di == 0:
            return Fraction(0)
        value *= Fraction(di, N) ** xi * Fraction(N - di, N) ** (n - xi)
    return value


def binom_positive(d: dict[tuple[str, ...], int], x: dict[tuple[str, ...], int], N: int, n: int) -> Fraction:
    """Product over the observed support only (zero-count factors dropped)."""
    value = Fraction(1)
    for t, xi in x.items():
        di = d.get(t, 0)
        if di == 0:
            return Fraction(0)
        value *= Fraction(di, N) ** xi * Fraction(N - di, N) ** (n - xi)
    return value


def exact_same_length_ratio(
    dD: dict[tuple[str, ...], int], dS: dict[tuple[str, ...], int], x: dict[tuple[str, ...], int]
) -> Fraction:
    """Same-length exact multinomial ratio: prod (d_D(w)/d_S(w))^{x_w}."""
    ratio = Fraction(1)
    for t, xi in x.items():
        ratio *= Fraction(dD.get(t, 0), dS.get(t, 0)) ** xi
    return ratio


def check(name: str, got, want) -> None:
    assert got == want, f"{name}: got {got!r}, want {want!r}"
    print(f"  ok  {name}: {got}")


def main() -> int:
    print("candidate-universe reconciliation checks")

    # ---- U_seq witnesses: #31 exact, #32 literal binomial -----------------
    print("[U_seq] fixed-length sequence witnesses")

    S, D, L, starts = "AAABB", "AAAAB", 3, [0, 1, 4]
    dS, dD = spectrum(S, L, False), spectrum(D, L, False)
    x = observed(S, L, starts, False)
    check("#31 exact same-length ratio", exact_same_length_ratio(dD, dS, x), Fraction(2))
    assert not is_spelled_circuit(dS, x) and not is_spelled_circuit(dD, x)
    print("  ok  #31 truth and competitor carry unobserved windows (not spelled circuits)")

    S, D, L, starts = "AAACC", "AAAAC", 3, [0, 1, 4]
    dS, dD = spectrum(S, L, False), spectrum(D, L, False)
    x = observed(S, L, starts, False)
    check("#32 literal full-product binomial ratio", binom_full(dD, x, 5, 3) / binom_full(dS, x, 5, 3), Fraction(1125, 512))
    check("#32 positive-support binomial ratio", binom_positive(dD, x, 5, 3) / binom_positive(dS, x, 5, 3), Fraction(9, 8))
    assert not is_spelled_circuit(dS, x) and not is_spelled_circuit(dD, x)
    print("  ok  #32 truth and competitor carry unobserved windows (not spelled circuits)")

    # ---- U_spell / U_flow witnesses: molecule classes over {A,T} ----------
    print("[U_spell / U_flow] spelled section 6.2 circuit witnesses")

    # variable length: AAATT -> AAAATT
    S, D, L, starts = "AAATT", "AAAATT", 3, [0, 1, 4]
    dS, dD = spectrum(S, L, True), spectrum(D, L, True)
    x = observed(S, L, starts, True)
    check("var truth spectrum", {k: v for k, v in sorted(dS.items())}, {("A", "A", "A"): 1, ("A", "A", "T"): 2, ("T", "A", "A"): 2})
    check("var competitor spectrum", {k: v for k, v in sorted(dD.items())}, {("A", "A", "A"): 2, ("A", "A", "T"): 2, ("T", "A", "A"): 2})
    assert is_spelled_circuit(dS, x) and is_spelled_circuit(dD, x)
    print("  ok  var: truth and competitor are spelled circuits (per-vertex LB 1)")
    assert per_occurrence_lb(dS, x) and per_occurrence_lb(dD, x)
    print("  ok  var: per-occurrence strengthening d>=x also holds (so it transfers)")
    check("var binomial ratio", binom_full(dD, x, 5, 3) / binom_full(dS, x, 5, 3), Fraction(9, 8))

    # same length: AAATAT -> AAAAAT
    S, D, L, starts = "AAATAT", "AAAAAT", 3, [0, 0, 1, 3, 5]
    dS, dD = spectrum(S, L, True), spectrum(D, L, True)
    x = observed(S, L, starts, True)
    check("same truth spectrum", {k: v for k, v in sorted(dS.items())}, {("A", "A", "A"): 1, ("A", "A", "T"): 1, ("A", "T", "A"): 3, ("T", "A", "A"): 1})
    check("same competitor spectrum", {k: v for k, v in sorted(dD.items())}, {("A", "A", "A"): 3, ("A", "A", "T"): 1, ("A", "T", "A"): 1, ("T", "A", "A"): 1})
    assert is_spelled_circuit(dS, x) and is_spelled_circuit(dD, x)
    print("  ok  same: truth and competitor are spelled circuits (per-vertex LB 1)")
    assert not per_occurrence_lb(dS, x) and per_occurrence_lb(dD, x)
    print("  ok  same: per-occurrence strengthening FAILS for the truth (d_S(AAA)=1 < x=2)")
    check("same binomial ratio", binom_full(dD, x, 6, 5) / binom_full(dS, x, 6, 5), Fraction(5))
    check("same exact same-length ratio", exact_same_length_ratio(dD, dS, x), Fraction(3))

    # ---- strict oriented index inverts the same-length witness ------------
    print("[index] strict oriented 4^k indexing")
    oriented_S = spectrum("AAATAT", L, False)
    oriented_D = spectrum("AAAAAT", L, False)
    check("oriented d_S(TAT)", oriented_S.get(("T", "A", "T"), 0), 1)
    check("oriented d_D(TAT)", oriented_D.get(("T", "A", "T"), 0), 0)
    print("  ok  strict oriented: competitor factor is 0 against an observed TAT")

    print("\nall candidate-universe reconciliation checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
