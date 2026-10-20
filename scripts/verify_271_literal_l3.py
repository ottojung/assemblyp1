#!/usr/bin/env python3
"""Independent verifier for the #271 read-length-3 literal-event oriented adapter.

Re-derives, from the exact source predicates transcribed in
`AssemblyP1/SourceFaithfulIs.lean` and `AssemblyP1/HistoricalCovers.lean`, the
finite model of `AssemblyP1/ConditionalVsMLLiteralL3Adapter271.lean`:

  * six binary circular genomes of length 4 (one per rotation-orbit class),
  * oriented read length 3,
  * the literal §6.4 historical event
    `HistoricalInformationFeasibleLiteral`, and
  * the normalized single-read pmf `p_g(w) = #starts spelling w / 4`,

and checks that at the single observed read string `000`:

  * the truth orbit `1` (`0001`) satisfies the literal event through the
    NON-SATURATED placement `{0,1,3}`, and no other orbit satisfies it;
  * ordinary R-only ML strictly prefers the wrong orbit `0` (`0000`).

It also checks the Lean source for the expected theorem names and for the
absence of `sorry`/`admit`/`axiom`/`native_decide`.

Exit status 0 iff every check passes.
"""

from __future__ import annotations

import itertools
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODULE = ROOT / "AssemblyP1" / "ConditionalVsMLLiteralL3Adapter271.lean"

G = 4
L = 3
REPS = [
    (0, 0, 0, 0),
    (0, 0, 0, 1),
    (0, 0, 1, 1),
    (0, 1, 0, 1),
    (0, 1, 1, 1),
    (1, 1, 1, 1),
]
OBS = (0, 0, 0)


def window(g, e, s):
    return tuple(g[(s + d) % G] for d in range(e))


def agree(g, e, a, b):
    return window(g, e, a) == window(g, e, b)


def preceding(g, t):
    return g[(t + G - 1) % G]


def following(g, e, t):
    return g[(t + e) % G]


def is_repeat(g, e, a, b):
    return (
        1 <= e < G
        and a != b
        and agree(g, e, a, b)
        and preceding(g, a) != preceding(g, b)
        and following(g, e, a) != following(g, e, b)
    )


def is_triple_occurrence(g, e, a, b, c):
    if not (1 <= e < G):
        return False
    if len({a, b, c}) != 3:
        return False
    return agree(g, e, a, b) and agree(g, e, a, c) and agree(g, e, b, c)


def in_open_arc(g, a, b, p):
    return 0 < (p - a) % G < (b - a) % G


def interleaved(g, a, b, c, d):
    if len({a, b, c, d}) != 4:
        return False
    return in_open_arc(g, a, b, c) != in_open_arc(g, a, b, d)


def bridges_copy(g, R, e, t):
    for r in R:
        for d in range(L):
            if d + e + 1 < L and (r + d + 1) % G == t:
                return True
    return False


def observed_types(g, R):
    return {window(g, L, s) for s in R}


def match_starts(g, obs):
    return {t for t in range(G) if window(g, L, t) in obs}


def historical_covers(g, obs):
    ms = match_starts(g, obs)
    return all(any((t + d) % G in ms for d in range(L - 1)) for t in range(G))


def literal(g, R):
    obs = observed_types(g, R)
    ms = match_starts(g, obs)
    if not historical_covers(g, obs):
        return False
    for e in range(G):
        for a in range(G):
            for b in range(G):
                for c in range(G):
                    if is_triple_occurrence(g, e, a, b, c) and not (
                        bridges_copy(g, ms, e, a)
                        and bridges_copy(g, ms, e, b)
                        and bridges_copy(g, ms, e, c)
                    ):
                        return False
    for e1 in range(G):
        for e2 in range(G):
            for a in range(G):
                for b in range(G):
                    for c in range(G):
                        for d in range(G):
                            if (
                                is_repeat(g, e1, a, b)
                                and is_repeat(g, e2, c, d)
                                and interleaved(g, a, b, c, d)
                                and not (
                                    bridges_copy(g, ms, e1, a)
                                    or bridges_copy(g, ms, e1, b)
                                    or bridges_copy(g, ms, e2, c)
                                    or bridges_copy(g, ms, e2, d)
                                )
                            ):
                                return False
    return True


def subsets():
    for mask in range(1, 1 << G):
        yield frozenset(i for i in range(G) if mask >> i & 1)


def E(g, w):
    return any(
        any(window(g, L, s) == w for s in T) and literal(g, T) for T in subsets()
    )


def pcount(g, w):
    return sum(1 for s in range(G) if window(g, L, s) == w)


def main() -> int:
    errors: list[str] = []

    def check(name, cond):
        if not cond:
            errors.append(name)

    # 1. Non-saturated literal witness for the truth orbit 1.
    check(
        "truth orbit 1 is literally feasible at the non-saturated placement {0,1,3}",
        literal(REPS[1], {0, 1, 3}),
    )
    check("witness {0,1,3} is non-saturated", len({0, 1, 3}) == 3)

    # 2. The literal event pins the truth orbit at read 000.
    ev = {i: E(REPS[i], OBS) for i in range(6)}
    check("E holds for the truth orbit 1 at read 000", ev[1] is True)
    for i in range(6):
        if i != 1:
            check(f"E fails for orbit {i} at read 000", ev[i] is False)

    # 3. Exact single-read pmf at read 000.
    mult = [pcount(g, OBS) for g in REPS]
    check("pmf table at 000 = (4,1,0,0,0,0)", mult == [4, 1, 0, 0, 0, 0])

    # 4. Ordinary ML strictly prefers the wrong orbit 0 over the truth orbit 1.
    check("ordinary ML strictly prefers orbit 0 over truth 1", mult[0] > mult[1])
    check("truth 1 is not an ML maximizer", not (mult[1] >= max(mult)))

    # 5. Converse: at read 000 the all-zero orbit 0 is the unique ML maximizer.
    check("orbit 0 is the unique ML maximizer", mult[0] > max(mult[1:]))

    # 6. Lean source integrity.
    src = MODULE.read_text(encoding="utf-8")
    for name in (
        "literalFeasible_nonsaturated",
        "E_one_000",
        "E_zero_000",
        "E_iff_at_000",
        "sep_posteriorMass_one",
        "sep_truth_not_ml",
        "sep_ordinary_not_certain",
        "separation_genome",
        "conv_ml_unique",
        "conv_ordinary_not_certain",
        "converse_genome",
        "model_axes",
    ):
        check(f"Lean module declares {name}", name in src)
    code = re.sub(r"/-.*?-/", "", src, flags=re.DOTALL)
    code = re.sub(r"--[^\n]*", "", code)
    for token in ("sorry", "admit", "axiom", "native_decide"):
        check(f"Lean module has no `{token}`", not re.search(rf"\b{token}\b", code))

    if errors:
        print("FAILED checks:")
        for e in errors:
            print("  -", e)
        return 1

    print("All #271 literal-L3 adapter checks passed:")
    print(f"  E(orbit, 000) = {ev}")
    print(f"  pmf multiplicities at 000 = {mult}")
    print("  literal witness for orbit 1: non-saturated placement {0,1,3}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
