#!/usr/bin/env python3
"""Verify the #284 window-box sharpness refutation.

`AssemblyP1/Section62WindowBoxSharpness.lean` proves, kernel-checked, that no
observed-window designation hypothesis sharpens the invariant window box

    WindowBox L W d  <->  forall u, d u <= windowCount L u W

to the exact physical feasible-throughput image

    PhysImage L W d  <->  exists vs ovs, GenuineWalk L vs ovs
                            and spellWalk vs ovs = W and d = throughputOf vs.

This script independently re-derives the refutation on the definitions:

1. the general prefix-delta obstruction: for every word `W` with `L < |W|` the
   vector `delta (W.take L)` lies in the box and satisfies endpoint designation
   (when prefix = suffix) but is *not* realized by any genuine walk spelling `W`;
2. the generic `W = 01200`, `L = 2` two-endpoint obstruction: `delta_01 + delta_00`
   is in the box and endpoint-designated but not realized;
3. a finite sweep over all words `W` over `{0,1,2}` of length up to 5 and all
   `L` with `1 <= L < |W|`, re-checking the prefix-delta obstruction against an
   explicit enumeration of every genuine walk spelling `W` (all read-window
   sequences up to `|W| - L + 1` reads, all proper overlaps);
4. the Lean module is hygiene-clean (no sorry/admit/axiom/native_decide), every
   endpoint carries a `#print axioms` command, and the documentation exists and
   states the refutation and the read-count obstruction.

Exit 0 iff every assertion holds.
"""

from __future__ import annotations

import itertools
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODULE = ROOT / "AssemblyP1" / "Section62WindowBoxSharpness.lean"
DOC = ROOT / "docs" / "section62-window-box-sharpness-284.md"

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def spell_walk(reads: list[list[int]], overlaps: list[int]) -> list[int]:
    word = list(reads[0])
    for read, ov in zip(reads[1:], overlaps):
        word += read[ov:]
    return word


def windows(word: list[int], k: int) -> list[tuple[int, ...]]:
    return [tuple(word[i : i + k]) for i in range(len(word) - k + 1)]


def count(seq, x) -> int:
    return sum(1 for y in seq if y == x)


def genuine_walk(reads: list[list[int]], overlaps: list[int], length: int) -> bool:
    """The GenuineWalk predicate of the module, re-checked here."""
    if len(reads) != len(overlaps) + 1:
        return False
    if any(len(r) != length for r in reads):
        return False
    for v, w, o in zip(reads, reads[1:], overlaps):
        if not (0 <= o < length):
            return False
        if v[length - o :] != w[:o]:
            return False
    return True


def window_count(word: list[int], k: int, u: tuple[int, ...]) -> int:
    return count(windows(word, k), u)


def in_box(word: list[int], k: int, d: dict) -> bool:
    """WindowBox k word d, with d a sparse dict word -> count."""
    for u in set(windows(word, k)) | set(d):
        if d.get(u, 0) > window_count(word, k, u):
            return False
    return True


def throughput(reads: list[list[int]]) -> dict:
    d: dict = {}
    for r in reads:
        d[tuple(r)] = d.get(tuple(r), 0) + 1
    return d


def image(word: list[int], k: int) -> list[dict]:
    """Enumerate every physical throughput vector: every genuine walk spelling
    `word`, by all read-window sequences up to `|word| - k + 1` reads and all
    proper overlaps.  (A walk spelling a word of length `n` has at most `n - k + 1`
    reads because each proper overlap adds at least one symbol.)"""
    n = len(word)
    wins = windows(word, k)
    out: list[dict] = []
    max_reads = n - k + 1
    for nreads in range(1, max_reads + 1):
        for reads in itertools.product(wins, repeat=nreads):
            for overlaps in itertools.product(range(k), repeat=nreads - 1):
                if not genuine_walk([list(r) for r in reads], list(overlaps), k):
                    continue
                if spell_walk([list(r) for r in reads], list(overlaps)) != word:
                    continue
                out.append(throughput([list(r) for r in reads]))
    return out


def endpoint_designated(word: list[int], k: int, d: dict) -> bool:
    prefix = tuple(word[:k])
    suffix = tuple(word[len(word) - k :])
    return d.get(prefix, 0) >= 1 and d.get(suffix, 0) >= 1


def check_prefix_obstruction(word: list[int], k: int) -> list[str]:
    errs: list[str] = []
    prefix = tuple(word[:k])
    d = {prefix: 1}
    if not in_box(word, k, d):
        errs.append(f"prefix delta not in box for W={word}, L={k}")
    if d in image(word, k):
        errs.append(f"prefix delta realized by a walk for W={word}, L={k}")
    return errs


def strip_lean_comments(text: str) -> str:
    """Remove Lean block (/- -/, nested) and line (--) comments."""
    out: list[str] = []
    i, depth, n = 0, 0, len(text)
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j == -1 else j
            continue
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(text[i])
        i += 1
    return "".join(out)


def main() -> int:
    errors: list[str] = []

    # 1. General prefix-delta obstruction on the explicit witnesses.
    for word, k in (([0, 1, 2, 3, 0, 1], 2), ([0, 1, 2, 0, 0], 2),
                    ([0, 1, 2, 3, 4, 1, 2, 0, 0], 5)):
        errors.extend(check_prefix_obstruction(word, k))

    # 1b. The endpoint-designated witness W = 012301, L = 2.
    epw, epk = [0, 1, 2, 3, 0, 1], 2
    epd = {tuple(epw[:epk]): 1}
    if not in_box(epw, epk, epd):
        errors.append("endpoint prefix delta not in box")
    if not endpoint_designated(epw, epk, epd):
        errors.append("endpoint prefix delta is not endpoint-designated")
    if epd in image(epw, epk):
        errors.append("endpoint prefix delta realized by a walk")

    # 1c. The generic two-endpoint witness W = 01200, L = 2.
    gw, gk = [0, 1, 2, 0, 0], 2
    gd = {(0, 1): 1, (0, 0): 1}
    if not in_box(gw, gk, gd):
        errors.append("two-endpoint vector not in box")
    if not endpoint_designated(gw, gk, gd):
        errors.append("two-endpoint vector is not endpoint-designated")
    if gd in image(gw, gk):
        errors.append("two-endpoint vector realized by a walk")
    # and the read-count obstruction: any walk realizing it would have 2 reads,
    # spelling at most 2*L = 4 < 5 = |W| symbols.
    if sum(gd.values()) * gk >= len(gw):
        errors.append("read-count obstruction arithmetic is wrong")

    # 2. Finite sweep: all words over {0,1,2} up to length 5, all 1 <= L < |W|.
    checked = 0
    for n in range(2, 6):
        for word in itertools.product((0, 1, 2), repeat=n):
            word = list(word)
            for k in range(1, n):
                errors.extend(check_prefix_obstruction(word, k))
                checked += 1
    if checked == 0:
        errors.append("finite sweep checked no instances")

    # 3. Lean module hygiene.
    if not MODULE.exists():
        errors.append(f"missing module: {MODULE.relative_to(ROOT)}")
    else:
        lean = strip_lean_comments(MODULE.read_text(encoding="utf-8"))
        for token in ("sorry", "admit", "axiom ", "native_decide"):
            if token in lean:
                errors.append(f"module contains forbidden token: {token!r}")
        endpoints = (
            "physImage_subset_windowBox", "genuineWalk_spell_length_le",
            "prefix_delta_mem_box", "delta_prefix_not_mem_image",
            "no_prefix_support_designation_sharpens", "endpoint_prefix_refuted",
            "endpoint_pair_refuted",
        )
        for decl in endpoints:
            if f"#print axioms {decl}" not in lean:
                errors.append(f"module missing #print axioms command for {decl}")
        root = strip_lean_comments((ROOT / "AssemblyP1.lean").read_text(encoding="utf-8"))
        for decl in endpoints:
            if f"#print axioms AssemblyP1.Section62WindowBoxSharpness.{decl}" not in root:
                errors.append(f"root missing qualified #print axioms for {decl}")

    # 4. Documentation exists and states the refutation and the obstruction.
    if not DOC.exists():
        errors.append(f"missing documentation: {DOC.relative_to(ROOT)}")
    else:
        text = DOC.read_text(encoding="utf-8")
        for marker in ("designation", "WindowBox", "PhysImage", "read-count", "refut"):
            if marker not in text:
                errors.append(f"docs missing marker: {marker!r}")

    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    print("window-box sharpness refuted: no observed-window designation hypothesis "
          "sharpens the invariant window box to the exact physical image")
    return 0


if __name__ == "__main__":
    sys.exit(main())
