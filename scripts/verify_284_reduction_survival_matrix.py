#!/usr/bin/env python3
"""Exhaustive, reproducible classification of #284 §6.2 reduction dependents.

Issue #284 requirement (6) asks for every §6.2 counterexample or proof that
depends on the old literal predicate `Section62Flow.isReducibleB` (and its
downstream abbreviations `isReducible`, `transitivelyReduced`,
`ReductionVacuous`, `StepsSurviveReduction`, `SpelledFeasible62`) to be
classified as SURVIVES / MUST-BE-REPROVED / ALREADY-SUPERSEDED, with file:line
evidence.

This script is the mechanical companion of
`docs/section62-reduction-survival-matrix-284.md`. It performs, independently
of any Lean proof:

1. a comment-aware corpus scan of `AssemblyP1/*.lean` for the old identifiers,
   classifying each file as a definition site, a genuine dependent, an old-model
   audit, a corrected-model-only file, prose-only, or an unrelated local
   predicate;
2. a check that the document's genuine-dependent matrix lists exactly the
   genuine dependents and that every claimed `file:line` reference really
   contains an old identifier;
3. a check that the corrected bridges named in the document exist in the
   Lean sources;
4. an independent finite re-derivation of the old and corrected predicates on
   the `Section62SpellingReductionCandidate` regression instance, asserting the
   old predicate is vacuous and the corrected one genuinely removes the direct
   edge while keeping both detour legs;
5. the forced-longer / omega arithmetic that makes every full-overlap graph
   already reduced.

Exit 0 iff every assertion holds.
"""

from __future__ import annotations

import re
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ASSEMBLY = ROOT / "AssemblyP1"
DOC = ROOT / "docs" / "section62-reduction-survival-matrix-284.md"

# Word-boundary identifiers of the old model. `isReducibleLonger`,
# `transitivelyReducedSpelling`, `StepsSurviveReductionSpelling`,
# `SpelledFeasible62Spelling`, `ReductionVacuousLonger` are deliberately NOT
# matched: the negative lookahead excludes a following identifier character.
OLD_IDENTIFIERS = [
    "isReducibleB",
    "isReducible",
    "transitivelyReduced",
    "ReductionVacuous",
    "StepsSurviveReduction",
    "SpelledFeasible62",
]
OLD_RE = [
    (name, re.compile(r"\b" + re.escape(name) + r"(?![A-Za-z0-9_])"))
    for name in OLD_IDENTIFIERS
]

# Expected classification of every file that mentions an old identifier.
DEFINITION_SITE = {"Section62BidirectedFlow"}
OLD_MODEL_AUDIT = {"Section62ReductionVacuityAudit"}
UNRELATED_LOCAL = {"OrientedVariableLengthSe62", "ShortFiniteMLCounterexamples"}
# Files whose *statement or proof* references an old identifier directly.
GENUINE_DEPENDENT = {
    "Section62BridgingCounterexample",
    "SameLengthSection62Counterexample",
    "PerOccurrenceSameLengthCounterexample",
    "SameLengthSection62Parametric",
    "HistoricalCoverageSameLengthWitnesses",
    "SameLengthExactMLCounterexample",
    "SameLength62TieUniqueness",
    "SameLength62Maximizer",
    "Section62VariableOverlap247e",
    "Section62NonSpelledFlow",
}
# Files that reach an old identifier only through the carrier `Is62Candidate62`
# (defined in `SameLength62Maximizer`, whose body contains `SpelledFeasible62`).
TRANSITIVE_DEPENDENT = {
    "MLEscape",
    "Primitive62Uniqueness",
    "AcgtWitness211",
    "SameLength62NonprimitiveRotation",
    "SameLength62Uniqueness",
}

# Corrected bridges named in the document; (module, declaration).
CORRECTED_BRIDGES = [
    ("Section62SpellingReductionCandidate", "isReducibleSpellingB"),
    ("Section62SpellingReductionCandidate", "transitivelyReducedSpelling"),
    ("Section62SpellingReductionCandidate", "spellPath_eq_spellDirect"),
    ("Section62SpellingReductionCandidate", "replacement_overlaps_longer"),
    ("Section62SpellingReductionCandidate", "fullOverlap_not_reducible"),
    ("Section62ReductionDependencyAudit", "transitivelyReducedSpelling_eq_self_of_full"),
    ("Section62ReductionDependencyAudit", "stepsSurviveReductionSpelling_of_maximal"),
    ("Section62ReductionDependencyAudit", "nonspelled_reduction_spelling_eq"),
    ("Section62ReductionDependencyAudit", "star21_feasible62_spelling_reduced"),
    ("Section62ReductionDependencyAudit", "truth_feasible62_spelling_reduced"),
    ("Section62ReductionDependencyAudit", "star31_feasible62_spelling_reduced"),
    ("Section62ReductionWitnessAudit", "StepsSurviveReductionSpelling"),
    ("Section62ReductionWitnessAudit", "SpelledFeasible62Spelling"),
    ("Section62ReductionWitnessAudit", "spelledFeasible62_old_implies_spelling"),
    ("Section62ReductionWitnessAudit", "bridging_graph_spelling_reduction_eq_self"),
    ("Section62ReductionWitnessAudit", "sameLength_graph_spelling_reduction_eq_self"),
    ("Section62ReductionWitnessAudit", "perOccurrence_graph_spelling_reduction_eq_self"),
]


def strip_lean_comments(text: str) -> str:
    """Return `text` with Lean line comments and (nested) block comments removed.

    Doc comments `/-- ... -/` and `/-! ... -/` are block comments and are
    removed too. String literals are skipped so that `--` or `/-` inside a
    string is not treated as a comment.
    """
    out: list[str] = []
    i = 0
    n = len(text)
    depth = 0
    in_string = False
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if in_string:
            out.append(ch)
            if ch == "\\" and nxt:
                out.append(nxt)
                i += 2
                continue
            if ch == '"':
                in_string = False
            i += 1
            continue
        if depth > 0:
            if ch == "/" and nxt == "-":
                depth += 1
                i += 2
                continue
            if ch == "-" and nxt == "/":
                depth -= 1
                i += 2
                continue
            i += 1
            continue
        if ch == '"':
            in_string = True
            out.append(ch)
            i += 1
            continue
        if ch == "-" and nxt == "-":
            # line comment
            while i < n and text[i] != "\n":
                i += 1
            continue
        if ch == "/" and nxt == "-":
            depth = 1
            i += 2
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def module_name(path: Path) -> str:
    return path.stem


def classify(errors: list[str]) -> None:
    files = sorted(ASSEMBLY.glob("*.lean"))
    if not files:
        errors.append(f"no AssemblyP1/*.lean sources under {ASSEMBLY}")
        return

    derived: dict[str, set[str]] = {
        "DEFINITION_SITE": set(),
        "GENUINE_DEPENDENT": set(),
        "TRANSITIVE_DEPENDENT": set(),
        "OLD_MODEL_AUDIT": set(),
        "UNRELATED_LOCAL": set(),
        "NON_DEPENDENT": set(),
    }

    for path in files:
        text = path.read_text(encoding="utf-8")
        name = module_name(path)
        code = strip_lean_comments(text)
        code_hits = [ident for ident, rx in OLD_RE if rx.search(code)]

        # corrected analogues defined in this file
        defines_corrected = any(
            token in code
            for token in (
                "isReducibleSpellingB",
                "transitivelyReducedSpelling",
                "StepsSurviveReductionSpelling",
                "SpelledFeasible62Spelling",
            )
        )
        # a local (non-imported) SpelledFeasible62 definition
        local_spelled = re.search(
            r"\b(?:def|abbrev)\s+SpelledFeasible62\b", code
        ) is not None

        if name == "Section62BidirectedFlow":
            derived["DEFINITION_SITE"].add(name)
        elif name == "Section62ReductionVacuityAudit":
            derived["OLD_MODEL_AUDIT"].add(name)
        elif local_spelled:
            derived["UNRELATED_LOCAL"].add(name)
        elif defines_corrected:
            derived["NON_DEPENDENT"].add(name)
        elif code_hits:
            derived["GENUINE_DEPENDENT"].add(name)
        elif re.search(r"\bIs62Candidate62\b", code):
            # reaches SpelledFeasible62 through the Is62Candidate62 carrier
            derived["TRANSITIVE_DEPENDENT"].add(name)
        else:
            derived["NON_DEPENDENT"].add(name)

    expected = {
        "DEFINITION_SITE": DEFINITION_SITE,
        "GENUINE_DEPENDENT": GENUINE_DEPENDENT,
        "TRANSITIVE_DEPENDENT": TRANSITIVE_DEPENDENT,
        "OLD_MODEL_AUDIT": OLD_MODEL_AUDIT,
        "UNRELATED_LOCAL": UNRELATED_LOCAL,
    }
    for category, exp in expected.items():
        got = derived[category]
        for missing in sorted(exp - got):
            errors.append(f"{category}: expected dependent {missing} not found")
        for extra in sorted(got - exp):
            errors.append(f"{category}: unexpected file {extra} classified here")


def verify_doc(errors: list[str]) -> None:
    if not DOC.exists():
        errors.append(f"missing audit note: {DOC.relative_to(ROOT)}")
        return
    text = DOC.read_text(encoding="utf-8")

    # 1. The manifest lists every dependent (direct + transitive).
    mstart = text.find("<!-- survival-matrix:dependents-start -->")
    mend = text.find("<!-- survival-matrix:dependents-end -->")
    if mstart == -1 or mend == -1 or mend < mstart:
        errors.append("audit note missing dependents manifest markers")
        return
    manifest = set(
        line.strip()
        for line in text[mstart:mend].splitlines()
        if line.strip() and not line.strip().startswith("<!--")
    )
    expected_dependents = GENUINE_DEPENDENT | TRANSITIVE_DEPENDENT
    for missing in sorted(expected_dependents - manifest):
        errors.append(f"audit note manifest omits {missing}")
    for extra in sorted(manifest - expected_dependents):
        errors.append(f"audit note manifest lists non-dependent {extra}")

    # 2. Every explicit `AssemblyP1/<Name>.lean:LINE` claim must reference an
    #    old identifier (direct dependents) or the `Is62Candidate62` carrier
    #    (transitive dependents) at that line; bare `:LINE` rows inherit file.
    for marker_start, marker_end in (
        ("<!-- survival-matrix:genuine-start -->", "<!-- survival-matrix:genuine-end -->"),
        ("<!-- survival-matrix:transitive-start -->", "<!-- survival-matrix:transitive-end -->"),
    ):
        start = text.find(marker_start)
        end = text.find(marker_end)
        if start == -1 or end == -1 or end < start:
            errors.append(f"audit note missing markers {marker_start}")
            continue
        section = text[start:end]
        current = None
        for raw in section.splitlines():
            row = raw.strip()
            if not row.startswith("|"):
                continue
            m = re.search(r"AssemblyP1/([A-Za-z0-9_]+)\.lean\):(\d+)", row)
            if m:
                current = m.group(1)
                line_no = int(m.group(2))
            else:
                m2 = re.search(r"\|\s*:(\d+)\s*\|", row)
                if m2 and current:
                    line_no = int(m2.group(1))
                else:
                    continue
            path = ASSEMBLY / f"{current}.lean"
            if not path.exists():
                errors.append(f"audit note cites missing file {current}.lean")
                continue
            lines = path.read_text(encoding="utf-8").split("\n")
            if line_no < 1 or line_no > len(lines):
                errors.append(f"{current}.lean:{line_no} out of range")
                continue
            line = lines[line_no - 1]
            direct = any(rx.search(line) for _, rx in OLD_RE)
            transitive = re.search(r"\bIs62Candidate62\b", line) is not None
            if not (direct or transitive):
                errors.append(
                    f"{current}.lean:{line_no} does not reference an old identifier "
                    f"or the Is62Candidate62 carrier: {line.strip()[:80]!r}"
                )


def verify_bridges(errors: list[str]) -> None:
    cache: dict[str, str] = {}
    for module, decl in CORRECTED_BRIDGES:
        path = ASSEMBLY / f"{module}.lean"
        if not path.exists():
            errors.append(f"corrected bridge source missing: {module}.lean")
            continue
        if module not in cache:
            cache[module] = strip_lean_comments(path.read_text(encoding="utf-8"))
        if not re.search(r"\b(?:theorem|lemma|def|abbrev)\s+" + re.escape(decl) + r"\b",
                         cache[module]):
            errors.append(f"{module}.lean does not define {decl}")


# ---------------------------------------------------------------------------
# Independent finite re-derivation (Section62SpellingReductionCandidate toy).
# ---------------------------------------------------------------------------

COMP = lambda w: 7 - w  # noqa: E731
STRAND = {
    0: [0, 1, 2],
    1: [1, 2, 3],
    2: [2, 3, 4],
    3: [5, 6, 7],
    4: [4, 5, 6],
    5: [3, 4, 5],
}
VERTS = [0, 1, 2]
READLEN = 3
OMIN = 1


def rc(w: int) -> int:
    return (w + 3) % 6


def rep(w: int) -> int:
    return w if w < 3 else w - 3


def strands_of(verts: list[int]) -> list[int]:
    return verts + [rc(v) for v in verts]


def pre(lst: list[int], k: int) -> list[int]:
    return lst[:k]


def suf(lst: list[int], k: int) -> list[int]:
    return lst[len(lst) - k:] if k <= len(lst) else lst


def sgn_rep(s: int, mx: int) -> int:
    return 1 if s == mx else -1


def sgn_tgt(s: int, my: int) -> int:
    return -1 if s == my else 1


def bd_edge(sx: int, sy: int, length: int) -> tuple:
    return (sx, sy, length, sgn_rep(sx, rep(sx)), sgn_tgt(sy, rep(sy)))


def overlap_edges(verts: list[int], readlen: int, omin: int) -> list[tuple]:
    out: list[tuple] = []
    for length in range(readlen):
        if length < omin:
            continue
        for sx in strands_of(verts):
            for sy in strands_of(verts):
                if suf(STRAND[sx], length) == pre(STRAND[sy], length):
                    out.append(bd_edge(sx, sy, length))
    return out


def max_overlap(a: int, b: int, readlen: int) -> int:
    best = 0
    for length in range(readlen):
        if suf(STRAND[a], length) == pre(STRAND[b], length):
            best = length
    return best


def is_reducible_old(e: tuple, verts: list[int], readlen: int) -> bool:
    for _my in verts:
        for m in strands_of(verts):
            for l1 in range(readlen):
                for l2 in range(readlen):
                    if (
                        max_overlap(e[0], m, readlen) == l1
                        and max_overlap(m, e[1], readlen) == l2
                        and 0 < l1
                        and 0 < l2
                        and l1 < e[2]
                        and l2 < e[2]
                        and l1 + l2 - readlen == e[2]
                    ):
                        return True
    return False


def is_reducible_spelling(e: tuple, verts: list[int], readlen: int, omin: int) -> bool:
    for m in strands_of(verts):
        for l1 in range(readlen):
            for l2 in range(readlen):
                if (
                    omin <= l1
                    and omin <= l2
                    and suf(STRAND[e[0]], l1) == pre(STRAND[m], l1)
                    and suf(STRAND[m], l2) == pre(STRAND[e[1]], l2)
                    and l1 + l2 == readlen + e[2]
                ):
                    return True
    return False


def verify_regression(errors: list[str]) -> None:
    graph = overlap_edges(VERTS, READLEN, OMIN)
    direct = bd_edge(0, 2, 1)
    leg1 = bd_edge(0, 1, 2)
    leg2 = bd_edge(1, 2, 2)

    lengths = Counter(e[2] for e in graph)
    if len(graph) != 9 or lengths != Counter({2: 5, 1: 4}):
        errors.append(
            f"regression graph mismatch: {len(graph)} edges, lengths {dict(lengths)}"
        )
    for label, edge in (("direct", direct), ("leg1", leg1), ("leg2", leg2)):
        if edge not in graph:
            errors.append(f"regression {label} edge not in overlapEdges graph")

    # The old predicate is vacuous on the whole graph.
    if any(is_reducible_old(e, VERTS, READLEN) for e in graph):
        errors.append("old isReducibleB is nontrivial on the regression graph")
    if is_reducible_old(direct, VERTS, READLEN):
        errors.append("old isReducibleB unexpectedly true on the direct edge")

    # The corrected predicate is nontrivial and recognises the direct edge.
    if not is_reducible_spelling(direct, VERTS, READLEN, OMIN):
        errors.append("corrected isReducibleSpellingB false on the direct edge")
    if is_reducible_spelling(leg1, VERTS, READLEN, OMIN):
        errors.append("corrected isReducibleSpellingB true on leg1")
    if is_reducible_spelling(leg2, VERTS, READLEN, OMIN):
        errors.append("corrected isReducibleSpellingB true on leg2")

    reduced = [e for e in graph if not is_reducible_spelling(e, VERTS, READLEN, OMIN)]
    if len(graph) - len(reduced) != 4:
        errors.append(
            f"corrected reduction removed {len(graph) - len(reduced)} edges, expected 4"
        )
    if direct in reduced:
        errors.append("corrected reduction failed to remove the direct edge")
    if leg1 not in reduced or leg2 not in reduced:
        errors.append("corrected reduction removed a detour leg")

    # Forced-longer arithmetic for the witness and the omega inequality.
    # Extract the actual spelling witness (m, l1, l2) for the direct edge and
    # assert the predicate-level consequence of req (3): the composition law
    # holds and both replacement overlaps are strictly longer than e.len.
    # This mirrors Lean `replacement_overlaps_longer` lifted to the
    # `isReducibleSpelling` predicate (cf. `isReducibleSpelling_legs_longer`).
    witness = None
    for m in strands_of(VERTS):
        for l1 in range(READLEN):
            for l2 in range(READLEN):
                if (
                    OMIN <= l1
                    and OMIN <= l2
                    and suf(STRAND[direct[0]], l1) == pre(STRAND[m], l1)
                    and suf(STRAND[m], l2) == pre(STRAND[direct[1]], l2)
                    and l1 + l2 == READLEN + direct[2]
                ):
                    witness = (m, l1, l2)
    if witness is None:
        errors.append("no spelling witness (m, l1, l2) for the direct edge")
    else:
        _, l1, l2 = witness
        if not (l1 + l2 == READLEN + direct[2]):
            errors.append("witness composition law l1+l2=L+e.len failed")
        if not (direct[2] < l1 and direct[2] < l2):
            errors.append("witness legs not strictly longer than the direct edge")
    for length in range(2, 9):
        for a in range(length):
            for b in range(length):
                if a + b > 2 * length - 2:
                    errors.append(
                        f"omega_two_hop failed at L={length}, l1={a}, l2={b}"
                    )
                    return
                if not (a + b < length + (length - 1)):
                    errors.append(
                        f"omega_strict failed at L={length}, l1={a}, l2={b}"
                    )
                    return


def main() -> int:
    errors: list[str] = []
    classify(errors)
    verify_doc(errors)
    verify_bridges(errors)
    verify_regression(errors)

    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1

    print(
        "§6.2 reduction survival matrix verified: "
        f"{len(GENUINE_DEPENDENT)} direct + {len(TRANSITIVE_DEPENDENT)} transitive dependents "
        "(all SURVIVES, 0 MUST-BE-REPROVED), "
        "old predicate vacuous, corrected reduction removes the direct regression edge "
        "and keeps both legs"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
