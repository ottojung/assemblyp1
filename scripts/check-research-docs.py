#!/usr/bin/env python3
"""Cheap, deterministic integrity checks for assemblyp1 research documentation."""

from __future__ import annotations

import re
import sys
from pathlib import Path
from urllib.parse import unquote

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = [
    "AGENTS.md",
    "README.md",
    "docs/open-problem.md",
    "docs/formalization-plan.md",
    "docs/research-orchestration.md",
    "docs/skills/README.md",
    "docs/skills/research-orchestrator.md",
    "docs/skills/literature-search.md",
    "docs/skills/formalization.md",
    "docs/skills/proof-search.md",
    "docs/skills/counterexample-search.md",
    "docs/skills/reconciliation.md",
]

MARKDOWN_LINK = re.compile(r"\[[^\]]*\]\(([^)]+)\)")
CONFLICT_MARKER = re.compile(r"^(?:<<<<<<<|=======|>>>>>>>)", re.MULTILINE)


def fail(message: str, errors: list[str]) -> None:
    errors.append(message)


def check_required(errors: list[str]) -> None:
    for relative in REQUIRED:
        if not (ROOT / relative).exists():
            fail(f"missing required research file: {relative}", errors)


def check_skill_index(errors: list[str]) -> None:
    index_path = ROOT / "docs/skills/README.md"
    if not index_path.exists():
        return
    index = index_path.read_text(encoding="utf-8")
    for skill in sorted((ROOT / "docs/skills").glob("*.md")):
        if skill.name == "README.md":
            continue
        if skill.name not in index:
            fail(f"docs/skills/README.md does not list {skill.name}", errors)


def check_markdown(errors: list[str]) -> None:
    markdown_files = [ROOT / "README.md", ROOT / "AGENTS.md"]
    markdown_files.extend(sorted((ROOT / "docs").rglob("*.md")))

    for path in markdown_files:
        if not path.exists():
            continue
        text = path.read_text(encoding="utf-8")
        rel = path.relative_to(ROOT)

        if CONFLICT_MARKER.search(text):
            fail(f"merge-conflict marker in {rel}", errors)

        for match in MARKDOWN_LINK.finditer(text):
            raw_target = match.group(1).strip()
            if not raw_target or raw_target.startswith("#"):
                continue
            if raw_target.startswith(("http://", "https://", "mailto:")):
                continue

            target = unquote(raw_target.split("#", 1)[0].split("?", 1)[0])
            if not target:
                continue
            resolved = (path.parent / target).resolve()
            try:
                resolved.relative_to(ROOT)
            except ValueError:
                fail(f"local link escapes repository in {rel}: {raw_target}", errors)
                continue
            if not resolved.exists():
                fail(f"broken local link in {rel}: {raw_target}", errors)


def main() -> int:
    errors: list[str] = []
    check_required(errors)
    check_skill_index(errors)
    check_markdown(errors)

    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1

    print("research documentation integrity checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
