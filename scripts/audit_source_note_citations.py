#!/usr/bin/env python3
"""Citation-provenance audit for docs/source-notes (issue #208 front).

The markdown-link checker in `scripts/check-research-docs.py` only sees
`[text](target)` links.  Source notes are more often cited as code spans
(`docs/source-notes/<name>.md`), which that checker cannot see, and a
code-span citation can be *labelled* as an unmerged-branch artifact while the
branch or commit locator printed beside it no longer resolves.  Both defects
have occurred in this repository: the first is recorded in
`docs/source-notes/finite-interpretation-universe-audit.md` §6 item 7 (two
notes referenced by live documentation were absent), the second in the same
register's item 8 (one labelled citation whose branch and commit locator do
not resolve).

This script measures, for the tracked working tree:

* **resolving** citations - the cited note exists;
* **labelled-unmerged** citations - the cited note is absent, but the citing
  paragraph says so and names a locator;
* **dead locator** - the citing paragraph says "unmerged branch artifact" but
  the branch it names does not exist on `origin`, or a commit token printed
  beside it is not a valid object in this repository.

Exits non-zero if a citation is neither resolving nor labelled, or if a
labelled citation carries a locator that does not resolve.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CITATION = re.compile(r"`(?:docs/)?source-notes/([A-Za-z0-9._-]+\.md)`")
BRANCH = re.compile(r"`((?:analysis|audit|research|source|board|front|"
                    r"integrate|integration|proof|reconcile|review|validate)/"
                    r"[A-Za-z0-9._/-]+)`")
COMMIT = re.compile(r"`([0-9a-f]{7,40})`")
LABEL = re.compile(r"unmerged[- ]branch", re.I)
# A paragraph that states a locator does not resolve is an audit register
# entry, not a citation that relies on the locator.
DEFECT = re.compile(r"does not resolve|do not resolve|no longer resolves|"
                    r"not on origin|not a valid object|dead (citation )?locator|"
                    r"unverifiable citation", re.I)


def run(args: list[str]) -> str:
    return subprocess.run(args, cwd=ROOT, capture_output=True,
                          text=True).stdout.strip()


def remote_branches() -> set[str]:
    try:
        out = run(["git", "ls-remote", "origin"])
    except Exception:
        return set()
    names = set()
    for line in out.splitlines():
        if "\t" in line:
            names.add(line.split("\t", 1)[1].replace("refs/heads/", "", 1))
    return names


def objects_present(tokens: list[str]) -> dict[str, bool]:
    out = {}
    for token in tokens:
        res = subprocess.run(["git", "cat-file", "-t", token], cwd=ROOT,
                             capture_output=True, text=True)
        out[token] = res.returncode == 0
    return out


def main() -> int:
    notes = {p.name for p in (ROOT / "docs/source-notes").glob("*.md")}
    md_files = [ROOT / "AGENTS.md", ROOT / "README.md"]
    md_files.extend(sorted((ROOT / "docs").rglob("*.md")))

    resolving, labelled, unlabelled, dead, reported = {}, {}, [], [], []
    for path in md_files:
        text = path.read_text(encoding="utf-8")
        for paragraph in text.split("\n\n"):
            names = CITATION.findall(paragraph)
            if not names:
                continue
            rel = path.relative_to(ROOT)
            for name in names:
                if name in notes:
                    resolving.setdefault(name, set()).add(str(rel))
                    continue
                if not LABEL.search(paragraph):
                    unlabelled.append((str(rel), name))
                    continue
                labelled.setdefault(name, set()).add(str(rel))
                # A paragraph that *records* a dead locator (an audit gap
                # register) is not a citation that claims the locator resolves,
                # so its tokens are reported rather than failed.
                records_defect = bool(DEFECT.search(paragraph))
                # A paragraph may cite several absent notes, each with its own
                # locator, so attribute each branch/commit token to the nearest
                # citation: the text from this citation to the next one.
                spans = []
                for match in CITATION.finditer(paragraph):
                    spans.append((match.group(1), match.start()))
                spans.append((None, len(paragraph)))
                for (who, start), (_, end) in zip(spans, spans[1:]):
                    if who is None:
                        continue
                    region = paragraph[start:end]
                    known = remote_branches()
                    for branch in [b for b in BRANCH.findall(region)
                                   if not b.endswith(".md")]:
                        if known and branch not in known:
                            entry = (str(rel), who,
                                     f"branch {branch} not on origin")
                            (reported if records_defect else dead).append(entry)
                    for commit, ok in objects_present(COMMIT.findall(region)).items():
                        if not ok:
                            entry = (str(rel), who,
                                     f"commit {commit} not a valid object")
                            (reported if records_defect else dead).append(entry)

    print(f"source-note citations: {sum(len(v) for v in resolving.values())} resolving "
          f"across {len(resolving)} distinct notes")
    for name in sorted(labelled):
        print(f"  labelled unmerged-branch artifact: {name} "
              f"(cited by {sorted(labelled[name])})")
    for where, name in sorted(set(unlabelled)):
        print(f"  ERROR: {name} cited by {where} is absent and not labelled "
              f"as an unmerged-branch artifact")
    for where, name, why in sorted(set(reported)):
        print(f"  recorded dead locator (audit register): {name} cited by "
              f"{where}: {why}")
    for where, name, why in sorted(set(dead)):
        print(f"  ERROR: {name} cited by {where}: {why}")

    if unlabelled or dead:
        # The current failure is the recorded defect of
        # `docs/source-notes/finite-interpretation-universe-audit.md` §6 item 8
        # (the locator of `se62-revcomp-index-decision.md` does not resolve);
        # it is reported, not repaired, because that note belongs to another
        # front.  Exiting non-zero is the intended signal while it stands.
        print("source-note citation audit FAILED "
              "(see the recorded gap and repair, or remove, the locator)")
        return 1
    print("source-note citation audit passed "
          "(absent notes are labelled, and their locators resolve)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
