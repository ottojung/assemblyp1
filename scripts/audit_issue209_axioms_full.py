#!/usr/bin/env python3
"""Generate a `#print axioms` sweep over EVERY theorem of the five modules that
issue #209 is responsible for, and check that each depends only on the three
permitted axioms.

Usage: python3 scripts/audit_issue209_axioms_full.py [--write FILE]

The theorem names are recovered from the sources with a small namespace-stack
parser (Lean 4 `namespace`/`end`), so the generated sweep cannot drift away
from the modules: add or remove a theorem and re-running regenerates the list.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

MODULES = [
    "AssemblyP1/SourceFaithfulIs.lean",
    "AssemblyP1/ExactVariantECounterexample.lean",
    "AssemblyP1/FixedLengthExactCounterexample.lean",
    "AssemblyP1/FixedLengthBinomialCounterexample.lean",
    "AssemblyP1/Issue209EAudit.lean",
]

PERMITTED = {"propext", "Classical.choice", "Quot.sound"}

NS_OPEN = re.compile(r"^namespace\s+([A-Za-z0-9_.]+)")
NS_CLOSE = re.compile(r"^end\s+([A-Za-z0-9_.]+)")
THEOREM = re.compile(r"^(?:protected\s+|private\s+|noncomputable\s+)*theorem\s+"
                     r"([^\s{[(]+)")


def theorems_of(path: Path):
    """Yield the fully-qualified name of every theorem in `path`."""
    stack = []
    names = []
    for line in path.read_text(encoding="utf-8").splitlines():
        m = NS_OPEN.match(line)
        if m:
            stack.append(m.group(1))
            continue
        m = NS_CLOSE.match(line)
        if m:
            if stack and stack[-1] == m.group(1):
                stack.pop()
            continue
        m = THEOREM.match(line)
        if m:
            head = ".".join(stack)
            name = m.group(1)
            names.append(head + "." + name if head else name)
    return names


def main() -> int:
    entries = []
    for rel in MODULES:
        path = ROOT / rel
        for name in theorems_of(path):
            entries.append((rel, name))
    print("found %d theorems in %d modules" % (len(entries), len(MODULES)))
    for rel, name in entries:
        print("  %-46s %s" % (name, rel))

    body = "\n".join(
        "import AssemblyP1.%s" % Path(rel).stem for rel in MODULES
    )
    body += "\n\n" + "\n".join("#print axioms %s" % name
                               for _rel, name in entries) + "\n"
    out = ROOT / "scratch-209" / "axioms-full.lean"
    if "--write" in sys.argv:
        out.write_text(body, encoding="utf-8")
        print("wrote %s" % out.relative_to(ROOT))

    proc = subprocess.run(
        ["lake", "env", "lean", str(out)],
        cwd=str(ROOT), capture_output=True, text=True,
    )
    text = proc.stdout + proc.stderr
    seen = {}
    for m in re.finditer(r"'(.+?)' depends on axioms: \[([^\]]*)\]", text):
        seen[m.group(1)] = {a.strip() for a in m.group(2).split(",") if a.strip()}
    # Lean reports "does not depend on any axioms" for the predicate-logic-only
    # lemmas; that is a strictly stronger result than the permitted three.
    for m in re.finditer(r"'(.+?)' does not depend on any axioms", text):
        seen[m.group(1)] = set()
    bad = {k: v for k, v in seen.items() if not v <= PERMITTED}
    missing = [n for _r, n in entries if n not in seen]
    print("\nreported %d / %d theorems" % (len(seen), len(entries)))
    print("  axiom-free: %d" % sum(1 for v in seen.values() if not v))
    print("  on the permitted three: %d"
          % sum(1 for v in seen.values() if v == PERMITTED))
    if missing:
        print("NO AXIOM REPORT (check the name): %s" % missing)
    if bad:
        print("AXIOM SURFACE NOT INSIDE %s:" % sorted(PERMITTED))
        for k, v in sorted(bad.items()):
            print("  %s -> %s" % (k, sorted(v)))
        return 1
    print("all %d reported theorems have an axiom surface inside %s"
          % (len(seen), sorted(PERMITTED)))
    return 0 if not missing else 2


if __name__ == "__main__":
    raise SystemExit(main())
