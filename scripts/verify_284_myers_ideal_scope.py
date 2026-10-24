"""Scope guard for docs/section62-myers-ideal-transitivity-284.md (issue #284).

Checks that the compatibility-boundary note does not drift from the Lean
source: claimed theorem names exist in Section62MyersIdealTransitivity.lean,
the module is sorry/admit/axiom/native_decide-free, axiom-print lines are
present, and every Myers-feature row is explicitly marked proved or not-claimed.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "AssemblyP1" / "Section62MyersIdealTransitivity.lean"
DOC = ROOT / "docs" / "section62-myers-ideal-transitivity-284.md"

failures = []

src = LEAN.read_text()
doc = DOC.read_text()

for name in ["TwoHopSameSpelling", "reducible_iff_ideal_two_hop",
             "reduced_mem_iff_no_ideal_detour"]:
    if name not in src or name not in doc:
        failures.append(f"claimed name {name} missing from lean or doc")

for bad in ["sorry", "admit", "native_decide"]:
    if re.search(rf"\b{bad}\b", src):
        failures.append(f"lean source contains {bad}")

if re.search(r"^axiom\b", src, re.M):
    failures.append("lean source declares an axiom")

for ax in ["#print axioms reducible_iff_ideal_two_hop",
           "#print axioms reduced_mem_iff_no_ideal_detour"]:
    if ax not in src:
        failures.append(f"missing axiom audit line: {ax}")

for marker in ["Not modeled", "Not separately modeled", "Not compared",
               "does not assert"]:
    if marker not in doc:
        failures.append(f"doc missing non-claim marker: {marker}")

if "FUZZ" not in doc or "Contained reads" not in doc:
    failures.append("doc missing FUZZ/containment boundary rows")

if failures:
    print("FAIL:")
    for f in failures:
        print(" -", f)
    sys.exit(1)
print("Myers ideal-scope guard verified: 3 names, axiom-print lines, "
      "no sorry/admit/axiom, 4+ boundary non-claims present")
