"""Contained-read boundary guard for docs/section62-myers-ideal-transitivity-284.md.

Issue #284 delegated increment (agent robinson): independently confirm ONE
Myers 2005 scope claim from inspectable source plus ONE survival-matrix entry
re-evaluation, without touching Lean sources or duplicating the prior
verify_284_myers_ideal_scope.py guard.

Claim under test (from the doc's compatibility-boundary table):
  "Contained reads ... Not separately modeled: every formal vertex is a
  fixed-length observed read and every edge is a proper overlap."

Checks (all against files already in this checkout, no network):
 1. The boundary doc contains the "Contained reads" row with a non-claim
    marker ("Not separately modeled").
 2. The Lean ideal-transitivity module only models proper overlaps:
    TwoHopSameSpelling requires l1 < L, l2 < L and the iff theorem requires
    e.len < L; no containment predicate is defined there.
 3. Survival-matrix entry re-evaluation: Section62NonSpelledFlow.lean:584
    still references an old-model identifier (graph_reduction_vacuous_literal
    region) and the corrected bridge nonspelled_reduction_spelling_eq exists
    in Section62ReductionDependencyAudit.lean, so the SURVIVES verdict for
    the non-spelled-flow dependent stands.

Exit 0 iff every assertion holds.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "AssemblyP1" / "Section62MyersIdealTransitivity.lean"
DOC = ROOT / "docs" / "section62-myers-ideal-transitivity-284.md"
FLOW = ROOT / "AssemblyP1" / "Section62NonSpelledFlow.lean"
BRIDGE = ROOT / "AssemblyP1" / "Section62ReductionDependencyAudit.lean"

failures = []

doc = DOC.read_text()
src = LEAN.read_text()

# 1. Doc boundary row present and explicitly a non-claim.
if "Contained reads" not in doc:
    failures.append("doc missing 'Contained reads' boundary row")
if "Not separately modeled" not in doc:
    failures.append("doc missing 'Not separately modeled' non-claim marker")

# 2. Lean module models proper overlaps only.
for snippet in ["l1 < L", "l2 < L", "e.len < L"]:
    if snippet not in src:
        failures.append(f"lean ideal module missing proper-overlap guard: {snippet}")
if re.search(r"\bcontained\b", src, re.I):
    # The module docstring mentions containment only to exclude it; a real
    # containment definition would introduce identifiers like these.
    if re.search(r"\b(?:def|abbrev|theorem|lemma)\s+\w*[Cc]ontain", src):
        failures.append("lean ideal module defines containment (scope drift)")

# 3. Survival-matrix entry: non-spelled-flow SURVIVES re-evaluation.
flow_lines = FLOW.read_text().split("\n")
if len(flow_lines) < 584:
    failures.append("Section62NonSpelledFlow.lean shorter than cited line 584")
else:
    window = "\n".join(flow_lines[570:595])
    if not re.search(r"\bisReducibleB\b|\btransitivelyReduced\b|\bReductionVacuous\b", window):
        failures.append("cited Section62NonSpelledFlow.lean:584 window lacks old identifier")
bridge = BRIDGE.read_text()
if "nonspelled_reduction_spelling_eq" not in bridge:
    failures.append("corrected bridge nonspelled_reduction_spelling_eq missing")

if failures:
    print("FAIL:")
    for f in failures:
        print(" -", f)
    sys.exit(1)
print("Myers contained-read boundary verified: doc non-claim present, "
      "ideal module proper-overlap-only, "
      "Section62NonSpelledFlow:584 SURVIVES with corrected bridge present")
