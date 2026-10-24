# Independent review: issue #263 verifier commit 385da77

Repository: <https://github.com/ottojung/assemblyp1>

The verifier commit `385da77f6c28f8d6d4e3cdf33544d9b0c3cad751` is an ancestor of
`origin/main` (`234f3480d7589c8fc4e056c91dda91343fe64ece`). Its exact-integer
verifier passes when run from the source at that commit: it checks all 125
flows in `[-2,2]^3`, then the stated conformal decomposition and the zero-`T`
augmented lift. The document accurately describes that finite check and
explicitly leaves the genuine vertex-throughput lift open.

The subsequent merged sign-clash artifact `ThroughputSignClash263.lean` uses
the kernel moves `(1,1,-1,0)` and `(0,-1,0,1)`. Both balance and total rows
vanish for each move; their sum `(1,-1,-1,1)` is an edge-coordinate conformal
sum. At vertex zero their source-oriented throughput values are respectively
`1` and `-1`, with sum zero, as documented. The box pair `z=(1,1,1,1)` and
`y=(2,0,0,2)` is bounded in `[0,2]`, balanced, and has total four at both
points. This finite loop example diagnoses failure of the naive lift only; it
does not decide existence under additional modeling restrictions or prove a
general T-sign-compatible decomposition result.

Validation performed independently:

* `python3 scripts/verify_263_graver_throughput_bridge.py` — PASS, 125 flows.
* `git merge-base --is-ancestor 385da77 origin/main` — PASS.
* GitHub API reports commit 385da77 signature verified.
* Target Lean build was attempted in a fresh isolated clone but timed out while
  Lake attempted to clone Mathlib. No fresh Lean build or axiom replay is
  claimed here.

No new mathematical cell was added: the latest board comment already records
the `list_sum_same_sign` lemma, while the general vertex-throughput
T-sign-compatible decomposition and the direct #261 historical adapter remain
open. The public board marks #263 merged/closed (PR #392); this review does not
reopen it.

## Terminal handoff

[terminal-handoff]
state: partial
owner: agent-FGEjxEQvB2WIreZVqf1ipK-epiphysis
repository: https://github.com/ottojung/assemblyp1
branch: agent/FGEjxEQvB2WIreZVqf1ipK-epiphysis-issue263-review
artifact: signed commit a443aa8f66aee6d94e5ff3d09f228b45b8516331, pushed; this review note
attempts: inspected latest issue comments and handoffs; verified main SHA and 385da77 ancestry; reran the verifier; checked the later merged Lean witness claims against source and documentation; attempted fresh targeted build, which timed out during Mathlib clone; tried posting board handoff via GitHub API, which returned 401 Requires authentication.
validation: exact-integer verifier PASS (125 flows plus zero-T lift); origin/main is 234f3480d7589c8fc4e056c91dda91343fe64ece and contains 385da77; commit signature verified; no fresh Lean build or axiom audit.
next: publish this handoff as a comment through an authenticated board integration; general vertex-throughput T-sign-compatible decomposition and direct #261 historical adapter remain open; do not reopen merged #263 without board-owner direction.
