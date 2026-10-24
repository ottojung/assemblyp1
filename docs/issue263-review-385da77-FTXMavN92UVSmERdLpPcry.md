# Independent review: issue #263 verifier commit 385da77

Reviewer: agent-FTXMavN92UVSmERdLpPcry-window. Verdict: **APPROVE**.
Keep #263 open for the general T-sign-compatible decomposition and the
direct #261 historical adapter, both explicitly out of scope here.

## Scope correction (supersedes part of the FGE review note)

Commit `385da77f6c28f8d6d4e3cdf33544d9b0c3cad751` is **not** an ancestor of
`origin/main` (`234f3480d7589c8fc4e056c91dda91343fe64ece`): it is a single
child commit on top of it on branch
`origin/agent/eTDw1U608NhbFNXrqX11nA-issue263-bridge-verifier`
(`git merge-base --is-ancestor 385da77 HEAD` exits 1; `git merge-base`
returns HEAD itself; `git diff --stat 234f348 385da77` shows only the two new
files below, zero `.lean` changes). The verifier script is therefore present
only on that branch, not on `origin/main`.

## What was independently re-verified at exact commit 385da77

* `python3 scripts/verify_263_graver_throughput_bridge.py` — PASS:
  125 flows (`BOX = range(-2, 3)`, `5^3`), conformal decomposition
  `delta=(3, 3, -6) = (1, 1, -2) + (2, 2, -4)`, zero-T lift and augmented-kernel
  checks all pass.
* `scripts/verify_263_graver_throughput_bridge.py:1-93` — the module docstring
  (lines 1-24) accurately bounds the claims to `flowLin_eq_zero_iff`
  (`AssemblyP1/GraverThroughputBridge.lean:127`) and the vanishing-T mechanism
  of `hasGraverDecomposition_aug` (`GraverThroughputBridge.lean:364`, whose
  hypothesis `hT : ∀ g, Graver ... → T g = 0` at line 366 is exactly the
  vanishing case). It explicitly disclaims the genuine vertex-throughput lift,
  consistent with `scripts/verify_263_throughput_sign_clash.py`.
* `docs/issue263-graver-throughput-bridge.md` section added by 385da77 —
  accurately describes the `5^3` exhaustive check and the lifted decomposition
  `(3, 3, -6, 0, 0)`; asserts nothing beyond the vanishing case.
* `grep -rnw -E "sorry|admit|axiom"` over `SeparableConvexGraver.lean`,
  `GraverThroughputBridge.lean`, `ExactMLOptimizerTransfer.lean`,
  `ExactMLOptimizerTransferAudit.lean` — clean (single hit is the English
  sentence "No `sorry`, `admit`, `axiom`" in
  `ExactMLOptimizerTransfer.lean:34`).
* `python3 scripts/check-research-docs.py` — PASS ("research documentation
  integrity checks passed").
* Lean build: no fresh `lake build` in this invocation (no warm `.lake`
  cache; full Mathlib fetch infeasible here). This is covered by evidence:
  the 385da77 diff touches zero `.lean` files, and the exact-head build at
  `234f348` was verified PASS (8928 jobs, 18 audit endpoints all
  `{propext, Classical.choice, Quot.sound}`) per the ETBMh board handoff.
* Exact-head CI status: `gh` is unavailable in this environment, so remote CI
  runs could not be listed; no CI claim is made here.
* `git show -s --format=%G? 385da77` reports `U` locally (key
  `1BEDDF96D7B1BA2B` not in the local keyring); GitHub-side signature status
  was not queried from here.

## Non-blocking observation

The checked conformal decomposition uses `g2 = 2 * g1`
(`scripts/verify_263_graver_throughput_bridge.py:63-64`), i.e. collinear
moves, so conformality is trivial. Valid for the vanishing-T mechanism check,
but a future strengthening could use linearly independent conformal moves.

## Verdict

APPROVE — merge the eTDw bridge-verifier branch at reviewer discretion. No new
theorems added by this note. General T-sign-compatible decomposition and the
direct #261 historical adapter remain OPEN.
