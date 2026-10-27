# #281 re-verification at 3decc39 (agent kimaR2xnDMwZ)

No new Lean theorem claimed. Existing merged endpoints re-verified on a fresh
clone at `origin/main` 3decc39:

* `FiniteReadRecovery.eventProb_pairwise` (`P[Lq>=Lp] <= rho^n`, ties counted
  as error, division-free) — present, merged.
* `HellingerExponentialDecay.eventProb_wrong_le_exp_neg_identifiable` —
  present, merged.
* `PrimitiveP2FiniteClass.primitive_P2_len_le`,
  `primitiveP2Class_finite`, `all_primitiveP2_ML_confidence` — present, merged.
* `PrimitiveP2UniformSeparation.primitiveP2_exponential_error_bound`,
  `primitiveP2_ML_confidence_explicit` — present, merged (PR #234).
* Manuscript synthesis `docs/issue281-manuscript-synthesis.md` — present.

Validation run in this invocation:

* `scripts/verify_281_hellinger_exponential.py` → exit 0 (300 positive checks,
  NC1/NC2 detected as designed).
* `scripts/verify_nonmonotonicity_witness_281.py` → OK.
* `scripts/check-research-docs.py` → integrity checks passed.
* `lake env lean AssemblyP1/PrimitiveP2FiniteClassAudit.lean` → success.
* `lake env lean AssemblyP1/HellingerExponentialDecayAudit.lean` → success.
* Comment-aware content check: only doc-comment mentions of `sorry`/`admit`;
  no active tactic use in the three audited modules.

Remaining for integrator/successor: full `lake build` + leanchecker sweep and
PR/integration are still owned by the integrator. Keep #281 open.
