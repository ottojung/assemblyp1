# #281 — generic Hellinger-affinity exponential decay of exact-ML error

Owner: agent-9a6b4f56d494. Repository: `ottojung/assemblyp1`.

## What was missing on `main`

The merged work already kernel-checks the **concrete sum-of-powers** form and a
**primitive-P2-specific** exponential form:

| Statement | Where on `main` |
| --- | --- |
| `P_p[L_q ≥ L_p] ≤ ρ(p,q)^n` (pairwise) | `AssemblyP1/FiniteReadRecovery.lean:247` `eventProb_pairwise` |
| `P_p[∃ q ∈ Θ : L_q ≥ L_p] ≤ Σ_q ρ(p,q)^n` | `AssemblyP1/FiniteReadRecovery.lean:309` `eventProb_wrong_le_sum`; `AssemblyP1/FiniteReadRecoveryGenome.lean:103` `circular_wrong_le_sum` |
| `≤ |Θ| · ρ_max^n` (uniform affinity) | `AssemblyP1/FiniteReadRecovery.lean:352` `eventProb_wrong_le_card`; `AssemblyP1/FiniteReadRecoveryGenome.lean:128` `circular_wrong_le_card` |
| primitive-P2 `N_C · exp(-n/(8B^4))`, `B = 2q^(L-1)` | `AssemblyP1/PrimitiveP2UniformSeparation.lean:317` `primitiveP2_exponential_error_bound`; paper `paper/sections/05-population.tex:562` `thm:p2-uniform-rate` |

What was **absent** is the *generic* Hellinger-affinity contraction step that
converts the merged `|Θ| · ρ_max^n` endpoint into the issue's exponential form
`|Θ| · exp(-c n)` with rate `c = -log ρ_max > 0`, together with the corresponding
finite-family exponential theorem under identifiability. The only `exp`
conversion present on `main` is the primitive-P2-specific
`Real.one_sub_le_exp_neg` step inside
`AssemblyP1/PrimitiveP2UniformSeparation.lean:267` (`exp_error_bound_of_length_bound`),
which is not a general `ρ^n = exp(-n·(-log ρ))` bridge.

## The increment

New module `AssemblyP1/HellingerExponentialDecay.lean`, reusing the merged
`FiniteReadRecovery` endpoints (no reproof of them):

* `hellinger_pow_eq_exp_neg` — the contraction step
  `ρ ^ n = exp (-(n : ℝ) * (- log ρ))` for `0 < ρ < 1`.
* `hellinger_pow_le_exp_neg` — its inequality form.
* `eventProb_wrong_le_exp_neg` — generic finite-family exponential bound
  `eventProb p n (wrongEvent p Θ n) ≤ |Θ| · exp (-n · (-log ρ_max))`, assuming
  `0 < ρ_max < 1` and `∀ q ∈ Θ, hellinger p q ≤ ρ_max`.
* `exists_uniform_affinity_lt_one` — under pairwise identifiability
  (`∀ q ∈ Θ, p ≠ q`) a uniform strictly-sub-unit `ρ_max` exists (empty family
  handled separately).
* `eventProb_wrong_le_exp_neg_identifiable` — the issue's target form: under
  identifiability there is a strictly positive rate `c` with
  `eventProb p n (wrongEvent p Θ n) ≤ |Θ| · exp (-n · c)`. The degenerate
  `ρ_max = 0` (disjoint supports) case is handled separately.

No `axiom`, `sorry`, `admit` or `native_decide`; the axiom audit
(`AssemblyP1/HellingerExponentialDecayAudit.lean`) reports only `propext`,
`Classical.choice`, `Quot.sound`.

## Verification

* `python3 scripts/verify_281_hellinger_exponential.py` — exit 0. Exact
  enumeration over finite read universes checks the affinity-sum, sum-of-powers
  and exponential forms for random families and every `n ≤ 4`, plus the
  contraction step. Two negative controls are *detected*:
  * **NC1 (identifiability necessary):** `Θ = {p}` gives error probability `1`,
    which exceeds `|Θ|·exp(-c n)` for any `c > 0` at large `n`.
  * **NC2 (uniform affinity necessary):** using `ρ_wrong = 0.4 < ρ_max ≈ 0.894`
    makes `|Θ|·ρ_wrong^n` fall below the true error probability.
* `python3 scripts/check-research-docs.py` — exit 0.
* `lake build --wfail` — full library.
* `lake env leanchecker AssemblyP1` — whole-library kernel replay.
* axiom-audit `--allow propext,Classical.choice,Quot.sound --root AssemblyP1
  --modules-from AssemblyP1` — green.

**CI-wiring limitation (honest):** the author's push token lacks the GitHub
`workflow` scope, so this increment cannot itself add the verifier to
`.github/workflows/ci.yml`. The verifier is committed and runnable; a reviewer
or integrator with `workflow` scope should add the step

```
      - name: Verify #281 generic Hellinger-affinity exponential decay
        run: python3 scripts/verify_281_hellinger_exponential.py
```

to the `research-docs` job of `.github/workflows/ci.yml`. Until then the
verifier's CI execution is the remaining integration obligation.

## Scope and remaining limits

* The generic lemma is stated for a finite family of **read distributions**
  (`IsPmf`), not for a genome-indexed family. Instantiating it at the genome
  level goes through `FiniteReadRecoveryGenome.circular_wrong_le_card`; the
  primitive-P2 instantiation with the explicit constant `1/(8B^4)` remains the
  sharper, already-merged `primitiveP2_exponential_error_bound`.
* The rate `c = -log ρ_max` is the worst-case affinity over the family; it is
  not an efficient or tight rate.
* The bound concerns the **error probability** (ties included), not likelihood
  growth, and does **not** assert monotone success in `n`.
* This module does not touch the manuscript; no existing paper claim is
  affected, so no paper-text edit is required by the delegated task.

## Addendum (agent-aRUSubXQn5b7EiR9ANbr47-hepburn): disjoint-support cell

* `eventProb_wrong_eq_zero_of_affinity_zero` in
  `AssemblyP1/HellingerExponentialDecay.lean`: when every competitor has
  `hellinger p q ≤ 0` (hence `= 0`, disjoint supports) and `0 < n`, the exact
  wrong-selection probability is `0`. Proof reuses the merged
  `eventProb_wrong_le_card` at `ρ_max = 0` plus `zero_pow` and
  `eventProb_wrong_nonneg`; no new axioms, no definition changes.
* Status: source-level proof reviewed against `FiniteReadRecovery.lean:297,352`;
  comment-aware `sorry/admit/axiom` grep clean (only a prose mention of "axiom"
  in the module docstring); `scripts/verify_281_hellinger_exponential.py`
  passes. Full `lake build` of the two Hellinger modules was started from a
  cold cache (deps only, no oleans) and is still running at commit time —
  kernel check pending, NOT claimed.
