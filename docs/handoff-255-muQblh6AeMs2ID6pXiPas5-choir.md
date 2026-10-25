# Issue #255 order-audit increment handoff

Owner: `agent-muQblh6AeMs2ID6pXiPas5-choir`  
Repository: <https://github.com/ottojung/assemblyp1>  
Branch: `agent/muQblh6AeMs2ID6pXiPas5-choir-issue255-order-audit`  
Commit: `2f6e13013bfe76b3336a97d1c59c51fa238daebb`

## Verification and bounded increment

- Confirmed `origin/main` at `234f3480d7589c8fc4e056c91dda91343fe64ece`.
- Confirmed prior requested audit commit
  `48447f5d17f7fe4060da23953bddc1025ba5d1ad` exists on remote branch
  `agent/fjENb66W46rKYjne8Cc38x-staples-issue255-order-audit` and is an
  ancestor of that remote branch. It is not an ancestor of current `main`.
- Re-ran the exact-rational verifier from that commit: PASS (`x=(2,1,1)`,
  coefficient 12; expected maximizing and minimizing candidate sets).
- Re-ran `scripts/verify_feasible_spectrum_ml_255.py`: PASS, including its
  974 truth/sample cases and the explicit report of 158 outside-spelled-class
  higher-likelihood cases.
- Extended the historical exact-rational order-transform verifier with
  fixed-`x` multinomial-coefficient cancellation checks for all 25 ordered
  pairs in its five-candidate example, including the zero-likelihood
  candidate. Exact coefficient-free scores preserve both argmax and argmin.
- `scripts/check-research-docs.py`, `git diff --check`, `git verify-commit
  HEAD`, and `scripts/verify_signed_commits.py --repo . --base origin/main
  --head HEAD`: PASS. No Lean axiom audit was applicable to this Python-only
  increment; the historical Lean audit module is not present on current main.

This is a bounded algebraic verifier increment, not a structural
characterization of when truth maximizes likelihood. The witness is not
claimed as proof of a general theorem. Child #258/#259/#261 scopes and all
broader classification cells remain outside this artifact; umbrella #255
remains OPEN.

## Suggested continuation

Review the exact-head verifier change. If the order-transform Lean module from
the verified prior commit is considered for integration, first reconcile its
branch against current `main`, validate the Lean module and root import, and
run its axiom audit/CI at that exact head. Continue the open matrix without
promoting this finite example to a universal claim.
