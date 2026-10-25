# #265 active-scope and source-traceability audit

Status: 2026-10-25. Repository remote verified as
`https://github.com/ottojung/assemblyp1.git`; inspected from a clone with
`origin/main` at `234f348`. This is a bounded handoff, not a deck or paper
rewrite.

## Ownership and scope

- `docs/presentation-arc-265.md` records the 14-slide programmers' main arc,
  preserved #254 opening, backup placement, and existing caveats. The
  #254 12–14-slide request versus subsequent expanded deck is still a scope
  conflict; no deck changes are authorized by this audit.
- `docs/audit-265-claim-labels-2026-10-18.md` explicitly says the maintained
  decks are under live #265 work (#327/#335) and were not edited by that audit.
  The biologists' accessible-level omissions and MB09 §6.1/§6.2 naming are
  called out there; assigning those additions to a deck owner is safer than
  duplicating the current deck work.
- Remote refs include active-looking #265 branches for the iterated
  Bayes-value monotonicity, finite-read definition, theorem matrix, deck arc,
  and worked example (`cja4...`, `cmLc...`, `Xnc...`, `xK7...`, and
  `issue265-20261023-*`). These refs establish overlap risk, not that board
  owners or latest comments have been verified.

## One additive gap for the next integration pass

`docs/verification.md`'s row “Finite-family Hellinger union bound” points to
`AssemblyP1/FiniteReadRecovery.lean` (`eventProb_pairwise`,
`eventProb_wrong_le_sum`, `eventProb_wrong_tendsto_zero`). The stronger exact
bridge used in the paper's `cor:p2-finite-recovery` at
`paper/sections/05-population.tex` lines 389–456 is not currently indexed as a
single claim-to-endpoint entry. Exact names checked in the present source are:

- `AssemblyP1/FiniteReadRecoveryP2Bridge.lean`:
  `circularReadPMF_eq_popSpectrum`, `equal_read_laws_imply_rotation`,
  `hellinger_lt_one_of_primitiveP2_not_rotation`,
  `finite_primitiveP2_family_affinity_gap`,
  `finite_primitiveP2_family_confidence`;
- `AssemblyP1/FiniteReadRecoveryP2Complete.lean`:
  `equal_laws_imply_rotation_of_primitiveP2`,
  `hellinger_lt_one_of_primitiveP2_not_rotation`,
  `finite_primitiveP2_family_uniform_affinity`,
  `finite_primitiveP2_ML_confidence`.

Suggested bounded follow-up: add an index row linked to the paper corollary
and both modules, stating the actual domain precisely: oriented circular
reads, independent uniform starts, error-free length `L >= 2`, primitive P2
truth, primitive P2-admissible nonrotational competitors; the whole class is
finite by `thm:p2-finite-class`/`PrimitiveP2FiniteClass`, but the exponential
bound is not a characterization of exact finite-sample maximizers. Ties are
counted as errors. Keep the existing generic finite-family theorem and this
structural specialization distinct. This is documentation-only and does not
upgrade external strong-law/KL consistency or MB09 objectives to Lean claims.

No source or slide edit was made: the claim can be added safely as a discrete
verification-index update by the integration owner after the overlapping
branch/checkpoint status is reconciled.

## Validation and access attempts

- `python3 scripts/check-research-docs.py` — passed after adding this note.
- `python3 scripts/verify_exponent_265.py` — passed (existing finite
  separation/exponent checks; not a check of the endpoint mapping above).
- `git fetch origin` — succeeded; verified repository remote and branch refs.
- `gh issue view 265 --repo ottojung/assemblyp1 --comments` and
  `gh api repos/ottojung/assemblyp1/issues/265/comments` — unavailable because
  `gh` is not installed. Therefore newest board comments and live issue owners
  could not be confirmed, and no board checkpoint/terminal-handoff comment was
  posted from this invocation.
