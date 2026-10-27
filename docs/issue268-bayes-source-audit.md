# Issue #268: finite Bayes theorem source audit

This note records an exact source-level audit of the manuscript's finite
Bayes/MAP headline. It is a citation and qualification aid for #265's active
manuscript integration, not a competing edit to the paper or slides.

## Verified Lean endpoint

In `AssemblyP1/FiniteBayesDecision.lean`:

- `pointwise_MAP_optimal` (lines 34--40) proves deterministic optimality for
  finite `Theta` and `X` when the selected rule pointwise maximizes the joint
  mass `J theta x`.
- `pointwise_MAP_optimal_randomized` (lines 42--64) proves the corresponding
  result for nonnegative, normalized decision weights.
- `chooseMAP_optimal` and `chooseMAP_optimal_randomized` (lines 84--97)
  instantiate those results for a finite, nonempty hypothesis universe and
  arbitrary real joint scores; no probability normalization is required by
  these algebraic endpoints.
- `finite_iid_MAP_optimal` (lines 135--147) instantiates deterministic
  optimality for iid product scores `pi theta * prod_i p theta (x i)` at every
  `n`, including zero, but assumes the pointwise maximizing rule as a
  hypothesis. It does not itself prove that `pi` and `p` are normalized
  probability distributions or that `m` is a MAP rule; `chooseMAP` supplies
  finite maximizer existence in the preceding endpoint for a finite universe.

The statistical interpretation `J(theta,x)=pi(theta) P(x|theta)`, the
zero-one success interpretation, and the identification of circular genomes
with rotation classes are modeling choices made by the paper. The separate
`GenomeOrbitAdapter.uniform_orbit_prior_ML` endpoint supplies the uniform
rotation-class MAP/ML connection. This theorem is generic finite decision
theory, not a theorem about MB09's product-binomial surrogate or a
source-faithful realization of the 2016 reconstruction algorithm.

## Manuscript alignment and bounded caveat

At the reviewed manuscript source on the #268 narrative branch (whose exact
two-question wording is also present on the active #265 finite-read branch),
Theorem `thm:bayes-optimal` states a finite
candidate universe, a correct common observation model, zero-one exact-class
loss, and uniform prior over equivalence classes for ML=MAP; it separately
states MAP for general priors and the iid every-finite-`n` specialization. Its
status line cites the exact deterministic, randomized, and iid endpoints, while
the proof gives the finite decision argument. The introduction's prior-average
wording is accurate and properly distinguishes this benchmark from the
pointwise 2016 question.

One precision worth preserving in any further shortening: `finite_iid_MAP_optimal`
assumes a pointwise maximizing rule, and the generic algebraic model does not
itself validate a genome read-generation distribution. The paper currently
addresses both boundaries by giving the pointwise MAP theorem/proof, citing
the finite maximizer endpoint, and explicitly labeling the circular read model
and uniform-start sampling as external modeling inputs. Avoid saying that the
iid Lean declaration alone proves a concrete genome model or MAP existence.

Evidence class: (i) the named Lean endpoints above, for the formal algebraic
statements; (iii) Berger (1985), cited by the paper, for the classical
decision-theoretic interpretation; and paper-level/modeling statements for
the embedding into the circular genome experiment. No 2016 premise is needed
for this Bayes theorem.
