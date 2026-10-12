# Recommendations for issues #265 and #254 (from #267 audit)

_Status: review note, 2026-10-12. Branch: `review/267-bayes-reconciliation`.
These recommendations are grounded in the theorems and audit findings of issue
#267. They are text/graphic suggestions only; the actual paper/slides changes
are owned by #265 and #254 respectively._

## Recommendations for #265 (whitepaper/presentations)

### R1: State Bayes optimality with its exact scope

**Do not write**: "ML is universally the best algorithm" or "ML maximizes
accuracy".

**Write instead**: "Under a uniform prior over rotation classes and zero-one
loss, the ML rule maximizes prior-averaged success at every sample size. This
is a statement averaged over the prior, not a per-truth guarantee: at any
fixed genome the rule can err, and our finite counterexamples show it erring
strictly."

**Grounds**: Theorem 1 (Bayes/MAP optimality, kernel-checked as
`bayes_optimality` in `AssemblyP1/FiniteMapOptimality.lean`); Proposition 3
(`E` not `R`-observable); W1-W6 witnesses.

### R2: Distinguish the five notions explicitly

The whitepaper should present the five notions as a table or figure, not as
interchangeable:

1. **Conditional guaranteed reconstruction** (Question A): corollary of the
   reconstruction theorem; silent about the unrestricted ranking.
2. **Prior-average Bayes optimality**: uniform prior over classes, zero-one
   loss, finite universe; maximizes prior-averaged success at every `n`.
3. **Pointwise finite-sample failure**: at a fixed truth and unrepresentative
   sample, ML can err strictly (W1-W6).
4. **Identifiability**: distinct candidates have distinct read distributions;
   fails in general (Example ABAB); proved for oriented primitive P2.
5. **Limiting consistency**: for a finite identifiable family, per-truth
   success tends to 1 as `n → ∞`; external theorem.

**Grounds**: `docs/bayes-optimality-conditional-feasibility-267.md` §5;
`docs/audit-267-finite-ml-vs-conditional-bayes.md` §3.

### R3: Label the MB09 objective correctly

**Do not write**: "The MB09 binomial is the Bayes posterior" or "MB09 ML is
Bayes-optimal".

**Write instead**: "The MB09 fixed-N product-binomial is a separable
pseudo-likelihood with an external N. Optimizing it is not optimizing the
Bayes rule of the sampling model. The exact multinomial is the i.i.d.
likelihood up to a constant (Proposition `multinomial-iid`)."

**Grounds**: `AssemblyP1.FiniteMapOptimality` (nonuniform prior example);
paper §3 Proposition `multinomial-iid`; framework Axis 2.

### R4: Use the 2×2 example as the hinge figure

A small figure showing the 2×2 joint law, the event `E`, and the two rules
(`δ_E` infallible on `E` with accuracy 1/4; `δ_MAP` with accuracy 3/4)
communicates the central distinction more effectively than prose alone.

**Grounds**: `map_beats_infallible_on_E` (kernel-checked); note §4.

### R5: Preserve witness scope labels

Each counterexample in the whitepaper should carry its exact scope: objective
(exact multinomial / binomial / §6.2 flow), candidate lengths, read-type
convention (oriented / molecule), and feasibility predicate (placement /
historical). Do not present one witness as evidence for another's cell.

**Grounds**: framework Axes 1-6; `docs/audit-267-finite-ml-vs-conditional-bayes.md`
§2.

## Recommendations for #254 (programmers' talk)

### T1: Open with the two-question distinction

The talk should open with: "The 2016 question splits into two. If the
candidate set is constrained to the feasible fiber, the answer is yes (a
corollary). If the original likelihood is maximized over its original
universe, the answer is no (strict counterexamples)."

**Grounds**: paper §3 `sec:two-questions`; note §5.

### T2: Show the W3 and W6 counterexamples side by side

Both are instances where the conditional-on-`E` MAP also fails (the
competitor satisfies `I_s`):

- **W3** (AABB → ABAB): same-length, same spectra; competitor wins by
  multiplicity reallocation.
- **W6** (AABBC → AABC): variable-length, same spectra; competitor wins by
  the `1/G^n` length factor.

A slide showing both makes the "conditional certainty is not universal"
point concretely.

**Grounds**: `docs/audit-267-finite-ml-vs-conditional-bayes.md` §2, §4.

### T3: Close with the theorem/assumption matrix

A one-slide version of the theorem/assumption matrix (paper Table
`tab:claims`) gives the audience a accurate map of what is proved, what is
kernel-checked, and what is open.

**Grounds**: paper Table `tab:claims`; framework §5 epistemic policy.

## Limits and caveats

These recommendations inherit the limits of the underlying theorems:

- **Equality**: Bayes optimality holds with equality for every MAP tie
  breaker; exact identification within a tie class of size `m` is limited by
  `1/m`.
- **Ties**: rotation classes are the canonical tie class; the strong schema
  (unique identification up to rotation) is the satisfiable one.
- **Prior/rotation**: the prior is placed on rotation classes, not on
  individual sequences; a nonuniform prior over classes changes the Bayes
  rule from ML to MAP.
- **Source fidelity**: the MB09 objective referent in the 2016 sentence
  remains **open**; no finite witness settles it. The recommendations above
  are conditional on the referent being the exact multinomial or the MB09
  binomial; if the referent is the §6.2 flow, the Bayes-optimality theorem
  does not directly apply.
