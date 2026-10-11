# Bayes optimality and conditional feasibility (issue #267)

_Status: mathematical note, 2026-10-11. Every claim is labelled **standard
statistics**, **mathematical proof**, **kernel-checked**, **source fact**, or
**open**. This note reconciles (a) the finite-candidate Bayes/MAP optimality
theorem, (b) exact finite-sample maximum likelihood sometimes selecting the
wrong genome, and (c) the conditional-on-`E` analysis of the information-
feasibility event. It is the foundational note for
`docs/audit-267-finite-ml-vs-conditional-bayes.md`, which audits the finite
counterexample witnesses against the conditional analysis of §3 below._

_Reproduction:_

```sh
lake build AssemblyP1.FiniteMapOptimality
lake env leanchecker AssemblyP1.FiniteMapOptimality
```

---

## 1. Finite-candidate Bayes/MAP optimality

**Setup.** Let `G` be a finite candidate set, `R` a finite observation set,
`π : G → ℚ≥0` a prior with `∑_g π(g) = 1`, and `P : G → R → ℚ≥0` a family of
likelihoods with `∑_r P(g,r) = 1` for each `g`. The joint law is

```
P(g, r) = π(g) · P(g, r).
```

The loss is zero-one on rotation classes: a decision rule `δ : R → G` scores
`1` if `δ(r)` is in the true rotation class of `g`, `0` otherwise. The
prior-averaged risk of `δ` is

```
risk(δ) = ∑_r [ P(R=r) − P(δ(r), r) ]
        = 1 − ∑_r π(δ(r)) · P(δ(r), r).
```

**Theorem 1 (Bayes/MAP optimality).** _The MAP rule
`δ*(r) ∈ argmax_g π(g)·P(g,r)` minimizes the prior-averaged risk over all
deterministic decision rules._

_Proof._ For any rule `δ` and any observation `r`,

```
π(δ(r))·P(δ(r),r) ≤ max_g π(g)·P(g,r) = π(δ*(r))·P(δ*(r),r).
```

Summing over `r` gives `accuracy(δ) ≤ accuracy(δ*)`, hence
`risk(δ*) ≤ risk(δ)`. ∎

**Equal prior ⇒ MAP = ML.** If `π(g) = 1/|G|` for all `g`, then
`argmax_g π(g)·P(g,r) = argmax_g P(g,r)`, so MAP and ML coincide (up to class
weighting and ties). **Standard statistics.**

**Nonuniform prior ⇒ ML need not be Bayes optimal.** With `π = (9/10, 1/10)`
and a single observation `a` with `P(g1,a) = 1/2`, `P(g2,a) = 1`, ML selects
`g2` (likelihood `1`) while MAP selects `g1` (joint weight `9/20 > 1/10`).
**Kernel-checked** (`AssemblyP1.FiniteMapOptimality.map_ne_ml_nonuniform`).

**Prior on sequences vs rotation classes.** The prior is placed on rotation
classes, not on individual sequences: rotations are observationally equivalent
(Remark `rem:rotations-equiv`), so they share a likelihood and must share a
prior weight. The strong schema (unique identification up to rotation) is the
satisfiable one. **Standard statistics** + **source fact** (MB09 §6.1).

---

## 2. The event `E = F(G,R)` is truth-dependent

Let `F : G × R → {0,1}` be a feasibility predicate. For the 2016 question,
`F(g,R)` is the source's coverage-and-bridging predicate `I_s^match` evaluated
on candidate `g` against the observed read set `R` — a property of `g` and `R`
alone. The information-feasibility event is

```
E = F(G, R) = {(g, r) : F(g, r) = 1}.
```

**Proposition 2.** _`E` is not `R`-observable in general: seeing the reads `R`,
one cannot determine whether `F(G,R) = 1` without knowing `G`._

_Proof._ `F` depends on `G` by definition. Two genomes `g, g'` can produce the
same read set `R` with `F(g,R) = 1` and `F(g',R) = 0` (e.g., the `AABB/ABAB`
witness: both are `I_s`-feasible, but a third genome `ABBA` is not). Hence `E`
is not measurable with respect to the `R`-marginal sigma-field. ∎

**Consequence.** Conditioning on `E` is conditioning on a truth-dependent
event. An `R`-only reconstruction rule cannot condition on `E` without
additional assumptions. This is the precise sense in which the conditional
analysis is a different experiment, not a refinement available to every
likelihood algorithm. **Mathematical proof.**

---

## 3. Conditioning on `E` alters the experiment

Conditioning on `E` gives a new joint law on `G × R`:

```
P_E(g, r) = P(g, r) · 1_F(g,r) / P(E),
```

where `P(E) = ∑_{g,r} π(g)·P(g,r)·1_F(g,r)`. This decomposes as:

- **Effective prior:** `π(g | E) = π(g) · P_g(F_g) / P(E)`, where
  `P_g(F_g) = ∑_r P(g,r)·1_F(g,r)` is the probability that `g` is feasible.
- **Conditional likelihood:** `P_E(r | g) = P(g,r)·1_F(g,r) / P_g(F_g)`,
  the original likelihood restricted to feasible observations.
- **Conditional MAP:** `argmax_{g : F(g,r)=1} π(g)·P(g,r)` — the MAP rule of
  the conditional experiment, restricted to the feasible fiber
  `{g : F(g,r) = 1}`.

**Proposition 3.** _The conditional-on-`E` MAP rule minimizes the
conditional risk `risk_E(δ) = 1 − ∑_r P_E(δ(r),r)`. It is optimal for the
conditional risk, not for the original prior-averaged risk._

_Proof._ Theorem 1 applied to the conditional joint law `P_E`. ∎

**Key distinction.** The conditional MAP is the MAP rule of a _different
experiment_ (conditioned on `E`). It is not the MAP rule of the original
experiment, and it is not available to an `R`-only algorithm (Proposition 2).
The original MAP rule remains optimal for the original prior-averaged risk.
**Mathematical proof.**

---

## 4. The `2×2` example: infallible on `E` yet losing to MAP

**Model.** Two genomes `g1, g2`, two observations `a, b`, equal prior `1/2`:

```
P(g1, a) = 1/4   P(g1, b) = 3/4
P(g2, a) = 3/4   P(g2, b) = 1/4
```

**Joint law** (prior × likelihood):

|       | `a`   | `b`   |
|-------|-------|-------|
| `g1`  | `1/8` | `3/8` |
| `g2`  | `3/8` | `1/8` |

**Event `E = {(g1,a), (g2,b)}`** (the truth is "feasible" in the toy sense):
`P(E) = 1/8 + 1/8 = 1/4`.

**Decision table:**

| Rule   | `a ↦` | `b ↦` | Accuracy on `E` | Prior-averaged accuracy |
|--------|-------|-------|-----------------|-------------------------|
| `δ_E`  | `g1`  | `g2`  | `1` (infallible)| `1/4`                   |
| `δ_MAP`| `g2`  | `g1`  | `0`             | `3/4`                   |

**Calculation.** `δ_E` is correct exactly on `E`, so its prior-averaged accuracy
is `P(E) = 1/4`. The unconstrained MAP rule selects `g2` at `a` (joint `3/8`)
and `g1` at `b` (joint `3/8`), giving accuracy `3/8 + 3/8 = 3/4`. Hence
`accuracy(δ_E) = 1/4 < 3/4 = accuracy(δ_MAP)`. **Kernel-checked**
(`AssemblyP1.FiniteMapOptimality.map_beats_infallible_on_E`).

**Interpretation.** An `R`-only rule can be infallible on `E` yet lose in
original prior-averaged accuracy to unconstrained MAP. This is not a paradox:
the two rules are optimal for different experiments (conditional vs
unconditional). **Mathematical proof** + **kernel-checked.**

---

## 5. Three notions distinguished

The literature circulates several properties of the ML rule. They are
independent, and conflating them produces false headlines.

1. **Conditional MAP finds truth.** _If_ the truth `S` is information-feasible
   (`F(S,R)`) _and_ the truth is the unique feasible candidate, _then_ the
   conditional-on-`E` MAP recovers the truth. This is an elementary
   consequence of deterministic reconstruction on the feasible fiber — a
   corollary of the reconstruction theorem, not a new ML result.
   **Mathematical proof.**

2. **Unrestricted finite ML finds truth.** At a fixed truth and a fixed
   (possibly unrepresentative) sample, the unrestricted ML rule can err
   strictly. The finite counterexamples `W1`–`W5` (audited in
   `docs/audit-267-finite-ml-vs-conditional-bayes.md`) exhibit feasible truths
   beaten by infeasible competitors. This is a _pointwise_ failure, fully
   compatible with prior-average Bayes optimality (Theorem 1).
   **Kernel-checked** for the specific witnesses.

3. **As `n→∞` ML succeeds almost surely.** For a finite identifiable family,
   per-truth success tends to `1` as `n → ∞` (Remark `rem:sample-complexity`,
   Hellinger affinity bound). This is an external theorem about finite
   families, distinct from the population theorem (which involves no sampling)
   and from the finite pointwise failures. **Standard statistics.**

**The conditional inference theorem is not a substitute for the population
theorem.** Notion 1 is a corollary of deterministic reconstruction: it says
_that if_ the truth is the unique feasible candidate, _then_ conditional MAP
finds it. It gives no conditions under which the truth _is_ the unique
feasible candidate. That is the content of the population `P2` normalized-
spectrum identifiability theorem, which is strictly stronger and is not
settled by any finite witness. **Mathematical proof** for the distinction;
**open** for the population `P2` theorem in full generality.

---

## 6. Relation to the population `P2` theorem

The population `P2` theorem (Theorem `rem:population`, kernel-checked as
`\popml`) states that for `L ≥ 2` and a primitive P2 truth, the truth maximizes
the population log-likelihood over every positive-length primitive P2
candidate, and every population tie is a cyclic rotation of the truth. This is
the nontrivial combinatorial heart of the identifiability step.

The conditional inference theorem (notion 1) is an elementary consequence of
deterministic reconstruction: on the feasible fiber, the truth is the unique
candidate, so any valid conditional MAP returns it. It is a corollary, not a
substitute, for the population theorem. The finite witnesses `W1`–`W5` show
that unrestricted finite ML can fail; they do not address the population
question, and they do not contradict the conditional theorem (the beating
competitors lie outside the feasible fiber, except for the `AABB/ABAB` witness
`W3`, where the competitor is also feasible — see the audit §4).

**Summary of the reconciliation:**

| Notion | Statement | Status |
|--------|-----------|--------|
| Prior-average Bayes optimality | MAP minimizes prior-averaged risk | **true** (Theorem 1, kernel-checked) |
| Equal prior ⇒ MAP = ML | up to class weighting/ties | **true** (standard statistics) |
| Nonuniform prior ⇒ ML ≠ Bayes | MAP is prior-weighted ML | **true** (kernel-checked) |
| `E = F(G,R)` not `R`-observable | truth-dependent event | **true** (Proposition 2) |
| Conditional MAP optimal for conditional risk | different experiment | **true** (Proposition 3) |
| Infallible-on-`E` rule can lose to MAP | `2×2` example | **true** (kernel-checked) |
| Conditional MAP recovers truth | when truth is unique feasible | **true** (elementary) |
| Conditional MAP recovers truth universally | for all instances | **refuted** (W3 counterexample) |
| Unrestricted finite ML always finds truth | pointwise | **refuted** (W1–W5) |
| ML succeeds as `n→∞` | finite identifiable family | **true** (standard statistics) |
| Population `P2` identifiability | primitive P2, oriented | **true** (kernel-checked, `\popml`) |
| Population `P2` identifiability | general candidate class | **open** |

---

## 7. Epistemic status

| Claim | Status |
|-------|--------|
| Theorem 1 (Bayes/MAP optimality) | **standard statistics** + **kernel-checked** |
| Proposition 2 (`E` not `R`-observable) | **mathematical proof** |
| Proposition 3 (conditional MAP optimal) | **mathematical proof** |
| `2×2` example arithmetic | **kernel-checked** |
| Notion 1 (conditional MAP finds truth) | **mathematical proof** (elementary) |
| Notion 2 (finite ML can fail) | **kernel-checked** (W1–W5) |
| Notion 3 (asymptotic consistency) | **standard statistics** |
| Population `P2` theorem | **kernel-checked** (primitive P2, oriented) |
| Population `P2` general class | **open** |
| MB09 objective referent | **open** (source ambiguity) |

Primary sources: Shomorony, Kim, Courtade & Tse (2016), _Bioinformatics_ 32(17)
i494–i502; Medvedev & Brudno (2009), _J. Comput. Biol._ 16(8) 1101–1116;
Berger, _Statistical Decision Theory and Bayesian Analysis_ (1985);
Cover–Thomas, _Elements of Information Theory_, ch. 11.
