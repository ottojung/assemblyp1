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
lake build AssemblyP1.MapDecisionExamples
lake env leanchecker AssemblyP1.MapDecisionExamples
python3 scripts/audit-267-independent-checks.py
```

The general finite-candidate Bayes/MAP optimality theorem itself is **not**
re-proved for this issue: it is
`AssemblyP1.FiniteBayesDecision.pointwise_MAP_optimal` together with the
constructed-rule corollary `chooseMAP_optimal`, merged on `main` via the
sibling Bayes issue #269 / PR #174. The file
`AssemblyP1/MapDecisionExamples.lean` contains only the concrete examples
below; it does not re-prove the general theorem.

---

## 1. Finite-candidate Bayes/MAP optimality

**Setup.** Let `G` be a finite candidate set, `R` a finite observation set,
`π : G → ℚ≥0` a prior with `∑_g π(g) = 1`, and `P : G → R → ℚ≥0` a family of
likelihoods with `∑_r P(g,r) = 1` for each `g`. The joint law is

```
J(g, r) = π(g) · P(g, r).
```

The loss is zero-one on rotation classes. Since rotations are observationally
equivalent, it is equivalent and cleaner to take the hypothesis space to be
the set of rotation **classes** (each class carries a single likelihood
`P_{[g]}` and prior `π([g])`); a decision rule `δ : R → classes` then scores
`1` iff `δ(r)` is the true class. The prior-averaged risk of `δ` is

```
risk(δ) = ∑_r [ P(R=r) − J(δ(r), r) ]
        = 1 − ∑_r π(δ(r)) · P(δ(r), r).
```

**Theorem 1 (Bayes/MAP optimality).** _The MAP rule
`δ*(r) ∈ argmax_g J(g,r) = argmax_g π(g)·P(g,r)` minimizes the prior-averaged
risk over all deterministic decision rules._ This is the standard finite-Bayesian
zero-one theorem; it is **kernel-checked on `main`** as
`AssemblyP1.FiniteBayesDecision.pointwise_MAP_optimal` (any pointwise
maximizer dominates every deterministic rule) and
`chooseMAP_optimal` (the constructed `chooseMAP` rule is such a maximizer),
merged via the sibling Bayes issue #269 / PR #174. Randomized rules cannot do
better (`pointwise_MAP_optimal_randomized`).

_Proof._ For any rule `δ` and any observation `r`,

```
J(δ(r),r) = π(δ(r))·P(δ(r),r) ≤ max_g π(g)·P(g,r) = J(δ*(r),r).
```

Summing over `r` gives `accuracy(δ) ≤ accuracy(δ*)`, hence
`risk(δ*) ≤ risk(δ)`. ∎

**Equal prior ⇒ MAP = ML.** If `π(g) = 1/|G|` for all `g`, then
`argmax_g π(g)·P(g,r) = argmax_g P(g,r)`, so MAP and ML coincide (up to class
weighting and ties). **Standard statistics.**

**Nonuniform prior ⇒ ML need not be Bayes optimal.** With `π = (9/10, 1/10)`
and a single observation `a` with `P(g1,a) = 1/2`, `P(g2,a) = 1`, ML selects
`g2` (likelihood `1`) while MAP selects `g1` (joint weight `9/20 > 1/10`).
**Kernel-checked** (`AssemblyP1.MapDecisionExamples.map_ne_ml_nonuniform`).

**Prior on sequences vs rotation classes.** The prior is placed on rotation
classes, not on individual sequences: rotations are observationally equivalent
(Remark `rem:cyclic`), so they share a likelihood and must share a
prior weight. Two warnings: (i) a uniform prior on individual linear
representatives is **not** uniform on the orbits when orbit sizes differ, so
the equal-prior `MAP = ML` identity must be stated on classes, not on raw
spellings; (ii) MAP over classes is the class whose **summed** posterior mass
is largest, `argmax_[S] ∑_{g ∈ [S]} π(g)P(g,r)`, not necessarily the class of
the pointwise joint maximizer. The strong schema (unique identification up to
rotation) is the satisfiable one. **Standard statistics** + **source fact**
(MB09 §6.1).

---

## 2. The event `E = F(G,R)` is truth-dependent

Let `F : G × R → {0,1}` be a feasibility predicate. For the 2016 question,
`F(g,R) = 1` iff candidate `g` satisfies the source's **latent-placement**
information-feasibility predicate `I_s` against the realized read placements
`R`: coverage of the realized start positions, all-bridged triple repeats, and
bridged interleaved repeats (Shomorony et al. 2016, Eq. (1); kernel-checked as
`SourceFaithfulIs.InformationFeasible`). This is a property of `g` and `R`
alone, evaluated on the *latent* placements, **not** the source's historical
read-**string** predicate `I_s^match` (paper Definition `def:historical-match`),
which matches observed read strings at any genomic position; the two predicates
are incomparable (paper Proposition `prop:historical-source`). The audit
(`docs/audit-267-finite-ml-vs-conditional-bayes.md` §1.7) classifies each
witness by read-type panel (oriented vs reverse-complement molecule classes),
coverage predicate (placement vs historical), and objective, and records which
witnesses match Not-So-Greedy's observable model. The information-feasibility
event is

```
E = F(G, R) = {(g, r) : F(g, r) = 1}.
```

**Proposition 2.** _`E` is not `R`-observable in general: seeing the reads `R`,
one cannot determine whether `F(G,R) = 1` without knowing `G`._

_Proof._ `F` depends on `G` by definition. Two genomes `g, g'` of different
length can produce the same observed read multiset `R` with `F(g,R) = 1` and
`F(g',R) = 0`: in the `ACGT/ACACGT` witness (audit §1, W4) both produce
`{AC:2, GT:1}`, the truth `ACGT` satisfies `I_s`, and the longer competitor
`ACACGT` fails the coverage clause of `I_s` (the truth's realized starts
`{0,0,2}` do not cover the competitor's six positions). Hence `E` is not
measurable with respect to the `R`-marginal sigma-field. ∎

**Consequence.** Conditioning on `E` is conditioning on a truth-dependent
event. An `R`-only reconstruction rule cannot condition on `E` without
additional assumptions. This is the precise sense in which the conditional
analysis is a different experiment, not a refinement available to every
likelihood algorithm. **Mathematical proof.**

---

## 3. Conditioning on `E` alters the experiment

Conditioning on `E` gives a new joint law on `G × R`:

```
P_E(g, r) = J(g, r) · 1_F(g,r) / P(E),
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

**Proposition 4 (conditional posterior `1` from deterministic reconstruction).**
_Let `C(r) = {g : π(g)·P(g,r) > 0 and F(g,r) = 1}` be the support of the
conditional posterior at `r`. If a deterministic reconstruction map `ρ` sends
every `g ∈ C(r)` to the same rotation class `[S]` (i.e. `ρ(g) = [S]` for all
`g ∈ C(r)`), then the conditional posterior is `1` on `[S]`:
`P_E([S] | r) = 1`._

_Proof._ The conditional posterior is supported on `C(r)` by definition of the
conditional joint law, and every member of `C(r)` lies in `[S]`. Hence all
conditional mass is in `[S]`. ∎

This is the precise content of "the conditional posterior is `1`". It is a
corollary of a deterministic reconstruction guarantee and it requires the
guarantee for **every** feasible `g ∈ C(r)`, not merely for the truth. The
Not-So-Greedy guarantee has exactly this form on `I_s`-feasible inputs, so on
the event `E` it forces `P_E([S] | r) = 1`. It does **not** say that ordinary
unconstrained ML returns `[S]`: the ordinary likelihood still ranges over the
whole candidate set and may rank a competitor above `[S]` (the finite
witnesses). On `E`, conditional MAP and Not-So-Greedy agree about the rotation
**class only**. Conditional MAP is **not** an `R`-only rule in the original
experiment (it conditions on the truth-dependent event `E`), whereas
Not-So-Greedy **is** a read-only reconstruction rule; the agreement on the class
does not make the two algorithms identical. **Mathematical proof.**

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
(`AssemblyP1.MapDecisionExamples.map_beats_infallible_on_E`; the optimality of
`δ_MAP` is the pointwise joint maximizer of this instance by the definitional
weights `AssemblyP1.MapDecisionExamples.J2`, so its prior-averaged optimality is
the general `AssemblyP1.FiniteBayesDecision.pointwise_MAP_optimal`, not a
separately kernel-checked instance lemma).

**Interpretation.** An `R`-only rule can be infallible on `E` yet lose in
original prior-averaged accuracy to unconstrained MAP. This is not a paradox:
the two rules are optimal for different experiments (conditional vs.
unconditional). **Mathematical proof** + **kernel-checked.**

### 4.1 The two-hypothesis toy: ML picks a nonfeasible candidate

The delegated statement of the reconciliation is the smallest case: two
hypotheses `g, h`, one observation `x`, with

```
P_g(x) = 1/10,   P_h(x) = 1/5,   E(g, x) = true,   E(h, x) = false,
```

and an equal prior `π(g) = π(h) = 1/2` (the `y` column completes each
likelihood to a pmf: `P_g(y) = 9/10`, `P_h(y) = 4/5`). Then:

- **Ordinary uniform-prior ML picks `h`** at `x`, since `P_h(x) = 1/5 > 1/10 =
  P_g(x)`. So does the ordinary (unconditional) MAP rule, the prior being
  uniform.
- **Conditioning on `E` kills `h` at `x`.** The conditional joint weight
  `π(g)P_g(x)1_F(g,x)` is `1/20` at `g` and `0` at `h`, so the conditional
  posterior on the feasible fiber is supported on `g` alone: mass `1` on `g`.
  The conditional MAP returns `g` with certainty.

This is exactly the three coexisting facts: (i) unconditional MAP maximizes
prior-averaged success but can be wrong on an individual `x`; (ii) ordinary
finite ML can rank a nonfeasible competitor `h` above the feasible truth `g`;
(iii) the conditional posterior given `E` is supported only on the feasible
set. There is no contradiction: conditioning on the truth-dependent event `E`
is a different experiment (§3), and `E` is not `R`-observable (§2).
**Kernel-checked** (`AssemblyP1.MapDecisionExamples.toy_ml_picks_h`,
`toy_cond_support`, `toy_cond_g_beats_h`, `toy_cond_normalized`).

---

## 5. Three notions distinguished

The literature circulates several properties of the ML rule. They are
independent, and conflating them produces false headlines.

1. **Conditional MAP finds the truth's rotation class.** _If_ a deterministic
   reconstruction guarantee sends **every** feasible candidate in the support
   `C(r)` to the same rotation class `[S]`, _then_ the conditional-on-`E` MAP
   returns `[S]` (Proposition 4); the case where the truth is the unique
   feasible candidate is the special case `C(r) = {S}`. This is an elementary
   consequence of deterministic reconstruction on the feasible fiber — a
   corollary of the reconstruction theorem, not a new ML result.
   **Mathematical proof.**

2. **Unrestricted finite ML finds truth.** At a fixed truth and a fixed
   (possibly unrepresentative) sample, the unrestricted ML rule can err
   strictly. The finite counterexamples `W1`–`W6` (audited in
   `docs/audit-267-finite-ml-vs-conditional-bayes.md`) exhibit `I_s`-feasible
   truths beaten by competitors; for `W1/W2/W4/W5` the competitor fails `I_s`
   (so conditional MAP would recover the truth), while for `W3` and `W6` the
   competitor is itself `I_s`-feasible, so even conditional MAP fails there.
   This is a _pointwise_ failure, fully compatible with prior-average Bayes
   optimality (Theorem 1). **Kernel-checked** for the specific witnesses.

3. **As `n→∞` ML succeeds almost surely.** For a finite identifiable family,
   per-truth success tends to `1` as `n → ∞` (Remark `rem:sample-complexity`,
   Hellinger affinity bound). This is an external theorem about finite
   families, distinct from the population theorem (which involves no sampling)
   and from the finite pointwise failures. **Standard statistics.**

**The conditional inference theorem is not a substitute for the population
theorem.** Notion 1 is a corollary of deterministic reconstruction: it says
_that if_ every feasible candidate reconstructs to the same class, _then_
conditional MAP finds it. It gives no conditions under which the feasible
support is a single class; the `W3` and `W6` witnesses show the support can
contain a feasible competitor, in which case conditional MAP fails too. The
content of the population `P2` normalized-spectrum identifiability theorem is
precisely to identify conditions under which the truth is the unique feasible
class. That theorem is strictly stronger and is not settled by any finite
witness. **Mathematical proof** for the distinction; **open** for the
population `P2` theorem in full generality.

---

## 6. Relation to the population `P2` theorem

The population `P2` theorem (Theorems `thm:open-population` and
`thm:population`, kernel-checked as `\popml`) states that for `L ≥ 2` a
primitive P2-admissible truth is a population maximum-likelihood genome over
every candidate class containing it, and is the unique such maximizer up to
cyclic rotation among primitive P2-admissible **oriented** circular candidates.
This is the nontrivial combinatorial heart of the identifiability step.

The conditional inference theorem (notion 1) is an elementary consequence of
deterministic reconstruction: on the feasible fiber, the truth is the unique
candidate, so any valid conditional MAP returns it. It is a corollary, not a
substitute, for the population theorem. The finite witnesses `W1`–`W6` show
that unrestricted finite ML can fail; they do not address the population
question, and they do not contradict the conditional theorem (the beating
competitors lie outside the feasible fiber for `W1/W2/W4/W5`, while for the
`AABB/ABAB` witness `W3` and the `AABBC/AABC` witness `W6` the competitor is
also feasible — see the audit §4).

**Summary of the reconciliation:**

| Notion | Statement | Status |
|--------|-----------|--------|
| Prior-average Bayes optimality | MAP minimizes prior-averaged risk | **true** (Theorem 1, kernel-checked) |
| Equal prior ⇒ MAP = ML | up to class weighting/ties | **true** (standard statistics) |
| Nonuniform prior ⇒ ML ≠ Bayes | MAP is prior-weighted ML | **true** (kernel-checked) |
| `E = F(G,R)` not `R`-observable | truth-dependent event | **true** (Proposition 2) |
| Conditional MAP optimal for conditional risk | different experiment | **true** (Proposition 3) |
| Infallible-on-`E` rule can lose to MAP | `2×2` example | **true** (kernel-checked) |
| Conditional MAP recovers class | when all feasible `g` reconstruct to one class | **true** (Proposition 4, elementary) |
| Conditional MAP recovers class universally | for all instances | **refuted** (W3 and W6 counterexamples) |
| Unrestricted finite ML always finds truth | pointwise | **refuted** (W1–W6) |
| ML succeeds as `n→∞` | finite identifiable family | **true** (standard statistics) |
| Population `P2` identifiability | primitive P2, oriented | **true** (kernel-checked, `\popml`) |
| Population `P2` identifiability | general candidate class | **open** |

---

## 7. Epistemic status

| Claim | Status |
|-------|--------|
| Theorem 1 (Bayes/MAP optimality) | **standard statistics** + **kernel-checked** (`FiniteBayesDecision`, PR #174) |
| Proposition 2 (`E` not `R`-observable) | **mathematical proof** |
| Proposition 3 (conditional MAP optimal) | **mathematical proof** |
| `2×2` example and two-hypothesis toy arithmetic | **kernel-checked** (`MapDecisionExamples`) |
| Notion 1 (conditional MAP finds truth) | **mathematical proof** (elementary) |
| Notion 2 (finite ML can fail) | **kernel-checked** (W1–W6) |
| Notion 3 (asymptotic consistency) | **standard statistics** |
| Population `P2` theorem | **kernel-checked** (primitive P2, oriented) |
| Population `P2` general class | **open** |
| MB09 objective referent | **open** (source ambiguity) |

Primary sources: Shomorony, Kim, Courtade & Tse (2016), _Bioinformatics_ 32(17)
i494–i502; Medvedev & Brudno (2009), _J. Comput. Biol._ 16(8) 1101–1116;
Berger, _Statistical Decision Theory and Bayesian Analysis_ (1985);
Cover–Thomas, _Elements of Information Theory_, ch. 11.
