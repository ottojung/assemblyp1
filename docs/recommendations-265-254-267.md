# Recommendations for issues #265 and #254 (issue #267, task 6)

_Status: 2026-10-12. Grounded in `docs/bayes-optimality-conditional-feasibility-267.md` (Theorem 1, Propositions 2–3) and `docs/audit-267-finite-ml-vs-conditional-bayes.md`. Labels: **standard statistics**, **mathematical proof**, **kernel-checked**, **source fact**, **open**._

---

## What #265 and #254 are

- **#265** owns the per-truth non-monotonicity witness: a computed instance where per-truth success $P_G(\delta = G)$ *drops* as reads accumulate, while prior-averaged success is non-decreasing (Remark `rem:mono-avg`, paper §3).
- **#254** is the programmers' talk deck (`slides/programmers.md`), which presents the project to a general technical audience.

---

## Text recommendations (apply to both #265 and #254)

### R1 — Do not write "ML is universally the best algorithm"

**Replace:** "ML always finds the truth" / "ML is the best algorithm"

**With:** "Under a uniform prior over rotation classes and zero-one loss, the ML rule maximizes *prior-averaged* success at every sample size $n$ — it does not maximize per-truth success for every fixed genome."

**Theorem basis:** Theorem 1 (`AssemblyP1.FiniteBayesDecision.pointwise_MAP_optimal` / `chooseMAP_optimal`, kernel-checked, merged via #269/PR #174) gives prior-averaged optimality. The per-truth strengthening is false: "no rule is uniformly optimal for every fixed truth unless $|\mathcal{C}| = 1$" (paper §3, standard statistics). Witness: W1–W6 show the truth can lose to a competitor on a specific sample. **Label: standard statistics + kernel-checked.**

### R2 — Do not call the MB09 approximate objective a Bayes posterior

**Replace:** "The MB09 binomial is the Bayes-optimal objective" / "the approximate objective is a posterior"

**With:** "The MB09 fixed-$N$ product-binomial is a separable pseudo-likelihood with an external $N$; optimizing it is not optimizing the Bayes rule of the sampling model."

**Theorem basis:** Proposition `prop:multinomial-iid` (paper §3): the exact multinomial equals the i.i.d. likelihood up to a constant; the binomial does not. **Label: mathematical proof + source fact (MB09 §6.1).**

### R3 — State the tie limitation explicitly

**Add:** "When $m$ candidates tie, every maximizer is Bayes-optimal for prior-averaged success, but exact identification *within* the tie class is limited by $1/m$."

**Theorem basis:** Paper §3, ties bullet. Rotations are the canonical tie class: they are observationally equivalent (Remark `rem:rotations-equiv`), so the prior is placed on rotation classes, not sequences. **Label: standard statistics.**

### R4 — Distinguish "a maximizer" from "the unique maximizer"

**Add:** "The 2016 sentence asks whether the truth is *the* maximum-likelihood sequence. Our results distinguish: (i) the truth *is a* maximizer (population P2 theorem, kernel-checked) from (ii) the truth is *the unique* maximizer up to rotation (same theorem). Finite witnesses W1–W6 show the truth need not be a maximizer at fixed $n$."

**Theorem basis:** Population P2 theorem (`\popml`, kernel-checked) vs. finite counterexamples W1–W6 (kernel-checked). **Label: kernel-checked.**

### R5 — Keep the conditional/unconditional distinction visible

**Add:** "Conditional on the information-feasibility event $E = F(G,R)$ (truth-dependent, not $R$-observable), the conditional MAP is optimal for the *conditional* risk — a different experiment from the original prior-averaged problem. An $R$-only algorithm cannot condition on $E$."

**Theorem basis:** Propositions 2–3 (mathematical proof). **Label: mathematical proof.**

---

## Graphic recommendations

### For #265 (per-truth non-monotonicity witness)

A two-panel figure:

- **Left panel:** prior-averaged success $S_n(\delta^*)$ vs. $n$ — non-decreasing curve (theorem).
- **Right panel:** per-truth success $P_G(\delta = G)$ vs. $n$ for the specific witness genome $G$ — a curve that dips at some $n$, with a marker showing the drop.

Caption: "Prior-average success is non-decreasing (left); per-truth success can drop (right). The ML rule improves *on average*, never *for every genome*." **Label: mathematical proof (left) + kernel-checked witness (right).**

### For #254 (programmers' talk)

A "five-notions" diagram (already in paper §3, suitable for a slide):

```
┌─────────────────────────────────────────────────────────┐
│  1. Conditional MAP finds truth  (corollary, elementary) │
│  2. Prior-average Bayes optimality (Thm 1, kernel-checked)│
│  3. Pointwise finite-sample failure   (W1–W6, kernel)    │
│  4. Identifiability                   (P2, kernel-checked)│
│  5. Limiting consistency n→∞          (standard stats)   │
└─────────────────────────────────────────────────────────┘
  Conflating any two → false headline
```

Each box carries its proof-to-claim label (\claimK, \claimT, \claimP, \claimS, or \claimO).

---

## Summary table

| Recommendation | Grounding | Label |
|---|---|---|
| R1: No "universally best" | Thm 1 + no-uniform-optimality | standard statistics + kernel-checked |
| R2: No "MB09 = Bayes posterior" | Prop `prop:multinomial-iid` | mathematical proof + source fact |
| R3: Tie limitation $1/m$ | Paper §3 ties bullet | standard statistics |
| R4: "A maximizer" vs "unique" | `\popml` vs. W1–W6 | kernel-checked |
| R5: Conditional vs unconditional | Props 2–3 | mathematical proof |
| #265 graphic: two-panel | `rem:mono-avg` + witness | proof + kernel-checked |
| #254 graphic: five-notions | Paper §3 | mixed labels |

---

## Limits

- R1–R3 are **standard statistics** (Berger 1985, Cover–Thomas ch. 11), not new results.
- R4's population P2 theorem is **kernel-checked** for the oriented primitive P2 class; the general candidate class is **open**.
- R5's conditional analysis assumes $E = F(G,R)$ is well-defined; whether the truth is the unique feasible candidate is the **open** population P2 normalized-spectrum identifiability question.
- Source fidelity: the MB09 objective referent (exact multinomial vs. binomial vs. §6.2 flow) for the 2016 sentence is **open** and not settled by any finite witness.
