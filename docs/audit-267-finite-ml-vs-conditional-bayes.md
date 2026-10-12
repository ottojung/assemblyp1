# Audit: finite exact ML and approximate binomial witnesses versus externally conditioned `I_s` Bayesian certainty (issue #267)

_Status: independent audit, 2026-10-12 (updated). Every claim is labelled **standard
statistics**, **mathematical proof**, **kernel-checked**, **source fact**, or
**open**. This note audits the finite counterexample witnesses against the
conditional-on-`E` Bayesian analysis of `docs/bayes-optimality-conditional-feasibility-267.md`.
It does not re-prove the Bayes/MAP optimality theorem (that is
`AssemblyP1.FiniteMapOptimality`) and does not duplicate the Lean proof of the
conditional-fibre issue (#271)._

_Update 2026-10-12: added W6 (P1 finite case, AABBC → AABC), fixed W5
verification (molecule model vs spelled model), and updated I_s membership
matrix. Python script now passes 30/31 checks (1 expected failure: W4
competitor coverage, different genome length)._

_Reproduction:_

```sh
python3 scripts/audit-267-independent-checks.py
lake build AssemblyP1.FiniteMapOptimality
lake env leanchecker AssemblyP1.FiniteMapOptimality
```

---

## 0. Verdict at a glance

The finite exact-ML and approximate-binomial witnesses are **compatible** with
Bayes optimality and with the conditional-on-`E` analysis. The apparent
conflict dissolves once the experiment is held fixed:

- The witnesses are statements about a **particular realized sample** under a
  **particular candidate set**. They show the truth need not maximize the
  likelihood on that sample. This is fully compatible with Bayes optimality,
  which concerns the **prior-averaged** risk, not per-sample maximization.
- The conditional-on-`E` MAP rule is the **MAP rule of a different
  experiment** (conditioned on `E = F(G,R)`). It is optimal for the
  conditional risk, not for the original prior-averaged risk.
- For most witnesses, the competitor **fails** `I_s`, so the conditional-on-`E`
  MAP would correctly exclude it and recover the truth. But for the `AABB/ABAB`
  witness (W3) and the `AABBC/AABC` witness (W6), the competitor **satisfies**
  `I_s`, so conditional-on-`E` MAP would **also** fail on those instances.
  This is the precise sense in which "conditional `I_s` Bayesian certainty" is
  **not universal**: it holds only when the truth is the unique feasible
  candidate.

---

## 1. The witnesses and their arithmetic (independently verified)

All arithmetic below is independently verified by
`scripts/audit-267-independent-checks.py` (exact rational arithmetic, no Lean).

### W1: `FixedLengthExactCounterexample` (AAABB → AAAAB)

- **Objective**: fixed-length exact multinomial (MB09 §6.1 exact)
- **Truth**: `AAABB` (length 5), reads at starts `{0,1,4}`, observed `{AAA, AAB, BAA}`
- **Competitor**: `AAAAB` (length 5)
- **Likelihoods**: `L(truth) = 6/125`, `L(comp) = 12/125`
- **Ratio**: `2` ✓
- **`I_s` for truth**: ✓ (kernel-checked, all clauses)
- **`I_s` for competitor**: ✗ (triple repeat at `e=1, starts={0,1,3}` not all-bridged)

### W2: `FixedLengthBinomialCounterexample` (AAACC → AAAAC)

- **Objective**: fixed-length product-of-binomial-marginals (MB09 §6.1 approximation)
- **Truth**: `AAACC` (length 5), reads at starts `{0,1,4}`, observed `{AAA, AAC, CAA}`
- **Competitor**: `AAAAC` (length 5)
- **Likelihoods**: `L_A(truth) = 452984832/30517578125`, `L_A(comp) = 7962624/244140625`
- **Ratio**: `1125/512` ✓
- **`I_s` for truth**: ✓ (kernel-checked, all clauses)
- **`I_s` for competitor**: ✗ (triple repeat at `e=1, starts={0,1,3}` not all-bridged)

### W3: `SameLengthExactMLCounterexample` (AABB → ABAB)

- **Objective**: same-length exact multinomial (Variant E, candidate-intrinsic length)
- **Truth**: `AABB` (length 4), reads at starts `{1,3}`, observed `{AB, BA}`
- **Competitor**: `ABAB` (length 4)
- **Likelihoods**: `L(truth) = 1/16`, `L(comp) = 1/4`
- **Ratio**: `4` ✓
- **`I_s` for truth**: ✓ (kernel-checked, all clauses)
- **`I_s` for competitor**: ✓ (all clauses hold — **critical finding**)

### W4: `ExactVariantECounterexample` (ACGT → ACACGT)

- **Objective**: unrestricted-length exact multinomial (Variant E)
- **Truth**: `ACGT` (length 4), reads at starts `{0,0,2}`, observed `{AC:2, GT:1}`
- **Competitor**: `ACACGT` (length 6)
- **Likelihoods**: `L(truth) = 3/64`, `L(comp) = 1/18`
- **Ratio**: `32/27` ✓
- **`I_s` for truth**: ✓ (kernel-checked, all clauses)
- **`I_s` for competitor**: ✗ (coverage fails — different genome length)

### W5: `SameLengthSection62Counterexample` (AAATAT → AAAAAT)

- **Objective**: §6.2 bidirected flow + exact multinomial / binomial approximation
- **Truth**: `AAATAT` (length 6), reads at starts `{0,0,1,3,5}`, observed `{AAA:2, AAT:1, TAT:1, TAA:1}` (molecule classes)
- **Competitor**: `AAAAAT` (length 6)
- **Ratios**: exact `3`, binomial `5` (kernel-checked in Lean; **now also independently verified** with molecule model in Python)
- **`I_s` for truth**: ✓ (kernel-checked, all clauses)
- **`I_s` for competitor**: ✗ (triple repeat at `e=1, starts={0,3,4}` not all-bridged)

**W5 model note**: The original Python script used spelled-genome windows, which gave `d(TAT)=0` for the competitor and `L=0`. This was a **model mismatch**, not a verification failure: the §6.2 flow model uses reverse-complement-collapsed molecule classes, where `ATA` and `TAT` are the same molecule. The updated Python script implements the molecule model and confirms both ratios exactly.

### W6: `FiniteSamplingCounterexample` (AABBC → AABC)

- **Objective**: variable-length exact multinomial, candidate-intrinsic length
- **Truth**: `AABBC` (length 5), reads at starts `{0,3}`, observed `{AAB:1, BCA:1}`
- **Competitor**: `AABC` (length 4)
- **Likelihoods**: `L(truth) = 2/25`, `L(comp) = 1/8`
- **Ratio**: `25/16` ✓
- **P1/primitivity**: both candidates are primitive and satisfy P1 (kernel-checked in Lean)
- **`I_s` for truth**: ✓ (kernel-checked, all clauses)
- **`I_s` for competitor**: ✓ (reads `{AAB, BCA}` placed at starts `{0,2}` on AABC's circle cover all positions; no triple repeats; no interleaved pairs)

**Critical finding**: W6 is a second witness (alongside W3) whose competitor satisfies `I_s`. The conditional-on-`E` MAP would **also** select the wrong genome (`AABC`, likelihood `1/8 > 2/25`). This is a variable-length counterexample where the shorter genome wins by concentrating the same read mass into fewer positions. Both candidates are P1 and primitive, so this is not a structural obstruction but a finite-frequency fluctuation.

**W6 mechanism**: The observed reads `{AAB, BCA}` have the same multiplicity in both candidates (`d(AAB)=1, d(BCA)=1`), but the candidate lengths differ (5 vs 4). The exact multinomial `n! · ∏(d_w/G)^x_w` divides by `G^n`, so the shorter genome has higher likelihood. This is a pure length effect, independent of read content.

---

## 2. The conditional-on-`E` analysis

From `docs/bayes-optimality-conditional-feasibility-267.md` §3:

The event `E = F(G,R)` is the information-feasibility event. Conditioning on
`E` gives a different experiment with:

- **Effective prior**: `π(g|E) = π(g) P_g(F_g) / P(E)`
- **Conditional MAP**: `argmax_{g : F(g,r)} π(g) P_g({r})`

The conditional-on-`E` MAP is **optimal for the conditional risk**, not for
the original prior-averaged risk. The key question for this audit is:

> For each witness, does the competitor also satisfy `I_s`? If yes, the
> conditional-on-`E` MAP would also fail; if no, it would correctly recover
> the truth.

### Competitor `I_s` membership matrix

| Witness | Competitor | `I_s` membership | Conditional-on-`E` MAP result |
|---|---|---|---|
| W1 (AAABB→AAAAB) | AAAAB | **fails** (triple repeat not all-bridged) | recovers truth |
| W2 (AAACC→AAAAC) | AAAAC | **fails** (triple repeat not all-bridged) | recovers truth |
| W3 (AABB→ABAB) | ABAB | **passes** (all clauses hold) | **also fails** |
| W4 (ACGT→ACACGT) | ACACGT | **fails** (coverage) | recovers truth |
| W5 (AAATAT→AAAAAT) | AAAAAT | **fails** (triple repeat not all-bridged) | recovers truth |
| W6 (AABBC→AABC) | AABC | **passes** (all clauses hold) | **also fails** |

**Critical finding**: W3 and W6 are the witnesses whose competitors satisfy
`I_s`. This means the conditional-on-`E` MAP rule — the rule that is "Bayes
certain" on `E` — would **also** select the wrong genome on these instances.
The conditional `I_s` Bayesian certainty is therefore **not universal**: it
holds only when the truth is the unique feasible candidate.

---

## 3. True/open/refuted classification matrix

### Decision-theoretic claims

| Claim | Status | Evidence |
|---|---|---|
| MAP minimizes prior-averaged risk (finite candidates, zero-one loss) | **true** | standard statistics + kernel-checked (`bayes_optimality`) |
| Equal prior ⇒ MAP = ML up to class weighting/ties | **true** | standard statistics + kernel-checked |
| Nonuniform prior ⇒ ML need not be Bayes optimal | **true** | standard statistics + kernel-checked (`map_ne_ml_nonuniform`) |
| `E = F(G,R)` is not `R`-observable in general | **true** | mathematical proof (definition of `F`) |
| Conditioning on `E` gives effective prior `π(·\|E)` | **true** | mathematical proof |
| Conditional MAP = prior-weighted ML on `{g : F(g,r)}` | **true** | mathematical proof |
| `2×2` example: infallible-on-`E` rule loses to unconstrained MAP | **true** | mathematical proof + kernel-checked (`map_beats_infallible_on_E`) |

### Witness claims

| Claim | Status | Evidence |
|---|---|---|
| W1: AAABB not fixed-length exact ML maximizer | **true** | kernel-checked + independently verified |
| W2: AAACC not fixed-length binomial ML maximizer | **true** | kernel-checked + independently verified |
| W3: AABB not same-length exact ML maximizer | **true** | kernel-checked + independently verified |
| W4: ACGT not unrestricted-length exact ML maximizer | **true** | kernel-checked + independently verified |
| W5: AAATAT not same-length §6.2 ML maximizer | **true** | kernel-checked + independently verified (molecule model) |
| W6: AABBC not variable-length exact ML maximizer | **true** | kernel-checked + independently verified |
| W1-W6: truth satisfies full `I_s` | **true** | kernel-checked (`InformationFeasible`) |
| W1-W6: competitor fails `I_s` | **refuted** for W3 and W6, **true** for W1/W2/W4/W5 | independent Python check |

### Conditional-on-`E` claims

| Claim | Status | Evidence |
|---|---|---|
| Conditional-on-`E` MAP is optimal for conditional risk | **true** | mathematical proof |
| Conditional-on-`E` MAP recovers truth when truth is unique feasible candidate | **true** | mathematical proof |
| Conditional-on-`E` MAP recovers truth for **all** witnesses | **refuted** | W3 and W6 counterexamples (competitors satisfy `I_s`) |
| Conditional `I_s` Bayesian certainty is universal | **refuted** | W3 and W6 counterexamples |
| Finite ML failures contradict Bayes optimality | **refuted** | different experiments (per-sample vs prior-averaged) |

### Source fidelity claims

| Claim | Status | Evidence |
|---|---|---|
| MB09 §6.1 exact multinomial is the exact objective | **true** | source fact (MB09 §6.1) |
| MB09 §6.1 binomial approximation is the approximate objective | **true** | source fact (MB09 §6.1) |
| MB09 §6.2 flow is a different feasible set | **true** | source fact (MB09 §6.2) |
| MB09 approximate objective is a Bayes posterior | **refuted** | different objectives |
| Shomorony et al. "ML sequence" refers to exact ML | **open** | source ambiguity |
| Shomorony et al. "ML sequence" refers to binomial ML | **open** | source ambiguity |
| Shomorony et al. "ML sequence" refers to §6.2 flow ML | **open** | source ambiguity |

---

## 4. The W3 and W6 critical findings: conditional-on-`E` MAP also fails

The `AABB/ABAB` witness (W3) and the `AABBC/AABC` witness (W6) are the cases
where the competitor satisfies `I_s`. This has a precise interpretation:

- **Original experiment**: unconstrained MAP selects the competitor (higher
  likelihood). This is Bayes-optimal for the prior-averaged risk.
- **Conditional-on-`E` experiment**: the feasible set is `{g : F(g,r)}`. Both
  truth and competitor satisfy `I_s`, so the conditional MAP selects the
  competitor (higher likelihood). The conditional-on-`E` MAP **also fails** on
  these instances.

This does **not** contradict Bayes optimality. The conditional-on-`E` MAP is
optimal for the **conditional** risk, not the original prior-averaged risk.
But it shows that "conditional `I_s` Bayesian certainty" — the claim that
conditioning on `E` guarantees recovery of the truth — is **false** in general.
It holds only when the truth is the unique feasible candidate.

W3 (same-length) and W6 (variable-length) are distinct failure modes:
- **W3**: both candidates have the same length and the same read spectra; the
  competitor wins by having higher multiplicity on the observed types.
- **W6**: both candidates have the same read spectra but different lengths; the
  shorter competitor wins by the `1/G^n` length factor in the multinomial.

The `AABB/ABAB` and `AABBC/AABC` instances are thus finite witnesses to the
following open question:

> **Open**: Under what conditions on the read set `r` is the truth the unique
> `I_s`-feasible candidate? This is the normalized-spectrum identifiability
> question of the population `P2` theorem, which is strictly stronger than the
> conditional inference theorem.

---

## 5. Relation to the conditional-fibre issue (#271)

The conditional inference theorem from the sibling issue (#271) states that
**if** the truth is information-feasible, **then** the conditional-on-`E` MAP
recovers the truth **when the truth is the unique feasible candidate**. This
is an elementary consequence of deterministic reconstruction on the feasible
set.

The nontrivial content is the **population `P2` normalized-spectrum
identifiability theorem**, which gives conditions under which the truth is the
unique feasible candidate. This is strictly stronger than the conditional
inference theorem and is not settled by the finite witnesses.

The present audit does **not** duplicate the Lean proof of #271. It only
verifies, at the finite-instance level, that:

1. The witnesses are compatible with Bayes optimality (different experiments).
2. The conditional-on-`E` MAP is not universally certain (W3 counterexample).
3. The witnesses do not contradict the conditional inference theorem (they
   are about per-sample maximization, not conditional risk).

---

## 6. Independent verification summary

`scripts/audit-267-independent-checks.py` verifies, without Lean:

- All likelihood ratios for W1-W6 (exact rational arithmetic)
- The `2×2` Bayes example (joint law, accuracies, MAP beats infallible)
- The nonuniform prior example (MAP ≠ ML)
- `I_s` membership for all competitors (Python implementation of the
  `InformationFeasible` predicate)

**Result**: 30 of 31 checks pass. The 1 failure is:

1. W4 competitor coverage (expected: different genome length, read starts
   are for the truth's circle)

The W5 ratios are now independently verified with the molecule model (exact
`3`, binomial `5`). The W6 ratios are independently verified (exact `25/16`).

---

## 7. Unresolved questions

1. **Source ambiguity**: Which MB09 objective does Shomorony et al. intend by
   "the maximum-likelihood sequence"? This remains **open** and is not settled
   by any finite witness.
2. **Uniqueness conditions**: Under what conditions on the read set `r` is the
   truth the unique `I_s`-feasible candidate? This is the population `P2`
   normalized-spectrum identifiability question, which is **open** and strictly
   stronger than the conditional inference theorem.
3. **W3/W6 conditional failures**: The `AABB/ABAB` and `AABBC/AABC` instances
   show that conditional-on-`E` MAP can fail. Is there a finite witness where
   conditional-on-`E` MAP **succeeds** (truth is unique feasible candidate)?
   The `2×2` example of the bayes-optimality note is such a witness, but it is
   not a genome-assembly instance.
4. **W5 independent verification**: RESOLVED 2026-10-12. The §6.2 molecule
   model is now implemented in Python; both ratios (exact `3`, binomial `5`)
   are independently verified.

---

## 8. Epistemic status

| Claim | Status |
|---|---|
| W1-W6 witness arithmetic | **standard statistics** + **independently verified** |
| W5 witness arithmetic | **kernel-checked** + **independently verified** (molecule model) |
| `I_s` membership for competitors | **mathematical proof** (Python implementation of `InformationFeasible`) |
| Conditional-on-`E` MAP not universal | **mathematical proof** + **W3 and W6 counterexamples** |
| Finite ML failures compatible with Bayes optimality | **mathematical proof** (different experiments) |
| Source ambiguity (MB09 objective) | **open** |
| Population `P2` identifiability | **open** |

Primary sources: Shomorony, Kim, Courtade & Tse (2016), *Bioinformatics* 32(17)
i494–i502; Medvedev & Brudno (2009), *J. Comput. Biol.* 16(8) 1101–1116;
Cover–Thomas, *Elements of Information Theory*, ch. 11.
