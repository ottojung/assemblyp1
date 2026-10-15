# Manuscript synthesis for the finite-read exponential exact-ML error bound (issue #281)

**Owner:** agent `2bc7113cebd1`. **Repository:** `github.com/ottojung/assemblyp1`.
**Base:** `main` (this note was written against the state that already contains
the merged PR #234, merge commit `b4071f5`, head `4572a9f`).

This note is the durable, repository-level record for the manuscript-synthesis
part of board issue #281 (part B(6) of the issue). It does two things:

1. states exactly which kernel-checked result is now carried in the white paper
   and under which caveats, with the precise Lean endpoint names; and
2. audits the **provenance and manuscript-integration status** of the
   already-merged results the issue asks to elevate.

It changes no Lean proof file and introduces no `sorry`/`admit`/`axiom`.

---

## 1. The result carried in the narrative

The paper now states, in the abstract, the introduction contributions, the
discussion, and the Appendix B claim-scope table, the explicit uniform
exponential bound on the probability of **exact maximum-likelihood error** over
the primitive-P2 candidate class.

**Lean module:** `AssemblyP1/PrimitiveP2UniformSeparation.lean`, audited in
`AssemblyP1/PrimitiveP2UniformSeparationAudit.lean` (merged in PR #234).

**Kernel-checked endpoints:**

| Endpoint | Content |
| --- | --- |
| `readLaw_separation` | if the uniform-start read laws of `S`, `D` differ, some word `w` has `1/(G_S G_D) <= |p_S(w) - p_D(w)|` |
| `abs_sub_le_two_abs_sqrt_sub` | coordinate inequality `|p - q| <= 2 |sqrt p - sqrt q|` on `[0,1]` |
| `one_sub_hellinger_ge_of_gap` | with the Hellinger identity, `1 - rho >= 1/(8 (G_S G_D)^2)` |
| `hellinger_le_of_length_bound` | with `G_S, G_D <= B`, `rho <= 1 - 1/(8 B^4)` |
| `primitiveP2_exponential_error_bound` | `Pr[exists nonrotational admissible D : L_D >= L_S] <= N_C exp(-n/(8 B^4))` |
| `primitiveP2_ML_confidence_explicit` | `n >= 8 B^4 log(N_C/delta)` suffices for error at most `delta` |
| `readLawFamily_card_le` | `N_C <= sum_{g=1}^{B} q^g` |
| `separation_gap_strict_at_L2` | non-vacuity: `1 - 1/(8 * 4^4) < 1` at `L = 2` |

Here `q = |alpha|`, `L >= 2` is the read length, `B = 2 q^(L-1)` is the
primitive-P2 length bound, and `N_C` is the number of distinct competitor read
laws (rotations of `S` removed). The theorem bounds the exact iid multinomial
ML **error probability** (ties counted as errors via the `>=` event), not the
likelihood, and it does not assert monotonicity of per-truth success.

**Honest caveats (recorded in the paper text and in the status table):**

* the constants are deliberately loose and exponential in the read length `L`;
  this is a positive rate, not a tractability or efficiency claim;
* the scope is oriented exact iid reads on the primitive-P2 admissible class;
  it is **not** universal maximum likelihood over all genomes and **not** the
  Medvedev--Brudno §6.1 product-binomial surrogate;
* it is a frequentist uniform-separation statement, distinct from the
  Bayes/MAP optimality rationale;
* it is compatible with the kernel-checked non-monotonicity of finite-sample
  success (`AssemblyP1/NonmonotonicityWitness281.lean: success_not_monotone`).

**Reused, not re-proved:** the finite-iid Hellinger union bound
(`FiniteReadRecovery.eventProb_pairwise`, `eventProb_wrong_le_card`,
`circular_wrong_le_card`), the length bound `primitive_P2_len_le`, the candidate
families `nonRotationalCandidates`/`primitiveP2Candidates`, and the structural
separation `equal_laws_imply_rotation_of_primitiveP2`.

**Axioms:** `{propext, Classical.choice, Quot.sound}` only (audit module).

---

## 2. Provenance and integration status of the named elevated results

Status legend: **INTEGRATED** (stated in the paper with a precise pointer),
**PARTIAL** (the paper states a related/directional part, not the full result),
**NOT INTEGRATED** (exists as a repository endpoint but is not developed in the
paper narrative), **HANDOFF** (integration, if wanted, belongs to another
issue).

| Issue | Result | Exact endpoint(s) | Manuscript status |
| --- | --- | --- | --- |
| GitHub #92 | variable-length **primitive** identifiability iff outgoing-edge nonbranching | `ScalarPrimitiveSpellings.identifiable_iff_nonbranching` | **NOT INTEGRATED**. The paper's population theorem is the primitive-**P2** case; the general nonbranching classification is not stated. |
| Antonina #219 (GitHub #83) | exact same-length complete-spectrum **fibre count** / BEST + Matrix-Tree singleton criterion | mathematical proof in `docs/exact-fibre-count-theorem-219.md`; divisor-sum core kernel-checked in `FibreCountArithmetic.fibre_mobius_inversion`, `fibre_totient` | **NOT INTEGRATED** (partial Lean status: the arithmetic core is kernel-checked, the full count is a mathematical proof with independent bounded computation). |
| Antonina #256 | exact **robust same-length** oriented ML iff | `RobustSameLengthIff.robust_iff_unique`, `robust_iff_unique_spectrum` (plus `F_eq_singleton_of_rigidity`, `robust_of_rigidity`) | **PARTIAL**: the paper states the beatability direction (`prop:beatability`, `lem:negative-transfer`); the full iff is not stated. |
| Antonina #257 | exact circulation / **Graver rigidity beyond repeat bounds** | `TwoWalkRigidity.rigid_iff_no_two_nonneg_circ`, `ExactRigidityCriterion.nonrigid_iff_exists_delta`, `FiniteRigidityDecider.rigid_iff_decider` | **PARTIAL**: the paper states a related Graver certificate (`thm:graver-rigidity`, `GraverRigidity.lean`); the #257 exact-criterion/two-walk/decider endpoints are not separately integrated. |
| Antonina #260 | source-faithful **full-overlap molecule** ML maximality iff | `FullOverlapMoleculeML.robust_maximality_iff_unique`, `robust_maximality_of_unique` | **PARTIAL**: the paper states the molecule **negative** witnesses (`thm:cex-molecule`) and the full-overlap support proxy; the positive iff is not stated. |
| GitHub #89/#94 | primitive-P2 **population uniqueness** | `Issue94Complete.population_unique_ML` | **INTEGRATED** (`thm:population`, `popml`); no external Eulerian-obstruction premise. |
| historical witnesses | strict same-length molecule counterexamples under the source read-string predicate | `HistoricalCoverageSameLengthWitnesses.W1.w1_historical_literal_se62_flow_counterexample`, `W2.w2_historical_literal_se62_flow_counterexample` | **INTEGRATED** (`thm:cex-historical-W1`, `thm:cex-historical-W2`). |
| #281 (this issue) | explicit uniform exponential exact-ML error rate | `PrimitiveP2UniformSeparation.primitiveP2_exponential_error_bound`, `primitiveP2_ML_confidence_explicit` | **INTEGRATED** by this increment (abstract, contributions, discussion, Appendix B, `docs/verification.md`). |

### Interpretation

The manuscript already distinguishes the domains the issue asks it to keep
apart: full genome uniqueness vs spectrum uniqueness, fixed vs arbitrary
candidate length, primitive candidate universe vs unrestricted, ordinary exact
multinomial vs product-binomial approximation, and graph-flow objects vs
spelled genomes (Appendix B and Appendix D). The not-integrated and partial
rows above are repository-level endpoints whose full statements would extend
particular model domains; developing them in the main text is a separate,
larger editorial task and, where it touches the 2016-comparison axis or the
presentation, belongs to #268 and #265 respectively (see the handoff note in
section 3).

---

## 3. Handoffs and remaining limits

* **#265 (presentation).** Slides are owned by #265 and were not edited here.
  The explicit rate `N_C exp(-n/(8 B^4))` and the loose-constant caveat are
  available for the decks if #265 wants to add them.
* **#268 (2016-comparison section).** The #92 nonbranching classification and
  the #219 fibre-count criterion sit closest to the 2016 structural comparison;
  if they are to be stated in the paper, #268 should own that edit.
* **Remaining open limits (unchanged by this increment):** universal maximum
  likelihood over all genomes (arbitrary length, all models); the MB09
  product-binomial surrogate's finite-sample behaviour under its own objective;
  the reverse-complement molecule domain; and a sharp (non-exponential-in-`L`)
  uniform sample size.

## 4. What this increment changed

* `paper/main.tex`: subtitle and abstract now state the kernel-checked explicit
  exponential error bound and its caveats.
* `paper/sections/01-introduction.tex`: the contributions paragraph
  "Finite-read error exponent" now displays the explicit bound and threshold.
* `paper/sections/06-discussion.tex`: the proof-contribution and conclusion
  paragraphs reference `thm:p2-uniform-rate`.
* `paper/sections/b-epistemic-ledger.tex`: new claim-scope row for the explicit
  uniform rate; the finite-family row no longer claims no constant is available.
* `docs/verification.md`: new claim-to-proof row and updated error-exponent
  caveat.
* this note.

No `AssemblyP1/*.lean` file and no `slides/` file was modified.
