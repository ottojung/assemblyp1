# The cross-variant implication lattice of the finite AssemblyP1 statement (issue #216)

_Status: research note for issue #216, 2026-10-09. It builds the rigorous
cross-variant transfer table requested by the issue, distinguishes the four
logical readings of “the maximum-likelihood sequence is the true sequence,”
proves which candidate-universe inclusions transfer **strict** counterexamples
and which do not, cross-checks the #88 correction, and indexes every claim to a
kernel-checked theorem, a verified computation, or a source note. It does **not**
select a published interpretation, settle the open problem, or promote a
project-level strengthening to a source fact._

## 0. What this note decides and what it leaves open

The published sentence

> “Understanding whether bridging conditions can be used to guarantee that the
> maximum-likelihood sequence is the true sequence is currently an open
> question.” (Shomorony, Kim, Courtade & Tse 2016, Discussion)

is logically under-determined along several independent axes. This note fixes
the *transfer logic* between those axes — the part that is source-independent
mathematics — and records, axis by axis, which strict counterexample reaches
which variant.

The load-bearing finding is:

> **Strictness transfers outward along candidate-universe inclusion; positive
> results transfer only inward; and a tie or a membership failure transfers
> along neither.** A strictly more likely candidate refutes every maximizer
> schema for *every* genome equivalence and *every* tie convention; a tied
> candidate can only ever refute a uniqueness schema; and a candidate that is
> not in the class does not refute a conditional whose antecedent is false.

This is the mathematical core. Everything else is instantiation on the axes.

| Axis | Values kept distinct here | Status |
|---|---|---|
| conclusion schema | dominance / conditional / maximizer-with-membership / uniqueness-up-to-`r` | source gap + mathematical fact |
| objective | exact multinomial `E`, fixed-`N` factor `A'`, literal §6.1 binomial `A_lit` | source fact (MB09 §6.1 defines `E` and `A`) |
| candidate length | fixed `|D| = G`, free `|D| ≠ G` | source gap |
| strand panel | oriented read types, reverse-complement molecule classes | source fact (MB09 §3.1/§4.1; Shomorony §2/§4.1) |
| genome equivalence | cyclic shift, dihedral (shift + reverse complement) | mathematical fact (coupled to panel) |
| candidate feasibility | free circular, §6.2 support-spelled, literal §6.2 flow | source fact + modeling |
| sample multiplicity | population, finite-sampled | mathematical fact |
| constraint kind | per-vertex/source vs. per-occurrence editorial (`d_w ≥ x_w`) | modeling |

## 1. The conclusion schemas and the implication graph

Over an arbitrary objective `L : C → ℝ`, an explicit candidate universe `U`, and
an explicit genome equivalence `r`, four schemas are separated in
`AssemblyP1/ImplicationLattice.lean` (Part 1):

```text
Dominates L U S                := ∀ D ∈ U, L D ≤ L S
MaximizesIfMember L U S        := S ∈ U → Dominates L U S
IsMaximizerWithMembership L U S := S ∈ U ∧ Dominates L U S
IsUniqueMaximizerUpTo L U S r  := S ∈ U ∧ Dominates L U S ∧ ∀ D ∈ U, L D = L S → r D S
```

The positive implication graph is the chain

```text
IsUniqueMaximizerUpTo  →  IsMaximizerWithMembership  →  { Dominates , MaximizesIfMember }
```

proved by `unique_implies_maximizer_with_membership`,
`maximizer_with_membership_implies_dominates`,
`maximizer_with_membership_implies_maximizes_if_member`. The **conditional**
`MaximizesIfMember` is the shape of the published bridging implication
(`AssemblyModel.BridgingImpliesMaximumLikelihood`); it is the weakest schema and
the only one that survives a membership failure.

### 1.1 What refutes what

| Hypothesis on the candidate `D` | Dominates | Maximizer+membership | Conditional | Unique up to `r` |
|---|---|---|---|---|
| `D ∈ U`, `L S < L D` (strict) | refuted | refuted | refuted **iff `S ∈ U`** | refuted, **every `r`** |
| `D ∈ U`, `L D = L S`, `¬ r D S` (tie) | survives | survives | survives | refuted |
| `S ∉ U` (membership) | survives | refuted | survives (vacuous) | refuted |

Kernel-checked by `strict_refutes_dominance`,
`strict_refutes_maximizer_membership`, `strict_refutes_maximizes_if_member`,
`strict_refutes_unique`, `tie_refutes_unique`,
`membership_failure_refutes_maximizer_with_membership`, and
`membership_failure_is_not_strict`. The last is the abstract form of the #88
correction (§6). `refuting_a_conditional_requires_the_antecedent` records that
refuting `H → C` requires `H`.

The strict column does not mention `r`, which is the formal content of
“strictness is equivalence-proof” (source note
`docs/source-notes/conclusion-semantics-strict-witness-robustness.md`, §3).

### 1.2 Candidate-universe inclusion

For `U' ⊆ U`:

- **Strict witnesses transfer outward** (`strict_refutes_superclass`): a strict
  witness inside the subclass refutes dominance over every superclass. This is
  the half the repository’s witnesses use.
- **Positive results transfer inward only** (`dominance_restricts`): dominance
  over `U` implies dominance over `U'`.
- **The converse does not hold** (`positive_result_does_not_lift`): a maximizer
  over `{0,2}` need not be a maximizer over `univ`. A theorem over a restricted
  candidate class is a restricted result.
- **Quotienting by a value-cofinal subuniverse changes nothing**
  (`dominance_of_cofinal`): if every candidate has an equal-value representative
  in `V ⊆ U`, dominance over `U` and `V` agree. This is why the rotation orbit of
  a candidate may be quotiented without touching the maximizer schema; the
  equivalence enters only the tie clause of the uniqueness schema.

### 1.3 The inclusion edges instantiated for this project

| Edge (sub ⊆ super) | strict witness | maximizer theorem | basis |
|---|---|---|---|
| length-`G` candidates ⊆ free length | transfers outward | does not lift | `strict_refutes_superclass`; witness `#31`/`W-sigma` |
| §6.2-spelled candidates ⊆ free length | transfers outward | does not lift | `#24`/`#40` |
| genuine §6.2 candidates ⊆ §6.2-spelled | transfers outward | does not lift | `SameLength62Maximizer.genuine62_molecule_eq` |
| literal §6.2 flow class ⊆ free length | transfers outward | does not lift | `#88` witness `ABAB` |
| §6.2-spelled vs. literal §6.2 flow | **no inclusion either way** | does not lift | the two classes branch |

The last row is the honest boundary: the support-spelled class and the literal
flow class are not nested (a literal flow may visit only a subset of the observed
read types), so no strict witness transfers between them.

## 2. The objective family and the exact/fixed-`N` conversion

Medvedev–Brudno (2009) §6.1 defines the **exact multinomial** with
candidate-intrinsic `N(D)` (contract Variant E) and a **fixed-`N`
product-of-binomial-marginals approximation** (Variant A). For a truth of length
`G`, competitor of length `m`, external `N = G`, and `n = ∑_w x_w` reads,
`conversion` proves

```text
E(D)/E(S) = (G/m)^n · A'(D)/A'(S).
```

Consequences, both kernel-checked:

- at `m = G` the length factor is `1`, so `E` and the fixed-`N` factor objective
  `A'` have **identical** ratios (`same_length_ratios_coincide`): a same-length
  strict witness transfers between the two objectives in both directions;
- at `m ≠ G` they differ by the length factor, so a free-length strict witness
  need not transfer. The witnesses `W-lambda1` (`AAT → AT`, shorter) and
  `W-lambda2` (`AT → ATAT`, longer) exhibit both failure directions: `E` strict /
  `A'` tie, and `A'` strict / `E` tie, respectively.

The literal §6.1 binomial `A_lit` (with its `n - x_i` exponents) is a third,
distinct objective; `W-lambda2` has `A_lit(D) = 0` because `d_w = N` at an
unobserved type (the `p = 1` boundary), while `E` ties and `A'` is strict.

## 3. The strand panel: oriented versus reverse-complement molecule

Two coupled read-type conventions over the DNA panel `{A,T,C,G}`:

- **oriented**: length-`L` circular substrings; genome equivalence = cyclic
  shift;
- **molecular** (MB09 §3.1/§4.1): reads are reverse-complement *classes*; genome
  equivalence = dihedral (cyclic shift + reverse complement).

The two conventions and the two equivalences are **one coupled choice**:
molecule read types force reverse complement into the equivalence; oriented read
types do not. This is a mathematical fact, recorded in
`docs/source-notes/conclusion-semantics-determination.md` §2.2–2.3.

The strand axis is **not** a one-way transfer. Both directions occur, and both
are kernel-checked in Part 4 (`ConcretePanel`):

- `W-sigma` (`AATT → AAAT`, same length): oriented ratio `2` (strict,
  `sigma_oriented_strict`), molecular ratio `1` (tie, `sigma_molecular_tie`);
  the literal §6.1 binomial behaves the same
  (`sigma_alit_oriented_strict`, `sigma_alit_molecular_tie`).
- `W-upsilon` (`AAT → AATT`, longer): molecular ratio `27/16 > 1` (strict,
  `upsilon_molecular_strict`), oriented ratio `27/64 < 1` (competitor strictly
  worse, `upsilon_oriented_not_strict`). This is the missing second direction,
  supplied by #216.
- `W-tau` (`AAT → ATT`, same length): every objective ties
  (`tau_E_tie_oriented`, `tau_E_tie_molecular`), and `D = rc(S)`
  (`tau_D_eq_rc_S`) is not a rotation of `S`, so the uniqueness-up-to-rotation
  schema is refuted while uniqueness-up-to-dihedral is not.

So a strict counterexample under one strand panel does **not** transfer to the
other, in either direction.

## 4. The transfer table

Every entry below is a ratio `L(D)/L(S)` recomputed exactly by
`scripts/verify_implication_lattice_216.py` (79/79 checks pass, exit non-zero on
failure). The `W-*` rows are additionally kernel-checked in Part 4
(`ConcretePanel`) of `AssemblyP1/ImplicationLattice.lean`; the `#`-rows are
kernel-checked in their own modules (§7.3). `STRICT` means ratio `> 1`; `tie`
means `= 1`; `<1` means the competitor is strictly worse; `D=0` means the
competitor cannot spell an observed type under that panel, so its likelihood is
`0` (not a witness); `n/a` means the panel is undefined (abstract alphabet).

```text
witness                  |D|=G | E/or  E/mol  A'/or  A'/mol  A_lit/or  A_lit/mol
#31 fixed-length exact   True  | STRICT n/a    STRICT n/a     STRICT    n/a
#32 fixed-length binomial True  | STRICT STRICT STRICT STRICT  STRICT    STRICT
#24 free-length exact    False | STRICT tie    STRICT STRICT  STRICT    STRICT
#43 §6.2 same-length     True  | D=0    STRICT D=0    STRICT  D=0       STRICT
#40 §6.2 free-length     False | STRICT STRICT STRICT STRICT  STRICT    STRICT
#88 §6.2 dominance       True  | STRICT n/a    STRICT n/a     STRICT    n/a
W-sigma                  True  | STRICT tie    STRICT tie     STRICT    tie
W-upsilon                False | <1     STRICT tie    STRICT  <1        STRICT
W-lambda1                False | STRICT STRICT tie    tie     STRICT    STRICT
W-lambda2                False | tie    tie    STRICT STRICT  D=0       D=0
W-tau                    True  | tie    tie    tie    tie     tie       tie
```

The schema reach of each witness (Part 1 applied):

- **any strict cell** refutes dominance, maximizer-with-membership, the
  conditional (where the truth is a member), and uniqueness-up-to-`r` for every
  `r`; every witness except `W-tau` has a strict cell;
- **`W-tau`** has only tie cells and `D = rc(S)`, so it refutes uniqueness only
  under the rotation-only equivalence, not under dihedral. This is the canonical
  “tie refutes only uniqueness” instance.

## 5. The sample-multiplicity axis

The board research-assistant comments (2026-10-09) add a finite-sampling axis,
kernel-checked in Part 3 of `AssemblyP1/ImplicationLattice.lean`:

- **Exact multinomial (E).** Adding `m` further observations of an
  already-observed type `w` multiplies the exact ratio by `(p_D(w)/p_S(w))^m`
  with candidate-intrinsic `p_X(w) = d_X(w)/|X|`
  (`multinomialRatio_addRead`).
- **Fixed-`N` binomial (A).** The same operation multiplies the ratio by `Q_w^m`
  with `Q_w = (p_D(w)/p_S(w)) · ∏_{i≠w} (1-p_D(i))/(1-p_S(i))` and external
  `p_X(i) = d_X(i)/N` (`binomialRatio_addRead`). The two multipliers differ:
  the binomial’s `n - x_i` exponents move for every `i ≠ w`; `Q_w < 1` is
  possible even when `p_D(w) > p_S(w)`.
- **Population KL.** When the observation is exactly proportional to the truth’s
  spectrum, `log L_E(S|x) − log L_E(D|x) = n·KL(p_S‖p_D) ≥ 0`
  (`population_KL`, `population_D_le_S`), with equality iff the spectra agree
  (`population_eq_iff_spectra`). At equal length that is equal k-spectrum, which
  is **not** “`D` is a rotation of `S`” — the maximizer-of-counts versus
  unique-sequence distinction.

The multiplier regimes are the three interpretation cells:
`amplification_strict_of_qMul_gt_one` (`Q_w > 1` amplifies any positive base
ratio past `1`: a strict witness), `amplification_tie_of_qMul_eq_one` (`Q_w = 1`
preserves a tie), and `amplification_failure_of_qMul_lt_one` (`Q_w < 1` drives
the ratio to `0`: the competitor is eventually strictly worse). The zero-`p`
and `p = 1` boundaries are recorded separately
(`multinomialFactor_eq_zero_of_zero_count`, `boundary_strict`,
`binomialFactor_eq_zero_of_full_count`).

**Scope marker.** The amplification preserves per-vertex/source constraints
(`spells_addRead` monotonicity) but does **not** preserve the per-occurrence
editorial constraint `d_w ≥ x_w` of #212: adding copies of `w` raises `x_w`, so
that constraint must be rechecked. The ratio lemmas are silent about both
constraint kinds.

## 6. Cross-check of the #88 correction

The #88 instance is `S = AABB`, `D = ABAB`, `L = 2`, faithful starts `{1,3}`
(so the observation is `{AB:1, BA:1}`). The audit correction
(`docs/same-length-exact-ml-88-refutation.md`) states two points, both
reproduced here:

1. the refuted predicate is **dominance** over the §6.2-feasible class, not
   “truth is a §6.2 candidate and maximizes”;
2. the §6.2 acceptance boundary is **asymmetric**: `AABB` is *not* itself
   §6.2-spelled (its windows `AA`, `BB` are unobserved, so its window walk fails
   `VisitsObserved`), while `ABAB` *is*. The maximizer-with-membership claim has
   a false antecedent at this instance and is not refuted by it.

The Python script checks all six facts: `I_s` certified, `E` and `A'` ratios
`4` (strict), truth **not** §6.2-spelled, competitor §6.2-spelled, truth support
strictly larger than the observation, and dihedral orbits disjoint. The abstract
shape is `membership_failure_is_not_strict` (Part 1): a membership failure
refutes `IsMaximizerWithMembership` but is **not** a strictness refutation, and
the conditional survives it. So the #88 instance refutes dominance (by its
strict competitor) and the membership-bearing schemas (by membership), but does
not test a bridging *implication* whose hypothesis fails.

## 7. Theorem / witness index

### 7.1 Kernel-checked (`AssemblyP1/ImplicationLattice.lean`)

| Theorem | Content | Part |
|---|---|---|
| `unique_implies_maximizer_with_membership` | schema chain | 1 |
| `maximizer_with_membership_implies_dominates` | schema chain | 1 |
| `maximizer_with_membership_implies_maximizes_if_member` | schema chain | 1 |
| `strict_refutes_dominance` | strict refutes dominance | 1 |
| `strict_refutes_maximizer_membership` | strict refutes membership schema | 1 |
| `strict_refutes_maximizes_if_member` | strict refutes conditional (if `S ∈ U`) | 1 |
| `strict_refutes_unique` | strict refutes uniqueness, every `r` | 1 |
| `tie_refutes_unique` | tie refutes uniqueness only | 1 |
| `membership_failure_refutes_maximizer_with_membership` | membership refutes membership schema | 1 |
| `membership_failure_is_not_strict` | #88 correction, abstract | 1 |
| `strict_refutes_superclass` | strict transfers outward | 1 |
| `dominance_restricts` | positive transfers inward | 1 |
| `positive_result_does_not_lift` | converse fails | 1 |
| `dominance_of_cofinal` | quotient by value-cofinal subuniverse | 1 |
| `refuting_a_conditional_requires_the_antecedent` | conditional logic | 1 |
| `multinomialFactor_eq_div_pow` | exact-multinomial algebra | 2 |
| `conversion` | `E(D)/E(S) = (G/m)^n · A'(D)/A'(S)` | 2 |
| `same_length_ratios_coincide` | same-length E/A′ coincidence | 2 |
| `spells_addRead` | source-support monotonicity | 3 |
| `multinomialFactor_pos` / `binomialFactor_pos` | interior-domain positivity | 3 |
| `multinomialFactor_addRead` / `binomialFactor_addRead` | read-addition algebra | 3 |
| `multinomialRatio_addRead` | exact-multinomial amplification | 3 |
| `binomialRatio_addRead` | fixed-`N` amplification, `Q_w` | 3 |
| `multinomialFactor_eq_zero_of_zero_count` / `boundary_D_zero` / `boundary_strict` | zero-`p` boundary | 3 |
| `binomialFactor_eq_zero_of_zero_count` / `binomialFactor_eq_zero_of_full_count` | binomial boundaries | 3 |
| `amplification_strict_of_qMul_gt_one` | `Q_w > 1` ⟹ strict | 3 |
| `amplification_tie_of_qMul_eq_one` | `Q_w = 1` preserves tie | 3 |
| `amplification_failure_of_qMul_lt_one` | `Q_w < 1` ⟹ eventually worse | 3 |
| `kl_pointwise_le` / `kl_eq_sum` / `kl_nonneg` / `kl_eq_zero_iff_eq` | Gibbs and equality case | 3 |
| `log_multinomialFactor` / `population_KL` | population KL decomposition | 3 |
| `population_D_le_S` | truth is a population maximizer | 3 |
| `population_eq_iff_spectra` | equality iff equal spectra | 3 |
| `ConcretePanel.sigma_Is` / `upsilon_Is` / `lambda1_Is` / `lambda2_Is` / `tau_Is` | `I_s` membership of the five `W-*` witnesses | 4 |
| `ConcretePanel.sigma_oriented_strict` / `sigma_molecular_tie` | strand non-transfer, direction 1 | 4 |
| `ConcretePanel.sigma_alit_oriented_strict` / `sigma_alit_molecular_tie` | same, literal §6.1 binomial | 4 |
| `ConcretePanel.upsilon_molecular_strict` / `upsilon_oriented_not_strict` | strand non-transfer, direction 2 | 4 |
| `ConcretePanel.lambda1_E_strict` / `lambda1_A_tie` | objective/length non-transfer, direction 1 | 4 |
| `ConcretePanel.lambda2_A_strict` / `lambda2_E_tie` | objective/length non-transfer, direction 2 | 4 |
| `ConcretePanel.tau_E_tie_oriented` / `tau_E_tie_molecular` / `tau_D_eq_rc_S` | the tie witness | 4 |

### 7.2 Verified computation (`scripts/verify_implication_lattice_216.py`)

Exact `fractions.Fraction` recomputation, independent of the Lean source (it
transcribes the read/bridging layer itself), 79/79 checks:

| Evidence | Content |
|---|---|
| witnesses `#31 #32 #24 #43 #40 #88` | recomputed under both panels and all three objectives |
| `W-sigma W-upsilon W-lambda1 W-lambda2 W-tau` | five new `I_s`-certified witnesses |
| transfer assertions | strictness by panel, ties, exact/fixed-`N` conversion |
| bounded census | counts of each transfer category over binary genomes `G ≤ 4`, `|D| ≤ 5`, `≤ 3` reads; **bounded evidence, not proofs** |
| rendered transfer table | E1 inclusion edges, E2 witness × cell, E3 schema reach |

The census is a **negative search result**, not a theorem: e.g. it finds no
same-length `E`/`A_lit` disagreement in its range, but that is not a proof.

### 7.3 Kernel-checked elsewhere on `main` (concrete witnesses)

| Witness | Lean module | Note |
|---|---|---|
| `#31` fixed-length exact | `AssemblyP1.FixedLengthExactCounterexample` | |
| `#32` fixed-length binomial | `AssemblyP1.FixedLengthBinomialCounterexample` | |
| `#24` free-length exact | `AssemblyP1.ExactVariantECounterexample` | |
| `#43` §6.2 same-length | `AssemblyP1.SameLengthSection62Counterexample` | `docs/section62-same-length-bidirected-counterexample.md` |
| `#40` §6.2 free-length | `AssemblyP1.Section62BridgingCounterexample` | `docs/bridging-se62-flow-ml-counterexample.md` |
| `#88` §6.2 dominance | `AssemblyP1.SameLengthExactMLCounterexample` | `docs/same-length-exact-ml-88-refutation.md` |
| finite-sampling | `AssemblyP1.FiniteSamplingCounterexample` | |

The `W-*` witnesses are kernel-checked in Part 4 (`ConcretePanel`) of
`AssemblyP1/ImplicationLattice.lean`: each `I_s` membership and each key
comparison is a closed `decide` over the concrete genomes, with no
`native_decide`. The exact rational ratio *values* quoted in §3 are the Python
script’s output; Part 4 proves the strict/tie/worse *comparisons* from the
coefficient-free integer keys, which is the logically decisive content.

## 8. Source and assumption surface

- **Source facts.** MB09 §6.1 defines both the exact multinomial with
  candidate-intrinsic `N(D)` and the fixed-`N` binomial approximation; MB09
  §3.1/§4.1 make a read a reverse-complement molecule class; Shomorony et al.
  §2 use oriented length-`L` substrings of a circular genome and leave the
  maximizer-versus-uniqueness reading undetermined. Hashes and locators are in
  `docs/source-notes/conclusion-semantics-determination.md` §1 and
  `docs/source-notes/same-length-witnesses-candidate-set-inclusion.md` §1.
- **Modeling choices (project-level, not source facts).** The explicit
  candidate universes (`U`), the value-cofinal subuniverse, and the separation of
  the per-vertex/source constraint from the per-occurrence editorial constraint
  `d_w ≥ x_w` are this repository’s modeling organization
  (`docs/ml-formalization-contract.md`). The `W-*` witnesses and the census range
  are project-level constructions.
- **Unresolved.** Which objective, candidate length, strand convention, and
  sample regime the published sentence intends; whether the conclusion is
  maximizer or unique-up-to-equivalence. This note preserves those as visible
  forks.

## 9. Reproduce

```sh
lake build AssemblyP1.ImplicationLattice
python3 scripts/verify_implication_lattice_216.py
```

`lake build` compiles the kernel-checked lattice; the Python script exits
non-zero on any failed check. The axiom set of every exported theorem is the
three the project permits — `propext`, `Classical.choice`, `Quot.sound` — with no
`axiom`, `sorry`, `admit`, or `native_decide`.

## 10. Cross-references

- `docs/ml-formalization-contract.md`: the schemas, variants E/A/F, and the
  candidate-universe discipline.
- `docs/source-notes/conclusion-semantics-determination.md`: the source
  determination and residual ambiguity.
- `docs/source-notes/conclusion-semantics-strict-witness-robustness.md`:
  strictness is equivalence-proof.
- `docs/source-notes/same-length-witnesses-candidate-set-inclusion.md`: negative
  transfer across candidate classes.
- `docs/same-length-exact-ml-88-refutation.md`: the #88 correction.
- `docs/open-problem.md`: the source-faithful open statement.
- Parent synthesis: antonina board issue #217.
