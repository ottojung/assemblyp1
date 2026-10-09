# The implication lattice of the finite AssemblyP1 statement (issue #216)

_Status: META front #217 integration record, 2026-10-09. This note is the
prose half of the cross-variant transfer table whose kernel-checked half is
`AssemblyP1/ImplicationLattice.lean` and whose computational half is
`scripts/verify_implication_lattice_216.py` (79/79 assertions pass, exact
`fractions.Fraction`). It was referenced by the #216 module and script but was
never committed; front #217 records it here so the reference is no longer
dangling. Nothing in it selects a referent for the 2016 sentence; see
[`source-notes/mb-formulation-referent-reconciliation.md`](source-notes/mb-formulation-referent-reconciliation.md)._

Every claim is tagged **F** (source fact), **I** (source-supported inference),
**C** (modelling choice), **M** (mathematical fact), **K** (kernel-checked),
**V** (verified computation), or **O** (open), as in the interpretation matrix
[`source-notes/interpretation-matrix-217.md`](source-notes/interpretation-matrix-217.md).

---

## 0. Purpose

The published sentence “whether bridging conditions can be used to guarantee
that the maximum-likelihood sequence is the true sequence” can denote several
logically distinct propositions, indexed by objective, strand convention,
candidate class, candidate length, and conclusion schema. A strict witness in
one cell settles every *superset* cell that contains the same pair, but a
positive result does **not** lift from a subclass to a superclass. This note
records those transfer edges and the schema reach of each witness, so that the
matrix's “resolved” claim is not read as settling cells a witness cannot reach.

## 1. The axes

### 1.1 Objective family (the likelihood layer)

| tag | definition | source |
|---|---|---|
| `E` | exact MB09 §6.1 multinomial with candidate-intrinsic `N(D)`: `∏ᵢ (dᵢ/N(D))^{xᵢ}` (the observation-only coefficient cancels in every ratio) | **F** |
| `A'` | fixed-`N` multinomial *factor* part with external `N`: `∏ᵢ (dᵢ/N)^{xᵢ}(1−dᵢ/N)^{n−xᵢ}` | **F** |
| `A_lit` | the literal §6.1 product of binomial marginals with the `C(n,xᵢ)` coefficients retained | **F** |

`E` and `A'`/`A_lit` differ: `E` uses candidate-intrinsic length and no
complementary `(1−p)` factor; `A'`/`A_lit` fix `N` externally and include the
complementary factor. **[M]** The exact/fixed-`N` conversion identity
`E(D)/E(S) = (G/|D|)^n · A'(D)/A'(S)` is kernel-checked (`conversion`) and
verified computationally on every panel below. **[K]**, **[V]**

### 1.2 Panel (strand convention)

| tag | definition | source |
|---|---|---|
| oriented | oriented length-`L` read strings, no reverse-complement collapse | **F** for Shomorony §2 |
| molecular | reverse-complement molecule classes `{w, rc(w)}` | **F** for MB09 §3.1/§4.1 |

The abstract `{A,B}` alphabet of the #31/#32/#88 witnesses has no complement
map, so the molecular panel is **undefined** there (recorded as `n/a`, not as a
non-strict cell). **[M]**

### 1.3 Candidate classes and inclusion edges

The classes form a partial order by inclusion. A **strict** witness refutes the
maximizer schema over every class that contains its competitor (transfer
outward); a **positive** result over a subclass does **not** lift to a
superclass (`positive_result_does_not_lift`). **[K]**

### 1.4 Conclusion schemas

Five schemas, from weakest to strongest: dominance over the class
(`Dominates`); maximizer conditional on membership
(`MaximizesIfMember`); maximizer with the truth's membership
(`IsMaximizerWithMembership`); uniqueness up to rotation; uniqueness up to
dihedral equivalence. `unique_implies_maximizer_with_membership` and
`maximizer_with_membership_implies_dominates`/`…maximizes_if_member` give the
implication chain; a strict witness refutes all of them
(`strict_refutes_dominance`, `strict_refutes_maximizer_membership`,
`strict_refutes_maximizes_if_member`, `strict_refutes_unique`); a tie refutes
only the uniqueness schemas (`tie_refutes_unique`). **[K]** A membership
failure refutes `IsMaximizerWithMembership` but is **not** a strict witness
(`membership_failure_refutes_maximizer_with_membership`,
`membership_failure_is_not_strict`). **[K]**

## 2. Candidate-universe inclusion edges (rendered by the script, §E1)

| edge (sub ⊆ super) | strict witness | maximizer theorem | note |
|---|---|---|---|
| length-`G` candidates → free length | transfers outward | does **not** lift | same-length witness reaches the free class |
| §6.2-spelled candidates → free length | transfers outward | does **not** lift | #24/#40 reach every superset |
| genuine §6.2 candidates → §6.2-spelled | transfers outward | does **not** lift | `genuine62_support_eq` gives the bridge |
| literal §6.2 flow class → free length | transfers outward | does **not** lift | the #88 witness `ABAB` reaches the free class |
| §6.2-spelled candidates ↔ literal §6.2 flow class | no transfer | no transfer | no inclusion either way: they branch |

## 3. Witness × interpretation cell (rendered by the script, §E2)

`STRICT` = certified ratio `> 1`; `tie` = ratio `= 1`; `D=0` = the competitor
cannot spell an observed type in that panel so its likelihood is `0` (not a
witness); `< 1` = the competitor is strictly worse (not a counterexample);
`n/a` = panel undefined.

| witness | `|D|=G` | `E/or` | `E/mol` | `A'/or` | `A'/mol` | `A_lit/or` | `A_lit/mol` |
|---|---|---|---|---|---|---|---|
| #31 fixed-length exact | yes | STRICT | n/a | STRICT | n/a | STRICT | n/a |
| #32 fixed-length binomial | yes | STRICT | STRICT | STRICT | STRICT | STRICT | STRICT |
| #24 free-length exact | no | STRICT | tie | STRICT | STRICT | STRICT | STRICT |
| #43 §6.2 same-length | yes | `D=0` | STRICT | `D=0` | STRICT | `D=0` | STRICT |
| #40 §6.2 free-length | no | STRICT | STRICT | STRICT | STRICT | STRICT | STRICT |
| #88 §6.2 dominance | yes | STRICT | n/a | STRICT | n/a | STRICT | n/a |
| W-σ | yes | STRICT | tie | STRICT | tie | STRICT | tie |
| W-υ | no | `<1` | STRICT | tie | STRICT | `<1` | STRICT |
| W-λ₁ | no | STRICT | STRICT | tie | tie | STRICT | STRICT |
| W-λ₂ | no | tie | tie | STRICT | STRICT | `D=0` | `D=0` |
| W-τ | yes | tie | tie | tie | tie | tie | tie |

The five new `I_s`-certified witnesses of §B (W-σ, W-υ, W-λ₁, W-λ₂, W-τ)
separate panels that the `main` witnesses do not; W-τ is the tie witness whose
competitor is `rc(S)`, so it refutes uniqueness under rotation but **not** under
dihedral equivalence. **[V]**

## 4. Schema reach of each witness (rendered by the script, §E3)

Every `STRICT` witness refutes all five schemas, because strictness alone
refutes even the weakest dominance schema. **[M]** W-τ is the sole exception:
it is a tie, so it refutes uniqueness only under the rotation equivalence and
not under dihedral equivalence (`D = rc(S)`). **[V]**

## 5. Kernel-checked schema facts (`AssemblyP1/ImplicationLattice.lean`)

Part 1 (schemas over an explicit candidate universe): `Dominates`,
`MaximizesIfMember`, `IsMaximizerWithMembership`, `IsUniqueMaximizerUpTo`, and
the implication/refutation lemmas `unique_implies_maximizer_with_membership`,
`maximizer_with_membership_implies_dominates`,
`maximizer_with_membership_implies_maximizes_if_member`,
`strict_refutes_dominance`, `strict_refutes_maximizer_membership`,
`strict_refutes_maximizes_if_member`, `strict_refutes_unique`,
`tie_refutes_unique`, `membership_failure_refutes_maximizer_with_membership`,
`membership_failure_is_not_strict`, `strict_refutes_superclass`,
`dominance_restricts`, `positive_result_does_not_lift`,
`dominance_of_cofinal`, `refuting_a_conditional_requires_the_antecedent`.
Part 2 (objective family): `multinomialFactor_eq_div_pow`, `conversion`,
`same_length_ratios_coincide`. Every one depends only on
`[propext, Classical.choice, Quot.sound]`. **[K]**

## 6. Computational verification

`python3 scripts/verify_implication_lattice_216.py` re-implements the read and
bridging layers independently of `AssemblyP1/SourceFaithfulIs.lean`, recomputes
every witness and ratio above under every panel, checks the conversion identity,
and runs a bounded census of the transfer categories. **79/79 checks pass.**
The census counts are **bounded evidence**, not proofs: a zero count in a range
is a negative search result, never a theorem. **[V]**

## 7. The sample-multiplicity axis (amplification): pending in this module

A later #216 research pass added a *sample-multiplicity* axis — how the ratio
changes when the same observed read type is seen `m` more times. Its exact
statements (the `E` multiplier `(p_D(w)/p_S(w))^m`, the fixed-`N` binomial
multiplier `Q_w^m`, the population `KL` decomposition, and the three
strict/tie/failure regimes) are recorded in an **uncommitted** `Part 6` of
`AssemblyP1/ImplicationLattice.lean` that **does not compile** (its `Finset`
reindexing and `omega` steps fail). It is therefore **not** part of the
kernel-checked lattice and is not claimed here. **[O]**

The *result* of that axis is nonetheless already landed independently by front
**#210**: `docs/source-notes/oriented-variable-length-se62.md` proves the
exact-ML amplification lemma and the fixed-`N` binomial amplification lemma as
mathematical facts, and `AssemblyP1/OrientedVariableLengthSe62.lean`
kernel-checks concrete instances (ratios `15625/11664` at `M = 1`,
`2109375/823543` at `M = 2`; binomial `81/64`, `27/16`), with the growing- and
fixed-competitor families strict for every `M ≥ 1`. The amplification mechanism
is thus kernel-checked in the matrix rows R14 and R10/R12; only the *general*
`Part 6` formalization remains pending. **[K]** for #210; **[O]** for `Part 6`.

## 8. Epistemic status

| claim | status |
|---|---|
| The five conclusion schemas and their implication/refutation relations | **K** (`ImplicationLattice` Part 1) |
| The exact/fixed-`N` conversion identity | **K** (`conversion`) + **V** |
| The transfer edges and the witness × cell table | **V** (script §E) |
| A strict witness refutes every schema; a tie refutes only uniqueness | **K** (`strict_refutes_*`, `tie_refutes_unique`) |
| W-τ refutes rotation-uniqueness but not dihedral-uniqueness | **V** |
| The sample-multiplicity amplification `Part 6` formalization | **O** (uncommitted, does not compile) |
| The amplification result itself | **K** via #210 (`OrientedVariableLengthSe62`) |
| The 2016 likelihood referent | source gap, unchanged |
