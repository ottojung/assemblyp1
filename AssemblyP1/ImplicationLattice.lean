import Mathlib
import AssemblyP1.SourceFaithfulIs

/-!
# The implication lattice of the finite AssemblyP1 statement (issue #216)

This module is the kernel-checked half of the cross-variant transfer table
documented in `docs/implication-lattice-216.md`; the computational half is
`scripts/verify_implication_lattice_216.py`, which transcribes the read/bridging
layer *independently* of `AssemblyP1.SourceFaithfulIs.lean` so that the two
implementations cross-check each other.

**Axiom set.** Every theorem below is proved from `Mathlib` and
`AssemblyP1.SourceFaithfulIs` only. `#print axioms` on each exported theorem
reports the three axioms the project permits — `propext`, `Classical.choice`,
`Quot.sound` — and nothing else. There is no `axiom`, `sorry`, `admit`, or
`native_decide` in this file.

**What this module is for.** The published sentence "the maximum-likelihood
sequence is the true sequence" can denote several logically distinct
conclusions, and each of those conclusions can be tested against several
logically distinct candidate universes measured by several logically distinct
objectives. The four parts below separate those axes and then say, for each
pair of axes, whether a *strict* counterexample transfers.

* **Part 1** proves the source-independent transfer logic of the four conclusion
  schemas over an arbitrary objective and an explicit candidate universe.
* **Part 2** proves the exact/fixed-`N` conversion identity that governs the
  length axis between the two §6.1 objectives.
* **Part 3** proves the finite-sampling and population facts that govern the
  sample-multiplicity axis.
* **Part 4** instantiates the logic on the concrete DNA strand panel and
  kernel-checks the five new `W-*` witnesses: the two directions of strand
  non-transfer, the two directions of objective non-transfer, and the tie
  witness.

The eleven-witness by-cell transfer table is computed in
`scripts/verify_implication_lattice_216.py` and rendered in
`docs/implication-lattice-216.md`; the witnesses already integrated on `main`
are kernel-checked in their own modules (indexed in the note).  Nothing in this
module selects a published interpretation.

**Part 1 — the conclusion schemas as propositions over an explicit candidate
universe.**  The four schemas the English sentence can denote, over an
*arbitrary* objective `L : C → ℝ`, an *explicit* candidate universe `U : Set C`,
and an *explicit* genome equivalence `r`:

* `Dominates L U S` — every candidate is no more likely than the truth, with no
  membership conjunct and no tie rule (the contract's `MaximizerSchema`);
* `MaximizesIfMember L U S` — dominance *conditional on the truth being a
  candidate* (the shape of `AssemblyModel.BridgingImpliesMaximumLikelihood`);
* `IsMaximizerWithMembership L U S` — dominance plus unconditional membership;
* `IsUniqueMaximizerUpTo L U S r` — the above, plus every tied candidate is
  `r`-equivalent to the truth (the contract's `UniqueSchema`).

  The transfer facts proved in Part 1 are source-independent mathematical facts:

* the schemas form the chain `IsUniqueMaximizerUpTo → IsMaximizerWithMembership
  → {Dominates, MaximizesIfMember}` (`unique_implies_maximizer_with_membership`,
  `maximizer_with_membership_implies_dominates`,
  `maximizer_with_membership_implies_maximizes_if_member`);
* a **strictly** more likely candidate refutes `Dominates`,
  `IsMaximizerWithMembership` and `IsUniqueMaximizerUpTo` for *every* equivalence
  `r` and every tie convention, and refutes `MaximizesIfMember` whenever the
  truth is a candidate (`strict_refutes_dominance`,
  `strict_refutes_maximizer_membership`, `strict_refutes_unique`,
  `strict_refutes_maximizes_if_member`);
* a **tied** candidate that `r` does not identify refutes only the uniqueness
  schema (`tie_refutes_unique`), which is why a strict witness is stronger than
  a tie-based one;
* a *membership* failure (`S ∉ U`) refutes `IsMaximizerWithMembership` but is
  **not** a strictness refutation of anything else
  (`membership_failure_refutes_maximizer_with_membership`,
  `membership_failure_is_not_strict`) — the audit correction of issue #88;
* strict witnesses transfer **outward** along candidate-universe inclusion
  (`strict_refutes_superclass`), while dominance transfers only **inward**
  (`dominance_restricts`) and the converse direction is refuted by an explicit
  finite instance (`positive_result_does_not_lift`);
* refuting a conditional `H → C` requires an instance satisfying `H`
  (`refuting_a_conditional_requires_the_antecedent`), so a strict witness
  against a conclusion schema refutes the bridging *implication* only where the
  bridging hypothesis holds;
* dominance is unchanged by passing to a value-cofinal subuniverse
  (`dominance_of_cofinal`), the formal content of "quotienting the candidate
  universe by an invariance of the objective does not change the maximizer
  schema".

**Part 2 — the objective family and the exact/fixed-`N` conversion.**  For a
truth of length `G`, a competitor of length `m`, an external size `N = G` and
`n` observed reads, `conversion` proves

```
E(D)/E(S) = (G/m)^n · A'(D)/A'(S)
```

so the exact multinomial (candidate-intrinsic `N(D)`, contract Variant E) and
the fixed-`N` factor objective (contract Variant A, factor part) have
*identical* ratios at `m = G` and differ by the length factor otherwise.  This
is the reason same-length strict witnesses transfer between the two objectives
and free-length witnesses need not; `same_length_ratios_coincide` and the
`W-lambda*` witnesses of the note are the two halves of that statement.

**Part 3 — the sample-multiplicity axis.**  Two exact finite-sampling
theorems and one population fact, independent of the graph details:

* adding `m` further observations of an already-observed read type `w`
  multiplies the exact-multinomial ratio by `(p_D(w)/p_S(w))^m`
  (`multinomialRatio_addRead`);
* it multiplies the fixed-`N` binomial ratio by
  `Q_w^m = ((p_D(w)/p_S(w)) · ∏_{i≠w}(1-p_D(i))/(1-p_S(i)))^m`
  (`binomialRatio_addRead`), which is a genuinely different multiplier;
* at the population point `x_w = n·p_S(w)`, the truth is *a* maximizer with
  `log L_E(S|x) - log L_E(D|x) = n·KL(p_S‖p_D) ≥ 0` (`population_KL`,
  `population_D_le_S`), with equality iff the spectra agree
  (`population_eq_iff_spectra`) — equal spectra, not unique sequence.

The multiplier regimes `Q_w > 1`, `= 1`, `< 1` are the strict, tie, and
eventually-worse cells (`amplification_strict_of_qMul_gt_one`,
`amplification_tie_of_qMul_eq_one`, `amplification_failure_of_qMul_lt_one`);
the zero-`p` and `p = 1` boundaries are recorded separately.

Source facts used here (recorded in `docs/source-notes/…`): Medvedev–Brudno
(2009) §6.1 defines both the exact multinomial with candidate-intrinsic `N(D)`
and the separable product-of-binomial-marginals approximation with an external,
assumed-known `N`; §3.1/§4.1 make a read a DNA molecule (an unordered
reverse-complement pair), so the molecule panel is indexed by
reverse-complement classes.  Shomorony, Kim, Courtade & Tse (2016) §2 use
oriented length-`L` substrings of a circular genome, and §5 leaves the
maximizer-versus-uniqueness reading undetermined.  Nothing here selects a
published interpretation.
-/

namespace AssemblyP1.ImplicationLattice

/-! ## Part 1: conclusion schemas over an explicit candidate universe -/

section Schemas

variable {C : Type _}

/-- An objective on a candidate type: an arbitrary function to `ℝ`.  Keeping the
objective abstract is what makes the transfer facts below true for the whole
variant family rather than for one formula. -/
abbrev Objective (C : Type _) : Type _ := C → ℝ

/-- **Dominance** — the weakest schema the English sentence can denote: every
candidate of the universe `U` is no more likely than the truth.  There is no
membership conjunct and no tie rule.  (This is
`AssemblyModel.IsMaximumLikelihood` of `AssemblyP1/Model.lean`, with the
candidate universe made explicit.) -/
def Dominates (L : Objective C) (U : Set C) (S : C) : Prop :=
  ∀ D ∈ U, L D ≤ L S

/-- **Maximizes if a member**: dominance conditional on the truth itself being
a candidate of `U`.  This is the shape of the published bridging implication
(`AssemblyModel.BridgingImpliesMaximumLikelihood`): a conditional whose
antecedent can be false, in which case nothing is refuted. -/
def MaximizesIfMember (L : Objective C) (U : Set C) (S : C) : Prop :=
  S ∈ U → Dominates L U S

/-- Dominance **with membership**: the truth is itself a candidate of `U`.
Without this conjunct, a claim about a class that does not contain the truth is
not refutable by a good member of that class. -/
def IsMaximizerWithMembership (L : Objective C) (U : Set C) (S : C) : Prop :=
  S ∈ U ∧ Dominates L U S

/-- The **uniqueness** schema: dominance, membership, and every tie explained
by the equivalence `r`. -/
def IsUniqueMaximizerUpTo (L : Objective C) (U : Set C) (S : C)
    (r : C → C → Prop) : Prop :=
  S ∈ U ∧ Dominates L U S ∧ ∀ D ∈ U, L D = L S → r D S

/-! ### The schema lattice: what implies what -/

/-- The uniqueness schema is the strongest: it implies the maximizer-with-
membership schema, which in turn implies both the bare dominance schema and the
conditional one. -/
theorem unique_implies_maximizer_with_membership (L : Objective C) (U : Set C)
    (S : C) (r : C → C → Prop) (h : IsUniqueMaximizerUpTo L U S r) :
    IsMaximizerWithMembership L U S := ⟨h.1, h.2.1⟩

/-- **Positive implication (b) → (c).** -/
theorem maximizer_with_membership_implies_dominates (L : Objective C)
    (U : Set C) (S : C) (h : IsMaximizerWithMembership L U S) :
    Dominates L U S := h.2

/-- **Positive implication (b) → (a).** -/
theorem maximizer_with_membership_implies_maximizes_if_member (L : Objective C)
    (U : Set C) (S : C) (h : IsMaximizerWithMembership L U S) :
    MaximizesIfMember L U S := fun _ => h.2

/-! ### What a *strict* witness refutes -/

/-- A strictly more likely candidate refutes dominance.  The equivalence `r`
does not appear, so this holds for every equivalence and every tie convention. -/
theorem strict_refutes_dominance (L : Objective C) (U : Set C) (S D : C)
    (hD : D ∈ U) (hL : L S < L D) : ¬ Dominates L U S := by
  intro hdom
  have := hdom D hD
  linarith

/-- A strictly more likely candidate refutes the maximizer-with-membership
schema, **regardless of whether the truth is itself a member** of `U`: the
`Dominates` conjunct is refuted either way.  This is the #88 audit correction:
the strict witness is decisive for the conclusion schema even when the
acceptance boundary is asymmetric. -/
theorem strict_refutes_maximizer_membership (L : Objective C) (U : Set C)
    (S D : C) (hD : D ∈ U) (hL : L S < L D) :
    ¬ IsMaximizerWithMembership L U S :=
  fun ⟨_, hdom⟩ => strict_refutes_dominance L U S D hD hL hdom

/-- A strictly more likely candidate refutes the conditional schema, provided
the truth is a candidate.  If the truth is *not* a candidate the conditional is
vacuously true and the witness is silent about it. -/
theorem strict_refutes_maximizes_if_member (L : Objective C) (U : Set C)
    (S D : C) (hS : S ∈ U) (hD : D ∈ U) (hL : L S < L D) :
    ¬ MaximizesIfMember L U S :=
  fun h => strict_refutes_dominance L U S D hD hL (h hS)

/-- A strictly more likely candidate refutes the full uniqueness schema for
*every* equivalence `r`: the equivalence is reachable only for tied candidates,
and a strict candidate is not tied. -/
theorem strict_refutes_unique (L : Objective C) (U : Set C) (S D : C)
    (r : C → C → Prop) (_hS : S ∈ U) (hD : D ∈ U) (hL : L S < L D) :
    ¬ IsUniqueMaximizerUpTo L U S r :=
  fun ⟨_, hdom, _⟩ => strict_refutes_dominance L U S D hD hL hdom

/-! ### What a *tie* witness refutes -/

/-- A tied candidate that the equivalence does not identify refutes the
uniqueness schema.  This is the only kind of counterexample that an equivalence
convention can create or destroy. -/
theorem tie_refutes_unique (L : Objective C) (U : Set C) (S D : C)
    (r : C → C → Prop) (hD : D ∈ U) (hEq : L D = L S) (hNr : ¬ r D S) :
    ¬ IsUniqueMaximizerUpTo L U S r := by
  intro ⟨_, _, huniq⟩
  exact hNr (huniq D hD hEq)

/-! ### Two finite objectives for the concrete instances below -/

/-- `fin3Val 0 = 1`, `fin3Val 1 = 2`, `fin3Val 2 = 1`: candidate `0` is a
maximizer of the two-point class `{0, 2}` but not of `Fin 3`.  Spelled out by
cases so that every value below is a closed numeral. -/
def fin3Val : Fin 3 → ℝ
  | 0 => 1
  | 1 => 2
  | 2 => 1

/-- `constVal`: every candidate ties.  Used for the membership-only instances,
where no strictness is available at all. -/
def constVal : Fin 3 → ℝ := fun _ => 1

/-! ### What a *membership* failure refutes (the #88 audit correction) -/

/-- A truth that is not a candidate refutes the maximizer-with-membership
schema.  Note that this uses no strictness hypothesis at all. -/
theorem membership_failure_refutes_maximizer_with_membership (L : Objective C)
    (U : Set C) (S : C) (hS : S ∉ U) : ¬ IsMaximizerWithMembership L U S :=
  fun h => hS h.1

/-- **A membership failure is not a strictness refutation — the #88-shaped
separation.**  Take the one-element universe `U = {1}` over `Fin 3`, the truth
`S = 0 ∉ U`, and two objectives: `constVal` (every candidate ties, so **no**
strict witness exists in `U`) and `fin3Val` (`1` is strictly better than `0`, so
a strict witness exists in `U`).  The four conclusion schemas separate as
follows.

With `constVal` — no strictness available:

* `Dominates constVal U 0` **holds**;
* `MaximizesIfMember constVal U 0` **holds** (and would hold vacuously even if
  dominance failed, because its antecedent is false);
* `IsMaximizerWithMembership constVal U 0` **fails**, on membership alone;
* `IsUniqueMaximizerUpTo constVal U 0 r` **fails**, on membership alone, for
  *every* equivalence `r`.

With `fin3Val` — a strict witness `D = 1 ∈ U` with `L 0 < L 1`:

* `Dominates fin3Val U 0` **fails**, and so do both membership-bearing schemas;
* `MaximizesIfMember fin3Val U 0` still **holds**, because the conditional's
  antecedent `S ∈ U` is false.

So the only schema that survives *both* a membership failure and a strict
witness is the conditional maximizer schema — the shape of the published
bridging implication `AssemblyModel.BridgingImpliesMaximumLikelihood`.  That is
exactly the #88 instance `AABB` over the §6.2 class: the truth is outside the
class and the class contains a strictly better candidate, so `Dominates` is
refuted (by the strict witness) and the membership-bearing schemas are refuted
(by either reason), while a bridging *implication* about that class is not
tested by the instance at all. -/
theorem membership_failure_is_not_strict :
    Dominates constVal ({1} : Set (Fin 3)) 0
      ∧ MaximizesIfMember constVal ({1} : Set (Fin 3)) 0
      ∧ ¬ IsMaximizerWithMembership constVal ({1} : Set (Fin 3)) 0
      ∧ ¬ IsUniqueMaximizerUpTo constVal ({1} : Set (Fin 3)) 0 (fun a _ => a = 1)
      ∧ ¬ Dominates fin3Val ({1} : Set (Fin 3)) 0
      ∧ ¬ IsMaximizerWithMembership fin3Val ({1} : Set (Fin 3)) 0
      ∧ MaximizesIfMember fin3Val ({1} : Set (Fin 3)) 0
      ∧ ¬ IsUniqueMaximizerUpTo fin3Val ({1} : Set (Fin 3)) 0 (fun a _ => a = 1) := by
  have hnotin : (0 : Fin 3) ∉ ({1} : Set (Fin 3)) := by decide
  have hin : (1 : Fin 3) ∈ ({1} : Set (Fin 3)) := by decide
  have hstrict : fin3Val 0 < fin3Val 1 := by simp only [fin3Val]; norm_num
  have hdom_const : Dominates constVal ({1} : Set (Fin 3)) 0 := by
    intro D _hD
    simp [constVal]
  refine ⟨hdom_const, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun _ => hdom_const
  · exact fun h => hnotin h.1
  · exact fun h => hnotin h.1
  · exact strict_refutes_dominance fin3Val _ 0 1 hin hstrict
  · exact strict_refutes_maximizer_membership fin3Val _ 0 1 hin hstrict
  · exact fun h => absurd h hnotin
  · exact fun ⟨_, hdom, _⟩ => strict_refutes_dominance fin3Val _ 0 1 hin hstrict hdom

/-! ### Candidate-universe inclusion -/

/-- **Negative transfer.** A strict witness living in a subclass `U'` refutes
dominance over every superclass `U ⊇ U'`.  This is the half of the candidate-
universe lattice that transfers; the witnesses on `main` rely on it. -/
theorem strict_refutes_superclass (L : Objective C) (U U' : Set C) (S D : C)
    (hsub : U' ⊆ U) (hD : D ∈ U') (hL : L S < L D) : ¬ Dominates L U S :=
  strict_refutes_dominance L U S D (hsub hD) hL

/-- **Positive transfer runs the other way only.** Dominance over `U` implies
dominance over any subclass `U'`. -/
theorem dominance_restricts (L : Objective C) (U U' : Set C) (S : C)
    (hsub : U' ⊆ U) (hdom : Dominates L U S) : Dominates L U' S :=
  fun D hD => hdom D (hsub hD)

/-- The converse inclusion of the previous theorem is false.  Over the class
`U' = {0, 2}` the candidate `0` is a maximizer; over `U = univ` the candidate
`1` is strictly more likely.  A maximizer statement is therefore a statement
*about its universe*, and a theorem proved over a restricted candidate class is
a restricted result.  The §6.2-feasible class is a subclass of the free
candidate universe, so a strict witness *inside* it transfers outward, while a
strict witness *outside* it says nothing about it. -/
theorem positive_result_does_not_lift :
    Dominates fin3Val ({0, 2} : Set (Fin 3)) 0 ∧
      ¬ Dominates fin3Val Set.univ 0 := by
  constructor
  · intro i hi
    rcases Set.mem_insert_iff.1 hi with hi | hi
    · subst hi
      simp only [fin3Val]; norm_num
    · rcases Set.mem_singleton_iff.1 hi with rfl
      simp only [fin3Val]; norm_num
  · intro hdom
    have h1 : fin3Val 1 ≤ fin3Val 0 := hdom 1 (Set.mem_univ 1)
    simp only [fin3Val] at h1
    exact absurd h1 (by norm_num : ¬ ((2 : ℝ) ≤ 1))

/-- **Value-cofinal subuniverse.** If every candidate of `U` has an equal-value
representative in `V ⊆ U`, dominance over `U` and over `V` are equivalent.  This
is the formal content of "quotienting the candidate universe by a symmetry that
leaves the objective invariant does not change the maximizer schema": the
rotation orbit of a candidate is such a `V`.  It also shows exactly where the
equivalence *does* matter — only in the tie clause of the uniqueness schema,
never in dominance. -/
theorem dominance_of_cofinal (L : Objective C) (U V : Set C) (S : C)
    (hsub : V ⊆ U) (hcof : ∀ D ∈ U, ∃ D' ∈ V, L D' = L D) :
    Dominates L U S ↔ Dominates L V S := by
  constructor
  · exact dominance_restricts L U V S hsub
  · intro hdomV D hD
    obtain ⟨D', hD', hEq⟩ := hcof D hD
    have := hdomV D' hD'
    linarith

/-! ### Conditional versus conclusion -/

/-- Refuting a conditional `H → C` at an instance requires that instance to
satisfy the antecedent.  A strict witness against the *conclusion* schema is
therefore a proof that `H → C` fails only when `H` holds; when `H` fails the
conditional is vacuously true. -/
theorem refuting_a_conditional_requires_the_antecedent (H C : Prop)
    (h : ¬ (H → C)) : H ∧ ¬ C := by
  constructor
  · by_contra hn
    exact h (fun hh => absurd hh hn)
  · intro hc
    exact h (fun _ => hc)

end Schemas

/-! ## Part 2: the objective family and the exact/fixed-`N` conversion -/

section Conversion

variable {ι : Type} [Fintype ι]

/-- The **exact multinomial factor product** of Medvedev–Brudno §6.1 (contract
Variant E): the product of `(d w / len) ^ x w` over the read-type space, with
the candidate's own intrinsic length `len` in every probability.  The
observation-only multinomial coefficient `n! / ∏ w x w!` is omitted because it
is candidate-independent and cancels in every ratio.  The same formula with an
*external* `len` is the factor part of the §6.1 separable approximation
(contract Variant A), so one definition serves both objectives:
`multinomialFactor (D.len)` is Variant E and `multinomialFactor N` is Variant A. -/
def multinomialFactor (len : ℚ) (d : ι → ℕ) (x : ι → ℕ) : ℚ :=
  ∏ w, ((d w : ℚ) / len) ^ (x w)

/-- Pull the length out of the factor product:
`∏_w (d w / len) ^ x w = (∏_w (d w) ^ x w) / len ^ (∑_w x w)`. -/
theorem multinomialFactor_eq_div_pow (len : ℚ) (d : ι → ℕ) (x : ι → ℕ) :
    multinomialFactor len d x
      = (∏ w, (d w : ℚ) ^ (x w)) / len ^ (∑ w, x w) := by
  unfold multinomialFactor
  simp only [div_pow]
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]

/-- **Conversion identity.** For a truth of length `G`, a competitor of length
`m`, an external size `N = G` and `n = ∑_w x w` observed reads,

```
E(D)/E(S) = (G / m)^n · A'(D)/A'(S).
```

Consequences: at `m = G` the length factor is `1` and the two objectives have
*identical* ratios, so a same-length strict witness transfers between them in
both directions; at `m ≠ G` they differ by the length factor, so a free-length
strict witness can fail to transfer in either direction.  The instances of Part 4
exhibit both failure directions. -/
theorem conversion (G m : ℚ) (dS dD : ι → ℕ) (x : ι → ℕ)
    (hG : G ≠ 0) (hm : m ≠ 0) :
    multinomialFactor m dD x / multinomialFactor G dS x
      = (G / m) ^ (∑ w, x w) *
          (multinomialFactor G dD x / multinomialFactor G dS x) := by
  rw [multinomialFactor_eq_div_pow m dD x, multinomialFactor_eq_div_pow G dS x,
    multinomialFactor_eq_div_pow G dD x, div_pow]
  by_cases h : ∏ w, (dS w : ℚ) ^ (x w) = 0
  · rw [h]
    simp
  · field_simp

/-- At equal lengths the length factor is `1`, so the exact multinomial and the
fixed-`N` factor objective have *identical* candidate ratios.  This is the only
objective-to-objective transfer on the length axis, and it holds in both
directions: read through `conversion`, the identity is
`(G/G)^n · A'(D)/A'(S) = A'(D)/A'(S)`, so no hypothesis about the competitor
length beyond `m = G` is needed. -/
theorem same_length_ratios_coincide (G m : ℚ) (hG : G ≠ 0)
    (dS dD : ι → ℕ) (x : ι → ℕ) (hm : m = G) :
    multinomialFactor m dD x / multinomialFactor G dS x
      = multinomialFactor G dD x / multinomialFactor G dS x := by
  have hm0 : m ≠ 0 := by rw [hm]; exact hG
  rw [conversion G m dS dD x hG hm0, hm, div_self hG]
  simp

end Conversion

/-! ## Part 3: the sample-multiplicity axis

The board research-assistant comments of 2026-10-09 (issue #216) add one axis
to the transfer table: how the candidate ratio changes when the *same* read type
is observed repeatedly.  Two exact finite-sampling theorems and one population
fact, all independent of the graph details:

* **Exact multinomial (E).**  Adding `m` further observations of an
  already-observed read type `w` multiplies the exact likelihood ratio by
  `(p_D(w)/p_S(w))^m` with the candidate-intrinsic `p_X(w) = d_X(w)/|X|`
  (`multinomialRatio_addRead`).
* **Fixed-`N` binomial (A).**  The same operation multiplies the §6.1
  fixed-`N` binomial ratio by `Q_w^m`, where
  `Q_w = (p_D(w)/p_S(w)) · ∏_{i≠w} (1-p_D(i))/(1-p_S(i))` with the external
  `p_X(i) = d_X(i)/N` (`binomialRatio_addRead`).  The two multipliers differ:
  the binomial's `n - x_i` exponents move for every `i ≠ w`, which is exactly
  the correction the earlier comment said was missing.  On the interior domain
  `(1-p_X(i)) = (N-d_X(i))/N`, which is how `qMul` below writes the product.
* **Population KL.**  When the observation is exactly proportional to the
  truth's spectrum, `log L_E(S|x) - log L_E(D|x) = n·KL(p_S‖p_D) ≥ 0`
  (`population_KL`, `population_D_le_S`): the truth is *a* maximizer at the
  population point, with equality iff the spectra agree — which at equal length
  is equal k-spectrum, NOT unique sequence (`population_eq_iff_spectra`).

**Domain hypotheses.**  The ratio identities are stated under the interior
domain `0 < p < 1` (positivity of every factor that is divided by), plus the
support hypothesis `Spells dS x` (the truth spells the observation) and
`0 < x w` (the amplified type is observed).  The boundary is recorded
separately, as the board requests:

* `p_S(w) = 0` with `x w > 0`: the truth's likelihood is exactly `0`
  (`multinomialFactor_eq_zero_of_zero_count`), so a competitor that spells `w`
  strictly beats the truth *at `m = 0` already* (`boundary_strict`) — no
  amplification is needed, and the ratio is not a real number.
* `p_D(w) = 0` with `x w > 0`: the competitor's likelihood is `0`
  (`boundary_D_zero`): the `D = 0` cell of the transfer table, not a witness.
* `p_X(i) = 1` with an unobserved `i`: the binomial factor is `0`
  (`binomialFactor_eq_zero_of_full_count`): the `p = 1` boundary of the fixed-`N`
  product.

**Strict, tie, and failure from the multiplier.**  The three cells of the
interpretation matrix are the three regimes of the multiplier
(`amplification_strict_of_qMul_gt_one`, `amplification_tie_of_qMul_eq_one`,
`amplification_failure_of_qMul_lt_one`): `Q_w > 1` amplifies any positive base
ratio past `1` (a strict witness, which by Part 1 refutes every maximizer
schema over any universe containing `D`); `Q_w = 1` preserves the ratio (a tie
stays a tie, refuting only the uniqueness schema when `D` is not
`r`-equivalent to `S`); `Q_w < 1` drives the ratio to `0` (the competitor is
eventually strictly worse, the `< 1` cell).  Note `Q_w < 1` is possible for the
binomial even when `p_D(w) > p_S(w)`: the `∏_{i≠w}` factor can be small.

**Scope markers (the two constraint kinds are never mixed).**  The
amplification preserves the *per-vertex/source* constraints — `I_s` membership
and §6.2 support spelling are monotone under adding reads of an already-spelled
type (`spells_addRead`) — but it does NOT preserve the *per-occurrence
editorial* constraint `d_w ≥ x_w` of #212: adding `m` copies of `w` raises
`x_w`, so that constraint must be rechecked at the augmented observation.  The
lemmas below are stated for the likelihood ratios only and are silent about
both constraint kinds; the transfer table records which kind each candidate
class uses.
-/

section Amplification

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def addRead (x : ι → ℕ) (w : ι) (m : ℕ) : ι → ℕ :=
  fun i => if i = w then x i + m else x i

def Spells (d : ι → ℕ) (x : ι → ℕ) : Prop := ∀ i, 0 < x i → 0 < d i


omit [Fintype ι] in
theorem spells_addRead {d x : ι → ℕ} {w : ι} {m : ℕ}
    (h : Spells d x) (hw : 0 < x w) : Spells d (addRead x w m) := by
  intro i hi
  unfold addRead at hi
  split_ifs at hi with hw'
  · rw [hw']; exact h w hw
  · exact h i hi

omit [DecidableEq ι] in
theorem multinomialFactor_pos {m : ℚ} {d : ι → ℕ} {x : ι → ℕ}
    (hm : 0 < m) (hspell : Spells d x) : 0 < multinomialFactor m d x := by
  apply Finset.prod_pos
  intro i _
  by_cases hxi : x i = 0
  · rw [hxi, pow_zero]; exact zero_lt_one
  · exact pow_pos (div_pos (by exact_mod_cast hspell i (by omega)) hm) _

theorem multinomialFactor_addRead (len : ℚ) (d : ι → ℕ) (x : ι → ℕ) (w : ι) (m : ℕ) :
    multinomialFactor len d (addRead x w m)
      = multinomialFactor len d x * (d w / len) ^ m := by
  have hpoint : ∀ i, ((d i : ℚ) / len) ^ (addRead x w m i)
      = ((d i : ℚ) / len) ^ (x i) * (if i = w then ((d w : ℚ) / len) ^ m else 1) := by
    intro i
    unfold addRead
    by_cases hi : i = w
    · rw [ite_eq_left hi, ite_eq_left hi, hi, pow_add]
    · rw [ite_eq_right hi, ite_eq_right hi, mul_one]
  unfold multinomialFactor
  rw [Finset.prod_congr rfl (fun i _ => hpoint i), Finset.prod_mul_distrib,
    Finset.prod_ite_eq' Finset.univ w (fun _ => ((d w : ℚ) / len) ^ m)]
  simp

def binomialFactor (N : ℚ) (d : ι → ℕ) (x : ι → ℕ) : ℚ :=
  ∏ i, (d i / N) ^ (x i) * ((N - d i) / N) ^ (∑ j, x j - x i)

omit [DecidableEq ι] in
theorem binomialFactor_pos {N : ℚ} {d : ι → ℕ} {x : ι → ℕ}
    (hN : 0 < N) (hspell : Spells d x) (hbd : ∀ i, (d i : ℚ) < N) :
    0 < binomialFactor N d x := by
  apply Finset.prod_pos
  intro i _
  by_cases hxi : x i = 0
  · rw [hxi, pow_zero, one_mul]
    exact pow_pos (div_pos (by linarith [hbd i]) hN) _
  · exact mul_pos (pow_pos (div_pos (by exact_mod_cast hspell i (by omega)) hN) _)
      (pow_pos (div_pos (by linarith [hbd i]) hN) _)

theorem binomialFactor_addRead (N : ℚ) (d : ι → ℕ) (x : ι → ℕ) (w : ι) (m : ℕ) :
    binomialFactor N d (addRead x w m)
      = binomialFactor N d x * (d w / N) ^ m
          * (∏ i ∈ Finset.univ \ {w}, (N - d i) / N) ^ m := by
  have hsum : ∑ j, addRead x w m j = (∑ j, x j) + m := by
    have hp : ∀ j, addRead x w m j = x j + (if j = w then m else 0) := by
      intro j; unfold addRead; by_cases hj : j = w <;> simp [hj]
    simp only [hp]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ w (fun _ => m)]
    simp
  have hle : ∀ i, x i ≤ ∑ j, x j := fun i =>
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hpoint : ∀ i, ((d i : ℚ) / N) ^ (addRead x w m i)
        * (((N - d i : ℚ)) / N) ^ (∑ j, addRead x w m j - addRead x w m i)
      = ((d i : ℚ) / N) ^ (x i) * (((N - d i : ℚ)) / N) ^ (∑ j, x j - x i)
        * (if i = w then ((d w : ℚ) / N) ^ m else (((N - d i : ℚ)) / N) ^ m) := by
    intro i
    rw [hsum]
    unfold addRead
    by_cases hi : i = w
    · simp only [ite_eq_left hi]
      rw [hi]
      rw [show (∑ j, x j) + m - (x w + m) = ∑ j, x j - x w from by omega]
      rw [pow_add]
      ring
    · simp only [ite_eq_right hi]
      have hx := hle i
      rw [show (∑ j, x j) + m - x i = (∑ j, x j - x i) + m from by omega]
      rw [pow_add]
      ring
  have hprod : ∏ i, (if i = w then ((d w : ℚ) / N) ^ m
        else (((N - d i : ℚ)) / N) ^ m)
      = ((d w : ℚ) / N) ^ m
          * (∏ i ∈ Finset.univ \ {w}, (((N - d i : ℚ)) / N)) ^ m := by
    rw [Finset.prod_eq_mul_prod_sdiff_singleton w (fun i =>
      if i = w then ((d w : ℚ) / N) ^ m else (((N - d i : ℚ)) / N) ^ m)
      (fun hw => by exact absurd (Finset.mem_univ w) hw)]
    rw [ite_eq_left rfl]
    congr 1
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i hi
    simp only [ite_eq_right (by simpa using (Finset.mem_sdiff.mp hi).2)]
  unfold binomialFactor
  rw [Finset.prod_congr rfl (fun i _ => hpoint i), Finset.prod_mul_distrib, hprod]
  ring

def qMul (N : ℚ) (dS dD : ι → ℕ) (w : ι) : ℚ :=
  (dD w / dS w) * ∏ i ∈ Finset.univ \ {w}, (N - dD i) / (N - dS i)

theorem multinomialRatio_addRead (mS mD : ℚ) (dS dD : ι → ℕ) (x : ι → ℕ) (w : ι) (m : ℕ)
    (_hmS : 0 < mS) (_hmD : 0 < mD) (_hspell : Spells dS x) (_hspellD : Spells dD x)
    (_hobs : 0 < x w) :
    multinomialFactor mD dD (addRead x w m) / multinomialFactor mS dS (addRead x w m)
      = (multinomialFactor mD dD x / multinomialFactor mS dS x)
          * ((dD w / mD) / (dS w / mS)) ^ m := by
  rw [multinomialFactor_addRead, multinomialFactor_addRead, ← div_mul_div_comm, ← div_pow]

theorem binomialRatio_addRead (N : ℚ) (dS dD : ι → ℕ) (x : ι → ℕ) (w : ι) (m : ℕ)
    (hN : 0 < N) (_hbdS : ∀ i, (dS i : ℚ) < N) (_hbdD : ∀ i, (dD i : ℚ) < N)
    (_hspell : Spells dS x) (_hobs : 0 < x w) :
    binomialFactor N dD (addRead x w m) / binomialFactor N dS (addRead x w m)
      = (binomialFactor N dD x / binomialFactor N dS x) * qMul N dS dD w ^ m := by
  have hdN : (dD w / N) / (dS w / N) = dD w / dS w := by
    field_simp
  have hPDPS : (∏ i ∈ Finset.univ \ {w}, (N - dD i) / N)
        / (∏ i ∈ Finset.univ \ {w}, (N - dS i) / N)
      = ∏ i ∈ Finset.univ \ {w}, (N - dD i) / (N - dS i) := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    field_simp
  rw [binomialFactor_addRead, binomialFactor_addRead,
    ← div_mul_div_comm, ← div_mul_div_comm, ← div_pow, ← div_pow, mul_assoc, ← mul_pow]
  unfold qMul
  rw [hdN, hPDPS]

omit [DecidableEq ι] in
theorem multinomialFactor_eq_zero_of_zero_count {m : ℚ} {d : ι → ℕ} {x : ι → ℕ} {w : ι}
    (hdw : d w = 0) (hxw : 0 < x w) : multinomialFactor m d x = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ w)
  rw [hdw, Nat.cast_zero, zero_div, zero_pow (by omega : x w ≠ 0)]

omit [DecidableEq ι] in
theorem boundary_D_zero {m : ℚ} {d : ι → ℕ} {x : ι → ℕ} {w : ι}
    (hdw : d w = 0) (hxw : 0 < x w) : multinomialFactor m d x = 0 :=
  multinomialFactor_eq_zero_of_zero_count hdw hxw

omit [DecidableEq ι] in
theorem boundary_strict {mS mD : ℚ} {dS dD : ι → ℕ} {x : ι → ℕ} {w : ι}
    (hmD : 0 < mD) (hdSw : dS w = 0) (hxw : 0 < x w)
    (hspellD : Spells dD x) : multinomialFactor mS dS x < multinomialFactor mD dD x := by
  rw [multinomialFactor_eq_zero_of_zero_count hdSw hxw]
  exact multinomialFactor_pos hmD hspellD

omit [DecidableEq ι] in
theorem binomialFactor_eq_zero_of_zero_count {N : ℚ} {d : ι → ℕ} {x : ι → ℕ} {w : ι}
    (hdw : d w = 0) (hxw : 0 < x w) : binomialFactor N d x = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ w)
  rw [hdw, Nat.cast_zero, zero_div, zero_pow (by omega : x w ≠ 0), zero_mul]

omit [DecidableEq ι] in
theorem binomialFactor_eq_zero_of_full_count {N : ℚ} {d : ι → ℕ} {x : ι → ℕ} {i : ι}
    (hdi : N = (d i : ℚ)) (hxi : x i < ∑ j, x j) : binomialFactor N d x = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [show (N - (d i : ℚ)) = 0 from by linarith, zero_div,
    zero_pow (by omega : ∑ j, x j - x i ≠ 0), mul_zero]

theorem amplification_strict_of_qMul_gt_one (r q : ℚ) (hr : 0 < r) (hq : 1 < q) :
    ∃ m, 1 < r * q ^ m := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / r) hq
  refine ⟨n, ?_⟩
  rw [mul_comm]
  exact (div_lt_iff₀ hr).mp hn

theorem amplification_tie_of_qMul_eq_one (r : ℚ) (m : ℕ) : r * (1:ℚ) ^ m = r := by
  simp

theorem amplification_failure_of_qMul_lt_one (r q : ℚ) (_hr : 0 ≤ r) (hq0 : 0 ≤ q)
    (hq1 : q < 1) : ∃ m, r * q ^ m < 1 := by
  by_cases hq0' : q = 0
  · refine ⟨1, ?_⟩
    rw [hq0', zero_pow (by omega : (1:ℕ) ≠ 0), mul_zero]
    exact zero_lt_one
  · have hq' : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq0')
    have hr' : (1:ℚ) < 1 / q := by
      rw [one_lt_div hq']; exact hq1
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt r hr'
    refine ⟨n, ?_⟩
    have h1 : 0 < (1 / q) ^ n := pow_pos (div_pos one_pos hq') _
    have h2 : r * q ^ n = r / (1 / q) ^ n := by
      rw [one_div, inv_pow, div_inv_eq_mul]
    rw [h2]
    exact (div_lt_one h1).mpr hn

-- KL

noncomputable def kl (p q : ι → ℝ) : ℝ := ∑ w, p w * (Real.log (p w) - Real.log (q w))

omit [Fintype ι] [DecidableEq ι] in
theorem kl_pointwise_le {p q : ι → ℝ} (hp : ∀ w, 0 ≤ p w) (hq : ∀ w, 0 ≤ q w)
    (hsupp : ∀ w, 0 < p w → 0 < q w) :
    ∀ w, p w - q w ≤ p w * Real.log (p w / q w) := by
  intro w
  by_cases hpw : p w = 0
  · rw [hpw]
    simp only [zero_mul]
    linarith [hq w]
  · have h1 : 0 < p w := lt_of_le_of_ne (hp w) (Ne.symm hpw)
    have h2 : 0 < q w := hsupp w h1
    have h3 : 0 < q w / p w := div_pos h2 h1
    have h4 : Real.log (q w / p w) ≤ q w / p w - 1 := Real.log_le_sub_one_of_pos h3
    have h5 : p w * Real.log (q w / p w) ≤ p w * (q w / p w - 1) :=
      mul_le_mul_of_nonneg_left h4 (le_of_lt h1)
    have h6 : p w * (q w / p w) = q w := by field_simp
    have h7 : p w * (q w / p w - 1) = p w * (q w / p w) - p w := by ring
    have h8 : Real.log (p w / q w) = - Real.log (q w / p w) := by
      rw [Real.log_div (ne_of_gt h1) (ne_of_gt h2),
        Real.log_div (ne_of_gt h2) (ne_of_gt h1)]
      ring
    rw [h8]
    linarith

omit [DecidableEq ι] in
theorem kl_eq_sum {p q : ι → ℝ} (hp : ∀ w, 0 ≤ p w)
    (hsupp : ∀ w, 0 < p w → 0 < q w) :
    kl p q = ∑ w, p w * Real.log (p w / q w) := by
  apply Finset.sum_congr rfl
  intro w _
  by_cases hpw : p w = 0
  · simp [hpw]
  · have h1 : 0 < p w := lt_of_le_of_ne (hp w) (Ne.symm hpw)
    have h2 : 0 < q w := hsupp w h1
    rw [Real.log_div (ne_of_gt h1) (ne_of_gt h2)]

omit [DecidableEq ι] in
theorem kl_nonneg {p q : ι → ℝ} (hp : ∀ w, 0 ≤ p w) (hq : ∀ w, 0 ≤ q w)
    (hp1 : ∑ w, p w = 1) (hq1 : ∑ w, q w = 1)
    (hsupp : ∀ w, 0 < p w → 0 < q w) : 0 ≤ kl p q := by
  have hle := kl_pointwise_le hp hq hsupp
  rw [kl_eq_sum hp hsupp]
  have hsum : ∑ w, (p w - q w) ≤ ∑ w, p w * Real.log (p w / q w) :=
    Finset.sum_le_sum (fun w _ => hle w)
  have h0 : ∑ w, (p w - q w) = 0 := by
    rw [Finset.sum_sub_distrib, hp1, hq1, sub_self]
  linarith

omit [DecidableEq ι] in
theorem kl_eq_zero_iff_eq {p q : ι → ℝ} (hp : ∀ w, 0 ≤ p w) (hq : ∀ w, 0 ≤ q w)
    (hp1 : ∑ w, p w = 1) (hq1 : ∑ w, q w = 1)
    (hsupp : ∀ w, 0 < p w → 0 < q w) : kl p q = 0 ↔ p = q := by
  have hle := kl_pointwise_le hp hq hsupp
  constructor
  · intro h0
    have hkl_eq := kl_eq_sum hp hsupp
    have hfsum : ∑ w, (p w * Real.log (p w / q w) - (p w - q w)) = 0 := by
      rw [Finset.sum_sub_distrib]
      have hsum0 : ∑ w, (p w - q w) = 0 := by
        rw [Finset.sum_sub_distrib, hp1, hq1, sub_self]
      rw [← hkl_eq, h0, hsum0, sub_zero]
    have hfw : ∀ w, p w * Real.log (p w / q w) - (p w - q w) = 0 :=
      fun w => (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => sub_nonneg.mpr (hle w))).mp
        hfsum w (Finset.mem_univ w)
    ext w
    have hw := hfw w
    have hw' : p w * Real.log (p w / q w) = p w - q w := sub_eq_zero.mp hw
    by_cases hpw : p w = 0
    · rw [hpw, zero_mul] at hw'
      linarith [hw']
    · have h1 : 0 < p w := lt_of_le_of_ne (hp w) (Ne.symm hpw)
      have h2 : 0 < q w := hsupp w h1
      have hx : p w / q w = 1 := by
        by_contra hne
        have hxpos : 0 < p w / q w := div_pos h1 h2
        have hinv : (p w / q w)⁻¹ ≠ 1 := by
          intro h
          apply hne
          have h2 := congrArg (fun x => x⁻¹) h
          rw [inv_inv, inv_one] at h2
          exact h2
        have hlt := Real.log_lt_sub_one_of_pos (inv_pos.mpr hxpos) hinv
        rw [Real.log_inv] at hlt
        have hlogx : Real.log (p w / q w) = 1 - q w / p w := by
          have hpne : p w ≠ 0 := ne_of_gt h1
          field_simp
          linarith [hw']
        have hinveq : (p w / q w)⁻¹ = q w / p w := by field_simp
        rw [hinveq] at hlt
        nlinarith [hlt, hlogx]
      field_simp at hx
      linarith [hx]
  · intro hpq
    rw [hpq]
    simp [kl]

omit [DecidableEq ι] in
theorem log_multinomialFactor {m : ℚ} {d : ι → ℕ} {x : ι → ℕ}
    (hm : 0 < m) (hpos : ∀ w, 0 < x w → 0 < (d w : ℚ)) :
    Real.log ((multinomialFactor m d x : ℚ) : ℝ)
      = ∑ w, (x w : ℝ) * Real.log (((d w : ℚ) : ℝ) / (m : ℝ)) := by
  have hcast : ((multinomialFactor m d x : ℚ) : ℝ)
      = ∏ w, ((((d w : ℚ) : ℝ) / (m : ℝ)) ^ (x w)) := by
    unfold multinomialFactor
    push_cast
    rfl
  rw [hcast, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro w _
    by_cases hxw : x w = 0
    · simp [hxw]
    · rw [Real.log_pow]
  · intro w _
    by_cases hxw : x w = 0
    · rw [hxw, pow_zero]; exact one_ne_zero
    · exact pow_ne_zero _ (ne_of_gt (div_pos (by exact_mod_cast hpos w (by omega))
        (by exact_mod_cast hm)))

omit [DecidableEq ι] in
theorem population_KL (mS mD : ℚ) (dS dD : ι → ℕ) (x : ι → ℕ)
    (hmS : 0 < mS) (hmD : 0 < mD)
    (hspell : Spells dS x)
    (hsupp : ∀ w, 0 < (dS w : ℚ) → 0 < (dD w : ℚ))
    (hprop : ∀ w, (x w : ℚ) = (∑ j, x j) * ((dS w : ℚ) / mS)) :
    Real.log ((multinomialFactor mS dS x : ℚ) : ℝ)
      - Real.log ((multinomialFactor mD dD x : ℚ) : ℝ)
        = (∑ j, x j : ℕ) * kl (fun w => ((dS w : ℚ) : ℝ) / (mS : ℝ))
          (fun w => ((dD w : ℚ) : ℝ) / (mD : ℝ)) := by
  have hposS : ∀ w, 0 < x w → 0 < (dS w : ℚ) := fun w hw => by exact_mod_cast hspell w hw
  have hposD : ∀ w, 0 < x w → 0 < (dD w : ℚ) := fun w hw => hsupp w (hposS w hw)
  have hlogS := log_multinomialFactor hmS hposS
  have hlogD := log_multinomialFactor hmD hposD
  rw [hlogS, hlogD, ← Finset.sum_sub_distrib]
  unfold kl
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  have hpropR : (x w : ℝ) = ((∑ j, x j : ℕ) : ℝ) * (((dS w : ℚ) : ℝ) / (mS : ℝ)) := by
    exact_mod_cast hprop w
  rw [hpropR]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem supportR {mS mD : ℚ} {dS dD : ι → ℕ}
    (hmS : 0 < mS) (hmD : 0 < mD)
    (hsupp : ∀ w, 0 < (dS w : ℚ) → 0 < (dD w : ℚ)) :
    ∀ w, 0 < ((dS w : ℚ) : ℝ) / (mS : ℝ) → 0 < ((dD w : ℚ) : ℝ) / (mD : ℝ) := by
  intro w hw
  have hmSr : (0:ℝ) < (mS : ℝ) := by exact_mod_cast hmS
  have h1 : 0 < ((dS w : ℚ) : ℝ) := by
    by_contra h
    rw [not_lt] at h
    have : ((dS w : ℚ) : ℝ) / (mS : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg h (le_of_lt hmSr)
    linarith
  have h2 : 0 < (dS w : ℚ) := by exact_mod_cast h1
  exact div_pos (by exact_mod_cast hsupp w h2) (by exact_mod_cast hmD)

omit [DecidableEq ι] in
theorem population_D_le_S (mS mD : ℚ) (dS dD : ι → ℕ) (x : ι → ℕ)
    (hmS : 0 < mS) (hmD : 0 < mD)
    (hspell : Spells dS x) (hspellD : Spells dD x)
    (hsupp : ∀ w, 0 < (dS w : ℚ) → 0 < (dD w : ℚ))
    (hprop : ∀ w, (x w : ℚ) = (∑ j, x j) * ((dS w : ℚ) / mS))
    (htotS : ∑ w, (dS w : ℚ) = mS) (htotD : ∑ w, (dD w : ℚ) = mD) :
    multinomialFactor mD dD x ≤ multinomialFactor mS dS x := by
  have hkl := population_KL mS mD dS dD x hmS hmD hspell hsupp hprop
  have hp1 : ∑ w, ((dS w : ℚ) : ℝ) / (mS : ℝ) = 1 := by
    have hsum : ∑ w, ((dS w : ℚ) : ℝ) = (mS : ℝ) := by exact_mod_cast htotS
    rw [← Finset.sum_div, hsum, div_self (by exact_mod_cast (ne_of_gt hmS))]
  have hq1 : ∑ w, ((dD w : ℚ) : ℝ) / (mD : ℝ) = 1 := by
    have hsum : ∑ w, ((dD w : ℚ) : ℝ) = (mD : ℝ) := by exact_mod_cast htotD
    rw [← Finset.sum_div, hsum, div_self (by exact_mod_cast (ne_of_gt hmD))]
  have hkl0 : 0 ≤ kl (fun w => ((dS w : ℚ) : ℝ) / (mS : ℝ))
      (fun w => ((dD w : ℚ) : ℝ) / (mD : ℝ)) := by
    apply kl_nonneg
    · intro w; apply div_nonneg <;> [exact_mod_cast Nat.zero_le _; exact_mod_cast (le_of_lt hmS)]
    · intro w; apply div_nonneg <;> [exact_mod_cast Nat.zero_le _; exact_mod_cast (le_of_lt hmD)]
    · exact hp1
    · exact hq1
    · exact supportR hmS hmD hsupp
  have hlog : Real.log ((multinomialFactor mD dD x : ℚ) : ℝ)
      ≤ Real.log ((multinomialFactor mS dS x : ℚ) : ℝ) := by
    have hnn : (0:ℝ) ≤ (∑ j, x j : ℕ) * kl (fun w => ((dS w : ℚ) : ℝ) / (mS : ℝ))
        (fun w => ((dD w : ℚ) : ℝ) / (mD : ℝ)) :=
      mul_nonneg (by positivity) hkl0
    linarith [hkl]
  have hposS : (0:ℝ) < ((multinomialFactor mS dS x : ℚ) : ℝ) := by
    exact_mod_cast multinomialFactor_pos hmS hspell
  have hposD : (0:ℝ) < ((multinomialFactor mD dD x : ℚ) : ℝ) := by
    exact_mod_cast multinomialFactor_pos hmD hspellD
  exact_mod_cast (Real.log_le_log_iff hposD hposS).mp hlog

omit [DecidableEq ι] in
theorem population_eq_iff_spectra (mS mD : ℚ) (dS dD : ι → ℕ) (x : ι → ℕ)
    (hmS : 0 < mS) (hmD : 0 < mD)
    (hspell : Spells dS x) (hspellD : Spells dD x)
    (hsupp : ∀ w, 0 < (dS w : ℚ) → 0 < (dD w : ℚ))
    (hprop : ∀ w, (x w : ℚ) = (∑ j, x j) * ((dS w : ℚ) / mS))
    (htotS : ∑ w, (dS w : ℚ) = mS) (htotD : ∑ w, (dD w : ℚ) = mD)
    (hn : 0 < ∑ j, x j) :
    multinomialFactor mD dD x = multinomialFactor mS dS x
      ↔ (fun w => (dD w : ℚ) / mD) = (fun w => (dS w : ℚ) / mS) := by
  have hkl := population_KL mS mD dS dD x hmS hmD hspell hsupp hprop
  have hp1 : ∑ w, ((dS w : ℚ) : ℝ) / (mS : ℝ) = 1 := by
    have hsum : ∑ w, ((dS w : ℚ) : ℝ) = (mS : ℝ) := by exact_mod_cast htotS
    rw [← Finset.sum_div, hsum, div_self (by exact_mod_cast (ne_of_gt hmS))]
  have hq1 : ∑ w, ((dD w : ℚ) : ℝ) / (mD : ℝ) = 1 := by
    have hsum : ∑ w, ((dD w : ℚ) : ℝ) = (mD : ℝ) := by exact_mod_cast htotD
    rw [← Finset.sum_div, hsum, div_self (by exact_mod_cast (ne_of_gt hmD))]
  have hsuppR := supportR hmS hmD hsupp
  have hpnn : ∀ w, 0 ≤ ((dS w : ℚ) : ℝ) / (mS : ℝ) :=
    fun w => div_nonneg (by exact_mod_cast Nat.zero_le _) (by exact_mod_cast (le_of_lt hmS))
  have hqnn : ∀ w, 0 ≤ ((dD w : ℚ) : ℝ) / (mD : ℝ) :=
    fun w => div_nonneg (by exact_mod_cast Nat.zero_le _) (by exact_mod_cast (le_of_lt hmD))
  constructor
  · intro hEq
    have hlogEq : Real.log ((multinomialFactor mS dS x : ℚ) : ℝ)
        = Real.log ((multinomialFactor mD dD x : ℚ) : ℝ) := by rw [hEq]
    have hkl0 : kl (fun w => ((dS w : ℚ) : ℝ) / (mS : ℝ))
        (fun w => ((dD w : ℚ) : ℝ) / (mD : ℝ)) = 0 := by
      have hn0 : ((∑ j, x j : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
      have hprod : ((∑ j, x j : ℕ) : ℝ) * kl (fun w => ((dS w : ℚ) : ℝ) / (mS : ℝ))
          (fun w => ((dD w : ℚ) : ℝ) / (mD : ℝ)) = 0 := by linarith [hkl]
      exact (mul_eq_zero.mp hprod).resolve_left hn0
    have hspecR : (fun w => ((dS w : ℚ) : ℝ) / (mS : ℝ))
        = (fun w => ((dD w : ℚ) : ℝ) / (mD : ℝ)) :=
      (kl_eq_zero_iff_eq hpnn hqnn hp1 hq1 hsuppR).mp hkl0
    funext w
    exact_mod_cast (congrFun hspecR w).symm
  · intro hEq
    have hspecR : (fun w => ((dS w : ℚ) : ℝ) / (mS : ℝ))
        = (fun w => ((dD w : ℚ) : ℝ) / (mD : ℝ)) := by
      funext w
      exact_mod_cast (congrFun hEq w).symm
    have hkl0 : kl (fun w => ((dS w : ℚ) : ℝ) / (mS : ℝ))
        (fun w => ((dD w : ℚ) : ℝ) / (mD : ℝ)) = 0 := by
      rw [← hspecR]; simp [kl]
    have hlogEq : Real.log ((multinomialFactor mS dS x : ℚ) : ℝ)
        = Real.log ((multinomialFactor mD dD x : ℚ) : ℝ) := by
      have : ((∑ j, x j : ℕ) : ℝ) * kl (fun w => ((dS w : ℚ) : ℝ) / (mS : ℝ))
          (fun w => ((dD w : ℚ) : ℝ) / (mD : ℝ)) = 0 := by rw [hkl0, mul_zero]
      linarith [hkl]
    have hposS : (0:ℝ) < ((multinomialFactor mS dS x : ℚ) : ℝ) := by
      exact_mod_cast multinomialFactor_pos hmS hspell
    have hposD : (0:ℝ) < ((multinomialFactor mD dD x : ℚ) : ℝ) := by
      exact_mod_cast multinomialFactor_pos hmD hspellD
    have hreal : ((multinomialFactor mS dS x : ℚ) : ℝ)
        = ((multinomialFactor mD dD x : ℚ) : ℝ) :=
      Real.log_injOn_pos (Set.mem_Ioi.mpr hposS) (Set.mem_Ioi.mpr hposD) hlogEq
    exact_mod_cast hreal.symm


end Amplification
/-! ## Part 4: the concrete two-symbol strand panel and the `W-*` witnesses

Part 4 instantiates the abstract transfer logic on the concrete DNA panel so
that the strand and objective non-transfers are *kernel-checked*, not only
computed.  The panel is the four-symbol alphabet with the standard complement;
`oriOcc` counts oriented length-`L` circular windows; `molOcc` aggregates the
two reverse-complement orientations into one molecule class (MB09 §3.1/§4.1).
The integer keys are the coefficient-free likelihood numerators: for the exact
multinomial, `E(D) > E(S)` iff `key S · |D|^n < key D · |S|^n`; for the fixed-`N`
factor objective, iff `key S < key D`; for the literal §6.1 binomial, iff
`keyAlit S N < keyAlit D N`.  Every theorem below is a closed `decide` over the
concrete genomes, so it depends only on the permitted axioms.

The five `W-*` witnesses each separate variants that the witnesses already on
`main` do not separate; the two strand directions and the two length/objective
directions are the novel content of issue #216. -/

namespace ConcretePanel

open AssemblyP1.SourceFaithfulIs

inductive DNA where
  | A | T | C | G
  deriving DecidableEq, Inhabited, Repr

instance : Fintype DNA where
  elems := {DNA.A, DNA.T, DNA.C, DNA.G}
  complete := by intro x; cases x <;> simp

namespace DNA

def comp : DNA → DNA
  | A => T | T => A | C => G | G => C

end DNA

open DNA

abbrev Word (L : ℕ) := Fin L → DNA

/-- DNA reverse complement of a length-`L` word. -/
def rc {L : ℕ} (w : Word L) : Word L :=
  fun d => DNA.comp (w ⟨L - 1 - d.val, by omega⟩)

/-- A concrete circular genome from a nonempty symbol list. -/
abbrev genome (s : List DNA) (h : 0 < s.length) : Genome DNA where
  len := s.length
  len_pos := h
  sym := fun i => s.get i

/-- Oriented occurrence count: starts whose length-`L` circular window is `w`. -/
def oriOcc (S : Genome DNA) (L : ℕ) (w : Word L) : ℕ :=
  (Finset.univ.filter (fun r : Fin S.len => S.window L r = w)).card

/-- Molecule-class occurrence count: the reverse-complement class is counted
once (a palindromic class has one member). -/
def molOcc (S : Genome DNA) (L : ℕ) (w : Word L) : ℕ :=
  if w = rc w then oriOcc S L w else oriOcc S L w + oriOcc S L (rc w)

/-- Coefficient-free exact-multinomial numerator, oriented panel. -/
def keyOri (S : Genome DNA) (L : ℕ) (x : Word L → ℕ) : ℕ :=
  ∏ w : Word L, (oriOcc S L w) ^ (x w)

/-- Coefficient-free exact-multinomial numerator, molecular panel. -/
def keyMol (S : Genome DNA) (L : ℕ) (x : Word L → ℕ) : ℕ :=
  ∏ w : Word L, (molOcc S L w) ^ (x w)

/-- Coefficient-free literal §6.1 binomial numerator, oriented panel, external
`N`: `∏_t d_t^{x_t} (N-d_t)^{n-x_t}`. -/
def keyAlitOri (S : Genome DNA) (L : ℕ) (x : Word L → ℕ) (N : ℕ) : ℕ :=
  ∏ t : Word L, (oriOcc S L t) ^ (x t)
    * (N - oriOcc S L t) ^ ((∑ w : Word L, x w) - x t)

/-- Coefficient-free literal §6.1 binomial numerator, molecular panel. -/
def keyAlitMol (S : Genome DNA) (L : ℕ) (x : Word L → ℕ) (N : ℕ) : ℕ :=
  ∏ t : Word L, (molOcc S L t) ^ (x t)
    * (N - molOcc S L t) ^ ((∑ w : Word L, x w) - x t)

/-- Exact multinomial `D` strictly beats `S`, oriented panel. -/
abbrev eStrictOri (S D : Genome DNA) (L : ℕ) (x : Word L → ℕ) : Prop :=
  keyOri S L x * D.len ^ (∑ w : Word L, x w)
    < keyOri D L x * S.len ^ (∑ w : Word L, x w)

/-- Exact multinomial tie, oriented panel. -/
abbrev eTieOri (S D : Genome DNA) (L : ℕ) (x : Word L → ℕ) : Prop :=
  keyOri S L x * D.len ^ (∑ w : Word L, x w)
    = keyOri D L x * S.len ^ (∑ w : Word L, x w)

/-- Exact multinomial `D` strictly beats `S`, molecular panel. -/
abbrev eStrictMol (S D : Genome DNA) (L : ℕ) (x : Word L → ℕ) : Prop :=
  keyMol S L x * D.len ^ (∑ w : Word L, x w)
    < keyMol D L x * S.len ^ (∑ w : Word L, x w)

/-- Exact multinomial tie, molecular panel. -/
abbrev eTieMol (S D : Genome DNA) (L : ℕ) (x : Word L → ℕ) : Prop :=
  keyMol S L x * D.len ^ (∑ w : Word L, x w)
    = keyMol D L x * S.len ^ (∑ w : Word L, x w)

/-- Fixed-`N` factor objective `D` strictly beats `S`, oriented panel. -/
abbrev aStrictOri (S D : Genome DNA) (L : ℕ) (x : Word L → ℕ) : Prop :=
  keyOri S L x < keyOri D L x

/-- Fixed-`N` factor objective tie, oriented panel. -/
abbrev aTieOri (S D : Genome DNA) (L : ℕ) (x : Word L → ℕ) : Prop :=
  keyOri S L x = keyOri D L x

/-- Fixed-`N` factor objective `D` strictly beats `S`, molecular panel. -/
abbrev aStrictMol (S D : Genome DNA) (L : ℕ) (x : Word L → ℕ) : Prop :=
  keyMol S L x < keyMol D L x

/-- Fixed-`N` factor objective tie, molecular panel. -/
abbrev aTieMol (S D : Genome DNA) (L : ℕ) (x : Word L → ℕ) : Prop :=
  keyMol S L x = keyMol D L x

/-- Literal §6.1 binomial `D` strictly beats `S`, oriented panel. -/
abbrev alitStrictOri (S D : Genome DNA) (L : ℕ) (x : Word L → ℕ) (N : ℕ) : Prop :=
  keyAlitOri S L x N < keyAlitOri D L x N

/-- Literal §6.1 binomial tie, oriented panel. -/
abbrev alitTieOri (S D : Genome DNA) (L : ℕ) (x : Word L → ℕ) (N : ℕ) : Prop :=
  keyAlitOri S L x N = keyAlitOri D L x N

/-- Literal §6.1 binomial `D` strictly beats `S`, molecular panel. -/
abbrev alitStrictMol (S D : Genome DNA) (L : ℕ) (x : Word L → ℕ) (N : ℕ) : Prop :=
  keyAlitMol S L x N < keyAlitMol D L x N

/-- Literal §6.1 binomial tie, molecular panel. -/
abbrev alitTieMol (S D : Genome DNA) (L : ℕ) (x : Word L → ℕ) (N : ℕ) : Prop :=
  keyAlitMol S L x N = keyAlitMol D L x N

def xAA : Word 2 := ![A, A]
def xAT : Word 2 := ![A, T]
def xTA : Word 2 := ![T, A]

def xSigma : Word 2 → ℕ :=
  fun w => if w = xAA then 1 else if w = xAT then 1 else if w = xTA then 1 else 0

def xUpsilon : Word 2 → ℕ :=
  fun w => if w = xAA then 2 else if w = xAT then 1 else 0

def xLambda : Word 2 → ℕ :=
  fun w => if w = xAT then 2 else if w = xTA then 1 else 0

abbrev Ssigma : Genome DNA := genome [A, A, T, T] (by norm_num)
abbrev Dsigma : Genome DNA := genome [A, A, A, T] (by norm_num)
abbrev Supsilon : Genome DNA := genome [A, A, T] (by norm_num)
abbrev Dupsilon : Genome DNA := genome [A, A, T, T] (by norm_num)
abbrev Slambda1 : Genome DNA := genome [A, A, T] (by norm_num)
abbrev Dlambda1 : Genome DNA := genome [A, T] (by norm_num)
abbrev Slambda2 : Genome DNA := genome [A, T] (by norm_num)
abbrev Dlambda2 : Genome DNA := genome [A, T, A, T] (by norm_num)
abbrev Stau : Genome DNA := genome [A, A, T] (by norm_num)
abbrev Dtau : Genome DNA := genome [A, T, T] (by norm_num)

/-- `W-sigma` (`AATT → AAAT`) is `I_s`-certified at the faithful starts
`{0,1,3}`. -/
theorem sigma_Is : InformationFeasible Ssigma 2 ({0, 1, 3} : Finset (Fin 4)) := by
  unfold InformationFeasible; decide

/-- `W-upsilon` (`AAT → AATT`) is `I_s`-certified at the faithful starts
`{0,1}`. -/
theorem upsilon_Is : InformationFeasible Supsilon 2 ({0, 1} : Finset (Fin 3)) := by
  unfold InformationFeasible; decide

/-- `W-lambda1` (`AAT → AT`) is `I_s`-certified at the faithful starts `{1,2}`. -/
theorem lambda1_Is : InformationFeasible Slambda1 2 ({1, 2} : Finset (Fin 3)) := by
  unfold InformationFeasible; decide

/-- `W-lambda2` (`AT → ATAT`) is `I_s`-certified at the faithful starts
`{0,1,2}`. -/
theorem lambda2_Is : InformationFeasible Slambda2 2 ({0, 1, 2} : Finset (Fin 2)) := by
  unfold InformationFeasible; decide

/-- `W-tau` (`AAT → ATT`) is `I_s`-certified at the faithful starts `{1,2}`. -/
theorem tau_Is : InformationFeasible Stau 2 ({1, 2} : Finset (Fin 3)) := by
  unfold InformationFeasible; decide

/-- **`W-sigma`, oriented panel: strict.** The same-length oriented exact
multinomial makes the wrong candidate `AAAT` strictly more likely than `AATT`
(ratio `2`). -/
theorem sigma_oriented_strict : eStrictOri Ssigma Dsigma 2 xSigma := by decide

/-- **`W-sigma`, molecular panel: exact tie.** Collapsing reverse complements
turns the strict oriented witness into an exact tie (ratio `1`): the strictness
does **not** transfer to the molecule panel. -/
theorem sigma_molecular_tie : eTieMol Ssigma Dsigma 2 xSigma := by decide

/-- **`W-sigma`, literal §6.1 binomial, oriented: strict** (ratio `512/243`). -/
theorem sigma_alit_oriented_strict : alitStrictOri Ssigma Dsigma 2 xSigma 4 := by decide

/-- **`W-sigma`, literal §6.1 binomial, molecular: exact tie.** -/
theorem sigma_alit_molecular_tie : alitTieMol Ssigma Dsigma 2 xSigma 4 := by decide

/-- **`W-upsilon`, molecular panel: strict.** The longer competitor `AATT`
strictly beats `AAT` under the molecule panel (ratio `27/16`). -/
theorem upsilon_molecular_strict : eStrictMol Supsilon Dupsilon 2 xUpsilon := by decide

/-- **`W-upsilon`, oriented panel: not strict.** The same competitor is *worse*
under the oriented panel (ratio `27/64 < 1`): the strictness does **not**
transfer the other way either. This is the missing second direction of the
strand non-transfer. -/
theorem upsilon_oriented_not_strict : ¬ eStrictOri Supsilon Dupsilon 2 xUpsilon := by decide

/-- **`W-lambda1`, exact multinomial: strict** (ratio `27/8`). -/
theorem lambda1_E_strict : eStrictOri Slambda1 Dlambda1 2 xLambda := by decide

/-- **`W-lambda1`, fixed-`N` factor objective: exact tie.** The shorter
competitor `AT` ties `AAT` under the fixed-`N` factor objective: the strictness
does **not** transfer between the length-distinct objectives. -/
theorem lambda1_A_tie : aTieOri Slambda1 Dlambda1 2 xLambda := by decide

/-- **`W-lambda2`, fixed-`N` factor objective: strict** (ratio `8`). -/
theorem lambda2_A_strict : aStrictOri Slambda2 Dlambda2 2 xLambda := by decide

/-- **`W-lambda2`, exact multinomial: exact tie.** The longer competitor `ATAT`
ties `AT` under the exact multinomial: the opposite objective non-transfer. -/
theorem lambda2_E_tie : eTieOri Slambda2 Dlambda2 2 xLambda := by decide

/-- **`W-tau`, oriented panel: exact tie.** -/
theorem tau_E_tie_oriented : eTieOri Stau Dtau 2 xLambda := by decide

/-- **`W-tau`, molecular panel: exact tie.** -/
theorem tau_E_tie_molecular : eTieMol Stau Dtau 2 xLambda := by decide

/-- **`W-tau` is the reverse complement of the truth** (`ATT = rc(AAT)`): it is
not a rotation of the truth, so the tie refutes uniqueness-up-to-rotation while
uniqueness-up-to-dihedral survives. -/
theorem tau_D_eq_rc_S : Dtau.sym = rc Stau.sym := by decide

end ConcretePanel

