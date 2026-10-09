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
objectives. Parts 1-5 below separate those axes and then say, for each pair of
axes, whether a *strict* counterexample transfers.

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
`W-lambda*` witnesses are the two halves of that statement.

**Part 3 — the panel.**  Two coupled strand conventions over the two-symbol DNA
panel `{A, T}`: oriented read types (`E_ori`, `A_ori`, `Alit_ori`) and
reverse-complement class read types (`E_mol`, `A_mol`, `Alit_mol`), plus the
`§6.2` necessary condition `Spelled62` for candidate feasibility.  The two
conventions are one coupled choice: `IsCyclicShift` and `IsReverseComplement`
are the genome equivalences they force.

**Part 4 — five `I_s`-certified witnesses.**  Each witness separates variant
panels that the witnesses already on `main` do not separate:

* `W-sigma` (`AATT → AAAT`, same length): strict under the *oriented* read
  types, an exact tie under *reverse-complement-collapsed* read types;
* `W-lambda1` (`AAT → AT`, competitor shorter): strict for the exact
  multinomial, an exact tie for the fixed-`N` factor objective;
* `W-lambda2` (`AT → ATAT`, competitor longer, both spelled): strict for the
  fixed-`N` factor objective, an exact tie for the exact multinomial, and
  likelihood `0` for the literal product of binomial marginals;
* `W-upsilon` (`AAT → AATT`, competitor longer): strict for the exact
  multinomial in the *molecular* panel, not strict (ratio `27/64 < 1`) in the
  oriented panel — the missing second direction of the strand non-transfer;
* `W-tau` (`AAT → ATT`, same length): every objective ties and the competitor
  is not a cyclic shift of the truth, so the uniqueness-up-to-cyclic-shift schema
  is refuted while every maximizer schema survives.

**Part 5 — the transfer table as propositions.**  One block per axis: length,
strand, feasibility, schema, and the strictness/tie interaction.

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
