import Mathlib
import AssemblyP1.SourceFaithfulIs
import AssemblyP1.HistoricalCovers

/-!
# Conditional identifiability from the Not-So-Greedy information-feasibility guarantee

This module formalizes the *conditional* inference that follows from the
Shomorony--Kim--Courtade--Tse (2016) Not-So-Greedy (NSG) reconstruction
guarantee.  It is deliberately scoped: the NSG guarantee itself is a cited
external theorem and is **not** proved here.  Every theorem below is a
kernel-checked consequence of that guarantee taken as an explicit hypothesis.

The logical shape, matching issue #266:

1. **Feasible-fibre uniqueness.**  If a single deterministic read-only decoder
   `decode` is correct for every candidate `g` whose observation `r` is
   information-feasible, `F g r`, then a fixed `r` cannot be feasible for two
   candidate genomes in different rotation classes:
   `F g r → F h r → g ≈ h`.  This is uniqueness of the feasible *fibre*, not
   uniqueness of ordinary maximum-likelihood estimation.

2. **Conditional posterior certainty.**  For any finite candidate space and any
   (unnormalized) joint mass `J g r`, restricting the joint mass to the
   truth-dependent event `E := F G R` gives a posterior supported on the single
   rotation class of `decode r`: the conditional mass of that class equals the
   total conditional mass, so the conditional probability is `1`.  The event `E`
   is *not* a function of `r` alone; it is the joint event "the true genome and
   the observed reads satisfy `F`".

3. **Constrained MAP vs. ordinary ML.**  The constrained joint
   `J g r · 1_{F g r}` has support inside the rotation class of `decode r`, while
   a competitor `h` with `¬ F h r` can carry strictly larger ordinary mass
   `J h r`.  A concrete two-point witness is included.

4. **No rule beats the decoder on `E`.**  The orbit mass of any reported class
   is at most the total conditional mass, with equality for `decode`.

## Source fidelity: latent placements

The repository's literal §6.4 predicate
(`HistoricalCovers.HistoricalInformationFeasibleLiteral S L R`) is determined
by the candidate genome `S` and the *observed read-string set*
`observedTypes_ofFinset S L R`; the sampled start set `R` enters only through
that induced string set, and for a competitor of a different length the true
genome's start labels cannot be reused.  The **likelihood**, by contrast, is a
function of the candidate-specific placement, and several placements can induce
the same observed string set.

Consequently, when the source event is expressed at the placement level as a
predicate `E g T`, the scientifically correct event-weighted joint mass is

`∑_{T : consistent g T Y ∧ E g T} weight g T`,

i.e. a weighted marginalization over compatible placements, rather than a single
likelihood multiplied by an existential feasibility indicator.  `PlacementModel`
and `placementJoint` below formalize exactly this weighted sum, and
`placement_support_subset_orbit`/`placement_posterior_certain` are the
placement-level versions of (1) and (2).  The string-level `ReadModel` is the
clean abstraction the issue states; the placement-level model is the source
adapter, and the two are kept separate.

All results are proved from the NSG premise plus finite real algebra.  No new
biological or combinatorial conjecture is introduced, and the module introduces
no `axiom`, `sorry`, or `admit`.
-/

set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false

open Classical
open scoped Classical

namespace AssemblyP1.ConditionalIdentifiability

open AssemblyP1.SourceFaithfulIs

universe u v w

variable {Θ : Type u} {X : Type v} {Tp : Θ → Type v}

/-! ## 1. Abstract deterministic decoder and feasible-fibre uniqueness -/

/-- An abstract finite-read reconstruction problem.

* `orbit` is the genome equivalence induced by the observation model (cyclic
  shift for oriented reads; dihedral for reverse-complement-collapsed molecule
  classes).  It is required to be an equivalence relation.
* `decode` is the deterministic read-only reconstruction supplied by the source
  theorem.
* `feasible g r` is the source information-feasibility predicate `F g r`.
* `decode_correct` is the **external NSG premise**: the decoder recovers every
  feasible candidate up to the orbit equivalence. -/
structure ReadModel (Θ : Type u) (X : Type v) where
  /-- Genome equivalence (rotation / molecule class). -/
  orbit : Θ → Θ → Prop
  /-- `orbit` is an equivalence relation. -/
  orbit_equiv : Equivalence orbit
  /-- Deterministic read-only reconstruction `A(r)`. -/
  decode : X → Θ
  /-- Source information-feasibility `F(g,r)`. -/
  feasible : Θ → X → Prop
  /-- External Not-So-Greedy guarantee: `F g r → A r ≈ g`. -/
  decode_correct : ∀ g r, feasible g r → orbit (decode r) g

/-- **Feasible-fibre uniqueness (issue #266, item 1).**  From the external NSG
guarantee, two candidates that are both feasible for the *same* observation lie
in the same rotation class. -/
theorem ReadModel.feasible_fibre_unique (M : ReadModel Θ X)
    {g h : Θ} {r : X} (hg : M.feasible g r) (hh : M.feasible h r) :
    M.orbit g h :=
  M.orbit_equiv.trans (M.orbit_equiv.symm (M.decode_correct g r hg))
    (M.decode_correct h r hh)

/-- Every feasible candidate lies in the orbit of the decoder output. -/
theorem ReadModel.mem_orbit_decode (M : ReadModel Θ X) {g : Θ} {r : X}
    (hg : M.feasible g r) : M.orbit g (M.decode r) :=
  M.orbit_equiv.symm (M.decode_correct g r hg)

/-! ## 2. Conditional posterior certainty (string-level event) -/

/-- The joint mass restricted to the truth-dependent feasibility event
`E = F(G,R)`: `eventJoint M J g r = J g r` when `F g r` holds, and `0` otherwise. -/
noncomputable def eventJoint (M : ReadModel Θ X) (J : Θ → X → ℝ) : Θ → X → ℝ :=
  fun g r => if M.feasible g r then J g r else 0

/-- The event-restricted joint mass is nonnegative when `J` is. -/
theorem eventJoint_nonneg (M : ReadModel Θ X) (J : Θ → X → ℝ)
    (hJ : ∀ g r, 0 ≤ J g r) (g : Θ) (r : X) : 0 ≤ eventJoint M J g r := by
  classical
  by_cases hf : M.feasible g r <;> simp [eventJoint, hf, hJ g r]

/-- **Conditional posterior certainty (issue #266, item 2).**  The conditional
mass of the decoder's rotation class equals the total conditional mass, i.e.
`P([G] = [A r] | R = r, E) = 1` whenever the conditioning event has positive
mass.  The event `E = F(G,R)` is truth-dependent; nothing here is a statement
about conditioning on `R` alone. -/
theorem ReadModel.orbit_mass_eq_total [Fintype Θ] (M : ReadModel Θ X)
    (J : Θ → X → ℝ) (r : X) :
    (∑ g : Θ, if M.orbit g (M.decode r) then eventJoint M J g r else 0)
      = ∑ g : Θ, eventJoint M J g r := by
  classical
  refine Finset.sum_congr rfl ?_
  intro g _
  by_cases hg : M.orbit g (M.decode r)
  · simp [hg]
  · have hnf : ¬ M.feasible g r := fun hf => hg (M.mem_orbit_decode hf)
    simp [hg, eventJoint, hnf]

/-- The posterior probability of the decoder's rotation class is exactly `1`. -/
theorem ReadModel.conditional_posterior_eq_one [Fintype Θ] (M : ReadModel Θ X)
    (J : Θ → X → ℝ) (r : X)
    (hpos : 0 < ∑ g : Θ, eventJoint M J g r) :
    (∑ g : Θ, if M.orbit g (M.decode r) then eventJoint M J g r else 0)
        / (∑ g : Θ, eventJoint M J g r) = 1 := by
  rw [M.orbit_mass_eq_total J r]
  exact div_self (ne_of_gt hpos)

/-- The constrained support of `eventJoint` lies inside the decoder's rotation
class. -/
theorem ReadModel.constrained_support_subset_orbit (M : ReadModel Θ X)
    (J : Θ → X → ℝ) {g : Θ} {r : X} (h : eventJoint M J g r ≠ 0) :
    M.orbit g (M.decode r) := by
  classical
  by_cases hf : M.feasible g r
  · exact M.mem_orbit_decode hf
  · have hzero : eventJoint M J g r = 0 := by simp [eventJoint, hf]
    exact absurd hzero h

/-! ## 3. Constrained MAP, ordinary ML, and the no-better-rule corollary -/

/-- **Constrained MAP recovery (issue #266, item 3).**  Any candidate that
maximizes the constrained joint mass `π(g) P_g(r) 1_{F(g,r)}` with positive
constrained mass lies in the decoder's rotation class.  The value of the
relative likelihoods is irrelevant: the constraint alone pins the class. -/
theorem ReadModel.constrained_MAP_mem_orbit (M : ReadModel Θ X) (J : Θ → X → ℝ)
    {gstar : Θ} {r : X} (hpos : 0 < eventJoint M J gstar r) :
    M.orbit gstar (M.decode r) := by
  classical
  by_cases hf : M.feasible gstar r
  · exact M.mem_orbit_decode hf
  · simp [eventJoint, hf] at hpos

/-- **Ordinary ML can prefer an infeasible competitor (issue #266, item 3).**
A candidate `h` with `¬ F h r` carries zero constrained mass even when its
ordinary joint mass is strictly positive.  The next section exhibits a concrete
instance where it is strictly larger than the feasible one. -/
theorem ReadModel.infeasible_eventJoint_eq_zero (M : ReadModel Θ X) (J : Θ → X → ℝ)
    {h : Θ} {r : X} (hnf : ¬ M.feasible h r) : eventJoint M J h r = 0 := by
  classical
  simp [eventJoint, hnf]

/-- **No rule beats the decoder on the event (issue #266, item 4).**  For any
reported class `c`, its conditional mass is at most the total conditional mass;
equality holds for `c = decode r` by `ReadModel.orbit_mass_eq_total`.  Hence the
conditional zero-one accuracy cannot exceed `1`, and `decode` attains it. -/
theorem ReadModel.orbit_mass_le_total [Fintype Θ] (M : ReadModel Θ X)
    (J : Θ → X → ℝ) (hJ : ∀ g r, 0 ≤ J g r) (r : X) (c : Θ) :
    (∑ g : Θ, if M.orbit g c then eventJoint M J g r else 0)
      ≤ ∑ g : Θ, eventJoint M J g r := by
  classical
  apply Finset.sum_le_sum
  intro g _
  by_cases h : M.orbit g c
  · simp [h]
  · have hz : (if M.orbit g c then eventJoint M J g r else 0) = 0 := by simp [h]
    rw [hz]
    exact eventJoint_nonneg M J hJ g r

/-! ## 4. Source adapter: latent placements and the weighted event mass -/

/-- A latent-placement reconstruction problem.

* `Tp g` is the type of candidate-specific placements of reads on candidate `g`
  (e.g. `Finset (Fin g.len)`).
* `feasible g T` is the source information-feasibility event `E(g,T)`.
* `consistent g T Y` says the placement `T` on candidate `g` is compatible with
  the shared observed data `Y`.
* `decode_correct` is the external NSG guarantee, uniform over candidates and
  placements, and phrased against the *same* observation `Y`. -/
structure PlacementModel (Θ : Type u) (Tp : Θ → Type v) (X : Type w) where
  /-- Genome equivalence (rotation / molecule class). -/
  orbit : Θ → Θ → Prop
  /-- `orbit` is an equivalence relation. -/
  orbit_equiv : Equivalence orbit
  /-- Deterministic read-only reconstruction `A(Y)`. -/
  decode : X → Θ
  /-- Source information-feasibility `E(g,T)`. -/
  feasible : (g : Θ) → Tp g → Prop
  /-- Placement `T` on `g` is compatible with observation `Y`. -/
  consistent : (g : Θ) → Tp g → X → Prop
  /-- External NSG guarantee, uniform over candidates and placements. -/
  decode_correct : ∀ (g : Θ) (T : Tp g) (Y : X),
    consistent g T Y → feasible g T → orbit (decode Y) g

/-- The source-faithful event-weighted joint mass of observing `Y` under
candidate `g`:
`∑_{T : consistent g T Y ∧ E(g,T)} weight g T`.
This is the weighted sum over placements that the research note on #266
requires; it is **not** `weight · 1_{∃T …}`, because a candidate may have some
placements compatible with `Y` and others not. -/
noncomputable def placementJoint [∀ g, Fintype (Tp g)]
    (M : PlacementModel Θ Tp X) (weight : (g : Θ) → Tp g → ℝ) (Y : X) (g : Θ) : ℝ :=
  ∑ T : Tp g,
    if M.consistent g T Y ∧ M.feasible g T then weight g T else 0

/-- **Placement-level feasible-fibre uniqueness.**  Any candidate with positive
event-weighted mass is in the decoder's orbit, for the *same* observation `Y`. -/
theorem placement_support_subset_orbit [Fintype Θ] [∀ g, Fintype (Tp g)]
    (M : PlacementModel Θ Tp X) (weight : (g : Θ) → Tp g → ℝ) (Y : X) {g : Θ}
    (h : placementJoint M weight Y g ≠ 0) : M.orbit g (M.decode Y) := by
  classical
  by_contra hg
  apply h
  unfold placementJoint
  apply Finset.sum_eq_zero
  intro T _
  by_cases hc : M.consistent g T Y ∧ M.feasible g T
  · exact absurd (M.orbit_equiv.symm (M.decode_correct g T Y hc.1 hc.2)) hg
  · simp [hc]

/-- **Placement-level conditional posterior certainty.**  The conditional mass
of the decoder's orbit equals the total conditional mass under the source-faithful
weighted event mass. -/
theorem placement_posterior_certain [Fintype Θ] [∀ g, Fintype (Tp g)]
    (M : PlacementModel Θ Tp X) (weight : (g : Θ) → Tp g → ℝ) (Y : X) :
    (∑ g : Θ, if M.orbit g (M.decode Y) then placementJoint M weight Y g else 0)
      = ∑ g : Θ, placementJoint M weight Y g := by
  classical
  refine Finset.sum_congr rfl ?_
  intro g _
  by_cases hg : M.orbit g (M.decode Y)
  · simp [hg]
  · have hzero : placementJoint M weight Y g = 0 := by
      by_contra hne
      exact hg (placement_support_subset_orbit M weight Y hne)
    simp [hg, hzero]

/-! ## 5. Historically scoped endpoint (real repository definitions)

The next two definitions state the source event through the repository's
literal §6.4 predicate and the observation as the read **strings**.  The NSG
guarantee remains an explicit hypothesis: this is the exact trust boundary. -/

open AssemblyP1.HistoricalCovers

/-- The source-faithful historical information-feasibility event `E(g,R)`,
read through the repository's literal §6.4 predicate
`HistoricalInformationFeasibleLiteral` (coverage plus all-literal-triple
bridging plus interleaved-pair bridging, each quantified over the saturated
match starts). -/
def HistoricalEvent {α : Type u} [DecidableEq α] (S : Genome α) (L : ℕ)
    (R : Finset (Fin S.len)) : Prop :=
  HistoricalInformationFeasibleLiteral S L R

/-- **Historically scoped feasible-fibre uniqueness.**  Assume the external NSG
guarantee for the literal historical event: a deterministic read-only decoder
`A` returns, for every feasible `(S,R)`, a genome in `S`'s orbit.  Then two
candidates that are both historically feasible and induce the *same observed
read-string set* lie in the same orbit.

All subsequent theorems are kernel-checked FROM the `hNSG` hypothesis.
The exact `hNSG` interface here is an ADDITIONAL, STRONGER ASSUMPTION
than published Corollary 1: it gives the decoder only a Finset of DISTINCT
read strings, whereas the published algorithm works with N sampled READ
INSTANCES and constructs a graph with edge multiplicities. No theorem
establishes that the original decoder factors through the deduplicated
`observedTypes_ofFinset`, nor that it works outside the original
read-length/genome-length regime. Hence the source decoder adapter
remains OPEN. This endpoint establishes the stated conditional inference,
not a formal source-level instantiation of the 2016 corollary. -/
theorem historical_feasible_fibre_unique {α : Type u} [DecidableEq α] {L : ℕ}
    (A : Finset (Fin L → α) → Genome α)
    (orbit : Genome α → Genome α → Prop) (horb : Equivalence orbit)
    (hNSG : ∀ (S : Genome α) (R : Finset (Fin S.len)),
      HistoricalEvent S L R → orbit (A (observedTypes_ofFinset S L R)) S)
    {S T : Genome α} {R : Finset (Fin S.len)} {R' : Finset (Fin T.len)}
    (hS : HistoricalEvent S L R) (hT : HistoricalEvent T L R')
    (hobs : observedTypes_ofFinset S L R = observedTypes_ofFinset T L R') :
    orbit S T := by
  have hA : A (observedTypes_ofFinset S L R) = A (observedTypes_ofFinset T L R') := by
    rw [hobs]
  have h1 : orbit (A (observedTypes_ofFinset T L R')) S := by
    rw [← hA]; exact hNSG S R hS
  exact horb.trans (horb.symm h1) (hNSG T R' hT)

/-! ## 6. Concrete non-implication witness: ordinary ML can be infeasible

A two-point instance with `Θ = Bool`, `X = PUnit`, equality as the orbit, a
decoder returning `true`, and `F g _ := (g = true)`.  The infeasible competitor
`false` has strictly larger ordinary mass (`2 > 1`), while its constrained mass
is `0`. -/

namespace Example

/-- Orbit: equality of `Bool` (two distinct rotation classes). -/
def exOrbit : Bool → Bool → Prop := fun a b => a = b

theorem exOrbit_equiv : Equivalence exOrbit :=
  ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- Decoder: always returns `true`. -/
def exDecode : PUnit → Bool := fun _ => true

/-- Feasibility: only `true` is feasible. -/
def exFeasible : Bool → PUnit → Prop := fun g _ => g = true

theorem exDecode_correct : ∀ g r, exFeasible g r → exOrbit (exDecode r) g := by
  intro g r hg
  simpa [exOrbit, exDecode, exFeasible] using hg.symm

/-- The abstract model of the witness. -/
def exModel : ReadModel Bool PUnit :=
  { orbit := exOrbit, orbit_equiv := exOrbit_equiv, decode := exDecode,
    feasible := exFeasible, decode_correct := exDecode_correct }

/-- Ordinary joint mass: the infeasible competitor is strictly larger. -/
def exJ : Bool → PUnit → ℝ := fun g _ => if g then 1 else 2

/-- Ordinary ML prefers the infeasible competitor `false`. -/
theorem ordinary_ML_prefers_infeasible : exJ true PUnit.unit < exJ false PUnit.unit := by
  norm_num [exJ]

/-- The constrained mass kills the infeasible competitor and keeps the feasible
one, so constrained MAP recovers the decoder's class. -/
theorem constrained_kills_infeasible :
    eventJoint exModel exJ false PUnit.unit = 0 ∧
      eventJoint exModel exJ true PUnit.unit = 1 := by
  constructor <;> simp [eventJoint, exModel, exFeasible, exJ]

end Example

/-! ## Kernel-checking boundary

The `#print axioms` output confirms that every endpoint depends only on Lean's
three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and never on
a project `axiom`, `sorry`, or `admit`. -/

#print axioms ReadModel.feasible_fibre_unique
#print axioms ReadModel.orbit_mass_eq_total
#print axioms ReadModel.conditional_posterior_eq_one
#print axioms ReadModel.constrained_MAP_mem_orbit
#print axioms ReadModel.orbit_mass_le_total
#print axioms placement_support_subset_orbit
#print axioms placement_posterior_certain
#print axioms historical_feasible_fibre_unique

end AssemblyP1.ConditionalIdentifiability
