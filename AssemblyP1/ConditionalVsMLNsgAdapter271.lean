import AssemblyP1.ConditionalVsMLGenomeAdapter271
import AssemblyP1.ConditionalIdentifiability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# NSG-premised oriented adapter for the conditional-Bayes vs ordinary-ML separation (#271)

**Status: Lean kernel-checked instantiation in the exact AssemblyP1 finite
circular read model, with the external Not-So-Greedy (NSG) decoder guarantee
attributed as a premise and never claimed as proved.**

This module closes the oriented-adapter open item of #271: the conditional
recovery guarantee (A) is now derived **through the external NSG guarantee** —
the `decode_correct` field of `AssemblyP1.ConditionalIdentifiability.ReadModel`
— rather than through the direct finite-pmf support collapse of
`AssemblyP1/ConditionalVsMLGenomeAdapter271.lean`.  The ordinary-ML failure
(B) is unchanged: it is a prior-free, `E`-free fact about the same read model.

## What is built

The same finite model as the merged genome adapter (binary alphabet, circular
genomes of length `4`, oriented read length `2`, the three rotation-orbit
representatives `0001`, `0011`, `0101`) is re-read through the `ReadModel`
interface of #266:

* candidate universe `Θ = Fin 3` with orbit `nsgOrbit := (=)` (each candidate is
  a distinct rotation-orbit class, `orbit_injective` in the adapter);
* observation `X = Read`, the oriented length-`2` read string;
* feasibility `nsgFeasible := E`, the adapter's candidate-specific latent-start
  information-feasibility predicate built from the exact source predicate
  `SourceFaithfulIs.InformationFeasible`;
* joint mass `nsgJ := jointMassRead`, the ordinary read-model joint
  `π i · p_i(r)`;
* a deterministic read-only decoder `nsgDecode` (a finite lookup stand-in for
  the external NSG algorithm, which is **not** formalized).

The `decode_correct` field of the `ReadModel` is the **external NSG premise**:
`∀ g r, E g r → nsgDecode r = g`.  It is taken as the explicit hypothesis
`hNSG` of every (A)-side theorem below and is never proved, never axiomatized,
and never claimed.  The (B)-side theorems are premise-free.

## The two kernel-checked findings

1. **Separation (A ∧ ¬B), NSG-premised.**  Given `hNSG`, the conditional
   posterior on the truth orbit `1` at the separation observation `00` is
   exactly `1` (`nsg_conditional_posterior_eq_one`), via the merged #266 theorem
   `ReadModel.conditional_posterior_eq_one`.  Ordinary R-only ML strictly
   prefers the wrong orbit `0` (`sep_ml_strict`, `1/4 < 1/2`), so the truth is
   not a maximizer (`sep_truth_not_ml`) and the ordinary posterior on the truth
   is not certain (`sep_ordinary_not_certain`).  Packaged as `separation_nsg`.

2. **Precise boundary: the full uniform NSG premise fails in this model.**  At
   read `01` the two distinct orbits `1` (`0011`) and `2` (`0101`) are *both*
   information-feasible (`E_one_01`, and `E 2 (r2 0 1)`), so no deterministic
   decoder can recover both up to orbit; the feasible-fibre uniqueness
   corollary of the NSG guarantee fails (`nsg_full_premise_fails`).  Hence the
   NSG attribution is necessarily **instance-level** (at the separation
   observation `00`, where the only feasible candidate is the truth orbit `1`).

## Trust boundary and open items

* The NSG guarantee `hNSG` is an **external attributed premise** (the 2016
  manuscript's Theorem 1); the algorithm is not formalized and the guarantee is
  not proved here.
* The decoder `nsgDecode` is a finite lookup stand-in, not the NSG algorithm.
* The model is the bounded finite three-candidate witness of the merged adapter,
  not the general source-level theorem; the observation is a single oriented
  read string.
* `E → B` (conditional recovery implies ordinary ML recovery) remains **OPEN**
  and is not claimed; this module only exhibits the separation `A ∧ ¬B` and
  attributes (A) to the external NSG guarantee.

No `sorry`/`admit`/`axiom`/`native_decide`; the axiom audit is in
`AxiomAudit271.lean`.
-/

set_option linter.dupNamespace false

namespace AssemblyP1.ConditionalVsMLNsgAdapter271

open AssemblyP1.ConditionalVsMLGenomeAdapter271
open AssemblyP1.ConditionalIdentifiability
open AssemblyP1.FiniteBayesianSideInformation
open AssemblyP1.SourceFaithfulIs
open Finset BigOperators

/-- The candidate universe is `Fin 3`; the orbit is equality (each candidate is
a distinct rotation-orbit class).  Declared `abbrev` so that the `Decidable`
instance for the `if` in `ReadModel.conditional_posterior_eq_one` synthesizes. -/
abbrev nsgOrbit : Fin 3 → Fin 3 → Prop := fun a b => a = b

theorem nsgOrbit_equiv : Equivalence nsgOrbit :=
  ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-- The deterministic read-only decoder: a finite lookup stand-in for the
external Not-So-Greedy algorithm (not formalized).  At the separation
observation `00` it returns the truth orbit `1`. -/
def nsgDecode (w : Read) : Fin 3 :=
  if w = r2 0 0 then 1
  else if w = r2 0 1 then 2
  else if w = r2 1 0 then 2
  else 1

theorem nsgDecode_r00 : nsgDecode (r2 0 0) = 1 := by decide

theorem nsgDecode_r01 : nsgDecode (r2 0 1) = 2 := by decide

/-- The source-faithful feasibility event: the adapter's `E`, built from
`SourceFaithfulIs.InformationFeasible`. -/
def nsgFeasible : Fin 3 → Read → Prop := E

/-- The ordinary read-model joint mass `J i r = π i · p_i(r)`. -/
noncomputable def nsgJ : Fin 3 → Read → ℝ := jointMassRead

theorem nsgJ_nonneg (i : Fin 3) (r : Read) : 0 ≤ nsgJ i r := by
  unfold nsgJ jointMassRead
  exact mul_nonneg (prior_nonneg i) (p_nonneg i r)

/-- The `ReadModel` with the external NSG guarantee `hNSG` as its
`decode_correct` field.  The guarantee is the attributed premise, not a proved
fact.  Declared `reducible` so that the structure projections unfold to
`nsgOrbit`/`nsgDecode` in `simp`. -/
@[reducible] def nsgModelOf (hNSG : ∀ g r, nsgFeasible g r → nsgOrbit (nsgDecode r) g) :
    ReadModel (Fin 3) Read where
  orbit := nsgOrbit
  orbit_equiv := nsgOrbit_equiv
  decode := nsgDecode
  feasible := nsgFeasible
  decode_correct := hNSG

/-- The conditional posterior on orbit `g` at read `r` under the event-weighted
joint mass. -/
noncomputable def condPostGen (M : ReadModel (Fin 3) Read) (J : Fin 3 → Read → ℝ)
    (r : Read) (g : Fin 3) : ℝ :=
  eventJoint M J g r / (∑ h : Fin 3, eventJoint M J h r)

/-! ## The (A)-side via the external NSG guarantee -/

/-- The event-weighted joint mass is nonnegative. -/
theorem nsgEventJoint_nonneg (hNSG : ∀ g r, nsgFeasible g r → nsgOrbit (nsgDecode r) g)
    (g : Fin 3) (r : Read) :
    0 ≤ eventJoint (nsgModelOf hNSG) nsgJ g r :=
  eventJoint_nonneg (nsgModelOf hNSG) nsgJ nsgJ_nonneg g r

/-- The conditional mass at the separation observation is positive (the truth
orbit `1` alone contributes `π 1 · p_1(00) = 1/3 · 1/4`). -/
theorem nsg_hpos (hNSG : ∀ g r, nsgFeasible g r → nsgOrbit (nsgDecode r) g) :
    0 < ∑ g : Fin 3, eventJoint (nsgModelOf hNSG) nsgJ g (r2 0 0) := by
  have h1 : 0 < eventJoint (nsgModelOf hNSG) nsgJ 1 (r2 0 0) := by
    unfold eventJoint
    have hE : (nsgModelOf hNSG).feasible 1 (r2 0 0) := E_one_00
    rw [ite_eq_left hE]
    unfold nsgJ jointMassRead
    exact mul_pos (prior_pos 1) (by rw [p_1_00]; norm_num)
  exact lt_of_lt_of_le h1 (Finset.single_le_sum
    (fun g _ => nsgEventJoint_nonneg hNSG g (r2 0 0)) (Finset.mem_univ 1))

/-- The orbit-sum in the numerator of `conditional_posterior_eq_one` reduces to
the single `g = 1` term (the decoder returns `1` at read `00`).  Stated with
the same `Classical.propDecidable` instance the merged #266 theorem uses, so
that `rw` matches. -/
theorem nsg_num_eq (hNSG : ∀ g r, nsgFeasible g r → nsgOrbit (nsgDecode r) g) :
    (Finset.sum Finset.univ (fun g =>
        @ite ℝ ((nsgModelOf hNSG).orbit g ((nsgModelOf hNSG).decode (r2 0 0)))
          (Classical.propDecidable _) (eventJoint (nsgModelOf hNSG) nsgJ g (r2 0 0)) 0))
      = @ite ℝ ((nsgModelOf hNSG).orbit 1 ((nsgModelOf hNSG).decode (r2 0 0)))
          (Classical.propDecidable _) (eventJoint (nsgModelOf hNSG) nsgJ 1 (r2 0 0)) 0 := by
  refine Finset.sum_eq_single 1 ?_ ?_
  · intro g _ hne
    by_cases h : (nsgModelOf hNSG).orbit g ((nsgModelOf hNSG).decode (r2 0 0))
    · rw [ite_eq_left h]
      exfalso
      apply hne
      exact h
    · rw [ite_eq_right h]
  · intro h; exact absurd (Finset.mem_univ 1) h

/-- **Conditional recovery is certain, attributed to the external NSG
guarantee.**  Given the Not-So-Greedy decoder guarantee `hNSG` (the external
premise, NOT proved here), the conditional posterior on the truth orbit `1` at
the separation observation `00` is exactly `1` — via the merged #266 theorem
`ReadModel.conditional_posterior_eq_one`. -/
theorem nsg_conditional_posterior_eq_one
    (hNSG : ∀ g r, nsgFeasible g r → nsgOrbit (nsgDecode r) g) :
    condPostGen (nsgModelOf hNSG) nsgJ (r2 0 0) 1 = 1 := by
  have hpos := nsg_hpos hNSG
  have h1 := ReadModel.conditional_posterior_eq_one (nsgModelOf hNSG) nsgJ
    (r2 0 0) hpos
  rw [nsg_num_eq hNSG] at h1
  have horb1 : (nsgModelOf hNSG).orbit 1 ((nsgModelOf hNSG).decode (r2 0 0)) := by
    simp [nsgOrbit, nsgDecode]
  rw [ite_eq_left horb1] at h1
  exact h1

/-! ## The (B)-side: ordinary R-only ML strictly prefers the wrong orbit -/

/-- At read `00` the wrong orbit `0` (`0001`) strictly beats the truth orbit `1`
(`0011`): `1/2 > 1/4`.  Prior-free and `E`-free. -/
theorem nsg_ml_strict : p 1 (r2 0 0) < p 0 (r2 0 0) := sep_ml_strict

/-- The truth orbit `1` is not even an ordinary-ML maximizer at read `00`. -/
theorem nsg_truth_not_ml : ¬ MLMax 1 (r2 0 0) := sep_truth_not_ml

/-- The ordinary (no side information) posterior on the truth orbit is NOT
certain at read `00`: the wrong orbit `0` retains positive prior and positive
likelihood. -/
theorem nsg_ordinary_not_certain :
    posteriorMass prior p (fun _ _ => True) orbit (r2 0 0) (orbit 1) ≠ 1 :=
  sep_ordinary_not_certain

/-- **Genome-level separation (A ∧ ¬B), NSG-premised.**  On the exact read model
with the normalized orbit-class prior and the source-faithful feasibility event
`E`: given the external NSG guarantee `hNSG`, the conditional posterior on the
true orbit is `1`, while ordinary R-only ML strictly prefers the wrong orbit
`0` and the ordinary posterior on the truth is not certain. -/
theorem separation_nsg
    (hNSG : ∀ g r, nsgFeasible g r → nsgOrbit (nsgDecode r) g) :
    condPostGen (nsgModelOf hNSG) nsgJ (r2 0 0) 1 = 1 ∧
      p 1 (r2 0 0) < p 0 (r2 0 0) ∧
      ¬ MLMax 1 (r2 0 0) ∧
      posteriorMass prior p (fun _ _ => True) orbit (r2 0 0) (orbit 1) ≠ 1 :=
  ⟨nsg_conditional_posterior_eq_one hNSG, nsg_ml_strict, nsg_truth_not_ml,
    nsg_ordinary_not_certain⟩

/-! ## Precise boundary: the full uniform NSG premise fails in this model -/

/-- Candidate `1` (`0011`) is information-feasible at read `01`: start `1` of
`0011` spells `01`, and the placement `{1,3}` covers the circle with no triple
repeat (read length `2`). -/
theorem E_one_01 : E 1 (r2 0 1) :=
  ⟨({1, 3} : Finset (Fin 4)), ⟨1, by decide, by decide⟩, by decide⟩

/-- Candidate `2` (`0101`) is information-feasible at read `01`: start `0` of
`0101` spells `01`, and the placement `{0,2}` covers the circle with no triple
repeat. -/
theorem E_two_01 : E 2 (r2 0 1) :=
  ⟨({0, 2} : Finset (Fin 4)), ⟨0, by decide, by decide⟩, by decide⟩

/-- **The full uniform NSG premise fails in this finite model.**  At read `01`
the two distinct orbits `1` and `2` are both information-feasible, but the
decoder returns `2`; so `E 1 (r2 0 1) → nsgDecode (r2 0 1) = 1` is false.  The
feasible-fibre uniqueness corollary of the NSG guarantee does not hold here, so
the NSG attribution is necessarily instance-level (at the separation observation
`00`, where the only feasible candidate is the truth orbit `1`). -/
theorem nsg_full_premise_fails :
    ¬ (∀ g r, nsgFeasible g r → nsgOrbit (nsgDecode r) g) := by
  intro h
  have h1 : E 1 (r2 0 1) := E_one_01
  have h2 := h 1 (r2 0 1) h1
  simp only [nsgOrbit, nsgDecode_r01] at h2
  omega

/-! ## Kernel-checking boundary -/

#print axioms nsg_conditional_posterior_eq_one
#print axioms separation_nsg
#print axioms nsg_full_premise_fails
#print axioms E_one_01
#print axioms E_two_01
#print axioms nsg_num_eq
#print axioms nsg_hpos

end AssemblyP1.ConditionalVsMLNsgAdapter271
