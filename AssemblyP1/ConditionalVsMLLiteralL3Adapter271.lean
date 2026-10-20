import AssemblyP1.ConditionalVsMLGenomeAdapter271
import AssemblyP1.HistoricalCovers
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity

/-!
# Genome-level oriented adapter at read length `3` with the **literal** historical event (#271)

**Status: Lean kernel-checked source-faithful oriented adapter. This closes the
read-length-`≥3` item that the merged `ConditionalVsMLGenomeAdapter271` handoff
left open: the `(A ∧ ¬B)` separation is instantiated with the *literal* §6.4
historical predicate `HistoricalInformationFeasibleLiteral`, attained by a
**non-saturated** placement at a *single* observed read string.**

The merged adapter `AssemblyP1/ConditionalVsMLGenomeAdapter271` uses the
placement-based `SourceFaithfulIs.InformationFeasible` at read length `2`.  The
merged `AssemblyP1/ConditionalVsMLFullReadSet271` proved that the literal
*weighted placement mass* over the full observed read set vanishes at **every**
**singleton full-read-set** observation (`fullJoint_singleton_eq_zero`); that
statement is about the placement mass at a single full-read-set observation, not
about the satisfiability of the single-read-string event `E`.  At read length `2`
the literal event `E` is nonetheless satisfiable and already yields the
`(A ∧ ¬B)` separation, but only through the **saturated** placement `{0,1,2,3}`
(independently kernel-checked; external review artifact on board #271).  At read
length `3` the genuinely new content of this module is the first
**non-saturated** single-read literal witness, via the placement `{0,1,3}`.

## The model (fixed axes)

| axis | choice in this adapter |
| --- | --- |
| alphabet | `Sym = Fin 2` (binary) |
| genome length | `G = 4`; circular genome `ZMod 4 → Sym` |
| read length | `L = 3`; oriented read string `Read = Fin 3 → Sym` |
| candidate universe | six rotation-**orbit classes**: `0000`, `0001`, `0011`, `0101`, `0111`, `1111` up to rotation (`rep`, `orbit`) |
| observation model | `p i w = orbitReadPmf (G:=4) (L:=3) (orbit i) w = #{starts spelling w in g} / 4`; normalized (`p_sum_one`) and nonnegative (`p_nonneg`) |
| observation representation | oriented one-strand windows; **no** reverse-complement quotient (per #269/#260, and the merged `W1W2RcOrientedRepresentation271`) |
| prior | uniform `1/6` over the six orbit classes (`prior`), normalized (`prior_sum_one`) |
| likelihood objective | exact single-read pmf (the iid product is its `n`-fold power); **not** the MB09 fixed-`N` product-binomial and **not** the §6.2 feasible-flow objective |
| side information | candidate-specific **literal** §6.4 event `E i r := ∃ T, (∃ s ∈ T, window (genOf i) 3 s = r) ∧ HistoricalInformationFeasibleLiteral (genOf i) 3 T` |
| rotation | the genuine rotation action on `ZMod 4`; `readPmf` is rotation invariant (`readPmf_rotWord`), so `p` descends to orbits |

## The two kernel-checked endpoints

* **(A ∧ ¬B) — separation.** Truth orbit `1` (`0001`), observed read string
  `000`.  The literal event `E` holds for the truth via the **non-saturated**
  placement `{0,1,3}` (`literalFeasible_nonsaturated`) and fails for every other
  orbit (`E_zero_000` … `E_five_000`), so the conditional posterior on the truth
  orbit is `1` (`sep_posteriorMass_one`).  But ordinary R-only ML strictly
  prefers the wrong orbit `0` (`0000`, `p = 1 > 1/4 = p₁`), so the truth is not
  an ML maximizer (`sep_truth_not_ml`) and the ordinary posterior is not certain
  (`sep_ordinary_not_certain`).
* **(B ∧ ¬A) — converse.** Truth orbit `0` (`0000`), observed read string `000`:
  ordinary ML *uniquely* selects the truth (`conv_ml_unique`), yet the ordinary
  posterior on the truth is not certain (`conv_ordinary_not_certain`).

Both endpoints use **one and the same** generative read model: the same `p`, the
same orbit universe, and the same uniform prior.  The only additional ingredient
in (A) is the literal source event `E`.

## What is and is not claimed

* This is the source-faithful **oriented** adapter: the read is an oriented
  string, the event is the literal §6.4 `I_s`, and both are kernel-checked on the
  same model.  It does not identify the oriented observable with the
  reverse-complement-collapsed W1/W2 molecule observable (that separation is the
  merged `W1W2RcOrientedRepresentation271`).
* `E → B` is still **not** claimed (and is refuted here: `sep_truth_not_ml`).
  The uniform orbit prior does not create the (A)-side collapse; the literal
  event does.
* The ordinary-ML classification (#255/#258/#259/#261) is untouched.

No `sorry`/`admit`/`axiom`/`native_decide`; `#print axioms` is clean (only the
Mathlib foundations), audited in `AxiomAudit271.lean`.
-/

set_option maxHeartbeats 8000000

namespace AssemblyP1.ConditionalVsMLLiteralL3Adapter271

open AssemblyP1.GenomeOrbitAdapter
open AssemblyP1.FiniteBayesianSideInformation
open AssemblyP1.SourceFaithfulIs
open AssemblyP1.HistoricalCovers
open Finset BigOperators

/-- The binary symbol alphabet. -/
abbrev Sym : Type := Fin 2

/-- Oriented length-`3` read strings. -/
abbrev Read : Type := Fin 3 → Sym

/-- Circular binary genomes of length `4`. -/
abbrev Word : Type := ZMod 4 → Sym

/-- The circular word with the four listed symbols. -/
def g4 (a b c d : Sym) : Word
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c
  | _ => d

/-- The oriented length-`3` read string with the three listed symbols. -/
def r3 (a b c : Sym) : Read
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | _ => c

/-- Representatives of the six candidate rotation-orbit classes:
`0 ↦ 0000`, `1 ↦ 0001`, `2 ↦ 0011`, `3 ↦ 0101`, `4 ↦ 0111`, `5 ↦ 1111`. -/
def rep : Fin 6 → Word
  | 0 => g4 0 0 0 0
  | 1 => g4 0 0 0 1
  | 2 => g4 0 0 1 1
  | 3 => g4 0 1 0 1
  | 4 => g4 0 1 1 1
  | 5 => g4 1 1 1 1

/-- The candidate genome universe is the set of rotation-orbit classes of the
six representatives, embedded into the genuine orbit quotient. -/
def orbit : Fin 6 → Quotient (rotSetoid Sym 4) := fun i => Quotient.mk _ (rep i)

/-- The exact normalized per-candidate observation model over oriented read
strings: the rotation-orbit read pmf of `GenomeOrbitAdapter`. -/
noncomputable def p (i : Fin 6) (w : Read) : ℝ :=
  orbitReadPmf (G := 4) (L := 3) (orbit i) w

/-- The uniform prior over the six rotation-orbit classes. -/
noncomputable def prior (_ : Fin 6) : ℝ := 1 / 6

/-! ## The read model evaluates exactly -/

/-- The per-candidate observation model is the raw read pmf of the chosen orbit
representative (the descended pmf reduces on `Quotient.mk`). -/
theorem p_eq_readPmf (i : Fin 6) (w : Read) : p i w = readPmf (rep i) w := by
  unfold p orbit
  rfl

/-- The per-candidate observation model is nonnegative. -/
theorem p_nonneg (i : Fin 6) (w : Read) : 0 ≤ p i w := by
  rw [p_eq_readPmf]
  unfold readPmf
  positivity

/-- The per-candidate observation model is normalized: `∑_w p_g(w) = 1`. -/
theorem p_sum_one (i : Fin 6) : ∑ w : Read, p i w = 1 := by
  unfold p
  exact orbitReadPmf_sum_one (α := Sym) 4 3 (orbit i)

theorem prior_pos (i : Fin 6) : 0 < prior i := by norm_num [prior]

theorem prior_nonneg (i : Fin 6) : 0 ≤ prior i := le_of_lt (prior_pos i)

theorem prior_sum_one : ∑ i : Fin 6, prior i = 1 := by
  simp only [Fin.sum_univ_six, prior]
  norm_num

/-! ### Multiplicity and pmf table at the observed read `000` -/

theorem mult_rep0_000 : mult (rep 0) (r3 0 0 0) = 4 := by decide
theorem mult_rep1_000 : mult (rep 1) (r3 0 0 0) = 1 := by decide
theorem mult_rep2_000 : mult (rep 2) (r3 0 0 0) = 0 := by decide
theorem mult_rep3_000 : mult (rep 3) (r3 0 0 0) = 0 := by decide
theorem mult_rep4_000 : mult (rep 4) (r3 0 0 0) = 0 := by decide
theorem mult_rep5_000 : mult (rep 5) (r3 0 0 0) = 0 := by decide

theorem p_0_000 : p 0 (r3 0 0 0) = 1 := by
  rw [p_eq_readPmf]; unfold readPmf; rw [mult_rep0_000]; norm_num
theorem p_1_000 : p 1 (r3 0 0 0) = 1 / 4 := by
  rw [p_eq_readPmf]; unfold readPmf; rw [mult_rep1_000]; norm_num
theorem p_2_000 : p 2 (r3 0 0 0) = 0 := by
  rw [p_eq_readPmf]; unfold readPmf; rw [mult_rep2_000]; norm_num
theorem p_3_000 : p 3 (r3 0 0 0) = 0 := by
  rw [p_eq_readPmf]; unfold readPmf; rw [mult_rep3_000]; norm_num
theorem p_4_000 : p 4 (r3 0 0 0) = 0 := by
  rw [p_eq_readPmf]; unfold readPmf; rw [mult_rep4_000]; norm_num
theorem p_5_000 : p 5 (r3 0 0 0) = 0 := by
  rw [p_eq_readPmf]; unfold readPmf; rw [mult_rep5_000]; norm_num

/-! ## The truth orbit and the all-zero orbit are distinct classes -/

/-- Orbit `0` (`0000`) and orbit `1` (`0001`) are distinct rotation classes:
their read pmfs differ at `000` (`1` versus `1/4`). -/
theorem orbit_zero_ne_one : orbit 0 ≠ orbit 1 := by
  intro h
  have hp : p 0 (r3 0 0 0) = p 1 (r3 0 0 0) := by unfold p; rw [h]
  rw [p_0_000, p_1_000] at hp
  norm_num at hp

/-! ## Candidate-specific **literal** §6.4 information feasibility `E`

`E i r` is defined **inside** the model, from the exact source predicate
`HistoricalCovers.HistoricalInformationFeasibleLiteral` (the literal §6.4 `I_s`
of Shomorony et al. (2016)): candidate `i` admits a latent read-start set `T`
whose induced read-string set satisfies the literal historical `I_s`, and which
realizes the observed read string `r` at one of its starts.  There is no
externally supplied truth-dependent oracle. -/

/-- The source-faithful circular genome of a `ZMod 4`-indexed word. -/
abbrev toGenome (g : Word) : Genome Sym :=
  ⟨4, by norm_num, fun d => g (d.val : ZMod 4)⟩

/-- Candidate `i`'s representative read as a source-faithful circular genome. -/
abbrev genOf (i : Fin 6) : Genome Sym := toGenome (rep i)

/-- **Candidate-specific literal historical information feasibility.** Candidate
`i` admits a latent read-start set `T` whose induced read-string set satisfies
the literal §6.4 historical `I_s`, and that realizes the observed read string `r`
at one of its starts.  This is a predicate of the candidate and the read only; it
is not a function of the read alone and it is not an externally supplied
revelation. -/
def E (i : Fin 6) (r : Read) : Prop :=
  ∃ T : Finset (Fin 4),
    (∃ s ∈ T, (genOf i).window 3 s = r) ∧
      HistoricalInformationFeasibleLiteral (genOf i) 3 T

instance instDecidableE (i : Fin 6) (r : Read) : Decidable (E i r) := by
  unfold E
  infer_instance

instance : DecidableRel E := fun i r => instDecidableE i r

/-- The truth orbit `1` (`0001`) is literally feasible at the **non-saturated**
placement `{0,1,3}`: the reads at starts `0`, `1`, `3` give historical coverage,
the single maximal triple repeat is bridged, and read length `3` bridges the
length-`1` three-occurrence repeats. -/
theorem literalFeasible_nonsaturated :
    HistoricalInformationFeasibleLiteral (genOf 1) 3 ({0, 1, 3} : Finset (Fin 4)) := by
  decide

/-- The non-saturated witness `{0,1,3}` really is non-saturated: it omits a
position of the length-`4` circle. -/
theorem nonsaturated_card : ({0, 1, 3} : Finset (Fin 4)).card = 3 := by decide

/-- **The truth orbit satisfies the literal event at read `000`.** Start `0` of
`0001` spells `000`, and `{0,1,3}` is a literal historical placement. -/
theorem E_one_000 : E 1 (r3 0 0 0) :=
  ⟨({0, 1, 3} : Finset (Fin 4)), ⟨0, by decide, by decide⟩, literalFeasible_nonsaturated⟩

/-- **The all-zero orbit `0000` fails the literal event at read `000`.** Every
position is a match start, but the length-`2` three-occurrence repeat `00` cannot
be bridged by a length-`3` read (`bridgesCopy_length` forces `e + 2 ≤ L`, i.e.
`4 ≤ 3`), so no literal historical placement exists. -/
theorem E_zero_000 : ¬ E 0 (r3 0 0 0) := by decide

/-- Candidate `2` (`0011`) fails the literal event at read `000`. -/
theorem E_two_000 : ¬ E 2 (r3 0 0 0) := by decide

/-- Candidate `3` (`0101`) fails the literal event at read `000`. -/
theorem E_three_000 : ¬ E 3 (r3 0 0 0) := by decide

/-- Candidate `4` (`0111`) fails the literal event at read `000`. -/
theorem E_four_000 : ¬ E 4 (r3 0 0 0) := by decide

/-- Candidate `5` (`1111`) fails the literal event at read `000`. -/
theorem E_five_000 : ¬ E 5 (r3 0 0 0) := by decide

/-- **The literal event pins the truth orbit at read `000`.**  Exactly one of the
six candidates satisfies `E` at `000`, namely the truth orbit `1`. -/
theorem E_iff_at_000 (i : Fin 6) : E i (r3 0 0 0) ↔ i = 1 := by
  constructor
  · intro h
    fin_cases i
    · exact absurd h E_zero_000
    · rfl
    · exact absurd h E_two_000
    · exact absurd h E_three_000
    · exact absurd h E_four_000
    · exact absurd h E_five_000
  · rintro rfl; exact E_one_000

/-! ## Ordinary R-only maximum likelihood (prior- and `E`-free) -/

/-- Ordinary ML truth-maximality on the read model: `h` maximizes the exact
read-string likelihood at `r` (ties allowed). Neither the prior nor `E` enters. -/
def MLMax (h : Fin 6) (r : Read) : Prop := ∀ h' : Fin 6, p h' r ≤ p h r

/-! ## Separation (A ∧ ¬B): truth orbit `1`, observed read `000` -/

/-- At read `000` the wrong orbit `0` (`0000`) strictly beats the truth orbit `1`
(`0001`): `1 > 1/4`. -/
theorem sep_ml_strict : p 1 (r3 0 0 0) < p 0 (r3 0 0 0) := by
  rw [p_1_000, p_0_000]; norm_num

/-- The truth orbit `1` is not even an ordinary-ML maximizer at read `000`. -/
theorem sep_truth_not_ml : ¬ MLMax 1 (r3 0 0 0) := by
  intro h
  exact absurd (h 0) (not_le.mpr sep_ml_strict)

/-- The literal-event-conditioned predictive mass at read `000` is positive (the
truth orbit `1` alone contributes `1/6 · 1/4`). -/
theorem sep_hZ : 0 < predictiveMass prior p E (r3 0 0 0) := by
  have h1 : 0 < jointMass prior p E 1 (r3 0 0 0) := by
    rw [jointMass_pos_iff prior p E prior_nonneg (fun g r => p_nonneg g r)]
    exact ⟨prior_pos 1, by rw [p_1_000]; norm_num, E_one_000⟩
  unfold predictiveMass
  exact lt_of_lt_of_le h1
    (Finset.single_le_sum
      (fun h _ => jointMass_nonneg prior p E prior_nonneg (fun g r => p_nonneg g r) h (r3 0 0 0))
      (Finset.mem_univ 1))

/-- **Conditional recovery is certain (A).** Under the candidate-specific
literal historical event `E`, the conditional posterior on the true orbit is
exactly `1` — via the general #272 theorem `posteriorMass_eq_one_iff`. The only
candidate of positive prior and positive likelihood satisfying `E` at read `000`
is the truth orbit `1`. -/
theorem sep_posteriorMass_one :
    posteriorMass prior p E orbit (r3 0 0 0) (orbit 1) = 1 := by
  rw [posteriorMass_eq_one_iff prior p E orbit prior_nonneg
    (fun g r => p_nonneg g r) (r3 0 0 0) (orbit 1) sep_hZ]
  intro g _ _ hE
  have hg : g = 1 := (E_iff_at_000 g).mp hE
  rw [hg]

/-- The same certainty in the **excluded-competitor** form of #272: every
candidate of positive prior and positive likelihood outside the true orbit is
excluded by the literal event `E`. -/
theorem sep_posteriorMass_one_excluded :
    posteriorMass prior p E orbit (r3 0 0 0) (orbit 1) = 1 := by
  rw [posteriorMass_eq_one_iff_excluded prior p E orbit prior_nonneg
    (fun g r => p_nonneg g r) (r3 0 0 0) 1 sep_hZ]
  intro g _ _ hne hE
  exact hne (congrArg orbit ((E_iff_at_000 g).mp hE))

/-- The ordinary (no side information) posterior on the true orbit is NOT
certain at read `000`, because the wrong orbit `0` retains positive prior and
positive likelihood: the excluded-orbit boundary of #272 is not met. -/
theorem sep_ordinary_not_certain :
    posteriorMass prior p (fun _ _ => True) orbit (r3 0 0 0) (orbit 1) ≠ 1 := by
  intro h
  have hZ : 0 < predictiveMass prior p (fun _ _ => True) (r3 0 0 0) := by
    have h1 : 0 < jointMass prior p (fun _ _ => True) 1 (r3 0 0 0) := by
      rw [jointMass_pos_iff prior p (fun _ _ => True) prior_nonneg (fun g r => p_nonneg g r)]
      exact ⟨prior_pos 1, by rw [p_1_000]; norm_num, trivial⟩
    unfold predictiveMass
    exact lt_of_lt_of_le h1
      (Finset.single_le_sum
        (fun h _ => jointMass_nonneg prior p (fun _ _ => True) prior_nonneg (fun g r => p_nonneg g r) h (r3 0 0 0))
        (Finset.mem_univ 1))
  have hiff := (readOnly_posterior_eq_one_iff prior p orbit prior_nonneg
    (fun g r => p_nonneg g r) (r3 0 0 0) (orbit 1) hZ).mp h
  exact orbit_zero_ne_one (hiff 0 (prior_pos 0) (by rw [p_0_000]; norm_num))

/-- **Genome-level separation (A ∧ ¬B).** On the exact oriented read model with
the normalized orbit-class prior and the candidate-specific **literal** §6.4
information-feasibility event `E`: the conditional posterior on the true orbit is
`1`, ordinary R-only ML strictly prefers the wrong orbit `0`, and the ordinary
posterior on the truth is not certain. -/
theorem separation_genome :
    (∀ i : Fin 6, 0 ≤ prior i) ∧ (∑ i : Fin 6, prior i = 1) ∧
      (∀ i : Fin 6, ∑ w : Read, p i w = 1) ∧
      posteriorMass prior p E orbit (r3 0 0 0) (orbit 1) = 1 ∧
      p 1 (r3 0 0 0) < p 0 (r3 0 0 0) ∧ ¬ MLMax 1 (r3 0 0 0) ∧
      posteriorMass prior p (fun _ _ => True) orbit (r3 0 0 0) (orbit 1) ≠ 1 :=
  ⟨prior_nonneg, prior_sum_one, p_sum_one, sep_posteriorMass_one, sep_ml_strict,
    sep_truth_not_ml, sep_ordinary_not_certain⟩

/-! ## Converse (B ∧ ¬A): truth orbit `0`, observed read `000` -/

/-- At read `000` the truth orbit `0` (`0000`) strictly beats every other orbit:
`1 > 1/4 > 0`. -/
theorem conv_ml_strict (i : Fin 6) (hi : i ≠ 0) : p i (r3 0 0 0) < p 0 (r3 0 0 0) := by
  match i with
  | 0 => exact absurd rfl hi
  | 1 => rw [p_1_000, p_0_000]; norm_num
  | 2 => rw [p_2_000, p_0_000]; norm_num
  | 3 => rw [p_3_000, p_0_000]; norm_num
  | 4 => rw [p_4_000, p_0_000]; norm_num
  | 5 => rw [p_5_000, p_0_000]; norm_num

/-- Ordinary ML selects the truth orbit `0` at read `000`. -/
theorem conv_ml_max : MLMax 0 (r3 0 0 0) := by
  intro h'
  by_cases h : h' = 0
  · rw [h]
  · exact le_of_lt (conv_ml_strict h' h)

/-- The selection is UNIQUE: `0` is the only ordinary-ML maximizer at read `000`. -/
theorem conv_ml_unique : MLMax 0 (r3 0 0 0) ∧ ∀ h, MLMax h (r3 0 0 0) → h = 0 := by
  refine ⟨conv_ml_max, ?_⟩
  intro h hmax
  by_contra hne
  have hlt := conv_ml_strict h hne
  exact absurd (hmax 0) (not_le.mpr hlt)

/-- Even though ordinary ML uniquely selects the truth orbit `0`, the ordinary
posterior on the truth is NOT certain: the wrong orbit `1` retains positive prior
and positive likelihood at read `000`. -/
theorem conv_ordinary_not_certain :
    posteriorMass prior p (fun _ _ => True) orbit (r3 0 0 0) (orbit 0) ≠ 1 := by
  intro h
  have hZ : 0 < predictiveMass prior p (fun _ _ => True) (r3 0 0 0) := by
    have h1 : 0 < jointMass prior p (fun _ _ => True) 0 (r3 0 0 0) := by
      rw [jointMass_pos_iff prior p (fun _ _ => True) prior_nonneg (fun g r => p_nonneg g r)]
      exact ⟨prior_pos 0, by rw [p_0_000]; norm_num, trivial⟩
    unfold predictiveMass
    exact lt_of_lt_of_le h1
      (Finset.single_le_sum
        (fun h _ => jointMass_nonneg prior p (fun _ _ => True) prior_nonneg (fun g r => p_nonneg g r) h (r3 0 0 0))
        (Finset.mem_univ 0))
  have hiff := (readOnly_posterior_eq_one_iff prior p orbit prior_nonneg
    (fun g r => p_nonneg g r) (r3 0 0 0) (orbit 0) hZ).mp h
  exact orbit_zero_ne_one (hiff 1 (prior_pos 1) (by rw [p_1_000]; norm_num)).symm

/-- **Genome-level converse (B ∧ ¬A).** Ordinary ML uniquely selects the truth
orbit `0` at read `000`, yet the ordinary posterior on the truth is not
certain. -/
theorem converse_genome :
    MLMax 0 (r3 0 0 0) ∧ (∀ h, MLMax h (r3 0 0 0) → h = 0) ∧
      posteriorMass prior p (fun _ _ => True) orbit (r3 0 0 0) (orbit 0) ≠ 1 :=
  ⟨conv_ml_unique.1, conv_ml_unique.2, conv_ordinary_not_certain⟩

/-! ## The model axes, packaged

The adapter fixes the axes of issue #271 goal 1 and instantiates the separation
at read length `3` with the literal source event.  The remaining axis facts are
supplied by the merged modules named below rather than reproved here:

* reverse-complement collapse is a **different** observable (merged
  `W1W2RcOrientedRepresentation271`; this adapter quotients by rotation only);
* the exact single-read pmf is not the fixed-`N` product-binomial surrogate
  (merged `GenomeOrbitAdapter.ExactVsSurrogate.exact_ne_productBinomial`);
* MAP coincides with ML under the uniform orbit prior (merged
  `GenomeOrbitAdapter.uniform_orbit_prior_ML`), so the prior does not create the
  (A)-side collapse. -/

/-- **Model-axes packaging.**  The adapter is an oriented, exact, fixed-length
model on rotation-orbit classes with a normalized uniform prior and a normalized
per-candidate pmf; the literal §6.4 event `E` is model-internal and pins the
truth orbit at `000`; and the single-read literal event is attainable by a
non-saturated placement. -/
theorem model_axes :
    (∀ i : Fin 6, ∑ w : Read, p i w = 1) ∧
      (∀ i : Fin 6, 0 ≤ prior i) ∧ (∑ i : Fin 6, prior i = 1) ∧
      (∀ i : Fin 6, E i (r3 0 0 0) ↔ i = 1) ∧
      ({0, 1, 3} : Finset (Fin 4)).card = 3 :=
  ⟨p_sum_one, prior_nonneg, prior_sum_one, E_iff_at_000, nonsaturated_card⟩

/-! ## Kernel-checking boundary -/

#print axioms literalFeasible_nonsaturated
#print axioms E_one_000
#print axioms E_zero_000
#print axioms E_iff_at_000
#print axioms orbit_zero_ne_one
#print axioms sep_ml_strict
#print axioms sep_truth_not_ml
#print axioms sep_posteriorMass_one
#print axioms sep_posteriorMass_one_excluded
#print axioms sep_ordinary_not_certain
#print axioms separation_genome
#print axioms conv_ml_strict
#print axioms conv_ml_unique
#print axioms conv_ordinary_not_certain
#print axioms converse_genome
#print axioms model_axes

end AssemblyP1.ConditionalVsMLLiteralL3Adapter271
