import AssemblyP1.GenomeOrbitAdapter
import AssemblyP1.FiniteBayesianSideInformation
import AssemblyP1.SourceFaithfulIs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity

/-!
# Genome-level adapter for the conditional-Bayes vs ordinary-ML separation (#271)

**Status: Lean kernel-checked instantiation in the exact AssemblyP1 finite
circular read model, with a candidate-specific latent-start information-feasibility
predicate — not an externally supplied revelation.**

The abstract separation of `AssemblyP1/ConditionalVsOrdinaryMLSeparation.lean`
(#271) and the general orbit-class boundary
`AssemblyP1.FiniteBayesianSideInformation.posteriorMass_eq_one_iff` (#272) are
instantiated here on the concrete finite circular read model of
`AssemblyP1/GenomeOrbitAdapter.lean` (#269):

* candidate universe: three rotation-orbit classes of binary circular genomes of
  length `4` (`0001`, `0011`, `0101` up to rotation);
* observation: the oriented length-`2` read string `w : Fin 2 → Fin 2`;
* per-candidate observation model: the exact normalized read pmf
  `p_g(w) = orbitReadPmf g w = #{starts spelling w in g} / 4`, which is rotation
  invariant (`GenomeOrbitAdapter.readPmf_rotWord`) and hence well defined on
  rotation orbits;
* prior: the uniform prior `1/3` over the three orbit classes (NOT over raw
  spellings);
* promise: the candidate-specific latent-start information-feasibility predicate
  `E i w`, defined **inside** the model from the exact source predicate
  `SourceFaithfulIs.InformationFeasible` (the `I_s` of Shomorony et al. (2016),
  Eq. (1)): candidate `i` admits a latent read-start set `T` that is
  `I_s`-feasible and realizes the observed read string `w` at one of its starts.
  It is *not* a function of the read `w` alone (`E_not_dataOnly`), and it is
  *not* an externally supplied oracle: it is a function of the candidate and the
  read only.

The endpoints are the two-way separation, kernel-checked on this one shared
generative model:

* **separation (A ∧ ¬B).** With truth orbit `1` (`0011`) and observed read
  string `00`: conditioning on the latent-start feasibility event `E` gives
  conditional posterior `1` on the true orbit (`sep_posteriorMass_one`), while
  ordinary R-only ML strictly prefers the wrong orbit `0` (`0001`, `1/2 > 1/4`,
  `sep_ml_strict`), so the truth is not a maximizer (`sep_truth_not_ml`) and the
  ordinary posterior on the truth is not certain
  (`sep_ordinary_not_certain`).
* **converse (B ∧ ¬A).** With truth orbit `2` (`0101`) and observed read string
  `01`: ordinary ML *uniquely* selects the truth (`conv_ml_unique`), yet the
  ordinary posterior on the truth is not certain (`conv_ordinary_not_certain`).

The predicate `E` is the candidate-specific latent-start information-feasibility
predicate that the merged #271 handoff left open: it replaces the earlier
external support-revealing oracle `SupportEq t g`. It is built from the exact
source predicate `InformationFeasible`, so conditioning on `E(G, R)` is
conditioning on "the true genome admits an `I_s`-feasible placement explaining
the observed read", which is the source hypothesis, not an extra attributed
input. The model boundary is still recorded honestly (see
`docs/conditional-vs-ml-genome-adapter-271.md`): `E` is defined through the
chosen orbit representatives, `E` uses the source predicate at the representative
rather than descending it to orbits, and the read is a single observed string
rather than the full sampled read set, so this is a bounded finite witness rather
than the general source-level theorem.

No `sorry`/`admit`/`axiom`/`native_decide`; `#print axioms` is clean (only the
Mathlib foundations), audited in `AxiomAudit271.lean`.
-/

namespace AssemblyP1.ConditionalVsMLGenomeAdapter271

open AssemblyP1.GenomeOrbitAdapter
open AssemblyP1.FiniteBayesianSideInformation
open AssemblyP1.SourceFaithfulIs
open Finset BigOperators

/-- The binary symbol alphabet. -/
abbrev Sym : Type := Fin 2

/-- Oriented length-`2` read strings. -/
abbrev Read : Type := Fin 2 → Sym

/-- Circular binary genomes of length `4`. -/
abbrev Word : Type := ZMod 4 → Sym

/-- The circular word with the four listed symbols. -/
def g4 (a b c d : Sym) : Word
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c
  | _ => d

/-- The oriented length-`2` read string with the two listed symbols. -/
def r2 (a b : Sym) : Read
  | ⟨0, _⟩ => a
  | _ => b

/-- Representatives of the three candidate rotation-orbit classes:
`0 ↦ 0001`, `1 ↦ 0011`, `2 ↦ 0101`. -/
def rep : Fin 3 → Word
  | 0 => g4 0 0 0 1
  | 1 => g4 0 0 1 1
  | 2 => g4 0 1 0 1

/-- The candidate genome universe is the set of rotation-orbit classes of the
three representatives, embedded into the genuine orbit quotient. -/
def orbit : Fin 3 → Quotient (rotSetoid Sym 4) := fun i => Quotient.mk _ (rep i)

/-- The exact normalized per-candidate observation model over oriented read
strings: the rotation-orbit read pmf of `GenomeOrbitAdapter`. -/
noncomputable def p (i : Fin 3) (w : Read) : ℝ :=
  orbitReadPmf (G := 4) (L := 2) (orbit i) w

/-- The uniform prior over the three rotation-orbit classes. -/
noncomputable def prior (_ : Fin 3) : ℝ := 1 / 3

/-! ## The read model evaluates exactly -/

/-- The per-candidate observation model is the raw read pmf of the chosen orbit
representative (the descended pmf reduces on `Quotient.mk`). -/
theorem p_eq_readPmf (i : Fin 3) (w : Read) : p i w = readPmf (rep i) w := by
  unfold p orbit
  rfl

/-- The per-candidate observation model is nonnegative. -/
theorem p_nonneg (i : Fin 3) (w : Read) : 0 ≤ p i w := by
  rw [p_eq_readPmf]
  unfold readPmf
  positivity

/-- The per-candidate observation model is normalized: `∑_w p_g(w) = 1`. -/
theorem p_sum_one (i : Fin 3) : ∑ w : Read, p i w = 1 := by
  unfold p
  exact orbitReadPmf_sum_one (α := Sym) 4 2 (orbit i)

theorem prior_pos (i : Fin 3) : 0 < prior i := by norm_num [prior]

theorem prior_nonneg (i : Fin 3) : 0 ≤ prior i := le_of_lt (prior_pos i)

theorem prior_sum_one : ∑ i : Fin 3, prior i = 1 := by
  simp only [Fin.sum_univ_three, prior]
  norm_num

/-! ### Multiplicity and pmf table -/

theorem mult_rep0_00 : mult (rep 0) (r2 0 0) = 2 := by decide
theorem mult_rep0_01 : mult (rep 0) (r2 0 1) = 1 := by decide
theorem mult_rep0_10 : mult (rep 0) (r2 1 0) = 1 := by decide
theorem mult_rep0_11 : mult (rep 0) (r2 1 1) = 0 := by decide

theorem mult_rep1_00 : mult (rep 1) (r2 0 0) = 1 := by decide
theorem mult_rep1_01 : mult (rep 1) (r2 0 1) = 1 := by decide
theorem mult_rep1_10 : mult (rep 1) (r2 1 0) = 1 := by decide
theorem mult_rep1_11 : mult (rep 1) (r2 1 1) = 1 := by decide

theorem mult_rep2_00 : mult (rep 2) (r2 0 0) = 0 := by decide
theorem mult_rep2_01 : mult (rep 2) (r2 0 1) = 2 := by decide
theorem mult_rep2_10 : mult (rep 2) (r2 1 0) = 2 := by decide
theorem mult_rep2_11 : mult (rep 2) (r2 1 1) = 0 := by decide

theorem p_0_00 : p 0 (r2 0 0) = 1 / 2 := by
  rw [p_eq_readPmf]; unfold readPmf; rw [mult_rep0_00]; norm_num
theorem p_0_01 : p 0 (r2 0 1) = 1 / 4 := by
  rw [p_eq_readPmf]; unfold readPmf; rw [mult_rep0_01]; norm_num
theorem p_0_10 : p 0 (r2 1 0) = 1 / 4 := by
  rw [p_eq_readPmf]; unfold readPmf; rw [mult_rep0_10]; norm_num
theorem p_0_11 : p 0 (r2 1 1) = 0 := by
  rw [p_eq_readPmf]; unfold readPmf; rw [mult_rep0_11]; norm_num

theorem p_1_00 : p 1 (r2 0 0) = 1 / 4 := by
  rw [p_eq_readPmf]; unfold readPmf; rw [mult_rep1_00]; norm_num
theorem p_1_01 : p 1 (r2 0 1) = 1 / 4 := by
  rw [p_eq_readPmf]; unfold readPmf; rw [mult_rep1_01]; norm_num
theorem p_1_10 : p 1 (r2 1 0) = 1 / 4 := by
  rw [p_eq_readPmf]; unfold readPmf; rw [mult_rep1_10]; norm_num
theorem p_1_11 : p 1 (r2 1 1) = 1 / 4 := by
  rw [p_eq_readPmf]; unfold readPmf; rw [mult_rep1_11]; norm_num

theorem p_2_00 : p 2 (r2 0 0) = 0 := by
  rw [p_eq_readPmf]; unfold readPmf; rw [mult_rep2_00]; norm_num
theorem p_2_01 : p 2 (r2 0 1) = 1 / 2 := by
  rw [p_eq_readPmf]; unfold readPmf; rw [mult_rep2_01]; norm_num
theorem p_2_10 : p 2 (r2 1 0) = 1 / 2 := by
  rw [p_eq_readPmf]; unfold readPmf; rw [mult_rep2_10]; norm_num
theorem p_2_11 : p 2 (r2 1 1) = 0 := by
  rw [p_eq_readPmf]; unfold readPmf; rw [mult_rep2_11]; norm_num

/-! ## The three candidates are distinct rotation-orbit classes

Distinctness is proved through the read pmf, which is rotation invariant
(`GenomeOrbitAdapter.readPmf_rotWord`): equal orbits would have equal read
pmfs, but the three pmfs differ. -/

theorem orbit_zero_ne_one : orbit 0 ≠ orbit 1 := by
  intro h
  have hp : p 0 (r2 1 1) = p 1 (r2 1 1) := by unfold p; rw [h]
  rw [p_0_11, p_1_11] at hp
  norm_num at hp

theorem orbit_zero_ne_two : orbit 0 ≠ orbit 2 := by
  intro h
  have hp : p 0 (r2 0 0) = p 2 (r2 0 0) := by unfold p; rw [h]
  rw [p_0_00, p_2_00] at hp
  norm_num at hp

theorem orbit_one_ne_two : orbit 1 ≠ orbit 2 := by
  intro h
  have hp : p 1 (r2 0 1) = p 2 (r2 0 1) := by unfold p; rw [h]
  rw [p_1_01, p_2_01] at hp
  norm_num at hp

theorem orbit_injective : Function.Injective orbit := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
      | rfl
      | exact absurd hij orbit_zero_ne_one
      | exact absurd hij orbit_zero_ne_two
      | exact absurd hij orbit_one_ne_two
      | exact absurd hij (Ne.symm orbit_zero_ne_one)
      | exact absurd hij (Ne.symm orbit_zero_ne_two)
      | exact absurd hij (Ne.symm orbit_one_ne_two)

/-! ## Candidate-specific latent-start information feasibility `E`

`E i w` is defined **inside** the model, from the exact source predicate
`SourceFaithfulIs.InformationFeasible` (the `I_s` of Shomorony et al. (2016),
Eq. (1)): candidate `i` admits a latent read-start set `T` that is `I_s`-feasible
and that realizes the observed read string `w` at one of its starts. There is no
externally supplied truth-dependent oracle. -/

/-- The source-faithful circular genome of a `ZMod 4`-indexed word. -/
abbrev toGenome (g : Word) : Genome Sym :=
  ⟨4, by norm_num, fun d => g (d.val : ZMod 4)⟩

/-- Candidate `i`'s representative read as a source-faithful circular genome. -/
abbrev genOf (i : Fin 3) : Genome Sym := toGenome (rep i)

/-- **Candidate-specific latent-start information feasibility.** Candidate `i`
admits a latent read-start set `T` that is `I_s`-feasible and that realizes the
observed read string `r` at one of its starts. This is a predicate of the
candidate and the read only; it is not a function of the read alone
(`E_not_dataOnly`) and it is not an externally supplied revelation. -/
def E (i : Fin 3) (r : Read) : Prop :=
  ∃ T : Finset (Fin 4),
    (∃ s ∈ T, (genOf i).window 2 s = r) ∧
      InformationFeasible (genOf i) 2 T

instance instDecidableE (i : Fin 3) (r : Read) : Decidable (E i r) := by
  unfold E
  infer_instance

instance : DecidableRel E := fun i r => instDecidableE i r

/-- **Read length `2` makes bridging impossible for repeats of length `≥ 1`.**
A bridged copy of length `e` satisfies `e + 2 ≤ 2` (`bridgesCopy_length`), while a
repeat has `1 ≤ e`; hence an `I_s`-feasible placement has no triple repeat. -/
theorem informationFeasible_two_no_tripleRepeat {S : Genome Sym}
    {R : Finset (Fin S.len)} (h : InformationFeasible S 2 R)
    {e a b c : Fin S.len} (ht : S.IsTripleRepeat e.val a b c) : False := by
  obtain ⟨-, htri, -⟩ := h
  have hb := htri e a b c ht
  have hle := bridgesCopy_length hb.1
  have h1 : 1 ≤ e.val := ht.1
  omega

/-- Candidate `1` (`0011`) is information-feasible: the reads at starts `{0,2}`
cover the circle, and (read length `2`) there is no triple repeat. -/
theorem feasible_genOf_one :
    InformationFeasible (genOf 1) 2 ({0, 2} : Finset (Fin 4)) := by
  decide

/-- The truth orbit `1` satisfies the feasibility event at read `00`: start `0`
of `0011` spells `00`, and `{0,2}` is a feasible placement. -/
theorem E_one_00 : E 1 (r2 0 0) :=
  ⟨({0, 2} : Finset (Fin 4)), ⟨0, by decide, by decide⟩, feasible_genOf_one⟩

/-- Candidate `0` (`0001`) is **not** information-feasible at any placement: it
has the triple repeat of length `1` at starts `{0,1,2}`, which read length `2`
cannot bridge. -/
theorem E_zero_00 : ¬ E 0 (r2 0 0) := by
  rintro ⟨T, -, hfeas⟩
  exact informationFeasible_two_no_tripleRepeat (S := genOf 0) (R := T) hfeas
    (e := ⟨1, by norm_num⟩) (a := 0) (b := 1) (c := 2) (by decide)

/-- Candidate `2` (`0101`) never spells the read `00` (its windows are only `01`
and `10`), so it is infeasible for the observed read `00`. -/
theorem no_window_two_00 (s : Fin 4) : (genOf 2).window 2 s ≠ r2 0 0 := by
  fin_cases s <;> decide

theorem E_two_00 : ¬ E 2 (r2 0 0) := by
  rintro ⟨T, ⟨s, -, hs⟩, -⟩
  exact no_window_two_00 s hs

/-- `E` is not a function of the read alone: at the SAME read `00` it holds for
candidate `1` and fails for candidate `0`. Hence it cannot be inferred from `R`. -/
def DataOnly (E : Fin 3 → Read → Prop) : Prop :=
  ∃ f : Read → Prop, ∀ i r, E i r ↔ f r

theorem E_not_dataOnly : ¬ DataOnly E := by
  rintro ⟨f, hf⟩
  have h1 : E 1 (r2 0 0) := E_one_00
  have h0 : ¬ E 0 (r2 0 0) := E_zero_00
  rw [hf 1 (r2 0 0)] at h1
  rw [hf 0 (r2 0 0)] at h0
  exact h0 h1

/-! ## Ordinary R-only maximum likelihood (prior- and `E`-free) -/

/-- Ordinary ML truth-maximality on the read model: `h` maximizes the exact
read-string likelihood at `r` (ties allowed). Neither the prior nor `E` enters. -/
def MLMax (h : Fin 3) (r : Read) : Prop := ∀ h' : Fin 3, p h' r ≤ p h r

/-! ## Separation (A ∧ ¬B): truth orbit `1`, observed read `00` -/

/-- At read `00` the wrong orbit `0` (`0001`) strictly beats the truth orbit `1`
(`0011`): `1/2 > 1/4`. -/
theorem sep_ml_strict : p 1 (r2 0 0) < p 0 (r2 0 0) := by
  rw [p_1_00, p_0_00]; norm_num

/-- The truth orbit `1` is not even an ordinary-ML maximizer at read `00`. -/
theorem sep_truth_not_ml : ¬ MLMax 1 (r2 0 0) := by
  intro h
  exact absurd (h 0) (not_le.mpr sep_ml_strict)

/-- The feasibility-conditioned predictive mass at read `00` is positive (the
truth orbit `1` alone contributes `1/3 · 1/4`). -/
theorem sep_hZ : 0 < predictiveMass prior p E (r2 0 0) := by
  have h1 : 0 < jointMass prior p E 1 (r2 0 0) := by
    rw [jointMass_pos_iff prior p E prior_nonneg (fun g r => p_nonneg g r)]
    exact ⟨prior_pos 1, by rw [p_1_00]; norm_num, E_one_00⟩
  unfold predictiveMass
  exact lt_of_lt_of_le h1
    (Finset.single_le_sum
      (fun h _ => jointMass_nonneg prior p E prior_nonneg (fun g r => p_nonneg g r) h (r2 0 0))
      (Finset.mem_univ 1))

/-- **Conditional recovery is certain (A).** Under the candidate-specific
latent-start feasibility event `E`, the conditional posterior on the true orbit
is exactly `1` — via the general #272 theorem `posteriorMass_eq_one_iff`. The
only candidate of positive prior and positive likelihood satisfying `E` at read
`00` is the truth orbit `1`. -/
theorem sep_posteriorMass_one :
    posteriorMass prior p E orbit (r2 0 0) (orbit 1) = 1 := by
  rw [posteriorMass_eq_one_iff prior p E orbit prior_nonneg
    (fun g r => p_nonneg g r) (r2 0 0) (orbit 1) sep_hZ]
  intro g _ _ hE
  fin_cases g
  · exact absurd hE E_zero_00
  · rfl
  · exact absurd hE E_two_00

/-- The same certainty in the **excluded-competitor** form of #272: every
candidate of positive prior and positive likelihood outside the true orbit is
excluded by the latent-start feasibility event `E`. This is the literal "`E`
excludes every other orbit that `R` alone leaves possible" boundary. -/
theorem sep_posteriorMass_one_excluded :
    posteriorMass prior p E orbit (r2 0 0) (orbit 1) = 1 := by
  rw [posteriorMass_eq_one_iff_excluded prior p E orbit prior_nonneg
    (fun g r => p_nonneg g r) (r2 0 0) 1 sep_hZ]
  intro g _ _ hne hE
  fin_cases g
  · exact absurd hE E_zero_00
  · exact absurd rfl hne
  · exact absurd hE E_two_00

/-- The ordinary (no side information) posterior on the true orbit is NOT
certain at read `00`, because the wrong orbit `0` retains positive prior and
positive likelihood: the excluded-orbit boundary of #272 is not met. -/
theorem sep_ordinary_not_certain :
    posteriorMass prior p (fun _ _ => True) orbit (r2 0 0) (orbit 1) ≠ 1 := by
  intro h
  have hZ : 0 < predictiveMass prior p (fun _ _ => True) (r2 0 0) := by
    have h1 : 0 < jointMass prior p (fun _ _ => True) 1 (r2 0 0) := by
      rw [jointMass_pos_iff prior p (fun _ _ => True) prior_nonneg (fun g r => p_nonneg g r)]
      exact ⟨prior_pos 1, by rw [p_1_00]; norm_num, trivial⟩
    unfold predictiveMass
    exact lt_of_lt_of_le h1
      (Finset.single_le_sum
        (fun h _ => jointMass_nonneg prior p (fun _ _ => True) prior_nonneg (fun g r => p_nonneg g r) h (r2 0 0))
        (Finset.mem_univ 1))
  have hiff := (readOnly_posterior_eq_one_iff prior p orbit prior_nonneg
    (fun g r => p_nonneg g r) (r2 0 0) (orbit 1) hZ).mp h
  exact orbit_zero_ne_one (hiff 0 (prior_pos 0) (by rw [p_0_00]; norm_num))

/-- **Genome-level separation (A ∧ ¬B).** On the exact read model with the
normalized orbit-class prior and the candidate-specific latent-start
information-feasibility event `E`: the conditional posterior on the true orbit is
`1`, ordinary R-only ML strictly prefers the wrong orbit `0`, and the ordinary
posterior on the truth is not certain. -/
theorem separation_genome :
    (∀ i : Fin 3, 0 ≤ prior i) ∧ (∑ i : Fin 3, prior i = 1) ∧
      (∀ i : Fin 3, ∑ w : Read, p i w = 1) ∧
      posteriorMass prior p E orbit (r2 0 0) (orbit 1) = 1 ∧
      p 1 (r2 0 0) < p 0 (r2 0 0) ∧ ¬ MLMax 1 (r2 0 0) ∧
      posteriorMass prior p (fun _ _ => True) orbit (r2 0 0) (orbit 1) ≠ 1 :=
  ⟨prior_nonneg, prior_sum_one, p_sum_one, sep_posteriorMass_one, sep_ml_strict,
    sep_truth_not_ml, sep_ordinary_not_certain⟩

/-! ## Converse (B ∧ ¬A): truth orbit `2`, observed read `01` -/

/-- At read `01` the truth orbit `2` (`0101`) strictly beats every other orbit:
`1/2 > 1/4`. -/
theorem conv_ml_strict (i : Fin 3) (hi : i ≠ 2) : p i (r2 0 1) < p 2 (r2 0 1) := by
  match i with
  | 0 => rw [p_0_01, p_2_01]; norm_num
  | 1 => rw [p_1_01, p_2_01]; norm_num
  | 2 => exact absurd rfl hi

/-- Ordinary ML selects the truth orbit `2` at read `01`. -/
theorem conv_ml_max : MLMax 2 (r2 0 1) := by
  intro h'
  by_cases h : h' = 2
  · rw [h]
  · exact le_of_lt (conv_ml_strict h' h)

/-- The selection is UNIQUE: `2` is the only ordinary-ML maximizer at read
`01`. -/
theorem conv_ml_unique : MLMax 2 (r2 0 1) ∧ ∀ h, MLMax h (r2 0 1) → h = 2 := by
  refine ⟨conv_ml_max, ?_⟩
  intro h hmax
  by_contra hne
  have hlt := conv_ml_strict h hne
  exact absurd (hmax 2) (not_le.mpr hlt)

/-- Even though ordinary ML uniquely selects the truth orbit `2`, the ordinary
posterior on the truth is NOT certain: the wrong orbit `1` retains positive
prior and positive likelihood at read `01`. -/
theorem conv_ordinary_not_certain :
    posteriorMass prior p (fun _ _ => True) orbit (r2 0 1) (orbit 2) ≠ 1 := by
  intro h
  have hZ : 0 < predictiveMass prior p (fun _ _ => True) (r2 0 1) := by
    have h1 : 0 < jointMass prior p (fun _ _ => True) 2 (r2 0 1) := by
      rw [jointMass_pos_iff prior p (fun _ _ => True) prior_nonneg (fun g r => p_nonneg g r)]
      exact ⟨prior_pos 2, by rw [p_2_01]; norm_num, trivial⟩
    unfold predictiveMass
    exact lt_of_lt_of_le h1
      (Finset.single_le_sum
        (fun h _ => jointMass_nonneg prior p (fun _ _ => True) prior_nonneg (fun g r => p_nonneg g r) h (r2 0 1))
        (Finset.mem_univ 2))
  have hiff := (readOnly_posterior_eq_one_iff prior p orbit prior_nonneg
    (fun g r => p_nonneg g r) (r2 0 1) (orbit 2) hZ).mp h
  exact orbit_one_ne_two (hiff 1 (prior_pos 1) (by rw [p_1_01]; norm_num))

/-- **Genome-level converse (B ∧ ¬A).** Ordinary ML uniquely selects the truth
orbit `2` at read `01`, yet the ordinary posterior on the truth is not
certain. -/
theorem converse_genome :
    MLMax 2 (r2 0 1) ∧ (∀ h, MLMax h (r2 0 1) → h = 2) ∧
      posteriorMass prior p (fun _ _ => True) orbit (r2 0 1) (orbit 2) ≠ 1 :=
  ⟨conv_ml_unique.1, conv_ml_unique.2, conv_ordinary_not_certain⟩

/-! ## The ordinary posterior values (candidate-index form)

`postCandidate` is the posterior on the candidate INDEX (each candidate is a
distinct orbit class, `orbit_injective`), so it is the ordinary posterior on the
orbit class. It is used only to record the exact numeric boundary values; the
kernel-checked certainty statements above go through the #272 orbit posterior. -/

noncomputable def postCandidate (t : Fin 3) (r : Read) : ℝ :=
  prior t * p t r / ∑ g : Fin 3, prior g * p g r

/-- Ordinary posterior on the truth at read `00` is `1/3`, not `1`. -/
theorem postCandidate_sep : postCandidate 1 (r2 0 0) = 1 / 3 := by
  unfold postCandidate
  simp only [Fin.sum_univ_three, prior, p_0_00, p_1_00, p_2_00]
  norm_num

/-- Ordinary posterior on the truth at read `01` is `1/2`, not `1`. -/
theorem postCandidate_conv : postCandidate 2 (r2 0 1) = 1 / 2 := by
  unfold postCandidate
  simp only [Fin.sum_univ_three, prior, p_0_01, p_1_01, p_2_01]
  norm_num

/-! ## MAP = ML under the uniform orbit prior (reuse of #269)

The read-model joint mass and a concrete instantiation of #269's
`AssemblyP1.GenomeOrbitAdapter.PosteriorMAP.posterior_argmax_iff`. Under the
uniform orbit prior the joint is the positive constant `1/3` times the
likelihood, so the posterior (MAP) ordering coincides with the ordinary ML
ordering — the prior moves neither here. This is why the separation's (A)-side
needs the promise `E`, not just a prior. -/

/-- The read-model joint mass `J i r = π i · p_i(r)`. -/
noncomputable def jointMassRead (i : Fin 3) (r : Read) : ℝ := prior i * p i r

/-- **MAP = ML under the uniform orbit prior.** Instantiating #269
`PosteriorMAP.posterior_argmax_iff` on the read-model joint, posterior ordering
coincides with joint-mass ordering; since the joint is `1/3 · p`, that ordering
is the ordinary ML ordering. -/
theorem map_ml_agree_uniform (r : Read)
    (hZ : 0 < PosteriorMAP.predictiveMass jointMassRead r) (θ : Fin 3) :
    (PosteriorMAP.posterior jointMassRead r (ne_of_gt hZ) θ ≤
        PosteriorMAP.posterior jointMassRead r (ne_of_gt hZ)
          (AssemblyP1.FiniteBayesDecision.chooseMAP jointMassRead r)) ↔
      p θ r ≤ p (AssemblyP1.FiniteBayesDecision.chooseMAP jointMassRead r) r := by
  rw [PosteriorMAP.posterior_argmax_iff jointMassRead r hZ θ]
  unfold jointMassRead prior
  have hpos : (0 : ℝ) < 1 / 3 := by norm_num
  constructor
  · intro h
    exact le_of_mul_le_mul_left h hpos
  · intro h
    exact mul_le_mul_of_nonneg_left h (le_of_lt hpos)

end AssemblyP1.ConditionalVsMLGenomeAdapter271
