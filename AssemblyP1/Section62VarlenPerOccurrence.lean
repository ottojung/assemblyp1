import Mathlib
import AssemblyP1.Section62BridgingCounterexample

/-!
# Audit of the variable-length, per-occurrence, bidirected §6.2 witness (issue #213)

This module is the issue-#213 audit certificate for the finite Medvedev–Brudno
(2009) §6.2 witness `AAATT → AAAATT` recorded in
`docs/bridging-se62-flow-ml-counterexample.md` and kernel-checked in
`AssemblyP1.Section62BridgingCounterexample`.  It re-uses that module's
instance, its literal §6.2 bidirected-flow feasibility clauses and its literal
§6.1 objective, and adds the four things the issue-#213 audit asks for that the
merged module does not state:

1. **The §6.1 domain.** MB09 §6.1 bounds every candidate multiplicity by
   `0 ≤ d_i ≤ N`, with the external known genome size `N = 5`.  Both spectra of
   the witness are checked to lie in it.
2. **The lift from the spelled circuit to the flow universe.** `FlowThroughput`
   quantifies over *all* feasible §6.2 flows on the read-overlap graph of the
   observed read molecules, not over spelled candidates, and both throughput
   vectors are members.
3. **The two admissibility readings, kept apart.** The source's §6.2 rule is the
   per-vertex lower bound `1`; the per-occurrence strengthening `x ≤ d` is
   strictly stronger and is *not* the §6.2 definition.  Both hold here, so this
   refutation does not depend on which rule is used — which is what makes the
   *variable-length per-occurrence* cell a genuine negative result.
4. **The placement of the witness inside the objective domain.** Over the
   *whole* §6.1 domain the competitor's throughput vector is the objective's
   unique maximizer, so the refutation is not an artifact of a restricted
   candidate search.

The module also records, kernel-checked, the boundary of the witness: the
competitor's spectrum sums to `6 ≠ 5 = N`, so this pair does not reach the
same-length cell.  Nothing here decides which Medvedev–Brudno object the
Shomorony et al. (2016) sentence denotes, nor the single-strand reading, nor the
same-length per-occurrence case.
-/

namespace AssemblyP1.Section62VarlenPerOccurrence

open AssemblyP1.Section62BridgingCounterexample
open AssemblyP1.Section62Flow

/-! ## The §6.1 domain and the §6.2 flow universe -/

/-- The §6.1 domain of the literal product-of-binomial-marginals objective: the
external genome size is `N = 5` and MB09 §6.1 requires `0 ≤ d_i ≤ N`. -/
def Domain (d : Fin 8 → Nat) : Prop :=
  ∀ c, d c ≤ 5

/-- A throughput vector belongs to the **§6.2 flow universe** when some feasible
§6.2 bidirected flow on the read-overlap graph of the observed read molecules
realizes it.  This quantifies over all feasible flows, not only over spelled
candidates: a spelled circuit is the special case with no supersource/supersink
usage, which is why membership of a spelled circuit already gives membership
here, and why a refutation inside this universe is stronger than one stated only
for spelled molecules. -/
def FlowThroughput (d : Fin 8 → Nat) : Prop :=
  ∃ (f : BdFlow Base Strand3) (t : SuperTerminals Strand3),
    Feasible62 Base Strand3 rep3 readVerts graph f t (fun w => d (repCode w))

/-! ## The instance is in the domain and in the flow universe -/

/-- The truth's spectrum satisfies the §6.1 domain bound `d_i ≤ N = 5`. -/
theorem dS_domain : Domain dS := by
  unfold Domain dS spec5 window5 cyc5 cls code rc bitA comp truth
  decide

/-- The competitor's spectrum satisfies the §6.1 domain bound `d_i ≤ N = 5`. -/
theorem dD_domain : Domain dD := by
  unfold Domain dD spec6 window6 cyc6 cls code rc bitA comp competitor
  decide

/-- The truth's throughput vector is realized by a feasible §6.2 bidirected flow
(its own spelled circuit) — the lift from the spelled circuit to the flow
universe. -/
theorem dS_flow_throughput : FlowThroughput dS := by
  refine ⟨truthCircuitFlow, noTerm, ?_⟩
  rw [graph_eq]
  exact truth_feasible62

/-- The competitor's throughput vector is realized by a feasible §6.2 bidirected
flow. -/
theorem dD_flow_throughput : FlowThroughput dD := by
  refine ⟨competitorCircuitFlow, noTerm, ?_⟩
  rw [graph_eq]
  exact competitor_feasible62

/-! ## The two admissibility readings, kept apart -/

/-- The source's §6.2 rule, at the sequence level: every observed read molecule
occurs at least once (the vertex lower bound `1` read through Observation 7).
This is the **source** reading. -/
def PerVertexAdmissible (d : Fin 8 → Nat) : Prop :=
  ∀ v ∈ readVerts, 1 ≤ d (repCode v)

/-- The strictly stronger per-occurrence strengthening: every observed read
molecule occurs in the candidate at least as often as it was observed.  This is
**not** the MB09 §6.2 definition; it is an extra assumption about the candidate
class. -/
def PerOccurrenceAdmissible (d : Fin 8 → Nat) : Prop :=
  ∀ c, obs c ≤ d c

/-- The truth is admissible under the source per-vertex rule. -/
theorem truth_per_vertex : PerVertexAdmissible dS := by
  intro v hv
  have h1 := truth_vertex_lower_bounds v hv
  have h2 := truth_throughput_is_spectrum v hv
  simpa [dS', PerVertexAdmissible] using h1.trans (by rw [h2]; rfl)

/-- The competitor is admissible under the source per-vertex rule. -/
theorem competitor_per_vertex : PerVertexAdmissible dD := by
  intro v hv
  have h1 := competitor_vertex_lower_bounds v hv
  have h2 := competitor_throughput_is_spectrum v hv
  simpa [dD', PerVertexAdmissible] using h1.trans (by rw [h2]; rfl)

/-- The truth is admissible under the strictly stronger per-occurrence rule
`d(w) ≥ x(w)`. -/
theorem truth_per_occurrence : PerOccurrenceAdmissible dS := fun c =>
  (truth_feasible : SeqSupportLB dS obs).2 c

/-- The competitor is admissible under the stronger per-occurrence rule. -/
theorem competitor_per_occurrence : PerOccurrenceAdmissible dD := fun c =>
  (competitor_feasible : SeqSupportLB dD obs).2 c

/-- Both rules are satisfied by the *same* vector, and the truth's vector has
genuine slack in the two classes that the reverse-complement collapse feeds.
This is why the variable-length refutation does not depend on which rule is
used. -/
theorem truth_rule_agreement :
    PerVertexAdmissible dS ∧ PerVertexAdmissible dD ∧
      PerOccurrenceAdmissible dS ∧ PerOccurrenceAdmissible dD ∧
      (obs 1 < dS 1 ∧ obs 4 < dS 4) :=
  ⟨truth_per_vertex, competitor_per_vertex, truth_per_occurrence,
    competitor_per_occurrence, by decide, by decide⟩

/-! ## The §6.1 objective: per-coordinate behaviour -/

/-- On an observed class the §6.1 marginal has the shape
`C(3,1) (d/5) (1 - d/5)²`. -/
theorem marginal_of_obs_one (d : Fin 8 → Nat) (c : Fin 8) (h : obs c = 1) :
    marginal obs d c = 3 * ((d c : ℚ) / 5) * (1 - (d c : ℚ) / 5) ^ 2 := by
  unfold marginal
  rw [h]
  norm_num

/-- On an unobserved class the §6.1 marginal is `(1 - d/5)³`, and it is `1`
exactly when that class is empty. -/
theorem marginal_of_obs_zero (d : Fin 8 → Nat) (c : Fin 8) (h : obs c = 0) :
    marginal obs d c = (1 - (d c : ℚ) / 5) ^ 3 := by
  unfold marginal
  rw [h]
  norm_num

/-- The competitor's count on an observed class is `2`. -/
theorem dD_of_obs_one (c : Fin 8) (h : obs c = 1) : dD c = 2 := by
  fin_cases c
  · exact dD_0
  · exact dD_1
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact dD_4
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- The observed count of a class of this instance is `0` or `1`. -/
theorem obs_zero_or_one (c : Fin 8) : obs c = 0 ∨ obs c = 1 := by
  fin_cases c <;> decide

/-- The competitor's count on an unobserved class is `0`. -/
theorem dD_of_obs_zero (c : Fin 8) (h : obs c = 0) : dD c = 0 := by
  fin_cases c
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · have h32 : (2 : Fin 8) ∉ relevant := by decide
    exact (competitor_zero_off 2 h32).2
  · have h33 : (3 : Fin 8) ∉ relevant := by decide
    exact (competitor_zero_off 3 h33).2
  · exact absurd h (by decide)
  · have h35 : (5 : Fin 8) ∉ relevant := by decide
    exact (competitor_zero_off 5 h35).2
  · have h36 : (6 : Fin 8) ∉ relevant := by decide
    exact (competitor_zero_off 6 h36).2
  · have h37 : (7 : Fin 8) ∉ relevant := by decide
    exact (competitor_zero_off 7 h37).2

/-- The §6.1 marginal of an observed class is bounded by its value at `d = 2`
throughout the domain. -/
theorem marginal_one_le_54 (v : ℕ) (hv : v ≤ 5) :
    3 * (((v : ℕ) : ℚ) / 5) * (1 - ((v : ℕ) : ℚ) / 5) ^ 2 ≤
      3 * (((2 : ℕ) : ℚ) / 5) * (1 - ((2 : ℕ) : ℚ) / 5) ^ 2 := by
  interval_cases v <;> norm_num

/-- The bound is strict except at `d = 2`. -/
theorem marginal_one_lt_54 (v : ℕ) (hv : v ≤ 5) (hne : v ≠ 2) :
    3 * (((v : ℕ) : ℚ) / 5) * (1 - ((v : ℕ) : ℚ) / 5) ^ 2 <
      3 * (((2 : ℕ) : ℚ) / 5) * (1 - ((2 : ℕ) : ℚ) / 5) ^ 2 := by
  interval_cases v <;> first | (exfalso; omega) | norm_num

/-- The factor of an unobserved class is at most `1` throughout the domain. -/
theorem marginal_zero_le_one (v : ℕ) (hv : v ≤ 5) :
    ((1 - ((v : ℕ) : ℚ) / 5) ^ 3 : ℚ) ≤ ((1 - ((0 : ℕ) : ℚ) / 5) ^ 3 : ℚ) := by
  interval_cases v <;> norm_num

/-- The factor of an unobserved class is strictly below `1` unless the class is
empty.  (`interval_cases` uses the lower bound `1 ≤ v` in the context, so the
case `v = 0` is not generated.) -/
theorem marginal_zero_lt_one (v : ℕ) (hv : 1 ≤ v) (h5 : v ≤ 5) :
    ((1 - ((v : ℕ) : ℚ) / 5) ^ 3 : ℚ) < ((1 - ((0 : ℕ) : ℚ) / 5) ^ 3 : ℚ) := by
  interval_cases v <;> norm_num

/-- Nonnegativity of the marginal inside the domain, needed for the product
inequalities. -/
theorem marginal_nonneg_of_domain (d : Fin 8 → Nat) (c : Fin 8) (hd : d c ≤ 5) :
    0 ≤ marginal obs d c := by
  have h1 : (0 : ℚ) ≤ (d c : ℚ) / 5 := by positivity
  have h2 : (0 : ℚ) ≤ 1 - (d c : ℚ) / 5 := by
    have hd' : (d c : ℚ) / 5 ≤ 1 := by
      rw [div_le_one (by norm_num : (0 : ℚ) < 5)]
      simpa using (by exact_mod_cast hd : (d c : ℚ) ≤ 5)
    linarith
  have h3 : (0 : ℚ) ≤ (Nat.choose 3 (obs c) : ℚ) := Nat.cast_nonneg _
  unfold marginal
  positivity

/-- **The coordinate bound.** For every candidate `d` inside the §6.1 domain and
every molecule class, the §6.1 marginal of `d` is at most the marginal of the
competitor's throughput vector `dD`. -/
theorem marginal_le_marginal_dD (d : Fin 8 → Nat) (c : Fin 8) (hd : d c ≤ 5) :
    marginal obs d c ≤ marginal obs dD c := by
  by_cases h : obs c = 1
  · rw [marginal_of_obs_one d c h, marginal_of_obs_one dD c h, dD_of_obs_one c h]
    exact marginal_one_le_54 _ hd
  · have hx : obs c = 0 := by
      rcases obs_zero_or_one c with h0 | h1
      · exact h0
      · exact absurd h1 h
    rw [marginal_of_obs_zero d c hx, marginal_of_obs_zero dD c hx, dD_of_obs_zero c hx]
    exact marginal_zero_le_one _ hd

/-- **The coordinate strictness.** Where the two spectra disagree, the
competitor's marginal is strictly larger. -/
theorem marginal_lt_marginal_dD (d : Fin 8 → Nat) (c : Fin 8) (hd : d c ≤ 5)
    (hne : d c ≠ dD c) : marginal obs d c < marginal obs dD c := by
  by_cases h : obs c = 1
  · have hne2 : d c ≠ 2 := fun hh => hne (by rw [hh, dD_of_obs_one c h])
    rw [marginal_of_obs_one d c h, marginal_of_obs_one dD c h, dD_of_obs_one c h]
    exact marginal_one_lt_54 _ hd hne2
  · have hx : obs c = 0 := by
      rcases obs_zero_or_one c with h0 | h1
      · exact h0
      · exact absurd h1 h
    have hdD : dD c = 0 := dD_of_obs_zero c hx
    have hd0 : 1 ≤ d c := by
      rcases Nat.eq_zero_or_pos (d c) with h0 | h0
      · exact absurd (by rw [h0, hdD]) hne
      · exact h0
    rw [marginal_of_obs_zero d c hx, marginal_of_obs_zero dD c hx, hdD]
    exact marginal_zero_lt_one _ hd0 hd

/-- **Global optimality.** Over the *entire* §6.1 domain, the competitor's
throughput vector maximizes the literal product-of-binomial-marginals objective.
So the refutation below is not an artifact of a restricted candidate search: no
throughput vector inside the domain — spelled circuit or not, longer or shorter
than the truth — is more likely than the competitor's. -/
theorem lik_le_likD_of_domain (d : Fin 8 → Nat) (hd : Domain d) :
    lik obs d ≤ lik obs dD := by
  unfold lik
  exact Finset.prod_le_prod₀ (fun c _ => marginal_nonneg_of_domain d c (hd c))
    fun c _ => marginal_le_marginal_dD d c (hd c)

/-- **Uniqueness of the optimizer.** The only throughput vector inside the §6.1
domain attaining that maximum is the competitor's. -/
theorem lik_lt_likD_of_ne (d : Fin 8 → Nat) (hd : Domain d) (hne : d ≠ dD) :
    lik obs d < lik obs dD := by
  by_cases hz : ∃ c : Fin 8, marginal obs d c = 0
  · obtain ⟨c, hc⟩ := hz
    have h0 : lik obs d = 0 := by
      unfold lik
      exact Finset.prod_eq_zero (Finset.mem_univ c) hc
    rw [h0]
    rw [lik_competitor]
    norm_num
  · push Not at hz
    obtain ⟨c, hc⟩ := Function.ne_iff.mp hne
    have hpos : ∀ i : Fin 8, 0 < marginal obs d i :=
      fun i => lt_of_le_of_ne (marginal_nonneg_of_domain d i (hd i)) (hz i).symm
    have hle : ∀ i : Fin 8, marginal obs d i ≤ marginal obs dD i :=
      fun i => marginal_le_marginal_dD d i (hd i)
    have hstrict : marginal obs d c < marginal obs dD c :=
      marginal_lt_marginal_dD d c (hd c) hc
    unfold lik
    exact Finset.prod_lt_prod₀ (fun i _ => hpos i) (fun i _ => hle i)
      ⟨c, Finset.mem_univ c, hstrict⟩

/-- The refuted statement, in the negative universal form: it is *not* the case
that every §6.2-feasible throughput vector inside the domain is at most as
likely as the truth's. -/
theorem not_all_feasible_throughputs_le_truth :
    ¬ ∀ d, FlowThroughput d → Domain d → lik obs d ≤ lik obs dS := by
  intro h
  exact absurd (h dD dD_flow_throughput dD_domain)
    (not_le.mpr competitor_strictly_better)

/-- The refutation, in the existential witness form: a feasible §6.2 flow's
throughput vector is strictly more likely than the truth's. -/
theorem truth_not_maximizer_in_flow_universe :
    ∃ d, FlowThroughput d ∧ Domain d ∧ lik obs dS < lik obs d :=
  ⟨dD, dD_flow_throughput, dD_domain, competitor_strictly_better⟩

/-- The competitor's throughput vector is the unique maximizer of the §6.1
objective over the §6.1 domain, and it is realized by a feasible §6.2 flow while
being different from the truth's throughput vector. -/
theorem competitor_is_unique_optimizer :
    (∀ d, Domain d → lik obs d ≤ lik obs dD) ∧
      (∀ d, Domain d → lik obs d = lik obs dD → d = dD) ∧
      FlowThroughput dD ∧ dD ≠ dS := by
  refine ⟨fun d hd => lik_le_likD_of_domain d hd, ?_, dD_flow_throughput, ?_⟩
  · intro d hd he
    by_contra hne
    exact absurd he (ne_of_lt (lik_lt_likD_of_ne d hd hne))
  · intro h
    have heq : lik obs dD = lik obs dS := by rw [h]
    have hlt : lik obs dS < lik obs dD := competitor_strictly_better
    rw [heq] at hlt
    exact absurd hlt (lt_irrefl _)

/-! ## The boundary: what this witness does not reach -/

/-- The truth's spectrum sums to `5 = N = |S|`. -/
theorem sum_dS : ∑ c : Fin 8, dS c = 5 := by
  unfold dS spec5 window5 cyc5 cls code rc bitA comp truth
  decide

/-- The competitor's spectrum sums to `6 = |D|`. -/
theorem sum_dD : ∑ c : Fin 8, dD c = 6 := by
  unfold dD spec6 window6 cyc6 cls code rc bitA comp competitor
  decide

/-- **Fixed-length boundary.** The competitor's multiplicities sum to
`6 ≠ 5 = N`, so the competitor lies *outside* the length-constrained domain
`∑ d_i = N` that the same-length cell would impose; this witness therefore does
not transfer to the same-length case. -/
theorem competitor_outside_length_constrained_domain :
    ∑ c : Fin 8, dD c ≠ ∑ c : Fin 8, dS c := by
  rw [sum_dD, sum_dS]
  decide

/-- The truth, by contrast, sits on `∑ d_i = N`: a same-length refutation has to
move a unit of multiplicity *within* the sum-constrained slice, which is exactly
what the variable-length witness does not do. -/
theorem truth_on_length_constrained_domain : ∑ c : Fin 8, dS c = 5 := sum_dS

end AssemblyP1.Section62VarlenPerOccurrence
