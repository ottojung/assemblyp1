import Mathlib
import AssemblyP1.GenomeOrbitAdapter
import AssemblyP1.Section62FlowCountVectorAdapter

/-!
# Separation of the MB09 §6.2 feasible-flow objective from the source-faithful
circular-oriented-genome likelihood (Antonina #269)

This module lands the last open prose-only subclaim of Antonina #269: the
`AssemblyP1.GenomeOrbitAdapter` docstring asserts that the uniformly sampled
genomic-start read model is

> "not the MB09 fixed-`N` product-binomial pseudo-likelihood and **not the §6.2
> feasible-flow optimization**",

but that §6.2 non-equivalence was not a Lean theorem.  Here it is made a
kernel-checked separation theorem against the existing
`AssemblyP1.Section62FlowCountVectorAdapter`.

## What is separated, and how

The §6.2 flow objective of `AssemblyP1.Section62FlowCountVectorAdapter` is, by
that module's own reduction, a function of the *throughput vector* `Θ f =
throughputVec rep f edges`:

* `flow_objective_factors_throughput` (reuse of `throughputVec_congr`) — every
  score that factors through `Θ` is constant on `Θ`-fibres, so the §6.2
  objective cannot see anything the throughput vector does not record;
* `flow_maximality_is_throughput_property` (reuse of `maximal_image_iff`) — §6.2
  ML-maximality over the feasible-flow set is exactly maximality over the
  throughput image `Θ(feasibleFlowSet)`.

The §6.2 throughput of a *spelled* genome is its molecule-class visit vector
(`classCount`): the number of genomic starts whose read window lies in each
reverse-complement **molecule class** (`classCount_eq_visits`, which identifies
`classCount` with `Spelling.visits`, the vector the merged
`AssemblyP1.Section62SpelledFlowAdapter.throughput_eq_visits` turns into
`throughputVec` of the walk flow).  This is the §4.1 convention "each `k`-molecule
is represented only once".

The source-faithful circular-oriented-genome likelihood of
`AssemblyP1.GenomeOrbitAdapter` is the exact product `∏ᵢ p_S(xᵢ)` of the oriented
window pmf `p_S(w) = multiplicity_S(w) / |G|`.  It is **not** a function of the
§6.2 molecule-class visit vector: the two length-`2` circular genomes

```text
S0 = 00        (all windows spell the oriented word 00)
S1 = 11        (all windows spell the oriented word 11)
```

are reverse complements, hence have the *same* §6.2 molecule-class visit vector
(`classCount_S0_eq_S1`), but the oriented likelihood of the sample `(00)` is `1`
under `S0` and `0` under `S1` (`likelihood_S0`, `likelihood_S1`,
`likelihood_S0_ne_S1`).  Consequently no function of the §6.2 throughput can be
the exact oriented likelihood (`exactLikelihood_not_factors_throughput`), and
therefore no §6.2 feasible-flow objective can equal it.

## What is *not* claimed

* This is a statement about the *objective and candidate encoding*, not about the
  MB09 §6.1 product-binomial versus exact iid distinction (that is
  `AssemblyP1.GenomeOrbitAdapter.ExactVsSurrogate.exact_ne_productBinomial`) and
  not about the throughput-image / spelled-circuit classification of #261
  (`AssemblyP1.Section62SpelledFlowImageRefutation`).
* It does not decide whether a genome and its reverse complement are
  *information-theoretically* distinguishable by every sequencing experiment; it
  exhibits the exact oriented uniform-start read model as one in which they are.
* No `sorry`/`admit`/`axiom`/`native_decide`; the only axioms are Mathlib's
  `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace AssemblyP1.Section62FlowGenomeSeparation

open Finset BigOperators
open AssemblyP1.GenomeOrbitAdapter

/-! ## 1. The §6.2 flow objective is a function of the throughput vector

These are direct reuses of `AssemblyP1.Section62FlowCountVectorAdapter`, not
re-proofs. -/

/-- **Rigidity of the §6.2 objective.**  Any score that factors through the §6.2
throughput vector `Θ f = throughputVec rep f edges` takes the same value on two
flows with the same throughput.  This is
`AssemblyP1.Section62FlowCountVectorAdapter.throughputVec_congr`, restated as the
statement that the §6.2 objective can only depend on the throughput. -/
theorem flow_objective_factors_throughput {A W : Type} [DecidableEq W] {rep : W → W}
    {f g : AssemblyP1.Section62Flow.BdFlow A W}
    {edges : List (AssemblyP1.Section62Flow.BdEdge A W)}
    (h : AssemblyP1.Section62FlowCountVectorAdapter.throughputVec rep f edges
        = AssemblyP1.Section62FlowCountVectorAdapter.throughputVec rep g edges)
    (score : (W → ℕ) → ℚ) :
    score (AssemblyP1.Section62FlowCountVectorAdapter.throughputVec rep f edges)
      = score (AssemblyP1.Section62FlowCountVectorAdapter.throughputVec rep g edges) :=
  AssemblyP1.Section62FlowCountVectorAdapter.throughputVec_congr h score

/-- **§6.2 maximality is a throughput property.**  Reuse of
`AssemblyP1.Section62FlowCountVectorAdapter.maximal_image_iff`: ML-maximality of a
truth flow over the feasible-flow set is equivalent to maximality of its
throughput over the throughput image.  So the §6.2 feasible-flow objective is
completely determined by the map `Θ`. -/
theorem flow_maximality_is_throughput_property {A W : Type} [DecidableEq W]
    (rep : W → W) (edges : List (AssemblyP1.Section62Flow.BdEdge A W))
    (F : Set (AssemblyP1.Section62Flow.BdFlow A W)) (score : (W → ℕ) → ℚ)
    (f₀ : AssemblyP1.Section62Flow.BdFlow A W) :
    AssemblyP1.Section62FlowCountVectorAdapter.Maximal
        (Set.image (fun f => AssemblyP1.Section62FlowCountVectorAdapter.throughputVec rep f edges) F)
        score (AssemblyP1.Section62FlowCountVectorAdapter.throughputVec rep f₀ edges) ↔
      AssemblyP1.Section62FlowCountVectorAdapter.Maximal F
        (fun f => score (AssemblyP1.Section62FlowCountVectorAdapter.throughputVec rep f edges)) f₀ :=
  AssemblyP1.Section62FlowCountVectorAdapter.maximal_image_iff rep edges F score f₀

/-! ## 2. The concrete two-genome witness -/

/-- Binary read alphabet. -/
abbrev A2 := Fin 2

/-- Oriented length-`2` read word. -/
abbrev Word2 := Fin 2 → A2

/-- Watson–Crick complement on the binary alphabet `0 ↔ 1`. -/
def comp2 (a : A2) : A2 := if a = 0 then 1 else 0

/-- Reverse complement of an oriented length-`2` word. -/
def rc2 (w : Word2) : Word2 := fun i => comp2 (w (1 - i))

/-- The oriented word `00`. -/
def w00 : Word2 := fun _ => 0

/-- The oriented word `11`. -/
def w11 : Word2 := fun _ => 1

/-- Molecule-class representative (MB09 §4.1): the reverse complement of `11` is
`00`, every other length-`2` word is its own representative.  This makes
`rep2` the RC-orbit map `{00,11} ↦ 00`, `{01} ↦ 01`, `{10} ↦ 10`. -/
def rep2 (w : Word2) : Word2 := if w = w11 then w00 else w

/-- The all-zero circular genome `00` (length `2`). -/
def S0 : ZMod 2 → A2 := fun _ => 0

/-- The all-one circular genome `11` (length `2`), the reverse complement of
`S0`. -/
def S1 : ZMod 2 → A2 := fun _ => 1

/-- **The §6.2 molecule-class visit vector of a circular genome.**  The number of
genomic starts whose oriented read window has molecule-class representative `v`
(MB09 §4.1: one representative per molecule class).  This is the count vector the
§6.2 throughput records, stated in the same list-filter shape as
`AssemblyP1.Section62Flow.Spelling.visits` so that `classCount_eq_visits` is
definitional. -/
def classCount (S : ZMod 2 → A2) : Word2 → ℕ :=
  fun v => ((List.finRange 2).filter
    (fun i : Fin 2 => decide (rep2 (window (α := A2) (L := 2) S (i : ZMod 2)) = v))).length

/-- `classCount` is the molecule-class multiplicity count: the number of starts
whose window lies in the class equals the card of the filtered start set. -/
theorem classCount_eq_card (S : ZMod 2 → A2) (v : Word2) :
    classCount S v =
      (Finset.univ.filter (fun s : ZMod 2 => rep2 (window (α := A2) (L := 2) S s) = v)).card := by
  unfold classCount
  rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ (List.nodup_finRange 2))]
  rw [← List.filter_toFinset]
  rw [List.toFinset_finRange]
  rfl

/-- The molecule-class multiplicity sum equals the filtered-start card: summing
the oriented window multiplicities over a class counts exactly the starts whose
window lies in that class. -/
theorem sumform_eq_card (S : ZMod 2 → A2) (v : Word2) :
    (∑ w : Word2, if rep2 w = v then mult (α := A2) (G := 2) (L := 2) S w else 0) =
      (Finset.univ.filter (fun s : ZMod 2 => rep2 (window (α := A2) (L := 2) S s) = v)).card := by
  have h : (∑ w : Word2, if rep2 w = v then mult (α := A2) (G := 2) (L := 2) S w else 0)
      = ∑ s : ZMod 2, (if rep2 (window (α := A2) (L := 2) S s) = v then 1 else 0) := by
    calc (∑ w : Word2, if rep2 w = v then mult (α := A2) (G := 2) (L := 2) S w else 0)
        = ∑ w : Word2, ∑ s : ZMod 2,
            (if rep2 w = v then (if window (α := A2) (L := 2) S s = w then 1 else 0) else 0) := by
          apply Finset.sum_congr rfl
          intro w _
          rw [mult_eq_sum]
          by_cases h : rep2 w = v <;> simp [h]
      _ = ∑ s : ZMod 2, ∑ w : Word2,
            (if rep2 w = v then (if window (α := A2) (L := 2) S s = w then 1 else 0) else 0) :=
          Finset.sum_comm
      _ = ∑ s : ZMod 2, (if rep2 (window (α := A2) (L := 2) S s) = v then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.sum_eq_single (window (α := A2) (L := 2) S s)]
          · simp
          · intro w _ hw
            simp [Ne.symm hw]
          · intro hmem
            exact absurd (Finset.mem_univ _) hmem
  rw [h]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- The list-filter form of `classCount` is the molecule-class multiplicity sum:
counting starts by the class of their window is the same as summing the oriented
window multiplicities over the class. -/
theorem classCount_eq_sum (S : ZMod 2 → A2) (v : Word2) :
    classCount S v = ∑ w : Word2, if rep2 w = v then mult (α := A2) (G := 2) (L := 2) S w else 0 := by
  rw [classCount_eq_card, ← sumform_eq_card]

/-- The exact source-faithful oriented likelihood of the sample `x`: the product
of the oriented uniform-start read pmf over the observed windows. -/
noncomputable def exactLikelihood (n : ℕ) (S : ZMod 2 → A2) (x : Fin n → Word2) : ℝ :=
  ∏ i : Fin n, readPmf (α := A2) (G := 2) (L := 2) S (x i)

/-- The one-read sample consisting of the oriented word `00`. -/
def x0 : Fin 1 → Word2 := fun _ => w00

/-! ### `decide`-checked facts about the witness -/

/-- Both windows of `S0` spell `00`, so `00` has multiplicity `2`. -/
theorem mult_S0_w00 : mult (α := A2) (G := 2) (L := 2) S0 w00 = 2 := by decide

/-- No window of `S1` spells `00`. -/
theorem mult_S1_w00 : mult (α := A2) (G := 2) (L := 2) S1 w00 = 0 := by decide

/-- **Equal §6.2 visit vectors.**  The genome `00` and its reverse complement
`11` induce the *same* §6.2 molecule-class visit vector: both visit the single
molecule class `{00,11}` twice. -/
theorem classCount_S0_eq_S1 : classCount S0 = classCount S1 := by decide

/-- The exact oriented likelihood of `(00)` under `S0` is `1`. -/
theorem likelihood_S0 : exactLikelihood 1 S0 x0 = 1 := by
  unfold exactLikelihood
  simp only [Fin.prod_univ_one]
  unfold readPmf
  rw [show mult (α := A2) (G := 2) (L := 2) S0 (x0 0) = 2 from by decide]
  norm_num

/-- The exact oriented likelihood of `(00)` under `S1` is `0`. -/
theorem likelihood_S1 : exactLikelihood 1 S1 x0 = 0 := by
  unfold exactLikelihood
  simp only [Fin.prod_univ_one]
  unfold readPmf
  rw [show mult (α := A2) (G := 2) (L := 2) S1 (x0 0) = 0 from by decide]
  norm_num

/-- **Oriented likelihood distinguishes the reverse-complement pair.** -/
theorem likelihood_S0_ne_S1 : exactLikelihood 1 S0 x0 ≠ exactLikelihood 1 S1 x0 := by
  rw [likelihood_S0, likelihood_S1]
  norm_num

/-! ## 3. The separation -/

/-- **The exact oriented likelihood does not factor through the §6.2
molecule-class visit vector.**  If it did, `S0` and `S1` — which have equal visit
vectors — would have equal likelihoods, contradicting `likelihood_S0_ne_S1`. -/
theorem exactLikelihood_not_factors_throughput :
    ¬ ∃ φ : (Word2 → ℕ) → ℝ, ∀ S : ZMod 2 → A2, exactLikelihood 1 S x0 = φ (classCount S) := by
  rintro ⟨φ, hφ⟩
  have h0 := hφ S0
  have h1 := hφ S1
  rw [← classCount_S0_eq_S1] at h1
  exact likelihood_S0_ne_S1 (h0.trans h1.symm)

/-- **Abstract separation.**  If a "throughput" map `Θ` is not injective enough to
separate two candidates whose exact likelihoods differ, then no §6.2-style
objective `score ∘ Θ` (a function of the throughput alone) can equal the exact
likelihood.  This is the general form of the §6.2 non-equivalence; the concrete
`Θ = classCount` instance is `exactLikelihood_not_factors_throughput`. -/
theorem no_flow_objective_eq_likelihood {W : Type}
    (Θ : (ZMod 2 → A2) → (W → ℕ))
    (hsep : ∃ S T : ZMod 2 → A2,
      Θ S = Θ T ∧ exactLikelihood 1 S x0 ≠ exactLikelihood 1 T x0) :
    ¬ ∃ score : (W → ℕ) → ℝ, ∀ S : ZMod 2 → A2, exactLikelihood 1 S x0 = score (Θ S) := by
  rintro ⟨score, hscore⟩
  obtain ⟨S, T, hΘ, hlik⟩ := hsep
  exact hlik (hscore S |>.trans (by rw [hΘ, hscore T]))

/-- **Headline §6.2 non-equivalence.**  There is no §6.2 throughput objective
(a function of the molecule-class visit vector) equal to the source-faithful
oriented circular-genome likelihood.  Since every §6.2 feasible-flow objective
factors through the throughput (`flow_objective_factors_throughput`,
`flow_maximality_is_throughput_property`), this separates the §6.2
feasible-flow optimization from the exact oriented genome model. -/
theorem section62_flow_objective_ne_genome_likelihood :
    ¬ ∃ score : (Word2 → ℕ) → ℝ, ∀ S : ZMod 2 → A2, exactLikelihood 1 S x0 = score (classCount S) :=
  exactLikelihood_not_factors_throughput

/-! ## 4. Bridge to the §6.2 spelled-circuit visit vector

`classCount` is not a module-local stand-in: it *is* the molecule-class visit
vector `Spelling.visits` of the genome's window walk, the vector that the merged
`AssemblyP1.Section62SpelledFlowAdapter.throughput_eq_visits` identifies with the
§6.2 `throughputVec` of the walk flow.  We record the identification of the two
combinatorial descriptions of the visit vector here. -/

open AssemblyP1.Section62Flow

/-- The window walk of a length-`2` genome as a §6.2 `Spelling`: position `i`
carries the oriented window at start `i`. -/
def spellingOf (S : ZMod 2 → A2) : Spelling A2 Word2 2 :=
  ⟨fun i => window (α := A2) (L := 2) S (i : ZMod 2), by norm_num⟩

/-- **`classCount` is the §6.2 visit vector.**  The molecule-class count of a
genome is *definitionally* the number of walk positions whose representative is
each class, i.e. `Spelling.visits` of its window walk.  Via
`AssemblyP1.Section62SpelledFlowAdapter.throughput_eq_visits` this is the §6.2
`throughputVec` of the walk flow, so `classCount` is not a module-local stand-in
for the §6.2 throughput. -/
theorem classCount_eq_visits (S : ZMod 2 → A2) (v : Word2) :
    classCount S v = Spelling.visits rep2 (spellingOf S) v := rfl

/-! ## Axiom audit -/

#print axioms flow_objective_factors_throughput
#print axioms flow_maximality_is_throughput_property
#print axioms classCount_eq_sum
#print axioms classCount_eq_visits
#print axioms likelihood_S0
#print axioms likelihood_S1
#print axioms likelihood_S0_ne_S1
#print axioms exactLikelihood_not_factors_throughput
#print axioms no_flow_objective_eq_likelihood
#print axioms section62_flow_objective_ne_genome_likelihood

end AssemblyP1.Section62FlowGenomeSeparation
