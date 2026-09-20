import AssemblyP1.ReadTiledCounterexample

/-!
# Section 6.2 feasibility obstruction for the canonical read-tiled witness

Issue #36 asks whether the repository's canonical fixed-length likelihood
counterexample is feasible under the Medvedev–Brudno §6.2 bidirected-flow
assembly constraints.  This module kernel-checks the answer for the current
canonical witness, the read-tiled instance

* truth `S = AAABCBC`, competitor `D = AAAAABC`, `L = 3`,
* observed read types `{AAA:3, AAB:1, ABC:1, BCA:1, CAA:1}`,

formalized in `AssemblyP1.ReadTiledCounterexample`.

## Reconstructed §6.2 sequence-level criterion

Section 6.2 searches a flow on the transitively reduced read-overlap graph whose
vertices are the reads, every vertex has lower bound `1`, and the output may be
a non-contiguous assembly.  By Observation 7 of the source, a circular molecule
`D` is spelled by a walk in that graph exactly when (source-note derivation in
`docs/section-6-2-feasible-set-membership.md` §2, not re-derived here)

1. every length-`L` window of `D` is an observed read type
   (`WindowSupported`); and
2. every observed read occurrence is used, i.e. the per-occurrence lower bounds
   `d_D(w) ≥ x_w` hold (`LowerBounded`).

Together these force support equality `supp(spec(D)) = supp(x)` and are exactly
the sequence-level §6.2 feasible set.

## Result

The competitor satisfies both conditions (`competitor_section62_feasible`),
but the **truth does not**: its windows `BCB` and `CBC` are unobserved, so no
closed walk in the read-overlap graph spells `S`.  Hence `S` is not even an
admissible §6.2 candidate, and this witness cannot refute the well-posed
sequence-level statement "_I_s_ ∧ `S ∈ F_flow` ⇒ `S` is ML over `F_flow`".
The obstruction to transferring the witness is the pair of unobserved truth
windows, kernel-checked in `truth_unobserved_windows`.

Scope.  This is one finite instance, fixed read length `L = 3`, single-strand
reading.  It does not settle the source-ambiguous Shomorony et al. open
question, the reverse-complement reading, or the non-spellable flow-level gap.
-/

namespace AssemblyP1.Section62FlowObstruction

open AssemblyP1.ReadTiledCounterexample

/-- Read type `BCB`. -/
def readBCB : Fin 3 → Base := ![Base.B, Base.C, Base.B]

/-- Read type `CBC`. -/
def readCBC : Fin 3 → Base := ![Base.C, Base.B, Base.C]

/-- The observed read types, i.e. the vertices of the §6.2 read-overlap graph. -/
def observedSupport : Finset (Fin 3 → Base) :=
  {readAAA, readAAB, readABC, readBCA, readCAA}

/--
Every length-`3` window of `g` is an observed read type: the cyclic window walk
of `g` stays on read vertices.  This is condition (1) of sequence-level §6.2
feasibility.  (Quantifying over the seven circular starts avoids needing a
`Fintype` instance on the function space `Fin 3 → Base`.)
-/
def WindowSupported (g : Genome) : Prop :=
  ∀ r : Fin 7, window g r ∈ observedSupport

/--
Per-occurrence lower bounds: every observed read occurrence is used by the
assembly.  The observed counts are `AAA:3, AAB:1, ABC:1, BCA:1, CAA:1`.
This is condition (2) of sequence-level §6.2 feasibility.
-/
def LowerBounded (g : Genome) : Prop :=
  occ g readAAA ≥ 3 ∧ occ g readAAB ≥ 1 ∧ occ g readABC ≥ 1 ∧
    occ g readBCA ≥ 1 ∧ occ g readCAA ≥ 1

/--
Sequence-level §6.2 feasibility with respect to the realized reads, in the
Observation-7 reading: every window of `g` is an observed read type and every
observed read occurrence is used. -/
def Section62Feasible (g : Genome) : Prop :=
  WindowSupported g ∧ LowerBounded g

/-- The read-tiled competitor `AAAAABC` is sequence-level §6.2 feasible. -/
theorem competitor_section62_feasible : Section62Feasible competitor := by
  unfold Section62Feasible WindowSupported LowerBounded observedSupport
  decide

/-- The truth `AAABCBC` is **not** sequence-level §6.2 feasible. -/
theorem truth_not_section62_feasible : ¬ Section62Feasible truth := by
  unfold Section62Feasible WindowSupported LowerBounded observedSupport
  decide

/--
Checkable obstruction: the truth carries the unobserved windows `BCB` and
`CBC`, each occurring once, and neither is an observed read type.  This is why
no walk in the read-overlap graph spells the truth.
-/
theorem truth_unobserved_windows :
    occ truth readBCB = 1 ∧ occ truth readCBC = 1 ∧
      readBCB ∉ observedSupport ∧ readCBC ∉ observedSupport := by
  unfold observedSupport
  decide

/--
Main finite theorem: the canonical read-tiled witness has a §6.2-feasible
competitor but a truth that is not a §6.2 candidate at all.  The witness
therefore does not transfer to the sequence-level §6.2 statement.
-/
theorem canonical_witness_section62_obstruction :
    Section62Feasible competitor ∧ ¬ Section62Feasible truth :=
  ⟨competitor_section62_feasible, truth_not_section62_feasible⟩

end AssemblyP1.Section62FlowObstruction
