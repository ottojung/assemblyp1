import AssemblyP1.SourceFaithfulIs
import AssemblyP1.RepeatAdapter
import AssemblyP1.Section62BidirectedFlow

/-!
# A kernel-checked counterexample: same-length exact ML fails under full `I_s`

This module is the decisive negative result of issue #88. It exhibits a
**genuine read realization** on a circular genome of length `4` with read
length `2`, which satisfies **full source-faithful information feasibility**
`R ∈ I_s` (Shomorony et al. 2016, Eq. (1), all three clauses, decided by
computation over every admissible repeat length and every selection of starts),
and for which the true genome is **not** a maximum-likelihood candidate among
circular genomes of the *same* length.

## The instance

Alphabet `{A, B}`. The truth is the circular genome

```
    0  1  2  3
    A  A  B  B
```

Read length `L = 2`. Its four length-`2` windows are

```
    start 0 : AA      start 1 : AB
    start 2 : BB      start 3 : BA
```

The realized reads are the two placements at starts `1` and `3`, i.e. one read
`AB` and one read `BA`. These are exactly the two distinct starts of the
realization, so the `Finset` handed to `InformationFeasible` is `{1, 3}` and the
observation is built from the *same* realization:

* `readStarts = {1, 3}` is the set of distinct latent starts;
* `observedAB` and `observedBA` are the reads those two placements return
  (`realized_reads`);
* `realizedReads = [observedAB, observedBA]` is the realized read multiset, and
  the objective consumes exactly this list.

Clause 1 (`Covers`) is satisfied and is the only non-vacuous clause: the read at
start `1` covers positions `{1, 2}` and the read at start `3` covers `{3, 0}`,
so together they cover all four positions. The truth has no *triple* repeat of
any length `1 ≤ e < 4` (the `A` positions are `{0, 1}` and the `B` positions are
`{2, 3}`, both of size two), so clause 2 is vacuous; and the only two repeats,
at starts `(0, 1)` and `(2, 3)`, do not interleave, so clause 3 is vacuous. All
of this is *checked by computation*, not assumed: `truth_information_feasible`
is a single `decide` on the full predicate, over every admissible repeat length
and every selection of starts.

## The competitor

The circular genome of the same length `4` with

```
    0  1  2  3
    A  B  A  B
```

has windows `AB, BA, AB, BA`, so it spells each observed read type **twice**.

## The arithmetic

`sameLengthExactLik g L reads` is `∏` over the realized reads of the factor
`d_g w / N(g)`, where `d_g w` is the number of starts of `g` returning the
length-`L` word `w` and `N(g) = g.len` is the candidate's *own* intrinsic
length. This is the exact Medvedev–Brudno multinomial likelihood of
`docs/ml-formalization-contract.md` Variant E with the observation-only
multinomial coefficient divided out; reinserting that coefficient multiplies
every candidate by the same positive constant, so it cannot move a maximizer.
Hence

```
    truth      = (1/4) · (1/4) = 1/16
    competitor = (2/4) · (2/4) = 1/4   >   1/16.
```

## Scope

* The candidate universe is `SourceFaithfulIs.Genome` restricted to
  `c.len = g.len`: the competitor is the **same length** as the truth. This is
  the case that `AssemblyP1.ExactVariantECounterexample` does *not* cover, since
  there the competitor is strictly longer than the truth.
* The truth is **not** a long-triple-repeat genome
  (`truth_no_long_triple_repeat`), so this instance is not an artifact of the
  wraparound regime characterised in `AssemblyP1.BridgingBridge`. It is a
  genuine failure of the likelihood claim in the regime where the oriented
  same-length rigidity chain's hypothesis actually holds.
* The failing candidates are exactly those whose length-`L` window **support**
  differs from the truth's. Over the same-support (spelled-circuit) candidate
  class that chain still applies; the honest statement of the remainder is the
  disjunction `AssemblyP1.OrientedSameLengthML.same_length_exactLik_maximizer_or_residual_gap`,
  and this module shows that its second disjunct is realized by a two-read
  realization.
-/

namespace AssemblyP1.SameLengthExactMLCounterexample

open SourceFaithfulIs

set_option maxHeartbeats 400000

noncomputable section

/-! ## The alphabet, the truth, and the realization -/

inductive Base where
  | A | B
  deriving DecidableEq, BEq, Repr, Inhabited

/-- The true circular genome `AABB`, in the shared source-faithful
representation. A reducible abbreviation, so that the `Decidable` instances of
the shared layer are found by instance search when `I_s` membership is decided. -/
abbrev truthGenome : Genome Base where
  len := 4
  len_pos := by norm_num
  sym := ![Base.A, Base.A, Base.B, Base.B]

/-- The distinct latent starts of the realization: the read at start `1`
returns `AB`, and the read at start `3` returns `BA`. -/
def readStarts : Finset (Fin 4) := {1, 3}

/-- The oriented length-`2` read `AB`. -/
def observedAB : Fin 2 → Base := ![Base.A, Base.B]

/-- The oriented length-`2` read `BA`. -/
def observedBA : Fin 2 → Base := ![Base.B, Base.A]

/-- The realized read multiset: one `AB` and one `BA`, from the two distinct
starts `1` and `3`, each used once. -/
def realizedReads : List (Fin 2 → Base) := [observedAB, observedBA]

/-- **The coupling between the hypothesis and the observation.** The two
placements really do return the two observed read types, and they are all the
starts used. The `Finset` in `InformationFeasible` is therefore the set of
distinct latent starts of the very realization whose reads the objective
consumes. -/
theorem realized_reads :
    truthGenome.window 2 1 = observedAB ∧ truthGenome.window 2 3 = observedBA := by
  decide

/-! ## The hypothesis: full source-faithful `I_s` -/

/-- **Full source-faithful information feasibility.** All three clauses of
Shomorony et al. Eq. (1) hold for the truth under the realized read placements,
checked by finite computation over every admissible repeat length and every
selection of starts. No repeat is enumerated by hand, and no clause is assumed
or replaced by a stand-in. -/
theorem truth_information_feasible :
    InformationFeasible truthGenome 2 readStarts := by
  unfold InformationFeasible
  decide

/-! ## The objective -/

/-- The number of starts of `g` at which the oriented length-`L` window is `w`:
the occurrence multiplicity `d_g w` of the read type `w` in the candidate. -/
def winCount {α : Type} [DecidableEq α] (g : Genome α) (L : ℕ) (w : Fin L → α) : ℕ :=
  ((Finset.univ : Finset (Fin g.len)).filter
    (fun r : Fin g.len => g.window L r = w)).card

/-- **The exact Medvedev–Brudno multinomial objective at the candidate's own
intrinsic length.** The product runs over the realized reads, so a read type
observed `x w` times contributes the factor `(d_g w / N(g))^x w`, and `N(g) =
g.len` is candidate-intrinsic, so genome size is *not* an externally fixed
parameter. The observation-only multinomial coefficient `n! / ∏_w x w!` is
divided out; reinserting it scales every candidate by the same positive
constant and therefore cannot move a maximizer. -/
def sameLengthExactLik {α : Type} [DecidableEq α] (g : Genome α) (L : ℕ)
    (reads : List (Fin L → α)) : ℚ :=
  (reads.map (fun w => (winCount g L w : ℚ) / (g.len : ℚ))).prod

/-- Maximum likelihood among circular genomes **of the same length** as the
truth. This is the restricted candidate universe of
`docs/ml-formalization-contract.md` Variant E, made a property of the statement
rather than a comment about it. -/
def IsSameLengthMaximumLikelihood {α : Type} [DecidableEq α] (g : Genome α) (L : ℕ)
    (reads : List (Fin L → α)) : Prop :=
  ∀ c : Genome α, c.len = g.len →
    sameLengthExactLik c L reads ≤ sameLengthExactLik g L reads

/-! ## The competitor and the arithmetic -/

/-- **The competitor: the same-length circular genome `ABAB`.** -/
abbrev competitorGenome : Genome Base where
  len := 4
  len_pos := by norm_num
  sym := ![Base.A, Base.B, Base.A, Base.B]

theorem competitor_same_length : competitorGenome.len = truthGenome.len := rfl

theorem truth_winCount_AB : winCount truthGenome 2 observedAB = 1 := by decide
theorem truth_winCount_BA : winCount truthGenome 2 observedBA = 1 := by decide
theorem competitor_winCount_AB : winCount competitorGenome 2 observedAB = 2 := by decide
theorem competitor_winCount_BA : winCount competitorGenome 2 observedBA = 2 := by decide

theorem truth_likelihood :
    sameLengthExactLik truthGenome 2 realizedReads = 1 / 16 := by
  simp only [sameLengthExactLik, realizedReads, List.map, List.prod_cons, List.prod_nil,
    List.prod_singleton]
  rw [truth_winCount_AB, truth_winCount_BA]
  norm_num [truthGenome]

theorem competitor_likelihood :
    sameLengthExactLik competitorGenome 2 realizedReads = 1 / 4 := by
  simp only [sameLengthExactLik, realizedReads, List.map, List.prod_cons, List.prod_nil,
    List.prod_singleton]
  rw [competitor_winCount_AB, competitor_winCount_BA]
  norm_num [competitorGenome]

theorem competitor_beats_truth :
    sameLengthExactLik truthGenome 2 realizedReads
      < sameLengthExactLik competitorGenome 2 realizedReads := by
  rw [truth_likelihood, competitor_likelihood]
  norm_num

theorem truth_not_maximum_likelihood :
    ¬ IsSameLengthMaximumLikelihood truthGenome 2 realizedReads := by
  intro h
  unfold IsSameLengthMaximumLikelihood at h
  have hc := h competitorGenome competitor_same_length
  rw [competitor_likelihood, truth_likelihood] at hc
  norm_num at hc

/-! ## The instance is not a wraparound artifact -/

/-- **The truth has no triple repeat at all.** Among the four positions of
`AABB` the `A` positions are `{0, 1}` and the `B` positions are `{2, 3}`, both of
size two, so no three distinct positions share a symbol. Checked by
computation. -/
theorem truth_no_triple_repeat :
    ¬ ∃ (a b c : Fin 4), a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      truthGenome.sym a = truthGenome.sym b ∧
      truthGenome.sym b = truthGenome.sym c := by
  decide

/-- **The truth is not a long-triple-repeat genome**, so this instance is *not*
an artifact of the wraparound regime of `AssemblyP1.BridgingBridge`: the
interface hypothesis of the oriented same-length rigidity chain
(`AssemblyP1.OrientedFinal.oriented_same_length_spectrum_rigidity`) holds here.
A maximal triple repeat at any length `ℓ ≥ L - 1 = 1` and three distinct
residue classes would make the three symbols agree, contradicting
`truth_no_triple_repeat`. -/
theorem truth_no_long_triple_repeat :
    ¬ RepeatAdapter.HasLongTripleRepeat truthGenome.len_pos truthGenome.sym 2 := by
  rintro ⟨a, b, c, ℓ, h1, hℓG, hab, hbc, hac, hag, _, _⟩
  have h0 := hag 0 (by omega)
  have e1 : truthGenome.sym ⟨a % 4, Nat.mod_lt _ truthGenome.len_pos⟩ = truthGenome.sym ⟨b % 4, Nat.mod_lt _ truthGenome.len_pos⟩ := by
    simpa [OrientedRigidity.cyc, Nat.zero_add] using h0.1
  have e2 : truthGenome.sym ⟨b % 4, Nat.mod_lt _ truthGenome.len_pos⟩ = truthGenome.sym ⟨c % 4, Nat.mod_lt _ truthGenome.len_pos⟩ := by
    simpa [OrientedRigidity.cyc, Nat.zero_add] using h0.2
  have d1 : (⟨a % 4, Nat.mod_lt _ truthGenome.len_pos⟩ : Fin 4) ≠ ⟨b % 4, Nat.mod_lt _ truthGenome.len_pos⟩ := by
    intro he
    exact hab (congrArg Fin.val he)
  have d2 : (⟨a % 4, Nat.mod_lt _ truthGenome.len_pos⟩ : Fin 4) ≠ ⟨c % 4, Nat.mod_lt _ truthGenome.len_pos⟩ := by
    intro he
    exact hac (congrArg Fin.val he)
  have d3 : (⟨b % 4, Nat.mod_lt _ truthGenome.len_pos⟩ : Fin 4) ≠ ⟨c % 4, Nat.mod_lt _ truthGenome.len_pos⟩ := by
    intro he
    exact hbc (congrArg Fin.val he)
  exact truth_no_triple_repeat
    ⟨⟨a % 4, Nat.mod_lt _ truthGenome.len_pos⟩, ⟨b % 4, Nat.mod_lt _ truthGenome.len_pos⟩, ⟨c % 4, Nat.mod_lt _ truthGenome.len_pos⟩, d1, d2, d3, e1, e2⟩

/-! ## The §6.2 support-spelling test: where the acceptance boundary lies

The strict candidate restriction relevant to #88 is the §6.2 one: a candidate
is a flow on the read-overlap graph whose **edges are the observed read types**,
so *every* length-`L` window of a §6.2-feasible candidate must be a read type
that was actually observed. Both halves of that test are checked here by
computation, and they come out differently for the truth and for the
competitor. -/

/-- The two observed read types, as a predicate on length-`2` words. -/
def IsObservedRead (w : Fin 2 → Base) : Prop := w = observedAB ∨ w = observedBA

instance (w : Fin 2 → Base) : Decidable (IsObservedRead w) := by
  unfold IsObservedRead
  infer_instance

/-- **The competitor is spelled on the observed support.** Every length-`2`
window of the same-length genome `ABAB` is one of the two read types the
realization actually produced. Together with the facts that its edge
multiplicities sum to `G` and that its flow is balanced, this makes it a
genuine §6.2 flow-feasible candidate, so the §6.2 restriction does **not**
rescue the maximum-likelihood claim. -/
theorem competitor_spelled_on_observed :
    ∀ r : Fin 4, IsObservedRead (competitorGenome.window 2 r) := by
  decide

/-- The competitor's total flow mass equals the genome length `G`, as §6.2
requires of a feasible assembly. -/
theorem competitor_total_mass :
    (Finset.univ.filter (fun r : Fin 4 => IsObservedRead (competitorGenome.window 2 r))).card
      = truthGenome.len := by
  decide

/-- **The truth is *not* spelled on the observed support.** The truth `AABB` has
length-`2` windows `AA` and `BB` that were never observed, so the truth itself is
**not** a member of the §6.2 flow-feasible set. This is the precise sense in
which the §6.2 candidate restriction does not apply symmetrically: it can
contain a competitor that beats the truth while excluding the truth.

Clause 1 of `I_s` is only *position* coverage: the two realized reads do cover
all four positions, yet two of the truth's windows go unobserved. Full
length-`L` window coverage is strictly stronger than `Covers`, and `I_s` does
not provide it. -/
theorem truth_not_spelled_on_observed :
    ∃ r : Fin 4, ¬ IsObservedRead (truthGenome.window 2 r) := by
  decide

/-- **The acceptance boundary, in one statement.** Over the §6.2 candidate class
the truth is a candidate exactly when every one of its length-`L` windows was
observed; the counterexample exhibits a full-`I_s` realization in which the
truth fails that condition, a §6.2-feasible same-length competitor succeeds,
and the competitor's exact likelihood is strictly larger. -/
theorem acceptance_boundary :
    InformationFeasible truthGenome 2 readStarts ∧
      (∃ r : Fin 4, ¬ IsObservedRead (truthGenome.window 2 r)) ∧
      (∀ r : Fin 4, IsObservedRead (competitorGenome.window 2 r)) ∧
      (¬ IsSameLengthMaximumLikelihood truthGenome 2 realizedReads) :=
  ⟨truth_information_feasible, truth_not_spelled_on_observed,
    competitor_spelled_on_observed, truth_not_maximum_likelihood⟩

/-! ## The conclusion -/

/-- **Kernel-checked counterexample to the oriented same-length exact
maximum-likelihood claim.**

The truth `AABB` is a circular genome of length `4`; the two realized length-`2`
reads are those returned by the placements at starts `1` and `3`; the set of
distinct latent starts is `{1, 3}`; and that set satisfies **full**
source-faithful information feasibility, all three clauses, by computation. Yet
the same-length circular genome `ABAB` attains exact likelihood `1/4` against
the truth's `1/16`.

Consequently the universal implication "`I_s` implies the true sequence is a
maximum-likelihood sequence" is **false** for the same-length exact
Medvedev–Brudno objective, under a genuine realization and with the competitor
at the same genome length as the truth. -/
theorem same_length_exact_ML_counterexample :
    InformationFeasible truthGenome 2 readStarts ∧
      ¬ IsSameLengthMaximumLikelihood truthGenome 2 realizedReads :=
  ⟨truth_information_feasible, truth_not_maximum_likelihood⟩

/-- The same counterexample, with the supporting facts attached: the failure is
not an artifact of the wraparound regime, and it is genuinely a same-length
comparison. -/
theorem same_length_exact_ML_counterexample_full :
    InformationFeasible truthGenome 2 readStarts ∧
      ¬ RepeatAdapter.HasLongTripleRepeat truthGenome.len_pos truthGenome.sym 2 ∧
      competitorGenome.len = truthGenome.len ∧
      ¬ IsSameLengthMaximumLikelihood truthGenome 2 realizedReads :=
  ⟨truth_information_feasible, truth_no_long_triple_repeat,
    competitor_same_length, truth_not_maximum_likelihood⟩


/-! ## The literal §6.2 acceptance boundary: `SpelledFeasible62`

The previous section used a hand-written "every window is an observed read"
criterion. This section instantiates the **literal** merged predicate
`AssemblyP1.Section62Flow.SpelledFeasible62` (#100), in strict oriented
single-strand mode, on the two observed length-`2` reads `AB` and `BA`, and
proves that the competitor `ABAB` satisfies it. -/

/-- The strand / molecule-class type: an oriented length-`2` word. In strict
oriented single-strand mode there is no reverse-complement collapse, so the two
strands of a class coincide and the class representative is the word itself. -/
abbrev W := Fin 2 → Base

/-- Linearization of a strand: the word as a list, which is what makes
suffix/prefix overlap lengths meaningful. -/
def strandToList : W → List Base := fun w => List.ofFn w

/-- Strict oriented single-strand mode: the identity molecule-class
representative. No reverse-complement identification is performed. -/
def idRep : W → W := fun w => w

/-- Strict oriented single-strand mode: the reverse complement is the identity,
so `strandsOf` enumerates each class once per strand slot and no class is
collapsed with its reverse complement. -/
def idRc : W → W := fun w => w

/-- The observed read molecules: `AB` and `BA`. These are the vertices of the
§6.2 bidirected overlap graph, i.e. exactly the read types the realization
produced. -/
def observedVerts : List W := [observedAB, observedBA]

/-- The §6.2 overlap graph on the observed reads, at read length `2` and
minimum overlap `1` (the maximum proper overlap, `readLen - 1`). -/
def overlapGraph : List (Section62Flow.BdEdge Base W) :=
  Section62Flow.overlapEdges Base W strandToList idRep idRc 2 1 observedVerts

/-- **The spelling of the competitor `ABAB`.** It is a circular molecule of
length `4`, read at each of its four cyclic read positions; the strand read at
position `i` is its length-`2` window there, so the walk is
`AB → BA → AB → BA`. -/
def competitorSpelling : Section62Flow.Spelling Base W 4 where
  strand := ![observedAB, observedBA, observedAB, observedBA]
  hn := by norm_num

/-- **The flow the spelling's cyclic walk carries.** Each of the two steps
types is traversed twice, so the flow is `2` on `AB → BA`, `2` on `BA → AB`, and
`0` elsewhere. This is the explicit finite certificate that
`SpelledFeasible62` takes as its `f` argument. -/
def walkFlow : Section62Flow.BdFlow Base W := fun e =>
  if e = Section62Flow.bdEdge idRep observedAB observedBA 1 then 2
  else if e = Section62Flow.bdEdge idRep observedBA observedAB 1 then 2
  else 0

/-- The candidate's throughput vector on the overlap graph. In strict
single-strand mode `strandsOf` enumerates each observed class once per strand
slot, so `overlapGraph` carries four copies of each of the two step types; the
walk traverses each twice, giving throughput `4 · 2 = 8` at each of the two
vertices. `d` is supplied to match, as the predicate intends. -/
def candidateThroughput : W → ℕ := fun _ => 8

-- AUDIT CORRECTION (see `docs/same-length-62-maximizer.md`): this predicate is
-- a **dominance** statement, not a maximizer statement.  It says that no
-- same-length §6.2-feasible spelled candidate has likelihood above the truth's.
-- It contains NO conjunct asserting that the truth is itself a §6.2 candidate,
-- so refuting it does NOT refute the maximizer-with-membership claim of #88.
-- At the `AABB`/`ABAB` instance the truth is not a member of the class at all
-- (see `truth_not_spelled_on_observed`), so the membership antecedent is false
-- there.  The repaired positive theorem over genuine §6.2 candidates is
-- `AssemblyP1.SameLength62Maximizer.informationFeasible_62_maximizer`.

/-- **The §6.2 dominance boundary for the maximum-likelihood claim.** No
same-length §6.2-feasible spelled candidate has exact likelihood above the
truth's.  This is a dominance statement; it is *not* the maximizer statement of
#88, which would additionally require the truth to be a §6.2 candidate.

The candidate class is the *literal* merged predicate
`AssemblyP1.Section62Flow.SpelledFeasible62` (#100) in strict oriented
single-strand mode on the two observed length-`2` reads, and the quantification
runs over all spellings `sp`, all flows `f`, all terminal choices `t` and all
throughput vectors `d`. So a single feasible competitor whose likelihood exceeds
the truth's refutes it, which is exactly what the next theorem exhibits. -/
def Is62MaximumLikelihood (g c : Genome Base) (L : ℕ) (reads : List (Fin L → Base)) : Prop :=
  ∀ (n : ℕ) (sp : AssemblyP1.Section62Flow.Spelling Base W n)
    (f : AssemblyP1.Section62Flow.BdFlow Base W)
    (t : AssemblyP1.Section62Flow.SuperTerminals W) (d : W → ℕ),
    n = c.len →
    AssemblyP1.Section62Flow.SpelledFeasible62 Base W strandToList idRep idRc L 1
      observedVerts sp f t d →
    sameLengthExactLik c L reads ≤ sameLengthExactLik g L reads

/-- **The competitor is a literal §6.2 feasible spelled candidate**, in strict
oriented single-strand mode, at the same genome length as the truth.

All five conjuncts of `SpelledFeasible62` are discharged: every visited vertex
is an observed read molecule; every step of the cyclic walk is an edge of the
§6.2 overlap graph; every step survives the transitive edge reduction (the
reduction is vacuous here, since a step has overlap length `1`, and no strictly
shorter *positive* overlap can spell an edge of length `1`); the walk is a
bidirected circuit, because in strict single-strand mode `sgnX = 1` and
`sgnY = -1` at every step; and the walk flow is a feasible §6.2 flow with no
terminal usage. -/
theorem competitor_spelledFeasible62 :
    AssemblyP1.Section62Flow.SpelledFeasible62 Base W strandToList idRep idRc 2 1
      observedVerts competitorSpelling walkFlow
      (AssemblyP1.Section62Flow.noTerminals W) candidateThroughput := by
  unfold AssemblyP1.Section62Flow.SpelledFeasible62
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> decide
  · show AssemblyP1.Section62Flow.StepsInGraph idRep 2 competitorSpelling overlapGraph
    intro i; fin_cases i <;> decide
  · show AssemblyP1.Section62Flow.StepsSurviveReduction Base W strandToList idRep
      idRc 2 observedVerts competitorSpelling overlapGraph
    intro i; fin_cases i <;> decide
  · intro i
    have h1 : ∀ j : Fin 4, (competitorSpelling.step idRep 2 j).sgnX = 1 := by
      intro j; fin_cases j <;> rfl
    have h2 : ∀ j : Fin 4, (competitorSpelling.step idRep 2 j).sgnY = -1 := by
      intro j; fin_cases j <;> rfl
    show (competitorSpelling.step idRep 2 i).sgnX =
      -((competitorSpelling.step idRep 2
        (AssemblyP1.Section62Flow.pred competitorSpelling i)).sgnY)
    rw [h1, h2]; norm_num
  · show AssemblyP1.Section62Flow.Feasible62 Base W idRep observedVerts overlapGraph
      walkFlow (AssemblyP1.Section62Flow.noTerminals W) candidateThroughput
    refine ⟨?_, AssemblyP1.Section62Flow.noTerminals_usage_zero W⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro e he; fin_cases he <;> decide
    · intro v hv; fin_cases hv <;> decide
    · intro v hv; fin_cases hv <;> decide
    · intro v hv; fin_cases hv <;> decide

/-- **Refutation of the §6.2 acceptance boundary.** The truth `AABB` is a
circular genome of length `4` whose realized length-`2` reads (the placements at
starts `1` and `3`) satisfy **full** source-faithful `InformationFeasible`; and
the same-length circular genome `ABAB` is a literal §6.2 `SpelledFeasible62`
candidate whose exact Medvedev–Brudno likelihood is strictly larger than the
truth's. So the §6.2 candidate restriction does **not** rescue the
maximum-likelihood claim. -/
theorem section62_maxLikelihood_refuted :
    ¬ Is62MaximumLikelihood truthGenome competitorGenome 2 realizedReads := by
  intro h
  have hc := h 4 competitorSpelling walkFlow
    (AssemblyP1.Section62Flow.noTerminals W) candidateThroughput rfl
    competitor_spelledFeasible62
  rw [competitor_likelihood, truth_likelihood] at hc
  norm_num at hc

/-! ## The single exported refutation theorem -/

/-- **The #88 acceptance boundary, settled in one theorem.** For the truth
`AABB` with realized length-`2` reads at starts `1` and `3`:

1. the set of distinct latent starts satisfies **full** source-faithful
   information feasibility `I_s` (all three clauses, by computation);
2. the same-length circular genome `ABAB` satisfies the **literal** §6.2
   predicate `Section62Flow.SpelledFeasible62` in strict oriented single-strand
   mode;
3. the competitor's exact same-length Medvedev–Brudno likelihood is strictly
   larger than the truth's (`1/4` against `1/16`).

Hence the maximum-likelihood conclusion of the #88 target does not follow, even
with the §6.2 support-spelled candidate restriction in force and even at equal
genome length. -/
theorem same_length_exact_ML_refutation_62 :
    InformationFeasible truthGenome 2 readStarts ∧
      competitorGenome.len = truthGenome.len ∧
      Section62Flow.SpelledFeasible62 Base W strandToList idRep idRc 2 1
        observedVerts competitorSpelling walkFlow (Section62Flow.noTerminals W)
        candidateThroughput ∧
      ¬ Is62MaximumLikelihood truthGenome competitorGenome 2 realizedReads ∧
      ¬ IsSameLengthMaximumLikelihood truthGenome 2 realizedReads :=
  ⟨truth_information_feasible, competitor_same_length,
    competitor_spelledFeasible62, section62_maxLikelihood_refuted,
    truth_not_maximum_likelihood⟩


end

end AssemblyP1.SameLengthExactMLCounterexample
