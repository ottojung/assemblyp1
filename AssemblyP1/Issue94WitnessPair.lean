import AssemblyP1.BBTFibrePeriod
import AssemblyP1.BBTLadder
import AssemblyP1.BBTEulerian

/-!
# Board 94, front `94wit` --- the interlaced condensed-branch pair does not exist

This module answers the steering question of board 94 dated 2026-10-04 by
**refuting**, with a kernel-checked minimal counterexample, the theorem the
steering asked for:

> the smallest theorem that EXTRACTS AN INTERLACED CONDENSED-BRANCH PAIR from
> `¬ VertexCycleEq`.

## The statement, and its verdict

`InterlacedBranchPair` (§2) is the minimal form: an alternative Eulerian cycle
`σ` of the `(L-1)`-mer multigraph whose vertex cycle is not the truth's own
forces two chords of the alternative traversal's pairing `AltF σ`
which interleave on the circle.

**It is false, and its smallest counterexample has `K = 5`, `L = 2` and a
three-letter alphabet** (§3, `interlacedBranchPair_refuted`).  The
counterexample is `S = 00102` and the listing `σ = (1 3)(2 4)`.  It is an
Eulerian cycle (`cex_EulerianCycle`), its vertex cycle is foreign
(`cex_not_vertexCycleEq`), and the conclusion fails in the most decisive way
available: **`AltF σ` has no 2-cycle at all**, so the pairing has *no chord*,
let alone two interlacing ones (`cex_AltF`, `cex_no_chord`,
`cex_no_interlaced_pair`).

The moral is structural and it is the reason the route suggested in the
steering cannot work: **an alternative Eulerian cycle need not swap at any
vertex.**  `choices_only_at_branch` says the two traversals differ only at
branch objects; it does *not* say they differ *everywhere* they are allowed to.
At `S = 00102` the alternative traversal is a derangement of the vertices that
fixes two of the five starts and has a 3-cycle on the other three, so the
whole "maximal-extend the pair and left-shift it" apparatus has no pair to be
applied to.  Fibres, degrees and maximal extensions are irrelevant: the
premise does not manufacture a single chord.

## Which hypothesis is missing

Not `SameExtension`, and not primitivity.  The counterexample **is** primitive
(`cex_is_primitive`), and the maximal-extension half of the suggested argument
is *already proved in the tree*: `BBTLadder.support_blocks_nonCrossing` is
`P2.imp_ExtCrossing` instantiated at the support of the alternative traversal,
so "two interlacing chords, maximal-extended, do not interlace" needs no work.
What that theorem takes as **input** is `hI : Interleaved a b c d`, i.e.
exactly the conclusion being extracted here.  The missing hypothesis is

> **`Interleaved` on two distinct chords of the alternative pairing**, in the
> global form assumed by `BBTLadder.LadderVertexCycle` (every crossing
> quadruple of support chords, not one chosen pair).

and it cannot be manufactured, because at the counterexample there are zero
chords to choose from.  Adding it would not help either: with it,
`support_blocks_nonCrossing` says the two extensions do *not* interlace, so
the extraction route terminates in `SameExtension` --- which is
`BBTLadder.CrossingChordsCoalesce`, the very `#89` proposition with no
inhabitant, not a step towards an interlaced pair.

`cex_not_P2` / `cex_LongObstruction` record the complementary fact: this word
carries a maximal triple repeat (the letter `0` occurs three times at
`L - 1 = 1`), so it fails `P2`.  That is exactly the hypothesis whose absence
produces the counterexample, and it is also why the `P2`-restricted extraction
is not refutable: under `P2` the conclusion is *impossible* (two interlacing
chords of the pairing extend to two maximal repeats of length `≥ L - 1`,
contradicting `P2`'s interleaved clause), so `P2` + extraction collapses onto
`thm:BBT`.

§1 records the one positive structural lemma that survives: under `Ukkonen`
and primitivity, a branch vertex of the condensation has **exactly two**
occurrences and a unique partner, so the "cyclic list of branch vertices, each
with exactly two occurrences" shape is well defined.  It is the part of the
steering's suggestion that is true, and it is not enough.

No `sorry`, no `admit`, no `native_decide`, no `unsafe`, no new axiom, no
linter suppression.
-/

set_option maxHeartbeats 800000

namespace AssemblyP1.Issue94WitnessPair

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1.BBTChords
open AssemblyP1
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.RepeatAdapter

/-! ## 1. A branch vertex of the condensation is a *pair* -/

section Fibres

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)

/-- **UNDER `Ukkonen` AND PRIMITIVITY, A BRANCH VERTEX HAS EXACTLY TWO
OCCURRENCES, AND THE PARTNER IS UNIQUE.**  This is the "represent the
condensed core by the cyclic list of branch vertices, each with exactly two
occurrences" shape, established rather than assumed: `BBTFibrePeriod`'s
`fibre_card_le_two_of_primitive` is the cap, and two distinct occurrences
force the fibre to be exactly the pair.

It is a *pairing lemma only*.  It says nothing about whether an alternative
traversal uses the pairing: §3 shows an alternative Eulerian cycle may use no
chord at all. -/
theorem branch_occurrences_pair (hL : 2 ≤ L) (hU : Ukkonen hG L S)
    (hprim : IsPrimitive hG S) {r z : Fin G} (hrz : r ≠ z)
    (hv : vtx hG L S r = vtx hG L S z) :
    ∀ (w : Fin G), vtx hG L S w = vtx hG L S r → w = r ∨ w = z := by
  have hcap : (fibre hG L S (vtx hG L S r)).card ≤ 2 :=
    fibre_card_le_two_of_primitive hG S hL hU hprim _
  have hr : r ∈ fibre hG L S (vtx hG L S r) := (mem_fibre hG L S).mpr rfl
  have hz : z ∈ fibre hG L S (vtx hG L S r) := (mem_fibre hG L S).mpr hv.symm
  have hsub : ({r, z} : Finset (Fin G)) ⊆ fibre hG L S (vtx hG L S r) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with h | h
    · rw [h]; exact hr
    · rw [h]; exact hz
  have hsub1 : ({r} : Finset (Fin G)) ⊆ fibre hG L S (vtx hG L S r) := by
    intro w hw
    simp only [Finset.mem_singleton] at hw
    rw [hw]; exact hr
  have hcard2 : ({r, z} : Finset (Fin G)).card = 2 := by simp [hrz]
  have hge : 2 ≤ (fibre hG L S (vtx hG L S r)).card := by
    have hle : 2 ≤ ({r, z} : Finset (Fin G)).card := by rw [hcard2]
    exact le_trans hle (Finset.card_le_card hsub)
  have h2 : (fibre hG L S (vtx hG L S r)).card = 2 := le_antisymm hcap hge
  have hsup : (fibre hG L S (vtx hG L S r)) ⊆ ({r, z} : Finset (Fin G)) := by
    intro w hw
    by_contra hc
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    have h3 : ({r, z, w} : Finset (Fin G)) ⊆ fibre hG L S (vtx hG L S r) := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with h | h | h
      · rw [h]; exact hr
      · rw [h]; exact hz
      · rw [h]; exact hw
    have hcard3' : ({r, z, w} : Finset (Fin G)).card = 3 :=
      Finset.card_eq_three.mpr ⟨r, z, w, hrz, Ne.symm hc.1, Ne.symm hc.2, rfl⟩
    have hcard3 : 3 ≤ (fibre hG L S (vtx hG L S r)).card := by
      have hle : 3 ≤ ({r, z, w} : Finset (Fin G)).card := by rw [hcard3']
      exact le_trans hle (Finset.card_le_card h3)
    omega
  have hF : (fibre hG L S (vtx hG L S r)) = {r, z} :=
    Finset.Subset.antisymm hsup (by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with h | h
      · rw [h]; exact hr
      · rw [h]; exact hz)
  intro w hw
  have hw' : w ∈ fibre hG L S (vtx hG L S r) := (mem_fibre hG L S).mpr hw
  rw [hF] at hw'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw'
  exact hw'

/-- **... and an unambiguous vertex has a single occurrence**, so the pair is
exactly the branch vertex and the two cases really are complementary. -/
theorem unambiguous_single {v : Fin (L - 1) → α} (hdeg : deg hG L S v ≤ 1) {r z : Fin G}
    (hr : vtx hG L S r = v) (hz : vtx hG L S z = v) : r = z :=
  occ_unique hG L S v hdeg hr hz

end Fibres

/-! ## 2. The extraction statement -/

section Extract

variable {α : Type} [DecidableEq α]

/-- **AN INTERLACED CONDENSED-BRANCH PAIR, extracted from a foreign vertex
cycle.**  If `σ` is an Eulerian cycle of the `(L-1)`-mer multigraph whose
vertex cycle is *not* the truth's own, then there are two chords of the
alternative traversal's pairing `AltF hK σ` --- `a ↦ b ↦ a` and
`c ↦ d ↦ c`, with the four starts pairwise distinct --- which interleave on
the circle.

This is the minimal extraction: it is `BBTLadder.CrossingChordsCoalesce`
without its `SameExtension` conclusion and without any `P2`/primality
hypothesis, so it is the weakest form the steering asked about.  §3 shows it
is false. -/
def InterlacedBranchPair (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α) (σ : Fin K ≃ Fin K),
    2 ≤ L → L ≤ K →
    EulerianCycle hK L S σ →
      ¬ VertexCycleEq hK L S σ (Equiv.refl (α := Fin K)) →
      ∃ (a b c d : Fin K),
        AltF hK σ a = b ∧ AltF hK σ b = a ∧ AltF hK σ c = d ∧ AltF hK σ d = c ∧
        a ≠ c ∧ b ≠ c ∧ a ≠ d ∧ b ≠ d ∧
        Interleaved (mkGenome hK S) a b c d

end Extract

/-! ## 3. The counterexample -/

section Counterexample

/-- `hK : 0 < 5`. -/
theorem hK5 : 0 < 5 := by decide

/-- **The word `S = 00102` on `K = 5` positions, over a three-letter
alphabet**, read at `L = 2` (so the vertices of the multigraph are the
single symbols). -/
def Sc5 : Fin 5 → Fin 3 := ![0, 0, 1, 0, 2]

/-- **The listing `σ = (1 3)(2 4)`, i.e. `σ 0 = 0`, `σ 1 = 3`, `σ 2 = 4`,
`σ 3 = 1`, `σ 4 = 2`.**  Its listing-successor is the permutation
`π = (0 3 4 1 2)` and its pairing is `AltF hK5 sig5 = [1, 3, 2, 0, 4]`. -/
def sig5 : Fin 5 ≃ Fin 5 := (Equiv.swap 1 3).trans (Equiv.swap 2 4)

/-- Decidability of the source's repeat and interlacing predicates on this
instance, so that the facts below are `decide`-closed.  These are
*instances*, added because the library does not provide them: `mkGenome` is
unfolded so that instance search does not get stuck on the structure
projections `.len`, `.window`, `.Preceding`.  No definition is changed. -/
local instance decIsRepeat5 (e : ℕ) (a b : Fin 5) :
    Decidable ((mkGenome hK5 Sc5).IsRepeat e a b) := by
  unfold Genome.IsRepeat Genome.Agree mkGenome
  exact inferInstance

local instance decIsTripleRepeat5 (e : ℕ) (a b c : Fin 5) :
    Decidable ((mkGenome hK5 Sc5).IsTripleRepeat e a b c) := by
  unfold Genome.IsTripleRepeat Genome.Agree mkGenome
  exact inferInstance

local instance decInterleaved5 (a b c d : Fin 5) :
    Decidable (Interleaved (mkGenome hK5 Sc5) a b c d) := by
  unfold Interleaved InOpenArc FourDistinct mkGenome
  exact inferInstance

/-- **It is an Eulerian cycle of the `(L-1)`-mer multigraph of `Sc5`.** -/
theorem cex_EulerianCycle : EulerianCycle hK5 2 Sc5 sig5 := by decide

/-- **Its vertex cycle is *not* the truth's own.**  The truth reads
`0, 0, 1, 0, 2` around the circle; `σ` reads `0, 0, 2, 0, 1`. -/
theorem cex_not_vertexCycleEq :
    ¬ VertexCycleEq hK5 2 Sc5 sig5 (Equiv.refl (α := Fin 5)) := by decide

/-- **The pairing `AltF hK5 sig5` is `[1, 3, 2, 0, 4]`**, spelled out. -/
theorem cex_AltF0 : AltF hK5 sig5 (0 : Fin 5) = 1 := by decide

theorem cex_AltF1 : AltF hK5 sig5 (1 : Fin 5) = 3 := by decide

theorem cex_AltF2 : AltF hK5 sig5 (2 : Fin 5) = 2 := by decide

theorem cex_AltF3 : AltF hK5 sig5 (3 : Fin 5) = 0 := by decide

theorem cex_AltF4 : AltF hK5 sig5 (4 : Fin 5) = 4 := by decide

/-- **It has NO chord at all**: `0 ↦ 1 ↦ 3 ↦ 0` is a 3-cycle, and `2` and `4`
are fixed.  So the pairing of the alternative traversal is *empty*, which is
why there is no interlaced pair to extract: the alternative traversal does not
swap at **any** vertex. -/
theorem cex_no_chord :
    ∀ (a b : Fin 5), AltF hK5 sig5 a = b → AltF hK5 sig5 b = a → a = b := by
  decide

set_option maxRecDepth 20000 in
/-- **No interlacing pair of chords**, in the `Fin`-indexed form the machine
checks.  (The quadruple is a single `Fintype` index so that one `decide`
suffices; `cex_no_interlaced_pair` below is the `¬ ∃` form.) -/
theorem cex_no_pair :
    ∀ q : Fin 5 × Fin 5 × Fin 5 × Fin 5,
      ¬ (AltF hK5 sig5 q.1 = q.2.1 ∧ AltF hK5 sig5 q.2.1 = q.1 ∧
        AltF hK5 sig5 q.2.2.1 = q.2.2.2 ∧ AltF hK5 sig5 q.2.2.2 = q.2.2.1 ∧
        q.1 ≠ q.2.2.1 ∧ q.2.1 ≠ q.2.2.1 ∧ q.1 ≠ q.2.2.2 ∧
        q.2.1 ≠ q.2.2.2 ∧
        Interleaved (mkGenome hK5 Sc5) q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  decide

/-- **... hence no interlaced pair**, which is the refuted conclusion. -/
theorem cex_no_interlaced_pair :
    ¬ ∃ (a b c d : Fin 5),
      AltF hK5 sig5 a = b ∧ AltF hK5 sig5 b = a ∧
      AltF hK5 sig5 c = d ∧ AltF hK5 sig5 d = c ∧
      a ≠ c ∧ b ≠ c ∧ a ≠ d ∧ b ≠ d ∧
      Interleaved (mkGenome hK5 Sc5) a b c d := by
  rintro ⟨a, b, c, d, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact cex_no_pair (a, b, c, d) ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- **The counterexample is primitive**, so primitivity is *not* the missing
hypothesis. -/
theorem cex_is_primitive : IsPrimitive hK5 Sc5 := by
  intro s hs hlt hsi
  interval_cases s
  · exact absurd (hsi 2) (by decide)
  · exact absurd (hsi 2) (by decide)
  · exact absurd (hsi 2) (by decide)
  · exact absurd (hsi 2) (by decide)

/-- **... and it carries a maximal triple repeat of length `1 = L - 1`** (the
letter `0` occurs at `0, 1, 3`, and both two-sided maximality clauses hold),
which is exactly the obstruction `P2` excludes.  So the missing hypothesis is
`P2` --- equivalently, here, the multiplicity cap `∀ v, deg v ≤ 2` --- and not
primitivity and not `SameExtension`. -/
theorem cex_triple_repeat :
    (mkGenome hK5 Sc5).IsTripleRepeat (1 : Fin 5) (0 : Fin 5) (1 : Fin 5)
      (3 : Fin 5) := by decide

/-- **THE REFUTATION.**  Over a three-letter alphabet no `L` satisfies
`InterlacedBranchPair`. -/
theorem interlacedBranchPair_refuted :
    ¬ (∀ (L : ℕ), InterlacedBranchPair (α := Fin 3) L) := by
  intro h
  rcases h 2 5 hK5 Sc5 sig5 (by decide) (by decide) cex_EulerianCycle
      cex_not_vertexCycleEq with ⟨a, b, c, d, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact cex_no_interlaced_pair ⟨a, b, c, d, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The refutation is minimal in `K` and in alphabet size.**  Below,
`no_foreign_eulerianCycle_Fin2_K2` states that over `Fin 2` at circle
size `2` **no** Eulerian cycle has a foreign vertex cycle, for *any* word and
listing and every read length index `L : Fin 2` (degenerate `L ≤ 1`
included).  Each is a complete `decide` over all `2^2` words and all `2!`
listings, so it is not a sample.  Together with `cex_*` (which supplies an
instance at `K = 5` over `Fin 3`) the counterexample is minimal: it needs a
three-letter alphabet and `K = 5`. -/
theorem no_foreign_eulerianCycle_Fin2_K2 :
    ∀ (L : Fin 2)
      (S : Fin 2 → Fin 2) (σ : Fin 2 ≃ Fin 2),
      EulerianCycle (hG := by decide) L.val S σ →
        VertexCycleEq (hG := by decide) L.val S σ (Equiv.refl (α := Fin 2)) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The refutation is minimal in `K` and in alphabet size.**  Below,
`no_foreign_eulerianCycle_Fin3_K2` states that over `Fin 3` at circle
size `2` **no** Eulerian cycle has a foreign vertex cycle, for *any* word and
listing and every read length index `L : Fin 2` (degenerate `L ≤ 1`
included).  Each is a complete `decide` over all `2^2` words and all `2!`
listings, so it is not a sample.  Together with `cex_*` (which supplies an
instance at `K = 5` over `Fin 3`) the counterexample is minimal: it needs a
three-letter alphabet and `K = 5`. -/
theorem no_foreign_eulerianCycle_Fin3_K2 :
    ∀ (L : Fin 2)
      (S : Fin 2 → Fin 3) (σ : Fin 2 ≃ Fin 2),
      EulerianCycle (hG := by decide) L.val S σ →
        VertexCycleEq (hG := by decide) L.val S σ (Equiv.refl (α := Fin 2)) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The refutation is minimal in `K` and in alphabet size.**  Below,
`no_foreign_eulerianCycle_Fin2_K3` states that over `Fin 2` at circle
size `3` **no** Eulerian cycle has a foreign vertex cycle, for *any* word and
listing and every read length index `L : Fin 3` (degenerate `L ≤ 1`
included).  Each is a complete `decide` over all `2^3` words and all `3!`
listings, so it is not a sample.  Together with `cex_*` (which supplies an
instance at `K = 5` over `Fin 3`) the counterexample is minimal: it needs a
three-letter alphabet and `K = 5`. -/
theorem no_foreign_eulerianCycle_Fin2_K3 :
    ∀ (L : Fin 3)
      (S : Fin 3 → Fin 2) (σ : Fin 3 ≃ Fin 3),
      EulerianCycle (hG := by decide) L.val S σ →
        VertexCycleEq (hG := by decide) L.val S σ (Equiv.refl (α := Fin 3)) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The refutation is minimal in `K` and in alphabet size.**  Below,
`no_foreign_eulerianCycle_Fin3_K3` states that over `Fin 3` at circle
size `3` **no** Eulerian cycle has a foreign vertex cycle, for *any* word and
listing and every read length index `L : Fin 3` (degenerate `L ≤ 1`
included).  Each is a complete `decide` over all `2^3` words and all `3!`
listings, so it is not a sample.  Together with `cex_*` (which supplies an
instance at `K = 5` over `Fin 3`) the counterexample is minimal: it needs a
three-letter alphabet and `K = 5`. -/
theorem no_foreign_eulerianCycle_Fin3_K3 :
    ∀ (L : Fin 3)
      (S : Fin 3 → Fin 3) (σ : Fin 3 ≃ Fin 3),
      EulerianCycle (hG := by decide) L.val S σ →
        VertexCycleEq (hG := by decide) L.val S σ (Equiv.refl (α := Fin 3)) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The refutation is minimal in `K` and in alphabet size.**  Below,
`no_foreign_eulerianCycle_Fin2_K4` states that over `Fin 2` at circle
size `4` **no** Eulerian cycle has a foreign vertex cycle, for *any* word and
listing and every read length index `L : Fin 4` (degenerate `L ≤ 1`
included).  Each is a complete `decide` over all `2^4` words and all `4!`
listings, so it is not a sample.  Together with `cex_*` (which supplies an
instance at `K = 5` over `Fin 3`) the counterexample is minimal: it needs a
three-letter alphabet and `K = 5`. -/
theorem no_foreign_eulerianCycle_Fin2_K4 :
    ∀ (L : Fin 4)
      (S : Fin 4 → Fin 2) (σ : Fin 4 ≃ Fin 4),
      EulerianCycle (hG := by decide) L.val S σ →
        VertexCycleEq (hG := by decide) L.val S σ (Equiv.refl (α := Fin 4)) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The refutation is minimal in `K` and in alphabet size.**  Below,
`no_foreign_eulerianCycle_Fin3_K4` states that over `Fin 3` at circle
size `4` **no** Eulerian cycle has a foreign vertex cycle, for *any* word and
listing and every read length index `L : Fin 4` (degenerate `L ≤ 1`
included).  Each is a complete `decide` over all `2^4` words and all `4!`
listings, so it is not a sample.  Together with `cex_*` (which supplies an
instance at `K = 5` over `Fin 3`) the counterexample is minimal: it needs a
three-letter alphabet and `K = 5`. -/
theorem no_foreign_eulerianCycle_Fin3_K4 :
    ∀ (L : Fin 4)
      (S : Fin 4 → Fin 3) (σ : Fin 4 ≃ Fin 4),
      EulerianCycle (hG := by decide) L.val S σ →
        VertexCycleEq (hG := by decide) L.val S σ (Equiv.refl (α := Fin 4)) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The refutation is minimal in `K` and in alphabet size.**  Below,
`no_foreign_eulerianCycle_Fin2_K5` states that over `Fin 2` at circle
size `5` **no** Eulerian cycle has a foreign vertex cycle, for *any* word and
listing and every read length index `L : Fin 5` (degenerate `L ≤ 1`
included).  Each is a complete `decide` over all `2^5` words and all `5!`
listings, so it is not a sample.  Together with `cex_*` (which supplies an
instance at `K = 5` over `Fin 3`) the counterexample is minimal: it needs a
three-letter alphabet and `K = 5`. -/
theorem no_foreign_eulerianCycle_Fin2_K5 :
    ∀ (L : Fin 5)
      (S : Fin 5 → Fin 2) (σ : Fin 5 ≃ Fin 5),
      EulerianCycle (hG := by decide) L.val S σ →
        VertexCycleEq (hG := by decide) L.val S σ (Equiv.refl (α := Fin 5)) := by
  decide

end Counterexample

end AssemblyP1.Issue94WitnessPair