import AssemblyP1.OrientedFinalRigidity
import AssemblyP1.SourceFaithfulIs
import AssemblyP1.BridgingBridge

/-!
# Oriented same-length ML: the model-boundary endpoint (issue #88)

This module is the *independent* part of the issue-#88 packet. It does three
things, and nothing else:

1. it identifies the `(L-1)`-window **node set** of a circular word with the
   image of `winPrefix` on its **window support**, and uses that to move the
   truth's balance equation from the candidate's node set to the truth's node
   set (`genomeNodes_of_support_eq`);
2. it converts a strict oriented same-length **spelled candidate** of the true
   length into exactly the hypotheses consumed by the mature rigidity chain
   `AssemblyP1.OrientedFinal.oriented_same_length_spectrum_rigidity` — no
   hypothesis is added or dropped (`candidate_circulation_hypotheses`,
   `same_length_candidate_spectrum_eq`);
3. it converts the resulting spectrum equality into the actual
   **spectrum-determined likelihood / maximizer endpoint** for two concrete
   oriented same-length objectives: the Medvedev–Brudno exact multinomial, and
   the §6.1 separable binomial approximation at the external length `N = G`.

Nothing here is `I_s`. The no-long-triple-repeat hypothesis is consumed as the
chain's own boundary premise `hno`, which the shared information-feasibility
layer (issue #90) is expected to discharge from the source-faithful `I_s`
predicate via note §3 Fact D. That implication is **not** formalized anywhere in
this repository, so `hno` is kept as an explicit premise in every theorem below
and never hidden. See `docs/oriented-same-length-ml-88.md` for the exact
reconciliation seam and for the residual-gap statement proved below.

## Modeling decisions recorded here (issue #88)

* **Orientation.** Read types are oriented single-strand length-`L` circular
  windows (`OrientedRigidity.window`); no reverse-complement collapse, matching
  the strict oriented same-length model settled for this packet and the
  requirement that genome equivalence and read-type convention be one coupled
  choice (`docs/source-notes/equivalence-and-tie-wellposedness.md`).
* **Candidate length is a type, not a hypothesis.** A candidate is a function
  `Fin G → α`, i.e. a circular genome of *the same length* `G` as the truth.
  In the exact objective `N(D) = G` is therefore intrinsic, exactly as
  `docs/ml-formalization-contract.md` Variant E requires; in the §6.1 objective
  the external size `N` is a separate explicit argument. Both are **restricted
  candidate universes** in the sense of the contract, and every theorem name and
  statement below says so.
* **Observation vs. realization.** The ML objective consumes only the observed
  read-type multiplicity `x : (Fin L → α) → ℕ`; a `Finset` of read starts is
  never used as the observation, and independently sampled starts that repeat
  must not be collapsed. The hypothesis that every observed read type is a
  window of the truth is an explicit premise of `truth_is_spelled_candidate`; it
  is the observable consequence of draws from the truth, and the layer that
  builds `x` from a genuine realization of latent starts is **not** formalized
  in this repository.
* **Spelled candidate.** `IsSameLengthSpelledCandidate` is the strict
  same-length spelling condition: the candidate's window support coincides with
  the truth's, and every observed read type is spelled by the candidate. Under
  §6.2 a spelled circuit of the read-overlap graph has exactly these two
  properties in the single-strand reading. The graph-theoretic
  circuit-to-support-adequacy correspondence is **not** formalized, so the
  restriction is named in the theorem statement and is *not* presented as
  quantification over every circular candidate. Section
  "`What this does not prove`" in the companion note is the explicit statement
  of the remaining gap.
* **Objectives kept separate.** Neither objective is advertised as *the*
  objective the 2016 sentence denotes, per
  `docs/source-notes/shomorony-ml-reference.md`. Exact multinomial and the §6.1
  separable approximation get separate definitions, separate congruence
  lemmas, and separate maximizer theorems; no theorem relates their maximizers.
* **The candidate space is characterized, not overstated.** Maximality is *not*
  quantified over all circular candidates. `spelled_observed_or_unsounded` and
  `same_length_exactLik_maximizer_or_residual_gap` prove the exact dichotomy:
  either the truth maximises the exact objective over the candidate, or the
  candidate spells every observed read type while having a *different* window
  support. That second case is the residual gap, and it is stated as such rather
  than hidden behind the spelled-candidate restriction.

* **Both conclusion schemas are stated separately.** `…_maximizer` is the
  maximizer-only reading; `…_unique_up_to_rotation_of_bbt` is the
  uniqueness-up-to-equivalence reading, with the external complete-spectrum
  (BBT) input kept as an explicit premise. Neither is designated as *the*
  published conjecture.
-/

namespace AssemblyP1.OrientedSameLengthML

open Finset
open BigOperators

set_option maxHeartbeats 800000

noncomputable section

/-! ## The observed read multiplicities

The observation is the multiplicity function `x : (Fin L → α) → ℕ`. Reads are
drawn independently, so two reads may share a latent start position; a set of
starts therefore does **not** determine `x`, and `x` is never recovered from a
`Finset` of starts in this module.
-/

/-- Observed oriented read-type multiplicities: `x w` is the number of the
`n` observed reads whose (oriented, single-strand) length-`L` word is `w`.
Repeated latent starts are counted repeatedly. -/
abbrev ObservedReads (α : Type) (L : ℕ) := (Fin L → α) → ℕ

/-- The number of observed reads. The objectives below take their sample size
from the observation rather than from a free parameter, so that the likelihood
is a function of the observation and the candidate only. -/
def totalReads {α : Type} [DecidableEq α] [Fintype α] {L : ℕ} (x : ObservedReads α L) : ℕ :=
  ∑ w, x w

/-- **Spectrum-determined oriented same-length exact-multinomial factor.**
`(d_D w / N(D)) ^ (x w)` with the candidate-intrinsic length `N(D) = G`; a read
type absent from the candidate contributes `0` when it was observed.

The parentheses matter: this is the whole base raised to the power `x w`, not
`d_D w / N(D) ^ (x w)`. -/
def exactFactor {α : Type} [DecidableEq α] [Fintype α] {G L : ℕ} (hG : 0 < G)
    (D : Fin G → α) (x : ObservedReads α L) (w : Fin L → α) : ℝ :=
  (((OrientedRigidity.specCount (L := L) hG D w : ℕ) : ℝ) / (G : ℝ)) ^ (x w)

/-- The oriented same-length exact Medvedev–Brudno multinomial objective, with
the observation-only positive factor `n! / ∏_w x w!` divided out (it does not
depend on the candidate and so does not affect any maximizer;
`exactLik_scale` below records the reinsertion). -/
def exactLik {α : Type} [DecidableEq α] [Fintype α] {G L : ℕ} (hG : 0 < G)
    (D : Fin G → α) (x : ObservedReads α L) : ℝ :=
  ∏ w : Fin L → α, exactFactor hG D x w

/-- The observation-only multinomial coefficient `n! / ∏_w x w!`, divided out
of `exactLik`. It is positive and candidate-independent, so the reinserted
probability is `exactLik * exactLik_scale`, which has exactly the same
maximizers. This is the "proved lemma, not silent deletion" requirement of
`docs/ml-formalization-contract.md` Variant E. -/
def exactLik_scale {α : Type} [DecidableEq α] [Fintype α] {L : ℕ} (x : ObservedReads α L) : ℝ :=
  ((totalReads x).factorial : ℝ) / ∏ w : Fin L → α, (x w).factorial

/-- One §6.1 binomial-marginal factor with external genome-size estimate `N`,
candidate count `d_D w` and observed count `x w`. The number of observed reads
of type `w` among the `n = totalReads x` reads is modelled as
`Binomial(n, d_D w / N)`, i.e. the separable/binomial approximation of
Medvedev–Brudno §6.1: the candidate-dependent `N(D)` is replaced by the
external `N`, and the count of *this* read type is the binomial variable.

Note that the binomial index is the **observed** count `x w`, not the candidate
count `d_D w`. -/
def binomialMarginal {α : Type} [DecidableEq α] [Fintype α] {G L : ℕ} (hG : 0 < G)
    (D : Fin G → α) (x : ObservedReads α L) (N : ℕ) (w : Fin L → α) : ℝ :=
  ((Nat.choose (totalReads x) (x w) : ℕ) : ℝ) *
    ((((OrientedRigidity.specCount (L := L) hG D w : ℕ) : ℝ) / (N : ℝ)) ^ (x w) *
      (1 - ((OrientedRigidity.specCount (L := L) hG D w : ℕ) : ℝ) / (N : ℝ)) ^
        (totalReads x - x w))

/-- The literal §6.1 product of binomial marginals over the oriented read-type
space, at the external size `N`. `N` is Medvedev–Brudno §6.1's external
genome-size estimate; it is an observation-level parameter, independent of the
candidate. -/
def binomialLik {α : Type} [DecidableEq α] [Fintype α] {G L : ℕ} (hG : 0 < G)
    (D : Fin G → α) (x : ObservedReads α L) (N : ℕ) : ℝ :=
  ∏ w : Fin L → α, binomialMarginal hG D x N w

/-! ## Windows, support, and node sets of an arbitrary same-length candidate -/

/-- The `winPrefix` of a length-`L` window is the `(L-1)`-window at the same
start. This is a local copy of the private lemma `OrientedRigidity.winPrefix_window`,
needed because this module reasons about the node set of an *arbitrary*
candidate, not only of the truth. -/
private lemma winPrefix_window' {α : Type} {G L : ℕ} (hG : 0 < G)
    (D : Fin G → α) (r : Fin G) :
    OrientedRigidity.winPrefix (OrientedRigidity.window (L := L) hG D r) =
      OrientedRigidity.nodeWindow (L := L) hG D r := by
  funext d
  rfl

/-- The `(L-1)`-window node set is the image of the prefix map on the window
support. -/
theorem genomeNodes_eq_image_winPrefix {α : Type} [DecidableEq α] [Fintype α] {G L : ℕ}
    (hG : 0 < G) (D : Fin G → α) :
    OrientedRigidity.genomeNodes (L := L) hG D =
      (OrientedRigidity.support (L := L) hG D).image
        (OrientedRigidity.winPrefix (α := α) (L := L)) := by
  ext k
  constructor
  · intro hk
    simp only [OrientedRigidity.genomeNodes, Finset.mem_image] at hk
    obtain ⟨r, _, rfl⟩ := hk
    exact Finset.mem_image.mpr
      ⟨OrientedRigidity.window (L := L) hG D r,
        Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩, winPrefix_window' hG D r⟩
  · intro hk
    simp only [Finset.mem_image] at hk
    obtain ⟨w, hw, hkw⟩ := hk
    simp only [OrientedRigidity.support, Finset.mem_image] at hw
    obtain ⟨r, _, rfl⟩ := hw
    subst hkw
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _,
      winPrefix_window' hG D r⟩

/-- Equal window support implies equal node set: the node set is determined by
the support. This is the piece needed to move `truth_balanced` from a candidate
to the truth's node set. -/
theorem genomeNodes_of_support_eq {α : Type} [DecidableEq α] [Fintype α] {G L : ℕ}
    (hG : 0 < G) (D S : Fin G → α)
    (h : OrientedRigidity.support (L := L) hG D =
      OrientedRigidity.support (L := L) hG S) :
    OrientedRigidity.genomeNodes (L := L) hG D =
      OrientedRigidity.genomeNodes (L := L) hG S := by
  rw [genomeNodes_eq_image_winPrefix, genomeNodes_eq_image_winPrefix, h]

/-- A window of `D` is in `D`'s support, and conversely a supported window is
some window of `D`. -/
theorem mem_support_iff_window {α : Type} [DecidableEq α] [Fintype α] {G L : ℕ}
    (hG : 0 < G) (D : Fin G → α) (w : Fin L → α) :
    w ∈ OrientedRigidity.support (L := L) hG D ↔ ∃ r : Fin G,
      OrientedRigidity.window (L := L) hG D r = w := by
  simp only [OrientedRigidity.support, Finset.mem_image]
  constructor
  · rintro ⟨r, _, rfl⟩
    exact ⟨r, rfl⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r, Finset.mem_univ _, rfl⟩

/-- **A word's spectrum is positive exactly on its window support.** -/
theorem specCount_pos_iff {α : Type} [DecidableEq α] [Fintype α] {G L : ℕ} (hG : 0 < G)
    (D : Fin G → α) (w : Fin L → α) :
    0 < OrientedRigidity.specCount (L := L) hG D w ↔
      w ∈ OrientedRigidity.support (L := L) hG D := by
  constructor
  · intro hw
    have hcard : 0 < (Finset.univ.filter
        (fun r' : Fin G => OrientedRigidity.window (L := L) hG D r' = w)).card := hw
    obtain ⟨r, hr⟩ := Finset.card_pos.mp hcard
    exact (mem_support_iff_window hG D w).mpr
      ⟨r, (Finset.mem_filter.mp hr).2⟩
  · intro hw
    obtain ⟨r, hwr⟩ := mem_support_iff_window hG D w |>.mp hw
    have hmem : r ∈ (Finset.univ.filter
        (fun r' : Fin G => OrientedRigidity.window (L := L) hG D r' = w)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwr⟩
    exact Finset.card_pos.mpr ⟨r, hmem⟩

/-! ## The strict oriented same-length spelled-candidate condition -/

/-- **Strict oriented same-length spelled candidate.** `D` is a circular word of
the same length `G` as the truth whose walk through the read-overlap graph is
spelled: its length-`L` window support coincides with the truth's (equivalently,
it uses only read-molecule edges and spells every window of the truth), and
every observed read type occurs in `D`.

This is a **restricted candidate universe**, named as such in every theorem that
uses it, per `docs/ml-formalization-contract.md` constraint 8. -/
def IsSameLengthSpelledCandidate {α : Type} [DecidableEq α] [Fintype α] {G L : ℕ}
    (hG : 0 < G) (S D : Fin G → α) (x : ObservedReads α L) : Prop :=
  OrientedRigidity.support (L := L) hG D = OrientedRigidity.support (L := L) hG S ∧
    ∀ w : Fin L → α, 0 < x w → 0 < OrientedRigidity.specCount (L := L) hG D w

/-- The candidate's support equality, projected. -/
theorem support_eq_of_spelled {α : Type} [DecidableEq α] [Fintype α] {G L : ℕ} (hG : 0 < G)
    {S D : Fin G → α} {x : ObservedReads α L}
    (h : IsSameLengthSpelledCandidate hG S D x) :
    OrientedRigidity.support (L := L) hG D = OrientedRigidity.support (L := L) hG S := h.1

/-- Every observed read type is spelled by the candidate. -/
theorem spells_observed_of_spelled {α : Type} [DecidableEq α] [Fintype α] {G L : ℕ}
    (hG : 0 < G) {S D : Fin G → α} {x : ObservedReads α L}
    (h : IsSameLengthSpelledCandidate hG S D x) :
    ∀ w : Fin L → α, 0 < x w → 0 < OrientedRigidity.specCount (L := L) hG D w := h.2

/-! ## From a spelled candidate to the rigidity chain's hypotheses -/

/-- **Support/positivity of the candidate's own spectrum, read on the truth's
support.** -/
theorem spec_support_iff {α : Type} [DecidableEq α] [Fintype α] {G L : ℕ} (hG : 0 < G)
    {S D : Fin G → α} (h : OrientedRigidity.support (L := L) hG D =
      OrientedRigidity.support (L := L) hG S) (w : Fin L → α) :
    w ∈ OrientedRigidity.support (L := L) hG S ↔ 0 < OrientedRigidity.specCount (L := L) hG D w := by
  constructor
  · intro hw
    have hwD : w ∈ OrientedRigidity.support (L := L) hG D := h.symm ▸ hw
    exact (specCount_pos_iff hG D w).mpr hwD
  · intro hw
    have hwD : w ∈ OrientedRigidity.support (L := L) hG D :=
      (specCount_pos_iff hG D w).mp hw
    exact h ▸ hwD

/-- **The candidate's own spectrum is a positive balanced circulation of total
mass `G` on the truth's window support.** This is the interface between the
model-level spelled-candidate condition and the abstract rigidity chain: no
hypotheses beyond spelledness are added, and no hypothesis is dropped. -/
theorem candidate_circulation_hypotheses {α : Type} [DecidableEq α] [Fintype α] {G L : ℕ}
    (hG : 0 < G) (S D : Fin G → α) (x : ObservedReads α L)
    (hD : IsSameLengthSpelledCandidate hG S D x) :
    (∀ w, w ∈ OrientedRigidity.support (L := L) hG S ↔
        0 < OrientedRigidity.specCount (L := L) hG D w) ∧
      OrientedRigidity.Balanced (OrientedRigidity.winPrefix (α := α) (L := L))
        (OrientedRigidity.winSuffix (α := α) (L := L))
        (OrientedRigidity.genomeNodes (L := L) hG S)
        (OrientedRigidity.support (L := L) hG S) (OrientedRigidity.specCount (L := L) hG D) ∧
      ∑ w ∈ (OrientedRigidity.support (L := L) hG S :
          Finset (Fin L → α)), OrientedRigidity.specCount (L := L) hG D w = G := by
  have hsup := support_eq_of_spelled hG hD
  have hnodes := genomeNodes_of_support_eq hG D S hsup
  refine ⟨spec_support_iff hG hsup, ?_, ?_⟩
  · have hbal := OrientedRigidity.truth_balanced (L := L) hG D
    rwa [hnodes, hsup] at hbal
  · have htot := OrientedRigidity.truth_total (L := L) hG D
    rwa [hsup] at htot

/-- **Spectrum rigidity for a spelled candidate.** A strict oriented
same-length spelled candidate has exactly the truth's spectrum, under the
chain's no-long-triple-repeat boundary premise. -/
theorem same_length_candidate_spectrum_eq {α : Type} [DecidableEq α] [Fintype α]
    {G L : ℕ} (hG : 0 < G) (S D : Fin G → α) (hL : 2 ≤ L) (hLG : L ≤ G)
    (hno : ¬ RepeatAdapter.HasLongTripleRepeat hG S L)
    (x : ObservedReads α L) (hD : IsSameLengthSpelledCandidate hG S D x) :
    ∀ w : Fin L → α, OrientedRigidity.specCount (L := L) hG D w =
      OrientedRigidity.specCount (L := L) hG S w := by
  obtain ⟨hsup, hbal, htot⟩ :=
    candidate_circulation_hypotheses hG S D x hD
  exact OrientedFinal.oriented_same_length_spectrum_rigidity hG S hL hLG hno
    (OrientedRigidity.specCount (L := L) hG D) hsup hbal htot

/-! ## Candidates that miss an observed read type are dominated, with no
    spelledness assumption at all

The remaining gap between the spelled candidate class and *all* same-length
candidates is confined to candidates that spell every observed read type. The
cases in which a candidate does not are settled here for arbitrary `D`, with no
support condition whatsoever. -/

/-- The exact objective is nonnegative. -/
theorem exactLik_nonneg {α : Type} [DecidableEq α] [Fintype α] {G L : ℕ} (hG : 0 < G)
    (D : Fin G → α) (x : ObservedReads α L) : 0 ≤ exactLik hG D x := by
  unfold exactLik
  refine Finset.prod_nonneg fun w _ => ?_
  exact pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg G)) _

/-- **Unsounded candidates have zero exact likelihood.** If the candidate does
not contain an observed read type, the exact multinomial likelihood is `0`. -/
theorem exactLik_eq_zero_of_unspelled_observed {α : Type} [DecidableEq α] [Fintype α]
    {G L : ℕ} (hG : 0 < G) (D : Fin G → α) (x : ObservedReads α L)
    (h : ∃ w : Fin L → α, 0 < x w ∧ OrientedRigidity.specCount (L := L) hG D w = 0) :
    exactLik hG D x = 0 := by
  obtain ⟨w, hxw, hd⟩ := h
  have hzero : exactFactor hG D x w = 0 := by
    unfold exactFactor
    rw [hd, Nat.cast_zero, zero_div, zero_pow (Nat.ne_of_gt hxw)]
  unfold exactLik
  exact Finset.prod_eq_zero (Finset.mem_univ w) hzero

/-- **Maximality against unsounded candidates, for arbitrary same-length
candidates.** No spelledness, no support condition: only "the candidate misses
some observed read type". -/
theorem exactLik_le_of_unspelled_observed {α : Type} [DecidableEq α] [Fintype α]
    {G L : ℕ} (hG : 0 < G) (S D : Fin G → α) (x : ObservedReads α L)
    (h : ∃ w : Fin L → α, 0 < x w ∧ OrientedRigidity.specCount (L := L) hG D w = 0) :
    exactLik hG D x ≤ exactLik hG S x :=
  le_trans (le_of_eq (exactLik_eq_zero_of_unspelled_observed hG D x h))
    (exactLik_nonneg hG S x)

/-- **Spelled or unsounded: the candidate dichotomy, in the only form in which
it is true.** Every same-length candidate either spells every observed read
type, or misses one of them. This is *not* the same as being a
`IsSameLengthSpelledCandidate`: that predicate additionally requires equality of
the whole window supports, which no observation can certify. -/
theorem spelled_observed_or_unsounded {α : Type} [DecidableEq α] [Fintype α]
    {G L : ℕ} (hG : 0 < G) (D : Fin G → α) (x : ObservedReads α L) :
    (∀ w : Fin L → α, 0 < x w → 0 < OrientedRigidity.specCount (L := L) hG D w) ∨
      (∃ w : Fin L → α, 0 < x w ∧
        OrientedRigidity.specCount (L := L) hG D w = 0) := by
  classical
  by_cases hpos : ∀ w : Fin L → α, 0 < x w →
      0 < OrientedRigidity.specCount (L := L) hG D w
  · exact Or.inl hpos
  · have hex : ∃ w : Fin L → α, ¬ (0 < x w →
        0 < OrientedRigidity.specCount (L := L) hG D w) := by
      by_contra hc
      exact hpos fun w => of_not_not (not_exists.1 hc w)
    obtain ⟨w, hn⟩ := hex
    push Not at hn
    exact Or.inr ⟨w, hn.1, by omega⟩

/-! ## The actual ML endpoint -/

/-- Two candidates with the same oriented spectrum have the same exact
multinomial objective value. -/
theorem exactLik_congr_of_specCount_eq {α : Type} [DecidableEq α] [Fintype α] {G L : ℕ}
    (hG : 0 < G) {D E : Fin G → α} {x : ObservedReads α L}
    (h : ∀ w : Fin L → α, OrientedRigidity.specCount (L := L) hG D w =
      OrientedRigidity.specCount (L := L) hG E w) :
    exactLik hG D x = exactLik hG E x := by
  unfold exactLik
  refine Finset.prod_congr rfl fun w _ => ?_
  unfold exactFactor
  rw [h w]

/-- Two candidates with the same oriented spectrum have the same §6.1
binomial-marginal objective value at the same external size `N`. -/
theorem binomialLik_congr_of_specCount_eq {α : Type} [DecidableEq α] [Fintype α]
    {G L : ℕ} (hG : 0 < G) {D E : Fin G → α} {x : ObservedReads α L} (N : ℕ)
    (h : ∀ w : Fin L → α, OrientedRigidity.specCount (L := L) hG D w =
      OrientedRigidity.specCount (L := L) hG E w) :
    binomialLik hG D x N = binomialLik hG E x N := by
  unfold binomialLik
  refine Finset.prod_congr rfl fun w _ => ?_
  unfold binomialMarginal
  rw [h w]

/-- The number of observed reads is determined by the observation, as the
§6.1 marginals require. -/
theorem totalReads_congr {α : Type} [DecidableEq α] [Fintype α] {L : ℕ}
    {x x' : ObservedReads α L} (h : ∀ w : Fin L → α, x w = x' w) :
    totalReads x = totalReads x' := by
  unfold totalReads
  exact Finset.sum_congr rfl fun w _ => h w

/-- **The scale factor depends only on the observation.** Reinserting the
multinomial coefficient cannot move a candidate, because the coefficient is a
function of `x` alone. -/
theorem exactLik_scale_congr {α : Type} [DecidableEq α] [Fintype α] {L : ℕ}
    {x x' : ObservedReads α L} (h : ∀ w : Fin L → α, x w = x' w) :
    exactLik_scale x = exactLik_scale x' := by
  have hn := totalReads_congr h
  unfold exactLik_scale
  rw [hn]
  have hp : (∏ w : Fin L → α, (x w).factorial) = ∏ w : Fin L → α, (x' w).factorial :=
    Finset.prod_congr rfl fun w _ => by rw [h w]
  rw [hp]

/-- **The reinserted multinomial coefficient is positive.** This is the
elementary arithmetic fact that makes the reinsertion in
`exactLik_scale_le_iff` legitimate, so the divided-out objective and the full
exact probability are proved to have the same comparisons, not merely the same
scale factor. -/
theorem exactLik_scale_pos {α : Type} [DecidableEq α] [Fintype α] {L : ℕ}
    (x : ObservedReads α L) : 0 < exactLik_scale x := by
  unfold exactLik_scale
  exact div_pos (Nat.cast_pos.mpr (Nat.factorial_pos _))
    (by positivity)

/-- The reinsertion step with positivity kept as an explicit argument, so that
the order-theoretic step is visible independently of the arithmetic. -/
theorem exactLik_scale_le_iff_of_pos {α : Type} [DecidableEq α] [Fintype α]
    {G L : ℕ} (hG : 0 < G) (S D : Fin G → α) (x : ObservedReads α L)
    (hc : 0 < exactLik_scale x) :
    exactLik hG D x * exactLik_scale x ≤ exactLik hG S x * exactLik_scale x ↔
      exactLik hG D x ≤ exactLik hG S x := by
  constructor
  · intro h
    exact le_of_mul_le_mul_of_pos_right h hc
  · intro h
    exact mul_le_mul_of_nonneg_right h (le_of_lt hc)

/-- **Reinserting the multinomial coefficient preserves the comparison between
two candidates.** In an ordered field, multiplication by a positive constant is
order-reflecting, so the maximizers of `exactLik * c` are exactly the maximizers
of `exactLik`; `exactLik_scale_pos` supplies the positivity, so the divided-out
objective and the full exact probability are proved to induce the same
comparisons. -/
theorem exactLik_scale_le_iff {α : Type} [DecidableEq α] [Fintype α] {G L : ℕ} (hG : 0 < G)
    (S D : Fin G → α) (x : ObservedReads α L) :
    exactLik hG D x * exactLik_scale x ≤ exactLik hG S x * exactLik_scale x ↔
      exactLik hG D x ≤ exactLik hG S x :=
  exactLik_scale_le_iff_of_pos hG S D x (exactLik_scale_pos x)

/-- **Oriented same-length ML maximizer theorem over spelled candidates
(exact multinomial objective, candidate length `G` intrinsic).** Under the
chain's no-long-triple-repeat premise, the true genome is a maximum of the
oriented same-length exact Medvedev–Brudno multinomial likelihood over all
strict oriented same-length spelled candidates. -/
theorem same_length_exactLik_maximizer {α : Type} [DecidableEq α] [Fintype α]
    {G L : ℕ} (hG : 0 < G) (S D : Fin G → α) (hL : 2 ≤ L) (hLG : L ≤ G)
    (hno : ¬ RepeatAdapter.HasLongTripleRepeat hG S L)
    (x : ObservedReads α L) (hD : IsSameLengthSpelledCandidate hG S D x) :
    exactLik hG D x ≤ exactLik hG S x :=
  le_of_eq (exactLik_congr_of_specCount_eq hG
    (same_length_candidate_spectrum_eq hG S D hL hLG hno x hD))

/-- **Oriented same-length ML maximizer theorem over spelled candidates
(§6.1 binomial-marginal approximation at the external size `N`).** -/
theorem same_length_binomialLik_maximizer {α : Type} [DecidableEq α] [Fintype α]
    {G L : ℕ} (hG : 0 < G) (S D : Fin G → α) (hL : 2 ≤ L) (hLG : L ≤ G)
    (hno : ¬ RepeatAdapter.HasLongTripleRepeat hG S L)
    (x : ObservedReads α L) (N : ℕ)
    (hD : IsSameLengthSpelledCandidate hG S D x) :
    binomialLik hG D x N ≤ binomialLik hG S x N :=
  le_of_eq (binomialLik_congr_of_specCount_eq hG N
    (same_length_candidate_spectrum_eq hG S D hL hLG hno x hD))

/-- Both objectives, at the same-length external size `N = G`, in one
statement. -/
theorem same_length_ML_maximizer_both {α : Type} [DecidableEq α] [Fintype α] {G L : ℕ}
    (hG : 0 < G) (S D : Fin G → α) (hL : 2 ≤ L) (hLG : L ≤ G)
    (hno : ¬ RepeatAdapter.HasLongTripleRepeat hG S L)
    (x : ObservedReads α L)
    (hD : IsSameLengthSpelledCandidate hG S D x) :
    exactLik hG D x ≤ exactLik hG S x ∧
      binomialLik hG D x G ≤ binomialLik hG S x G :=
  ⟨same_length_exactLik_maximizer hG S D hL hLG hno x hD,
    same_length_binomialLik_maximizer hG S D hL hLG hno x G hD⟩

/-- **Exact maximality, or the residual gap, stated exactly.** For *any*
same-length candidate `D` — no spelledness, no support condition — one of the
following holds: the truth maximises the exact objective over `D`, or `D` spells
every observed read type while having a *different* window support from the
truth.

This is the honest form of the "over all candidates" statement. The second
disjunct is the residual gap: such a candidate is not a spelled circuit of the
read-overlap graph in the sense of `IsSameLengthSpelledCandidate`, the rigidity
chain's balance equation cannot be moved to the truth's node set without
`genomeNodes_of_support_eq`, and no theorem here settles it. It is stated rather
than hidden; `docs/oriented-same-length-ml-88.md` discusses it. -/
theorem same_length_exactLik_maximizer_or_residual_gap {α : Type} [DecidableEq α]
    [Fintype α] {G L : ℕ} (hG : 0 < G) (S D : Fin G → α) (hL : 2 ≤ L) (hLG : L ≤ G)
    (hno : ¬ RepeatAdapter.HasLongTripleRepeat hG S L)
    (x : ObservedReads α L) :
    exactLik hG D x ≤ exactLik hG S x ∨
      ((∀ w : Fin L → α, 0 < x w →
          0 < OrientedRigidity.specCount (L := L) hG D w) ∧
        OrientedRigidity.support (L := L) hG D ≠
          OrientedRigidity.support (L := L) hG S) := by
  by_cases hD : IsSameLengthSpelledCandidate hG S D x
  · exact Or.inl (same_length_exactLik_maximizer hG S D hL hLG hno x hD)
  · rcases spelled_observed_or_unsounded hG D x with hpos | hun
    · exact Or.inr ⟨hpos, fun hsup => hD ⟨hsup, hpos⟩⟩
    · exact Or.inl (exactLik_le_of_unspelled_observed hG S D x hun)


/-! ## The second conclusion schema, stated separately: uniqueness up to
    cyclic shift, conditional on the external complete-spectrum input

`docs/ml-formalization-contract.md` constraint 7 requires the maximizer-only and
uniqueness-up-to-equivalence conclusions to be separate propositions. The
complete-spectrum (Bresler–Bresler–Tse) step is **not** formalized in this
repository, so it appears here as the explicit premise `hBBT`; see
`docs/exact-same-length-spectrum-fibre-count.md` for what the fibre count would
take to discharge it. -/

/-- **Same-length uniqueness up to cyclic shift, conditional on the external
complete-spectrum input.** The genome equivalence is `OrientedFinal.IsCyclicShift`
(rotation only; no reverse-complement identification is introduced, matching the
oriented read-type convention). -/
theorem same_length_unique_up_to_rotation_of_bbt {α : Type} [DecidableEq α] [Fintype α]
    {G L : ℕ} (hG : 0 < G) (S D : Fin G → α) (hL : 2 ≤ L) (hLG : L ≤ G)
    (hno : ¬ RepeatAdapter.HasLongTripleRepeat hG S L)
    (x : ObservedReads α L) (hD : IsSameLengthSpelledCandidate hG S D x)
    (hBBT : ∀ T : Fin G → α,
      (∀ w : Fin L → α, OrientedRigidity.specCount (L := L) hG T w =
        OrientedRigidity.specCount (L := L) hG S w) →
          OrientedFinal.IsCyclicShift hG T S) :
    OrientedFinal.IsCyclicShift hG D S :=
  hBBT D (same_length_candidate_spectrum_eq hG S D hL hLG hno x hD)

/-- **The two conclusion schemas together**, for the exact objective, over the
spelled same-length candidate class. The candidate `D` is not a hypothesis here:
the statement is already a quantification over every same-length candidate `T`,
so naming one particular `D` (and a hypothesis about it that the conclusion
never uses) would be redundant. -/
theorem same_length_maximality_and_rotation_uniqueness_of_bbt {α : Type}
    [DecidableEq α] [Fintype α] {G L : ℕ} (hG : 0 < G) (S : Fin G → α) (hL : 2 ≤ L)
    (hLG : L ≤ G) (hno : ¬ RepeatAdapter.HasLongTripleRepeat hG S L)
    (x : ObservedReads α L)
    (hBBT : ∀ T : Fin G → α,
      (∀ w : Fin L → α, OrientedRigidity.specCount (L := L) hG T w =
        OrientedRigidity.specCount (L := L) hG S w) →
          OrientedFinal.IsCyclicShift hG T S) :
    (∀ T : Fin G → α, IsSameLengthSpelledCandidate hG S T x →
        exactLik hG T x ≤ exactLik hG S x) ∧
      (∀ T : Fin G → α, IsSameLengthSpelledCandidate hG S T x →
        exactLik hG T x = exactLik hG S x → OrientedFinal.IsCyclicShift hG T S) :=
  ⟨fun T hT => same_length_exactLik_maximizer hG S T hL hLG hno x hT,
    fun T hT _ => same_length_unique_up_to_rotation_of_bbt hG S T hL hLG hno
      x hT hBBT⟩

/-! ## The observation is not a set of starts -/

/-- The likelihood layer consumes only `x`: it never inspects a realization.
Two observations with equal multiplicities score every candidate equally, even
when they come from different latent placements. -/
theorem objective_depends_only_on_observation {α : Type} [DecidableEq α] [Fintype α]
    {G L : ℕ} (hG : 0 < G) (D : Fin G → α) (x x' : ObservedReads α L) (N : ℕ)
    (h : ∀ w : Fin L → α, x w = x' w) :
    exactLik hG D x = exactLik hG D x' ∧
      binomialLik hG D x N = binomialLik hG D x' N := by
  constructor
  · unfold exactLik
    refine Finset.prod_congr rfl fun w _ => ?_
    unfold exactFactor
    rw [h w]
  · unfold binomialLik
    have hn := totalReads_congr h
    refine Finset.prod_congr rfl fun w _ => ?_
    unfold binomialMarginal
    rw [hn, h w]

/-! ## Non-vacuity: the truth is itself a spelled candidate -/

/-- If every observed read type is a window of the truth — the observable
consequence of a realization whose reads are drawn from the truth — then the
truth satisfies the spelled-candidate condition, so the maximizer statement
ranges over a nonempty candidate class. The realization-level version of this
hypothesis is discharged in `AssemblyP1.OrientedSameLengthRealization`. -/
theorem truth_is_spelled_candidate {α : Type} [DecidableEq α] [Fintype α] {G L : ℕ}
    (hG : 0 < G) (S : Fin G → α) (x : ObservedReads α L)
    (hobs : ∀ w : Fin L → α, 0 < x w → w ∈ OrientedRigidity.support (L := L) hG S) :
    IsSameLengthSpelledCandidate hG S S x :=
  ⟨rfl, fun w hw => by
    have hw' := OrientedRigidity.truth_pos_on_support (L := L) hG S w (hobs w hw)
    exact Nat.lt_of_lt_of_le (by omega) hw'⟩


/-! ## Reading a genuine realization into observed multiplicities

A *realization* is a list of `n` latent read starts `ρ : Fin n → Fin G`.
`observedOf` turns it into the observed read-type multiplicity function by
counting, so that two reads landing on the same start are counted twice. This
is the layer that was previously missing: the earlier endpoint
`truth_is_spelled_candidate` took "every observed read type is a window of the
truth" as a *hypothesis*, which is exactly the observable consequence of drawing
reads from the truth. It is now a theorem, and the endpoint below is phrased
from a realization rather than from that hypothesis. -/

/-- A realization of `n` reads: the latent start of each observed read. -/
abbrev Realization (G n : ℕ) := Fin n → Fin G

/-- The observed read-type multiplicities of a realization: `x w` is the number
of the `n` realized reads whose oriented length-`L` word is `w`. Repeated latent
starts are counted repeatedly, and a `Finset` of starts is never used as the
observation. -/
def observedOf {α : Type} [DecidableEq α] [Fintype α] {G L n : ℕ} (hG : 0 < G)
    (S : Fin G → α) (ρ : Realization G n) : ObservedReads α L :=
  fun w => ∑ i : Fin n, if OrientedRigidity.window (L := L) hG S (ρ i) = w then 1 else 0

/-- **Every observed read type is a window of the truth.** This is the
observable consequence of a realization whose reads were drawn from the truth,
and it is what used to be an explicit premise of the endpoint. -/
theorem observedOf_mem_support {α : Type} [DecidableEq α] [Fintype α] {G L n : ℕ}
    (hG : 0 < G) (S : Fin G → α) (ρ : Realization G n) (w : Fin L → α)
    (hw : 0 < observedOf (L := L) hG S ρ w) :
    w ∈ OrientedRigidity.support (L := L) hG S := by
  classical
  by_contra hn
  have hz : observedOf (L := L) hG S ρ w = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    refine if_neg ?_
    intro he
    exact hn (Finset.mem_image.mpr ⟨ρ i, Finset.mem_univ _, he⟩)
  omega

/-- **The truth is a strict same-length spelled candidate of its own
realization**, with no observation-level hypothesis: the support clause is
`rfl` and the spelling clause is `observedOf_mem_support`. -/
theorem truth_is_spelled_candidate_of_realization {α : Type} [DecidableEq α]
    [Fintype α] {G L n : ℕ} (hG : 0 < G) (S : Fin G → α) (ρ : Realization G n) :
    IsSameLengthSpelledCandidate (L := L) hG S S (observedOf hG S ρ) :=
  ⟨rfl, fun w hw =>
    (specCount_pos_iff hG S w).mpr (observedOf_mem_support hG S ρ w hw)⟩

/-! ## A positive boundary: covering constant reads force a constant genome

This is the theorem-level counterpart of the computational observation that the
"constant all-zero competitor" family of apparent counterexamples is impossible.
If every realized read returns the same symbol, and the realized starts cover
the genome, then the genome is itself constant, so the truth spells every one
of its length-`L` windows and its exact likelihood is `1`, the maximum value of
the objective. Hence **no counterexample to the same-length exact ML claim can
have a single-read-type observation**, for any read length — not because of any
repeat-theoretic consideration, but because of clause 1 of `I_s` alone. -/

/-- **Covering constant reads force a constant genome.** If every realized read
at every start in `R` returns the symbol `v`, and the realized starts cover the
genome, then every position carries `v`. -/
theorem covering_constant_reads_is_constant {α : Type} [DecidableEq α] {G L : ℕ}
    (hG : 0 < G) (hLG : L ≤ G) (S : Fin G → α) (v : α) (R : Finset (Fin G))
    (hobs : ∀ r ∈ R, ∀ d : Fin L, OrientedRigidity.cyc hG S (r.val + d.val) = v)
    (hcov : ∀ p : Fin G, ∃ r ∈ R, ∃ d : Fin L, p.val = (r.val + d.val) % G) :
    ∀ i : Fin G, OrientedRigidity.cyc hG S i.val = v := by
  intro i
  obtain ⟨r, hr, d, hd⟩ := hcov i
  have h1 : OrientedRigidity.cyc hG S i.val
      = OrientedRigidity.cyc hG S (r.val + d.val) := by
    unfold OrientedRigidity.cyc
    have hmod : i.val % G = (r.val + d.val) % G := by
      rw [hd, Nat.mod_mod]
    exact congrArg S (Fin.ext hmod)
  rw [h1]
  exact hobs r hr d

/-! ## The honest end-to-end endpoint, from `InformationFeasible`

The theorem below is the strongest statement of the #88 target that is *true*
in this repository. Its premise is a genuine realization together with **full
source-faithful** information feasibility of the set of distinct latent starts,
plus the sharp nondegeneracy condition on the truth; its conclusion is the
actual same-length exact Medvedev–Brudno objective. The wraparound regime that
`AssemblyP1.BridgingBridge` shows `I_s` cannot exclude is an explicit premise
here, and is *not* assumed away.

`AssemblyP1.SameLengthExactMLCounterexample` shows that without the
nondegeneracy — and, more decisively, without restricting the candidate class —
the same conclusion is false, and pins down exactly where the boundary lies. -/

/-- The `Genome` of a same-length truth, for the shared bridging layer. -/
def asGenome {α : Type} {G : ℕ} (hG : 0 < G) (S : Fin G → α) :
    SourceFaithfulIs.Genome α := ⟨G, hG, S⟩

/-- **The end-to-end endpoint.** Let `ρ` be a genuine realization of `n` reads on
the truth `S`, let `R` be a set of latent starts containing all of them, and
suppose `InformationFeasible (asGenome hG S) L R` at full strength. If the
truth carries no triple repeat in the bridging-permitted regime
`max (L - 1) (G - L) ≤ e`, then the truth maximises the oriented same-length
exact multinomial objective over the strict spelled same-length candidate class.

The hypothesis side goes through `AssemblyP1.BridgingBridge`, which discharges
`¬ HasLongTripleRepeat` from `InformationFeasible` plus exactly that
nondegeneracy; the conclusion side is the spectrum-rigidity chain composed with
the congruence lemmas of this module. -/
theorem informationFeasible_exactLik_maximizer
    {α : Type} [DecidableEq α] [Fintype α] {G L n : ℕ} (hG : 0 < G) (hL2 : 2 ≤ L)
    (hLG : L ≤ G) (S : Fin G → α) (ρ : Realization G n)
    (R : Finset (Fin G))
    (hR : ∀ i : Fin n, ρ i ∈ R)
    (hfeas : SourceFaithfulIs.InformationFeasible (asGenome hG S) L R)
    (hnr : BridgingBridge.SharpNoLongTripleRepeat (L := L) (S := asGenome hG S))
    (D : Fin G → α)
    (hD : IsSameLengthSpelledCandidate (L := L) hG S D (observedOf hG S ρ)) :
    exactLik (L := L) hG D (observedOf hG S ρ)
      ≤ exactLik (L := L) hG S (observedOf hG S ρ) := by
  have hno : ¬ RepeatAdapter.HasLongTripleRepeat hG S L :=
    BridgingBridge.informationFeasible_sharp_no_long_triple_repeat hL2 hLG hfeas hnr
  exact same_length_exactLik_maximizer hG S D hL2 hLG hno (observedOf hG S ρ) hD


end

end AssemblyP1.OrientedSameLengthML
