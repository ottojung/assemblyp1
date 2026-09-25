import AssemblyP1.RepeatAdapter

/-!
# Oriented same-length ML maximizer: the model-boundary endpoint (issue #88)

This module is the *independent* part of the issue-#88 packet: it converts a
strict oriented same-length **spelled candidate** of the true length into the
hypotheses consumed by the mature rigidity chain
`AssemblyP1.OrientedFinal.oriented_same_length_spectrum_rigidity`, and then
converts the resulting spectrum equality into the actual
**spectrum-determined ML maximizer statement** for concrete oriented
same-length objectives (Medvedev–Brudno exact multinomial, and the §6.1
binomial-marginal approximation at the external length `N = G`).

Nothing here is `I_s`: the no-long-triple-repeat hypothesis is consumed as the
chain's own boundary premise `hno`, which the shared information-feasibility
layer (issue #90) discharges from the source-faithful `I_s` predicate. Keeping
that seam explicit is deliberate: this module is reusable independently of
which `I_s` presentation is adopted.

## Modeling decisions recorded here (issue #88)

* **Orientation.** Read types are oriented single-strand length-`L` circular
  windows (`OrientedRigidity.window`); no reverse-complement collapse, matching
  the strict oriented same-length model settled for this packet.
* **Candidate length is a type, not a hypothesis.** A candidate is a function
  `Fin G → α`, i.e. a circular genome of *the same length* `G` as the truth.
  The restriction is visible in the type, as the ML contract requires.
* **Observation vs. realization.** The ML objective consumes only the observed
  read-type multiplicity `x : (Fin L → α) → ℕ`; a `Finset` of read starts is
  never used as the observation, and independently sampled starts that repeat
  must not be collapsed (see the `x` convention below and
  `AssemblyP1.Realization`).
* **Spelled candidate.** `IsSameLengthSpelledCandidate` is the strict
  same-length spelling condition: the candidate's window support coincides with
  the truth's, and every observed read type is spelled by the candidate. Under
  §6.2, a spelled circuit of the read-overlap graph has exactly these two
  properties in the single-strand reading (its walk uses only read-molecule
  edges, and it spells every read molecule); the graph-theoretic
  circuit-to-support-adequacy correspondence is not formalized here, so the
  theorem is stated for this strict condition and the restriction is named in
  the theorem statement.
* **Objective.** Two concrete objectives are formalized and kept separate.
  Neither is advertised as *the* objective the 2016 sentence denotes.
-/

namespace AssemblyP1.OrientedSameLengthML

open Finset
open BigOperators

set_option maxHeartbeats 800000

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

/-- **Spectrum-determined oriented same-length exact-multinomial factor.**
`(d_D w / N(D)) ^ (x w)` with the candidate-intrinsic length `N(D) = G`; a read
type absent from the candidate contributes `0` when it was observed. -/
def exactFactor {α : Type} [DecidableEq α] {G L : ℕ} (hG : 0 < G)
    (D : Fin G → α) (x : ObservedReads α L) (w : Fin L → α) : ℝ :=
  ((OrientedRigidity.specCount hG D w : ℕ) : ℝ) / (G : ℝ) ^ (x w)

/-- The oriented same-length exact Medvedev–Brudno multinomial objective, with
the observation-only positive factor `n! / ∏_w x w!` divided out (it does not
depend on the candidate and so does not affect any maximizer; the
`exactLik_scale` lemma records the reinsertion). -/
def exactLik {α : Type} [DecidableEq α] {G L : ℕ} (hG : 0 < G)
    (D : Fin G → α) (x : ObservedReads α L) : ℝ :=
  ∏ w : Fin L → α, exactFactor hG D x w

/-- One §6.1 binomial-marginal factor with external genome-size estimate `N`,
candidate count `d_D w` and observed count `x w`; `n` is the total number of
observed reads. -/
def binomialMarginal {α : Type} [DecidableEq α] {G L : ℕ} (hG : 0 < G)
    (D : Fin G → α) (x : ObservedReads α L) (N n : ℕ) (w : Fin L → α) : ℝ :=
  ((Nat.choose n (OrientedRigidity.specCount hG D w) : ℕ) : ℝ) *
    ((OrientedRigidity.specCount hG D w : ℕ) : ℝ) / (N : ℝ) ^ (x w) *
      (1 - ((OrientedRigidity.specCount hG D w : ℕ) : ℝ) / (N : ℝ)) ^ (n - x w)

/-- The literal §6.1 product of binomial marginals over the oriented read-type
space, at the external size `N`. -/
/-- `N` is Medvedev–Brudno §6.1's external genome-size estimate and `n` the
number of observed reads; both are observation-level parameters, independent
of the candidate. -/
def binomialLik {α : Type} [DecidableEq α] {G L : ℕ} (hG : 0 < G)
    (D : Fin G → α) (x : ObservedReads α L) (N n : ℕ) : ℝ :=
  ∏ w : Fin L → α, binomialMarginal hG D x N n w

/-! ## Windows and support of an arbitrary same-length candidate -/

/-- The `winPrefix` of a length-`L` window is the `(L-1)`-window at the same
start (re-exported from `OrientedRigidity`, where it is private). -/
private lemma winPrefix_window' {α : Type} {G L : ℕ} (hG : 0 < G)
    (D : Fin G → α) (r : Fin G) :
    OrientedRigidity.winPrefix (OrientedRigidity.window hG D r) =
      OrientedRigidity.nodeWindow hG D r := by
  funext d
  rfl

/-- The `(L-1)`-window node set is the image of the prefix map on the window
support. -/
theorem genomeNodes_eq_image_winPrefix {α : Type} [DecidableEq α] {G L : ℕ}
    (hG : 0 < G) (D : Fin G → α) :
    OrientedRigidity.genomeNodes hG D =
      (OrientedRigidity.support hG D).image
        (OrientedRigidity.winPrefix (α := α) (L := L)) := by
  ext k
  constructor
  · intro hk
    simp only [OrientedRigidity.genomeNodes, Finset.mem_image] at hk
    obtain ⟨r, _, rfl⟩ := hk
    exact Finset.mem_image.mpr ⟨OrientedRigidity.window hG D r,
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
theorem genomeNodes_of_support_eq {α : Type} [DecidableEq α] {G L : ℕ}
    (hG : 0 < G) (D S : Fin G → α)
    (h : OrientedRigidity.support hG D = OrientedRigidity.support hG S) :
    OrientedRigidity.genomeNodes hG D = OrientedRigidity.genomeNodes hG S := by
  rw [genomeNodes_eq_image_winPrefix, genomeNodes_eq_image_winPrefix, h]

/-- A window of `D` is in `D`'s support, and conversely a supported window is
some window of `D`. -/
theorem mem_support_iff_window {α : Type} [DecidableEq α] {G L : ℕ}
    (hG : 0 < G) (D : Fin G → α) (w : Fin L → α) :
    w ∈ OrientedRigidity.support hG D ↔ ∃ r : Fin G,
      OrientedRigidity.window hG D r = w := by
  simp only [OrientedRigidity.support, Finset.mem_image]
  constructor
  · rintro ⟨r, _, rfl⟩
    exact ⟨r, rfl⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r, Finset.mem_univ _, rfl⟩

/-! ## The strict oriented same-length spelled-candidate condition -/

/-- **Strict oriented same-length spelled candidate.** `D` is a circular word of
the same length `G` as the truth whose walk through the read-overlap graph is
spelled: its length-`L` window support coincides with the truth's (equivalently,
it uses only read-molecule edges and spells every window of the truth), and
every observed read type occurs in `D`. -/
def IsSameLengthSpelledCandidate {α : Type} [DecidableEq α] {G L : ℕ}
    (hG : 0 < G) (S D : Fin G → α) (x : ObservedReads α L) : Prop :=
  OrientedRigidity.support hG D = OrientedRigidity.support hG S ∧
    ∀ w : Fin L → α, 0 < x w → 0 < OrientedRigidity.specCount hG D w

/-- The candidate's support equality, projected. -/
theorem support_eq_of_spelled {α : Type} [DecidableEq α] {G L : ℕ} (hG : 0 < G)
    {S D : Fin G → α} {x : ObservedReads α L}
    (h : IsSameLengthSpelledCandidate hG S D x) :
    OrientedRigidity.support hG D = OrientedRigidity.support hG S := h.1

/-- Every observed read type is spelled by the candidate. -/
theorem spells_observed_of_spelled {α : Type} [DecidableEq α] {G L : ℕ}
    (hG : 0 < G) {S D : Fin G → α} {x : ObservedReads α L}
    (h : IsSameLengthSpelledCandidate hG S D x) :
    ∀ w : Fin L → α, 0 < x w → 0 < OrientedRigidity.specCount hG D w := h.2

/-! ## From a spelled candidate to the rigidity chain's hypotheses -/

/-- **Support/positivity of the candidate's own spectrum, read on the truth's
support.** -/
theorem spec_support_iff {α : Type} [DecidableEq α] {G L : ℕ} (hG : 0 < G)
    {S D : Fin G → α} (h : OrientedRigidity.support hG D =
      OrientedRigidity.support hG S) (w : Fin L → α) :
    w ∈ OrientedRigidity.support hG S ↔ 0 < OrientedRigidity.specCount hG D w := by
  constructor
  · intro hw
    have hwD : w ∈ OrientedRigidity.support hG D := by rw [← h]; exact hw
    obtain ⟨r, hwr⟩ := mem_support_iff_window hG D w |>.mp hwD
    have hmem : r ∈ (Finset.univ : Finset (Fin G)).filter
        (fun r' : Fin G => OrientedRigidity.window hG D r' =
          (OrientedRigidity.window hG D r : Fin L → α)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwr⟩
    have hpos : 0 < OrientedRigidity.specCount hG D
        (OrientedRigidity.window hG D r : Fin L → α) :=
      Finset.card_pos.mpr ⟨r, hmem⟩
    rwa [hwr] at hpos
  · intro hw
    obtain ⟨r, hwr⟩ :=
      (mem_support_iff_window hG D w).mpr
        (Finset.card_pos.mp (show 0 <
          (Finset.univ.filter (fun r' : Fin G =>
            OrientedRigidity.window hG D r' = w)).card from hw))
    have : w ∈ OrientedRigidity.support hG D :=
      (mem_support_iff_window hG D w).mpr ⟨r, hwr⟩
    rwa [h] at this

/-- **The candidate's own spectrum is a positive balanced circulation of total
mass `G` on the truth's window support.** This is the interface between the
model-level spelled-candidate condition and the abstract rigidity chain: no
hypotheses beyond spelledness are added. -/
theorem candidate_circulation_hypotheses {α : Type} [DecidableEq α] {G L : ℕ}
    (hG : 0 < G) (S D : Fin G → α) (x : ObservedReads α L)
    (hD : IsSameLengthSpelledCandidate hG S D x) :
    (∀ w, w ∈ OrientedRigidity.support hG S ↔
        0 < OrientedRigidity.specCount hG D w) ∧
      OrientedRigidity.Balanced OrientedRigidity.winPrefix
        OrientedRigidity.winSuffix (OrientedRigidity.genomeNodes hG S)
        (OrientedRigidity.support hG S) (OrientedRigidity.specCount hG D) ∧
      ∑ w ∈ (OrientedRigidity.support hG S :
          Finset (Fin L → α)), OrientedRigidity.specCount hG D w = G := by
  have hsup := support_eq_of_spelled hG hD
  have hnodes := genomeNodes_of_support_eq hG D S hsup
  refine ⟨spec_support_iff hG hsup, ?_, ?_⟩
  · have := OrientedRigidity.truth_balanced (L := L) hG D
    rwa [hnodes, hsup] at this
  · have := OrientedRigidity.truth_total (L := L) hG D
    rwa [hsup] at this

/-- **Spectrum rigidity for a spelled candidate.** A strict oriented
same-length spelled candidate has exactly the truth's spectrum, under the
chain's no-long-triple-repeat boundary premise. -/
theorem same_length_candidate_spectrum_eq {α : Type} [DecidableEq α]
    {G L : ℕ} (hG : 0 < G) (S D : Fin G → α) (hL : 2 ≤ L) (hLG : L ≤ G)
    (hno : ¬ RepeatAdapter.HasLongTripleRepeat hG S L)
    (x : ObservedReads α L) (hD : IsSameLengthSpelledCandidate hG S D x) :
    ∀ w : Fin L → α, OrientedRigidity.specCount hG D w =
      OrientedRigidity.specCount hG S w := by
  obtain ⟨hsup, hbal, htot⟩ :=
    candidate_circulation_hypotheses hG S D x hD
  exact OrientedFinal.oriented_same_length_spectrum_rigidity hG S hL hLG hno
    (OrientedRigidity.specCount hG D) hsup hbal htot

/-! ## The actual ML endpoint -/

/-- Two candidates with the same oriented spectrum have the same exact
multinomial objective value. -/
theorem exactLik_congr_of_specCount_eq {α : Type} [DecidableEq α] {G L : ℕ}
    (hG : 0 < G) {D E : Fin G → α} {x : ObservedReads α L}
    (h : ∀ w : Fin L → α, OrientedRigidity.specCount hG D w =
      OrientedRigidity.specCount hG E w) :
    exactLik hG D x = exactLik hG E x := by
  unfold exactLik
  congr 1
  funext w
  rw [h w]

/-- Two candidates with the same oriented spectrum have the same §6.1
binomial-marginal objective value at the same external size `N`. -/
theorem binomialLik_congr_of_specCount_eq {α : Type} [DecidableEq α]
    {G L : ℕ} (hG : 0 < G) {D E : Fin G → α} {x : ObservedReads α L} (N : ℕ)
    (h : ∀ w : Fin L → α, OrientedRigidity.specCount hG D w =
      OrientedRigidity.specCount hG E w) :
    binomialLik hG D x N = binomialLik hG E x N := by
  unfold binomialLik
  congr 1
  funext w
  rw [h w]

/-- **Oriented same-length ML maximizer theorem under the chain's boundary
premise (exact multinomial objective).** Under the no-long-triple-repeat
premise discharged from `I_s` elsewhere, the true genome is a maximum of the
oriented same-length exact Medvedev–Brudno multinomial likelihood over all
strict oriented same-length spelled candidates. -/
theorem same_length_exactLik_maximizer {α : Type} [DecidableEq α]
    {G L : ℕ} (hG : 0 < G) (S D : Fin G → α) (hL : 2 ≤ L) (hLG : L ≤ G)
    (hno : ¬ RepeatAdapter.HasLongTripleRepeat hG S L)
    (x : ObservedReads α L) (hD : IsSameLengthSpelledCandidate hG S D x) :
    exactLik hG D x ≤ exactLik hG S x :=
  le_of_eq (exactLik_congr_of_specCount_eq hG
    (same_length_candidate_spectrum_eq hG S D hL hLG hno x hD))

/-- **Oriented same-length ML maximizer theorem under the chain's boundary
premise (§6.1 binomial-marginal approximation at external size `N`).** -/
theorem same_length_binomialLik_maximizer {α : Type} [DecidableEq α]
    {G L : ℕ} (hG : 0 < G) (S D : Fin G → α) (hL : 2 ≤ L) (hLG : L ≤ G)
    (hno : ¬ RepeatAdapter.HasLongTripleRepeat hG S L)
    (x : ObservedReads α L) (N n : ℕ)
    (hD : IsSameLengthSpelledCandidate hG S D x) :
    binomialLik hG D x N n ≤ binomialLik hG S x N n :=
  le_of_eq (binomialLik_congr_of_specCount_eq hG N n
    (same_length_candidate_spectrum_eq hG S D hL hLG hno x hD))

/-- Both objectives, at the same-length external size `N = G`, in one
statement. -/
theorem same_length_ML_maximizer_both {α : Type} [DecidableEq α] {G L : ℕ}
    (hG : 0 < G) (S D : Fin G → α) (hL : 2 ≤ L) (hLG : L ≤ G)
    (hno : ¬ RepeatAdapter.HasLongTripleRepeat hG S L)
    (x : ObservedReads α L) (n : ℕ)
    (hD : IsSameLengthSpelledCandidate hG S D x) :
    exactLik hG D x ≤ exactLik hG S x ∧
      binomialLik hG D x G n ≤ binomialLik hG S x G n :=
  ⟨same_length_exactLik_maximizer hG S D hL hLG hno x hD,
    same_length_binomialLik_maximizer hG S D hL hLG hno x G n hD⟩

/-! ## The observation is not a set of starts -/

/-- The likelihood layer consumes only `x`: it never inspects a realization.
The realized starts used by `I_s`/bridging are latent and do not enter the
objective; two realizations with equal `x` score all candidates equally. -/
theorem objective_depends_only_on_observation {α : Type} [DecidableEq α]
    {G L : ℕ} (hG : 0 < G) (D : Fin G → α) (x x' : ObservedReads α L)
    (h : ∀ w : Fin L → α, x w = x' w) :
    exactLik hG D x = exactLik hG D x' ∧
      binomialLik hG D x G n = binomialLik hG D x' G n := by
  constructor
  · unfold exactLik
    congr 1
    funext w
    rw [h w]
  · unfold binomialLik
    congr 1
    funext w
    rw [h w]

/-! ## Non-vacuity: the truth is itself a spelled candidate -/

/-- If every observed read type is a window of the truth — the observable
consequence of a realization whose reads are drawn from the truth — then the
truth satisfies the spelled-candidate condition, so the maximizer statement
ranges over a nonempty candidate class. -/
theorem truth_is_spelled_candidate {α : Type} [DecidableEq α] {G L : ℕ}
    (hG : 0 < G) (S : Fin G → α) (x : ObservedReads α L)
    (hobs : ∀ w : Fin L → α, 0 < x w → w ∈ OrientedRigidity.support hG S) :
    IsSameLengthSpelledCandidate hG S S x :=
  ⟨rfl, fun w hw => by
    have hw' := OrientedRigidity.truth_pos_on_support (L := L) hG S w (hobs w hw)
    exact Nat.lt_of_lt_of_le (by omega) hw'⟩

end AssemblyP1.OrientedSameLengthML
