import Mathlib
import AssemblyP1.SourceFaithfulIs

/-!
# Historical read-string coverage and bridging (Shomorony et al. 2016, supplement §6.4)

This module is the **additive** historical-coverage layer for issue #247.  It
introduces separately named historical predicates and theorem endpoints and
does **not** modify, strengthen, weaken, or delete any preexisting theorem or
the old `Covers` predicate of `AssemblyP1.SourceFaithfulIs`.  Base coverage
remains a legitimate independent model; both models are first-class.

## Exact source semantics (§6.4, author-hosted supplement, PDF p. 22)

The author-hosted 2016 supplement
(`https://web.stanford.edu/~gkamath/nsgIlan.pdf`, §6.4, printed p. 22) states:

> "Given a set of reads R from a sequence s, an obvious necessary condition for
> perfect assembly is that the reads cover the strings; i.e., every base in the
> sequence should be part of at least one read. More precisely, we will require
> that every interval of length L−1 in s contains the starting point of at least
> one read. Notice that we consider intervals of length L−1 and not L so that
> consecutive reads overlap by at least one base. **Since a read r ∈ R can
> technically correspond to multiple locations in s due to repeats, we
> formalize the notion of coverage as follows.**
> **Definition 1.** A set of reads R covers a sequence s if for 1 ≤ t ≤ G
> there is a read r ∈ R such that r = s[τ : τ+L−1] for τ ∈ [t : t+L−2]."

Two source facts drive every definition below:

1. **The quantified object is the observed read STRING, not a latent sampled
   placement.**  A read `r ∈ R` is a string; the definition asks only that
   `r = s[τ : τ+L−1]` for *some* `τ` in the length-`(L−1)` interval
   `[t, t+L−2]`.  Because of repeats, the same observed string may match at
   many genomic positions, and every such matching occurrence counts.  The old
   `SourceFaithfulIs.Covers` instead requires every *base* to lie inside a read
   *placed at a sampled start*; it allows zero-overlap adjacency and ignores
   repeat-enabled matching.  The two notions are incomparable.
2. **The interval has length `L−1`, not `L`**, so that consecutive reads
   overlap by at least one base.  In the `Fin`-indexed 0-based normalization of
   `SourceFaithfulIs`, the source's 1-based `t ∈ [1, G]` and
   `τ ∈ [t, t+L−2]` become `t : Fin S.len` and `τ = (t + δ) % S.len` with
   `δ : Fin (L-1)`.

The same string-based reading governs §6.4 Definition 2 (bridged repeats):

> "A repeat s[t₁:t₁+ℓ−1] = s[t₂:t₂+ℓ−1] = x is bridged if there is a read
> r = s[τ : τ+L−1] for τ ∈ [t₁+ℓ+1−L : t₁−1] or τ ∈ [t₂+ℓ+1−L : t₂−1]."

Again `τ` is any position where the observed read string matches, not
necessarily a sampled start.  `HistoricallyBridged` below is therefore
*defined* as the existing placement-based `BridgesCopy` at the saturated
`MatchStarts` set — no `Nat` subtraction is used, so the circular predecessor
`G-1` of `t = 0` is handled correctly (wrap regressions at the end of this
module).

## Module interface

* `observedTypes_ofFinset S L R` — observed read types derived from the
  sampled start set `R`.
* `MatchStarts S L observedWords` — saturated set of matching positions.
* `HistoricalCovers S L observedWords` — §6.4 Definition 1, historical
  read-string coverage.
* `HistoricallyBridged S L observedWords e t` — §6.4 Definition 2, historical
  read-string bridging of the length-`e` copy at `t`.
* `HistoricalInformationFeasible S L R` — full historical `I_s`: historical
  coverage plus the triple/interleaved bridging clauses of the old
  `InformationFeasible`, each quantified over the saturated `MatchStarts` set
  rather than the sampled placements.
* `historicalInformationFeasible_of_matchStarts_eq` — transfer: when
  `MatchStarts` equals the sampled start set, the old placement-based
  `InformationFeasible` implies the historical one.
-/

set_option linter.dupNamespace false

namespace AssemblyP1.HistoricalCovers

universe u

variable {α : Type u} [DecidableEq α]

open AssemblyP1.SourceFaithfulIs

/-- The set of observed read *types*: the distinct length-`L` windows of `S`
at the sampled starts.  `R` is the set of distinct sampled start positions;
its multiplicities determine the likelihood, while coverage and bridging
consume only the induced type set. -/
def observedTypes_ofFinset (S : Genome α) (L : ℕ) (R : Finset (Fin S.len)) :
    Finset (Fin L → α) :=
  R.image (S.window L)

/-- Membership in `observedTypes_ofFinset` is exactly "the word is the window
at some sampled start". -/
theorem observedTypes_ofFinset_mem_iff {S : Genome α} {L : ℕ} {R : Finset (Fin S.len)}
    {w : Fin L → α} : w ∈ observedTypes_ofFinset S L R ↔ ∃ r ∈ R, w = S.window L r := by
  constructor
  · intro h
    simp only [observedTypes_ofFinset, Finset.mem_image] at h
    obtain ⟨r, hr, hrw⟩ := h
    exact ⟨r, hr, hrw.symm⟩
  · rintro ⟨r, hr, hrw⟩
    simp only [observedTypes_ofFinset, Finset.mem_image]
    exact ⟨r, hr, hrw.symm⟩

/-- **Saturated match starts**: every position of `S` at which some observed
read string matches.  This is the saturation of the actual sampled start set
under repeat matching — repeats permit multiple matching positions, and §6.4
quantifies over all of them. -/
def MatchStarts (S : Genome α) (L : ℕ) (observedWords : Finset (Fin L → α)) :
    Finset (Fin S.len) :=
  {t : Fin S.len | S.window L t ∈ observedWords}

theorem MatchStarts_mem_iff {S : Genome α} {L : ℕ} {observedWords : Finset (Fin L → α)}
    {τ : Fin S.len} : τ ∈ MatchStarts S L observedWords ↔
      ∃ w ∈ observedWords, w = S.window L τ := by
  constructor
  · intro h
    simp only [MatchStarts, Finset.mem_filter] at h
    exact ⟨S.window L τ, h.2, rfl⟩
  · rintro ⟨w, hw, hw2⟩
    simp only [MatchStarts, Finset.mem_filter]
    rw [← hw2]
    exact ⟨Finset.mem_univ τ, hw⟩

/-- **Historical coverage** in the exact sense of Shomorony et al. (2016)
supplement §6.4, Definition 1: for every `t` there is a position
`τ = (t + δ) % S.len` in the length-`(L−1)` interval `[t, t+L−2]` at which
some observed read string matches.

The source regime is `2 ≤ L ≤ S.len` (reads of length at least 2, at most the
genome length).  The definition is stated unconditionally; for `L < 2` the
interval `[t, t+L−2]` is empty (`Fin (L-1)` is empty), so historical coverage
fails, matching the source's empty interval.  Unlike the old `Covers`, the
quantified object is the observed read *string* matching at *any* occurrence,
not a base covered by a read placed at a sampled start. -/
def HistoricalCovers (S : Genome α) (L : ℕ) (observedWords : Finset (Fin L → α)) :
    Prop :=
  ∀ t : Fin S.len, ∃ d : Fin (L - 1),
    (⟨(t.val + d.val) % S.len, Nat.mod_lt _ S.len_pos⟩ : Fin S.len) ∈
      MatchStarts S L observedWords

/-- **Historical bridging** in the exact sense of §6.4 Definition 2: the
length-`e` copy at `t` is bridged iff some observed read string matches at a
position strictly straddling the copy.

The source's 1-based interval `[t₁+ℓ+1−L : t₁−1]` translates to 0-based as
`[t+e+1−L : t−1]` with `e = ℓ`.  The read must extend beyond the copy in both
directions: `τ ≤ t−1` (starts before the copy) and `τ ≥ t+e+1−L` (ends after
it).  Because the quantified object is the observed read *string* matching at
*any* occurrence, this is exactly the existing placement-based `BridgesCopy`
at the saturated `MatchStarts` set — no `Nat` subtraction is used, so the
circular predecessor `G-1` of `t = 0` is handled correctly. -/
def HistoricallyBridged (S : Genome α) (L : ℕ) (observedWords : Finset (Fin L → α))
    (e : ℕ) (t : Fin S.len) : Prop :=
  BridgesCopy S L (MatchStarts S L observedWords) e t

/-- **Historical `I_s`**: §6.4 Definition 1 historical coverage of the
observed read types derived from the sampled start set, plus the triple and
interleaved bridging clauses of the old `InformationFeasible` — every triple
repeat all-bridged, every interleaved pair of repeats bridged — with **each
bridge quantified over the saturated `MatchStarts` set** rather than the
sampled placements.  This is the full historical `I_s` of §6.4, not a
hybrid of historical coverage with placement-based bridging. -/
def HistoricalInformationFeasible (S : Genome α) (L : ℕ) (R : Finset (Fin S.len)) :
    Prop :=
  HistoricalCovers S L (observedTypes_ofFinset S L R) ∧
    (∀ (e : Fin S.len) (a b c : Fin S.len), S.IsTripleRepeat e.val a b c →
      IsTripleRepeatAllBridged S L (MatchStarts S L (observedTypes_ofFinset S L R))
        e.val a b c) ∧
    (∀ (e₁ e₂ : Fin S.len) (a b c d : Fin S.len),
      S.IsRepeat e₁.val a b → S.IsRepeat e₂.val c d → Interleaved S a b c d →
        IsInterleavedPairBridged S L (MatchStarts S L (observedTypes_ofFinset S L R))
          e₁.val e₂.val a b c d)

/-- **Transfer from the old placement-based `I_s`.**  When the saturated
`MatchStarts` set equals the sampled start set — in particular when every
observed read string matches only at its sampled start — the old
`InformationFeasible` implies the full historical `I_s`: the coverage clause
is the historical one by hypothesis, and the bridging clauses transfer
because the bridge positions are the same set. -/
theorem historicalInformationFeasible_of_matchStarts_eq {S : Genome α} {L : ℕ}
    {R : Finset (Fin S.len)}
    (hms : MatchStarts S L (observedTypes_ofFinset S L R) = R)
    (hcov : HistoricalCovers S L (observedTypes_ofFinset S L R))
    (hIs : InformationFeasible S L R) :
    HistoricalInformationFeasible S L R := by
  refine ⟨hcov, ?_, ?_⟩
  · intro e a b c h
    rw [hms]
    exact hIs.2.1 e a b c h
  · intro e₁ e₂ a b c d h₁ h₂ h₃
    rw [hms]
    exact hIs.2.2 e₁ e₂ a b c d h₁ h₂ h₃

/-! ## Decidability

The historical layer is finite for concrete `S` and `observedWords`, so
witness modules can discharge historical certificates by computation. -/

instance (S : Genome α) (L : ℕ) (observedWords : Finset (Fin L → α)) :
    Decidable (HistoricalCovers S L observedWords) := by
  unfold HistoricalCovers; infer_instance

instance (S : Genome α) (L : ℕ) (observedWords : Finset (Fin L → α)) (e : ℕ)
    (t : Fin S.len) : Decidable (HistoricallyBridged S L observedWords e t) := by
  unfold HistoricallyBridged; infer_instance

/-! ## Circular-wrap regressions

The blocking corrections on #247, kernel-checked: the old draft's
`HistoricallyBridged` used the `Nat` interval `t.val+e+1−L ≤ τ ≤ t.val−1`,
whose upper endpoint truncates to `0` at circular `t = 0` instead of the
predecessor `G−1`.  Both failure modes are pinned below. -/

section Regression

/-- Four-symbol alphabet for the regression examples. -/
inductive Nuc where
  | A | C | G | T
  deriving DecidableEq, Inhabited, Repr

instance : Fintype Nuc where
  elems := {Nuc.A, Nuc.C, Nuc.G, Nuc.T}
  complete := by intro x; cases x <;> simp

/-- The circular genome `ACGT` of length `4`. -/
def genomeW : Genome Nuc where
  len := 4
  len_pos := by norm_num
  sym := ![Nuc.A, Nuc.C, Nuc.G, Nuc.T]

/-- The observed read string `TAC` (the window at start `3`). -/
def wordTAC : Fin 3 → Nuc := ![Nuc.T, Nuc.A, Nuc.C]

/-- The observed read string `ACG` (the window at start `0`). -/
def wordACG : Fin 3 → Nuc := ![Nuc.A, Nuc.C, Nuc.G]

/-- **Wrap regression 1** (the old definition's false negative): with only
`TAC` observed, the length-`1` copy `A` at circular `t = 0` **is** bridged —
the read `TAC` at start `3` strictly straddles it across the origin
(`3 < 4 < 6` on the lift `t' = 4` of the copy).  The old `Nat`-truncating
definition said `false` because `t.val−1` truncated to `0`. -/
theorem historicallyBridged_wrap_true :
    HistoricallyBridged genomeW 3 {wordTAC} 1 ⟨0, genomeW.len_pos⟩ := by
  decide

/-- **Wrap regression 2** (the old definition's false positive): with only
`ACG` observed, the length-`1` copy `A` at circular `t = 0` is **not**
bridged — the read `ACG` at start `0` starts exactly at the copy, so it does
not extend before it.  The old `Nat`-truncating definition said `true`
because `τ = 0` satisfied the truncated interval `0 ≤ τ ≤ 0`. -/
theorem not_historicallyBridged_wrap_false :
    ¬ HistoricallyBridged genomeW 3 {wordACG} 1 ⟨0, genomeW.len_pos⟩ := by
  decide

end Regression

end AssemblyP1.HistoricalCovers
