import Mathlib
import AssemblyP1.SourceFaithfulIs
import AssemblyP1.BridgingBridge

/-!
# Historical read-string coverage (Shomorony et al. 2016, supplement §6.4)

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
> technically correspond to multiple locations in s due to repeats, we formalize
> the notion of coverage as follows.**
>
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
   repeat-enabled matching.  The two notions are **incomparable** (regression
   examples at the end of this module).
2. **The interval has length `L−1`, not `L`**, so that consecutive reads
   overlap by at least one base.  In the `Fin`-indexed 0-based normalization of
   `SourceFaithfulIs`, the source's 1-based `t ∈ [1, G]` and
   `τ ∈ [t, t+L−2]` become `t : Fin S.len` and `τ = (t + δ) % S.len` with
   `δ : Fin (L-1)`.

The same string-based reading governs §6.4 Definition 2 (bridged repeats):

> "A repeat s[t₁:t₁+ℓ−1] = s[t₂:t₂+ℓ−1] = x is bridged if there is a read
> r = s[τ : τ+L−1] for τ ∈ [t₁+ℓ+1−L : t₁−1] or τ ∈ [t₂+ℓ+1−L : t₂−1]."

Again `τ` is any position where the observed read string matches, not
necessarily a sampled start.  The existing placement-based
`SourceFaithfulIs.BridgesCopy` is exactly this condition with `τ` restricted
to the sampled start set; the historical version quantifies over all matching
occurrences.  The two are equivalent once the start set is saturated under
repeat matching (`historicallyBridged_iff_bridgesCopy` below).

## The saturated `MatchStarts` set

`MatchStarts S L observedWords` is the set of **all** positions at which some
observed read string matches.  It is the saturation of the actual sampled
start set under repeat matching: every sampled start is a match start, and
every repeat-enabled matching occurrence is included.  All historical
predicates are stated against `observedWords : Finset (Fin L → α)`, the set of
observed read *types*, which is derived from the sampled read multiset by
`observedTypes` (the multiset's multiplicities are what the likelihood
consumes; the type set is what coverage and bridging consume).

## Module interface (for the other #247 lanes)

* `observedTypes S L samples` — observed read types derived from the sampled
  read multiset `samples : List (Fin S.len)` (starts with multiplicity).
* `HistoricalCovers S L observedWords` — §6.4 Definition 1, historical
  read-string coverage.
* `DenseSampledStarts S L R` — every circular interval of `L−1` consecutive
  starts contains a sampled start; a *sufficient certificate* for historical
  coverage, not an equivalent definition.
* `MatchStarts S L observedWords` — saturated set of matching positions.
* `HistoricallyBridged S L observedWords e t` — §6.4 Definition 2, historical
  read-string bridging of the length-`e` copy at `t`.
* `HistoricalInformationFeasible S L R` — historical coverage plus the
  existing (placement-based, sampled-start) bridging clauses, clearly
  identified as such.

The existing structural result `BridgingBridge.informationFeasible_no_long_triple_repeat`
applies verbatim to `MatchStarts`: `informationFeasible_matchStarts` below
assembles `InformationFeasible S L (MatchStarts S L observedWords)` from
historical coverage and historical bridging certificates, and
`historical_no_long_triple_repeat` records the composition.  Lanes owning the
finite witnesses can discharge the two bridging certificate hypotheses with
`HistoricallyBridged` facts via `historicallyBridged_iff_bridgesCopy`.
-/

set_option linter.dupNamespace false

namespace AssemblyP1.HistoricalCovers

universe u

variable {α : Type u}

open AssemblyP1.SourceFaithfulIs

/-! ## Observed read types from the sampled read multiset -/

/-- The set of observed read *types*: the distinct length-`L` windows of `S`
at the sampled starts.  `samples` is the sampled read multiset (a list of
starts with multiplicity); its multiplicities determine the likelihood, while
coverage and bridging consume only the induced type set. -/
def observedTypes (S : Genome α) (L : ℕ) (samples : List (Fin S.len)) :
    Finset (Fin L → α) :=
  samples.toFinset.image (S.window L)

/-- Membership in `observedTypes` is exactly "the word is the window at some
sampled start". -/
theorem observedTypes_mem_iff {S : Genome α} {L : ℕ} {samples : List (Fin S.len)}
    {w : Fin L → α} : w ∈ observedTypes S L samples ↔ ∃ r ∈ samples, w = S.window L r := by
  constructor
  · intro h
    simp only [observedTypes, Finset.mem_image, List.mem_toFinset] at h
    obtain ⟨r, hr, hrw⟩ := h
    exact ⟨r, hr, hrw.symm⟩
  · rintro ⟨r, hr, hrw⟩
    simp only [observedTypes, Finset.mem_image, List.mem_toFinset]
    exact ⟨r, hr, hrw.symm⟩

/-- The observed types derived from a `Finset` of distinct sampled starts. -/
def observedTypes_ofFinset (S : Genome α) (L : ℕ) (R : Finset (Fin S.len)) :
    Finset (Fin L → α) :=
  R.image (S.window L)

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

/-! ## The saturated set of matching positions -/

/-- **Saturated match starts**: every position of `S` at which some observed
read string matches.  This is the saturation of the actual sampled start set
under repeat matching — repeats permit multiple matching positions, and §6.4
quantifies over all of them. -/
def MatchStarts (S : Genome α) (L : ℕ) (observedWords : Finset (Fin L → α)) :
    Finset (Fin S.len) :=
  {τ : Fin S.len | S.window L τ ∈ observedWords}

theorem MatchStarts_mem_iff {S : Genome α} {L : ℕ} {observedWords : Finset (Fin L → α)}
    {τ : Fin S.len} : τ ∈ MatchStarts S L observedWords ↔
      ∃ w ∈ observedWords, w = S.window L τ := by
  constructor
  · intro h
    simp only [MatchStarts] at h
    exact ⟨S.window L τ, h, rfl⟩
  · rintro ⟨w, hw, hw2⟩
    simp only [MatchStarts]
    rw [← hw2]
    exact hw

/-- Every sampled start is a match start: the sampled start set is contained
in its saturation. -/
theorem sampledStarts_subset_matchStarts {S : Genome α} {L : ℕ}
    {samples : List (Fin S.len)} {r : Fin S.len} (hr : r ∈ samples) :
    r ∈ MatchStarts S L (observedTypes S L samples) := by
  rw [MatchStarts_mem_iff]
  exact ⟨S.window L r, observedTypes_mem_iff.mpr ⟨r, hr, rfl⟩, rfl⟩

/-! ## Historical coverage (§6.4 Definition 1) -/

/-- **Historical coverage** in the exact sense of Shomorony et al. (2016)
supplement §6.4, Definition 1: for every `t` there is an observed read string
`w` and a position `τ = (t + δ) % S.len` in the length-`(L−1)` interval
`[t, t+L−2]` such that `w = s[τ : τ+L−1]`.

The source regime is `2 ≤ L ≤ S.len` (reads of length at least 2, at most the
genome length).  The definition is stated unconditionally; for `L < 2` the
interval `[t, t+L−2]` is empty (`Fin (L-1)` is empty), so historical coverage
fails, matching the source's empty interval.  Unlike the old `Covers`, the
quantified object is the observed read *string* matching at *any* occurrence,
not a base covered by a read placed at a sampled start. -/
def HistoricalCovers (S : Genome α) (L : ℕ) (observedWords : Finset (Fin L → α)) :
    Prop :=
  ∀ t : Fin S.len, ∃ w ∈ observedWords, ∃ δ : Fin (L - 1),
    w = S.window L ⟨(t.val + δ.val) % S.len, Nat.mod_lt _ S.len_pos⟩

/-- Historical coverage, iff-form: every length-`(L−1)` interval of starts
contains a saturated match start.  This is the exact §6.4 Definition 1
quantifier structure. -/
theorem historicalCovers_iff {S : Genome α} {L : ℕ}
    {observedWords : Finset (Fin L → α)} :
    HistoricalCovers S L observedWords ↔
      ∀ t : Fin S.len, ∃ δ : Fin (L - 1),
        (⟨(t.val + δ.val) % S.len, Nat.mod_lt _ S.len_pos⟩ : Fin S.len) ∈
          MatchStarts S L observedWords := by
  constructor
  · rintro h t
    obtain ⟨w, hw, δ, hw2⟩ := h t
    refine ⟨δ, ?_⟩
    rw [MatchStarts_mem_iff]
    exact ⟨w, hw, hw2⟩
  · rintro h t
    obtain ⟨δ, hδ⟩ := h t
    rw [MatchStarts_mem_iff] at hδ
    obtain ⟨w, hw, hw2⟩ := hδ
    exact ⟨w, hw, δ, hw2⟩

/-! ## DenseSampledStarts: a sufficient certificate -/

/-- **Dense sampled starts**: every circular interval of `L−1` consecutive
starts contains a sampled start (equivalently, the cyclic gap between
consecutive distinct sampled starts is at most `L−1`).

This is a *sufficient certificate* for historical coverage, not an equivalent
definition: with repeats, observed read strings may match at unsampled
positions, so historical coverage can hold without start density. -/
def DenseSampledStarts (S : Genome α) (L : ℕ) (R : Finset (Fin S.len)) : Prop :=
  ∀ t : Fin S.len, ∃ r ∈ R, ∃ δ : Fin (L - 1), (t.val + δ.val) % S.len = r.val

/-- **The sufficient lemma.**  If every length-`(L−1)` interval of starts
contains a sampled start, then every such interval contains a match of an
observed read string: the read sampled at `r` is an observed string matching at
`r` itself. -/
theorem denseSampledStarts_historicalCovers {S : Genome α} {L : ℕ}
    {R : Finset (Fin S.len)} (h : DenseSampledStarts S L R) :
    HistoricalCovers S L (observedTypes_ofFinset S L R) := by
  intro t
  obtain ⟨r, hr, δ, hδ⟩ := h t
  refine ⟨S.window L r, ?_, δ, ?_⟩
  · exact observedTypes_ofFinset_mem_iff.mpr ⟨r, hr, rfl⟩
  · have hmod : r.val % S.len = (t.val + δ.val) % S.len := by
      rw [← hδ, Nat.mod_mod]
    exact Genome.window_eq_of_modEq hmod

/-- Sufficiency endpoint tied to the sampled read multiset: distinct starts
dense ⟹ historical coverage of the observed types of the sample. -/
theorem historicalCovers_of_samples {S : Genome α} {L : ℕ}
    {samples : List (Fin S.len)} (h : DenseSampledStarts S L samples.toFinset) :
    HistoricalCovers S L (observedTypes S L samples) :=
  denseSampledStarts_historicalCovers h

/-- Start density implies the old base coverage (Lander–Waterman): if every
length-`(L−1)` interval of starts contains a sampled start, then every base
lies in a read placed at a sampled start. -/
theorem denseSampledStarts_covers {S : Genome α} {L : ℕ} {R : Finset (Fin S.len)}
    (h : DenseSampledStarts S L R) : Covers S L R := by
  intro p
  set t : Fin S.len := ⟨(p.val + S.len + 1 - L) % S.len, Nat.mod_lt _ S.len_pos⟩ with ht
  obtain ⟨r, hr, δ, hδ⟩ := h t
  have hδL : δ.val < L - 1 := δ.isLt
  refine ⟨r, hr, ⟨L - 1 - δ.val, by omega⟩, ?_⟩
  have hp : p.val = (t.val + (L - 1)) % S.len := by
    have e1 : (t.val + (L - 1)) % S.len
        = ((p.val + S.len + 1 - L) % S.len + (L - 1)) % S.len := by rw [ht]
    rw [Nat.mod_add_mod] at e1
    have e2 : (p.val + S.len + 1 - L) + (L - 1) = p.val + S.len := by omega
    rw [e2] at e1
    have e3 : (p.val + S.len) % S.len = p.val % S.len := by
      rw [Nat.add_mod, Nat.mod_self, Nat.zero_add]
    rw [e3, Nat.mod_eq_of_lt p.isLt] at e1
    exact e1.symm
  have hτ : (r.val + (L - 1 - δ.val)) % S.len = (t.val + (L - 1)) % S.len := by
    rw [← hδ, Nat.mod_add_mod]
    congr 1
    omega
  rw [hτ, hp]

/-- Historical coverage implies old base coverage **at the saturated
`MatchStarts` set** — not at the actual sampled starts.  This is the correct
adapter via the set of all matching positions: every base lies in a read
placed at a position where an observed read string matches. -/
theorem historicalCovers_covers_matchStarts {S : Genome α} {L : ℕ}
    {observedWords : Finset (Fin L → α)} (h : HistoricalCovers S L observedWords) :
    Covers S L (MatchStarts S L observedWords) := by
  intro p
  set t : Fin S.len := ⟨(p.val + S.len + 1 - L) % S.len, Nat.mod_lt _ S.len_pos⟩ with ht
  obtain ⟨w, hw, δ, hw2⟩ := h t
  have hδL : δ.val < L - 1 := δ.isLt
  set τ0 : Fin S.len := ⟨(t.val + δ.val) % S.len, Nat.mod_lt _ S.len_pos⟩ with hτ0
  refine ⟨τ0, ⟨w, hw, hw2⟩, ⟨L - 1 - δ.val, by omega⟩, ?_⟩
  have hp : p.val = (t.val + (L - 1)) % S.len := by
    have e1 : (t.val + (L - 1)) % S.len
        = ((p.val + S.len + 1 - L) % S.len + (L - 1)) % S.len := by rw [ht]
    rw [Nat.mod_add_mod] at e1
    have e2 : (p.val + S.len + 1 - L) + (L - 1) = p.val + S.len := by omega
    rw [e2] at e1
    have e3 : (p.val + S.len) % S.len = p.val % S.len := by
      rw [Nat.add_mod, Nat.mod_self, Nat.zero_add]
    rw [e3, Nat.mod_eq_of_lt p.isLt] at e1
    exact e1.symm
  have hτ : (τ0.val + (L - 1 - δ.val)) % S.len = (t.val + (L - 1)) % S.len := by
    rw [hτ0, Nat.mod_add_mod]
    congr 1
    omega
  rw [hτ, hp]

/-! ## Historical bridging (§6.4 Definition 2) -/

/-- **Historical bridging** in the exact sense of §6.4 Definition 2: the
length-`e` copy at `t` is bridged iff some observed read string matches at a
position `τ` in the source's interval `[t+e+1−L, t−1]` (on the canonical
0-based lift of `t`; the set of matching residues is lift-independent because
the interval shifts by `S.len` with the lift).

The source's 1-based interval `[t₁+ℓ+1−L : t₁−1]` translates to 0-based as
`[t+e+1−L : t−1]` with `e = ℓ`.  The read must extend beyond the copy in both
directions: `τ ≤ t−1` (starts before the copy) and `τ ≥ t+e+1−L` (ends after
it). -/
def HistoricallyBridged (S : Genome α) (L : ℕ) (observedWords : Finset (Fin L → α))
    (e : ℕ) (t : Fin S.len) : Prop :=
  ∃ w ∈ observedWords, ∃ τ : ℕ, t.val + e + 1 - L ≤ τ ∧ τ ≤ t.val - 1 ∧
    w = S.window L ⟨τ % S.len, Nat.mod_lt _ S.len_pos⟩

/-- Historical read-string bridging is **equivalent** to the existing
placement-based `BridgesCopy` at the saturated `MatchStarts` set.  This is the
explicit bridge between the historical and placement-based bridging notions. -/
theorem historicallyBridged_iff_bridgesCopy {S : Genome α} {L : ℕ}
    {observedWords : Finset (Fin L → α)} {e : ℕ} {t : Fin S.len} :
    HistoricallyBridged S L observedWords e t ↔
      BridgesCopy S L (MatchStarts S L observedWords) e t := by
  constructor
  · rintro ⟨w, hw, τ, hτ1, hτ2, hw2⟩
    set r : Fin S.len := ⟨τ % S.len, Nat.mod_lt _ S.len_pos⟩ with hr
    refine ⟨r, ?_, ⟨t.val - 1 - τ, by omega⟩, by omega, ?_⟩
    · rw [MatchStarts_mem_iff]
      exact ⟨w, hw, hw2.symm⟩
    · have e1 : (r.val + (t.val - 1 - τ) + 1) = (τ % S.len) + (t.val - τ) := by
        rw [hr]
        omega
      rw [e1, Nat.mod_add_mod]
      have e2 : τ + (t.val - τ) = t.val := by omega
      rw [e2, Nat.mod_eq_of_lt t.isLt]
  · rintro ⟨r, hr, d, hd, hrt⟩
    obtain ⟨w, hw, hw2⟩ := MatchStarts_mem_iff.mp hr
    refine ⟨w, hw, t.val - 1 - d.val, by omega, by omega, ?_⟩
    have hmod : r.val % S.len = (t.val - 1 - d.val) % S.len := by
      have h1 : (r.val + d.val + 1) % S.len = t.val % S.len := by
        rw [hrt, Nat.mod_eq_of_lt t.isLt]
      have h3 : (r.val + (d.val + 1)) % S.len
          = ((t.val - 1 - d.val) + (d.val + 1)) % S.len := by
        have e : (t.val - 1 - d.val) + (d.val + 1) = t.val := by omega
        rw [e]
        exact h1
      exact Nat.ModEq.add_right_cancel' (d.val + 1) h3
    exact hw2.trans (Genome.window_eq_of_modEq hmod)

/-- Placement-based `BridgesCopy` at the sampled starts implies historical
bridging against the observed types of the sample.  The converse fails in
general: repeated read strings may match at unsampled positions, so historical
bridging need not be witnessed by a sampled placement. -/
theorem bridgesCopy_historicallyBridged {S : Genome α} {L : ℕ}
    {R : Finset (Fin S.len)} {e : ℕ} {t : Fin S.len}
    (h : BridgesCopy S L R e t) :
    HistoricallyBridged S L (observedTypes_ofFinset S L R) e t := by
  obtain ⟨r, hr, d, hd, hrt⟩ := h
  obtain ⟨w, hw, hw2⟩ := observedTypes_ofFinset_mem_iff.mpr ⟨r, hr, rfl⟩
  refine ⟨w, hw, t.val - 1 - d.val, by omega, by omega, ?_⟩
  have hmod : r.val % S.len = (t.val - 1 - d.val) % S.len := by
    have h1 : (r.val + d.val + 1) % S.len = t.val % S.len := by
      rw [hrt, Nat.mod_eq_of_lt t.isLt]
    have h3 : (r.val + (d.val + 1)) % S.len
        = ((t.val - 1 - d.val) + (d.val + 1)) % S.len := by
      have e : (t.val - 1 - d.val) + (d.val + 1) = t.val := by omega
      rw [e]
      exact h1
    exact Nat.ModEq.add_right_cancel' (d.val + 1) h3
  exact hw2.trans (Genome.window_eq_of_modEq hmod)

/-! ## Historical `I_s` -/

/-- **Historical `I_s`**: §6.4 Definition 1 historical coverage of the observed
read types derived from the sampled start set, plus the existing
placement-based bridging clauses of `InformationFeasible` (every triple repeat
all-bridged, every interleaved pair of repeats bridged), which are unchanged
and clearly identified as the existing sampled-start clauses. -/
def HistoricalInformationFeasible (S : Genome α) (L : ℕ) (R : Finset (Fin S.len)) :
    Prop :=
  HistoricalCovers S L (observedTypes_ofFinset S L R) ∧
    (∀ (e : Fin S.len) (a b c : Fin S.len), S.IsTripleRepeat e.val a b c →
      IsTripleRepeatAllBridged S L R e.val a b c) ∧
    (∀ (e₁ e₂ : Fin S.len) (a b c d : Fin S.len),
      S.IsRepeat e₁.val a b → S.IsRepeat e₂.val c d → Interleaved S a b c d →
        IsInterleavedPairBridged S L R e₁.val e₂.val a b c d)

/-- The old `InformationFeasible` predicate assembled at the saturated
`MatchStarts` set from historical coverage and historical bridging
certificates.  This is the adapter through which the existing structural
no-long-triple-repeat proof applies to the historical model. -/
theorem informationFeasible_matchStarts {S : Genome α} {L : ℕ}
    {observedWords : Finset (Fin L → α)}
    (hcov : HistoricalCovers S L observedWords)
    (htrip : ∀ (e : Fin S.len) (a b c : Fin S.len), S.IsTripleRepeat e.val a b c →
      IsTripleRepeatAllBridged S L (MatchStarts S L observedWords) e.val a b c)
    (hint : ∀ (e₁ e₂ : Fin S.len) (a b c d : Fin S.len),
      S.IsRepeat e₁.val a b → S.IsRepeat e₂.val c d → Interleaved S a b c d →
        IsInterleavedPairBridged S L (MatchStarts S L observedWords) e₁.val e₂.val a b c d) :
    InformationFeasible S L (MatchStarts S L observedWords) :=
  ⟨historicalCovers_covers_matchStarts hcov, htrip, hint⟩

/-- The existing structural no-long-triple-repeat theorem
(`BridgingBridge.informationFeasible_no_long_triple_repeat`) applies to the
historical model at the saturated `MatchStarts` set. -/
theorem historical_no_long_triple_repeat {S : Genome α} {L : ℕ}
    {observedWords : Finset (Fin L → α)} [DecidableEq α] (hL2 : 2 ≤ L)
    (hcov : HistoricalCovers S L observedWords)
    (htrip : ∀ (e : Fin S.len) (a b c : Fin S.len), S.IsTripleRepeat e.val a b c →
      IsTripleRepeatAllBridged S L (MatchStarts S L observedWords) e.val a b c)
    (hint : ∀ (e₁ e₂ : Fin S.len) (a b c d : Fin S.len),
      S.IsRepeat e₁.val a b → S.IsRepeat e₂.val c d → Interleaved S a b c d →
        IsInterleavedPairBridged S L (MatchStarts S L observedWords) e₁.val e₂.val a b c d) :
    ¬ RepeatAdapter.HasLongTripleRepeat S.len_pos S.sym L :=
  BridgingBridge.informationFeasible_no_long_triple_repeat hL2
    (informationFeasible_matchStarts hcov htrip hint)

/-! ## Incomparable-coverage regression examples

The research-assistant counterexamples on #247, kernel-checked: historical
read-string coverage and old sampled-base coverage are **incomparable** —
neither implies the other.  These tiny lemmas pin the incomparability so that
no future refactor can silently conflate the two notions.  Both examples use
`L = 2` or `L = 3` with wraparound windows crossing the chosen origin. -/

section Regression

/-- Four-symbol alphabet for the regression examples. -/
inductive Nuc where
  | A | C | G | T
  deriving DecidableEq, Inhabited, Repr

instance : Fintype Nuc where
  elems := {Nuc.A, Nuc.C, Nuc.G, Nuc.T}
  complete := by intro x; cases x <;> simp

/-- **Case A** (`G = 4`, `L = 3`, only `AAA` sampled at start `0`): historical
coverage holds because `AAA` matches every start of the circular `AAAA`;
old sampled-base coverage fails because base `3` is never covered at the
sampled placement. -/
def genomeA : Genome Nuc where
  len := 4
  len_pos := by norm_num
  sym := ![Nuc.A, Nuc.A, Nuc.A, Nuc.A]

def startsA : Finset (Fin 4) := {⟨0, by norm_num⟩}

theorem historicalCovers_A :
    HistoricalCovers genomeA 3 (observedTypes_ofFinset genomeA 3 startsA) := by
  decide

theorem not_covers_A : ¬ Covers genomeA 3 startsA := by
  decide

/-- **Case B** (`G = 4`, `L = 2`, sampled starts `{0, 2}`, observed words
`{AC, GT}`): old sampled-base coverage holds (reads at `0` and `2` cover all
four bases); historical coverage fails because the length-`1` start intervals
at `1` and `3` contain no observed word match (`CG` and `TA` are unobserved).
This is the `L = 2` edge case, and the window at start `3` wraps around the
origin. -/
def genomeB : Genome Nuc where
  len := 4
  len_pos := by norm_num
  sym := ![Nuc.A, Nuc.C, Nuc.G, Nuc.T]

def startsB : Finset (Fin 4) := {⟨0, by norm_num⟩, ⟨2, by norm_num⟩}

theorem covers_B : Covers genomeB 2 startsB := by
  decide

theorem not_historicalCovers_B :
    ¬ HistoricalCovers genomeB 2 (observedTypes_ofFinset genomeB 2 startsB) := by
  decide

/-- **`L = 2` edge characterization**: for reads of length `2`, start density
means every position is sampled. -/
theorem denseSampledStarts_L2 {R : Finset (Fin 4)} :
    DenseSampledStarts genomeA 2 R ↔ ∀ p : Fin 4, p ∈ R := by
  constructor
  · intro h p
    obtain ⟨r, hr, δ, hδ⟩ := h p
    have hδv : δ.val = 0 := by simp
    have hrw : (p.val + δ.val) % 4 = r.val := hδ
    rw [hδv] at hrw
    have hp4 : p.val < 4 := p.isLt
    have hr4 : r.val < 4 := r.isLt
    have hpr : p = r := Fin.ext (by omega)
    rw [← hpr]
    exact hr
  · intro h p
    refine ⟨p, h p, ⟨0, by norm_num⟩, ?_⟩
    have hp4 : p.val < 4 := p.isLt
    omega

end Regression

/-! ## Decidability

The historical layer is finite for concrete `S` and `observedWords`, so
witness modules can discharge historical certificates by computation. -/

instance (S : Genome α) (L : ℕ) (observedWords : Finset (Fin L → α)) :
    Decidable (HistoricalCovers S L observedWords) := by
  unfold HistoricalCovers; infer_instance

instance (S : Genome α) (L : ℕ) (observedWords : Finset (Fin L → α)) (e : ℕ)
    (t : Fin S.len) : Decidable (HistoricallyBridged S L observedWords e t) := by
  unfold HistoricallyBridged; infer_instance

instance (S : Genome α) (L : ℕ) (R : Finset (Fin S.len)) :
    Decidable (DenseSampledStarts S L R) := by
  unfold DenseSampledStarts; infer_instance

end AssemblyP1.HistoricalCovers
