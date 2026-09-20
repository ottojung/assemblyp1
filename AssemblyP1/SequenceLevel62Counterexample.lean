import Mathlib

/-!
# Kernel-checked finite certificate for the sequence-level §6.2 counterexample

This file kernel-checks the concrete finite instance of
`docs/sequence-level-62-counterexample.md`:

* truth `S = AAAAAB` (circular, length `G = 6`), read length `L = 4`;
* realized read starts `{0, 2, 3, 4, 5}` (five reads);
* observed multiset `x = {AAAA:1, AAAB:1, AABA:1, ABAA:1, BAAA:1}`;
* read-tiled competitor `D = AAABA` (length `5`), `spec_4(D) = x`.

It proves, by `decide`/`norm_num` with exact rational arithmetic:

* `truth_information_feasible`: the source `I_s` hypothesis holds for
  `(S, reads)` — coverage, every maximal triple repeat all-bridged, every
  interleaved repeat pair bridged (all quantifiers range over finite types);
* `truth_section62_feasible` and `competitor_read_tiled`: both `S` and `D` are
  sequence-level §6.2 feasible (support equality and per-occurrence lower
  bounds);
* `competitor_beats_truth`: the exact multinomial likelihood of `D` strictly
  exceeds that of `S` (ratio `3888/3125`).

Scope.  Fixed read length `L = 4`, single-strand reading, binary effective
alphabet, this one finite instance.  This does not settle the source-ambiguous
Shomorony et al. open question, the reverse-complement reading, or the
non-spellable flow level.  The general negative mechanism is the read-tiled
dominance theorem recorded in `docs/read-tiled-counterexample.md`; this file is
the finite kernel check.
-/

namespace AssemblyP1.SequenceLevel62Counterexample

/-- Two-symbol effective alphabet (the witness uses only `A` and `B`). -/
inductive Base where
  | A
  | B
  deriving DecidableEq, Inhabited, Repr

/-- The truth is a circular genome of length `6`. -/
abbrev GenomeS := Fin 6 → Base

/-- The competitor is a circular genome of length `5`. -/
abbrev GenomeD := Fin 5 → Base

/-- A length-`4` read type. -/
abbrev Read := Fin 4 → Base

/-- The `i`-th symbol of a length-`6` circular genome. -/
def cycS (g : GenomeS) (i : Nat) : Base := g ⟨i % 6, Nat.mod_lt _ (by norm_num)⟩

/-- The `i`-th symbol of a length-`5` circular genome. -/
def cycD (g : GenomeD) (i : Nat) : Base := g ⟨i % 5, Nat.mod_lt _ (by norm_num)⟩

/-- The length-`4` circular window of `g` beginning at start `r`. -/
def winS (g : GenomeS) (r : Fin 6) : Read := fun d => cycS g (r.val + d.val)

/-- The length-`4` circular window of `d` beginning at start `r`. -/
def winD (d : GenomeD) (r : Fin 5) : Read := fun e => cycD d (r.val + e.val)

/-- Number of circular starts of `g` whose window is the read type `w`. -/
def occS (g : GenomeS) (w : Read) : Nat :=
  (Finset.univ.filter (fun r : Fin 6 => winS g r = w)).card

/-- Number of circular starts of `d` whose window is the read type `w`. -/
def occD (d : GenomeD) (w : Read) : Nat :=
  (Finset.univ.filter (fun r : Fin 5 => winD d r = w)).card

/-- Read type `AAAA`. -/
def readAAAA : Read := fun _ => Base.A
/-- Read type `AAAB`. -/
def readAAAB : Read := ![Base.A, Base.A, Base.A, Base.B]
/-- Read type `AABA`. -/
def readAABA : Read := ![Base.A, Base.A, Base.B, Base.A]
/-- Read type `ABAA`. -/
def readABAA : Read := ![Base.A, Base.B, Base.A, Base.A]
/-- Read type `BAAA`. -/
def readBAAA : Read := ![Base.B, Base.A, Base.A, Base.A]

/-- The observed support `{AAAA, AAAB, AABA, ABAA, BAAA}`. -/
def support : Finset Read :=
  {readAAAA, readAAAB, readAABA, readABAA, readBAAA}

/-- The true circular genome `S = AAAAAB`. -/
def truth : GenomeS := ![Base.A, Base.A, Base.A, Base.A, Base.A, Base.B]

/-- The read-tiled competitor `D = AAABA`. -/
def competitor : GenomeD := ![Base.A, Base.A, Base.A, Base.B, Base.A]

/-- The realized read start positions `{0, 2, 3, 4, 5}`. -/
def readStarts : Finset (Fin 6) := {0, 2, 3, 4, 5}

/-! ## `I_s` certificate for the truth -/

/-- Length-`ell` circular window of `g` at position `i`, as a list. -/
def winLen (g : GenomeS) (ell i : Nat) : List Base :=
  (List.range ell).map (fun j => cycS g (i + j))

/-- The symbol immediately preceding position `i`. -/
def prec (g : GenomeS) (i : Nat) : Base := cycS g (i + 6 - 1)

/-- The symbol immediately following a length-`ell` copy at position `i`. -/
def foll (g : GenomeS) (i ell : Nat) : Base := cycS g (i + ell)

/-- A maximal triple repeat: three equal length-`ell` windows whose preceding
symbols are not all equal and whose following symbols are not all equal. -/
abbrev TripleRepeat (g : GenomeS) (ell : Nat) (a b c : Fin 6) : Prop :=
  winLen g ell a.val = winLen g ell b.val ∧
  winLen g ell b.val = winLen g ell c.val ∧
  ¬(prec g a.val = prec g b.val ∧ prec g b.val = prec g c.val) ∧
  ¬(foll g a.val ell = foll g b.val ell ∧
      foll g b.val ell = foll g c.val ell)

/-- A maximal repeat pair: equal length-`ell` windows whose preceding symbols
differ and whose following symbols differ. -/
abbrev RepeatPair (g : GenomeS) (ell : Nat) (a b : Fin 6) : Prop :=
  a ≠ b ∧ winLen g ell a.val = winLen g ell b.val ∧
  prec g a.val ≠ prec g b.val ∧ foll g a.val ell ≠ foll g b.val ell

/-- Position `p` is covered by the read starting at `r` (length `4`). -/
abbrev CoveredBy (r : Fin 6) (p : Nat) : Prop :=
  ∃ d : Fin 4, p % 6 = (r.val + d.val) % 6

/-- The copy at position `t` is bridged: some realized read covers one base
strictly before and one base strictly after the length-`ell` copy. -/
abbrev Bridged (t ell : Nat) : Prop :=
  ∃ r ∈ readStarts, CoveredBy r (t + 6 - 1) ∧ CoveredBy r (t + ell)

/-- The four positions `a,b,c,d` in cyclic order (a sorted list of values). -/
def cyclicOrder (a b c d : Fin 6) : List Nat :=
  (List.range 6).filter
    (fun v => v = a.val ∨ v = b.val ∨ v = c.val ∨ v = d.val)

/-- Labels of the cyclic order: `0` for the first pair `{a,b}`, `1` otherwise. -/
def cyclicLabels (a b c d : Fin 6) : List Nat :=
  (cyclicOrder a b c d).map
    (fun v => if v = a.val ∨ v = b.val then (0 : Nat) else 1)

/-- The four positions alternate as two labelled pairs on the circle. -/
abbrev Interleaved (a b c d : Fin 6) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
  (cyclicLabels a b c d = [0, 1, 0, 1] ∨
    cyclicLabels a b c d = [1, 0, 1, 0])

/-- Coverage: the realized length-`4` reads cover all six positions. -/
abbrev Covers : Prop :=
  ∀ p : Fin 6, ∃ r ∈ readStarts, ∃ d : Fin 4, p.val = (r.val + d.val) % 6

/-- Every maximal triple repeat of the truth is all-bridged. -/
abbrev AllBridgedTriples (g : GenomeS) : Prop :=
  ∀ ell : Fin 5, ∀ a b c : Fin 6, TripleRepeat g (ell.val + 1) a b c →
    Bridged a.val (ell.val + 1) ∧ Bridged b.val (ell.val + 1) ∧
      Bridged c.val (ell.val + 1)

/-- Every interleaved repeat pair of the truth is bridged. -/
abbrev AllInterleavedBridged (g : GenomeS) : Prop :=
  ∀ e1 : Fin 5, ∀ a b : Fin 6, RepeatPair g (e1.val + 1) a b →
  ∀ e2 : Fin 5, ∀ c d : Fin 6, RepeatPair g (e2.val + 1) c d →
  Interleaved a b c d →
    (Bridged a.val (e1.val + 1) ∨ Bridged b.val (e1.val + 1)) ∨
      (Bridged c.val (e2.val + 1) ∨ Bridged d.val (e2.val + 1))

/-- The source information-feasible hypothesis `I_s` for this instance. -/
abbrev informationFeasibleS : Prop :=
  Covers ∧ AllBridgedTriples truth ∧ AllInterleavedBridged truth

set_option synthInstance.maxHeartbeats 1000000 in
set_option synthInstance.maxSize 4096 in
/-- The source `I_s` hypothesis holds (all predicates checked by `decide`). -/
theorem truth_information_feasible : informationFeasibleS := by
  refine ⟨?_, ?_, ?_⟩
  · unfold Covers; decide
  · unfold AllBridgedTriples; decide
  · unfold AllInterleavedBridged; decide

/-! ## Sequence-level §6.2 feasibility of `S` and `D` -/

/-- Every length-`4` window of the truth is an observed read type. -/
abbrev WindowSupportedS : Prop := ∀ r : Fin 6, winS truth r ∈ support

/-- Every observed read type occurs in the truth (so support equality holds). -/
abbrev SupportCoveredS : Prop := ∀ w ∈ support, occS truth w > 0

/-- Per-occurrence lower bounds for the truth: `d_S(w) ≥ x_w` with `x_w = 1`. -/
abbrev LowerBoundedS : Prop := ∀ w ∈ support, occS truth w ≥ 1

/-- The competitor is read-tiled: `spec_4(D) = x`. -/
abbrev ReadTiledD : Prop :=
  (∀ r : Fin 5, winD competitor r ∈ support) ∧
    (∀ w ∈ support, occD competitor w = 1)

/-- Sequence-level §6.2 feasibility of the truth. -/
abbrev Section62FeasibleS : Prop :=
  WindowSupportedS ∧ SupportCoveredS ∧ LowerBoundedS

/-- The truth is sequence-level §6.2 feasible. -/
theorem truth_section62_feasible : Section62FeasibleS := by
  unfold Section62FeasibleS WindowSupportedS SupportCoveredS LowerBoundedS
    support occS winS cycS truth
  decide

/-- The competitor is read-tiled, hence sequence-level §6.2 feasible. -/
theorem competitor_read_tiled : ReadTiledD := by
  unfold ReadTiledD support occD winD cycD competitor
  decide

/-! ## Exact multinomial likelihood -/

/-- Exact multinomial likelihood of the five observed reads (each type once,
`n = 5`) under a length-`6` circular candidate with occurrence counts `occS`. -/
def likelihoodTruth : ℚ :=
  (120 : ℚ) * ((occS truth readAAAA : ℚ) / 6) *
    ((occS truth readAAAB : ℚ) / 6) * ((occS truth readAABA : ℚ) / 6) *
    ((occS truth readABAA : ℚ) / 6) * ((occS truth readBAAA : ℚ) / 6)

/-- Exact multinomial likelihood under the length-`5` read-tiled competitor. -/
def likelihoodCompetitor : ℚ :=
  (120 : ℚ) * ((occD competitor readAAAA : ℚ) / 5) *
    ((occD competitor readAAAB : ℚ) / 5) * ((occD competitor readAABA : ℚ) / 5) *
    ((occD competitor readABAA : ℚ) / 5) * ((occD competitor readBAAA : ℚ) / 5)

theorem occS_AAAA : occS truth readAAAA = 2 := by decide
theorem occS_AAAB : occS truth readAAAB = 1 := by decide
theorem occS_AABA : occS truth readAABA = 1 := by decide
theorem occS_ABAA : occS truth readABAA = 1 := by decide
theorem occS_BAAA : occS truth readBAAA = 1 := by decide
theorem occD_AAAA : occD competitor readAAAA = 1 := by decide
theorem occD_AAAB : occD competitor readAAAB = 1 := by decide
theorem occD_AABA : occD competitor readAABA = 1 := by decide
theorem occD_ABAA : occD competitor readABAA = 1 := by decide
theorem occD_BAAA : occD competitor readBAAA = 1 := by decide

/-- Exact likelihood of the observed reads under the truth. -/
theorem likelihood_truth : likelihoodTruth = 5 / 162 := by
  unfold likelihoodTruth
  rw [occS_AAAA, occS_AAAB, occS_AABA, occS_ABAA, occS_BAAA]
  norm_num

/-- Exact likelihood of the observed reads under the competitor. -/
theorem likelihood_competitor : likelihoodCompetitor = 24 / 625 := by
  unfold likelihoodCompetitor
  rw [occD_AAAA, occD_AAAB, occD_AABA, occD_ABAA, occD_BAAA]
  norm_num

/-- The exact likelihood ratio is `3888/3125`. -/
theorem likelihood_ratio :
    likelihoodCompetitor / likelihoodTruth = 3888 / 3125 := by
  rw [likelihood_competitor, likelihood_truth]
  norm_num

/-- The read-tiled competitor strictly beats the truth in exact likelihood. -/
theorem competitor_beats_truth :
    likelihoodTruth < likelihoodCompetitor := by
  rw [likelihood_truth, likelihood_competitor]
  norm_num

/-- Main finite statement: the instance satisfies `I_s`, both genomes are
sequence-level §6.2 feasible, and the competitor strictly beats the truth. -/
theorem sequence_level_section62_counterexample :
    informationFeasibleS ∧ Section62FeasibleS ∧ ReadTiledD ∧
      likelihoodTruth < likelihoodCompetitor :=
  ⟨truth_information_feasible, truth_section62_feasible,
    competitor_read_tiled, competitor_beats_truth⟩

end AssemblyP1.SequenceLevel62Counterexample
