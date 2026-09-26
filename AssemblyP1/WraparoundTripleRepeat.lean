import AssemblyP1.SameLength62Maximizer

/-!
# The residual regime is non-empty even for truth-feasible realizations

This module is a small, self-contained witness for the single most important
negative fact about `AssemblyP1.SameLength62Maximizer.informationFeasible_62_maximizer`:
the premise `¬ RepeatAdapter.HasLongTripleRepeat` **cannot** be discharged from
source-faithful `InformationFeasible`, not even when the truth is itself a
genuine §6.2 candidate.

`AssemblyP1.BridgingBridge` already shows that `I_s` cannot exclude long triple
repeats, because a bridging read may wrap around the complement arc. The extra
content here is that the wraparound regime survives the *stronger* hypothesis
that the truth is spelled on the observed read support — which, by
`AssemblyP1.SameLength62Maximizer.genuine62_support_eq`, is exactly the
hypothesis that the truth is a genuine §6.2 candidate.

The instance is the circular genome `AAAAB` of length `5`, read length `3`,
read at all five starts.

* `wraparound_information_feasible`: full source-faithful
  `AssemblyP1.SourceFaithfulIs.InformationFeasible`, all three clauses, by
  `decide` on the predicate itself. Concretely, clause 1 (coverage) holds
  because `L = 3` and all five starts are used; clause 2 holds because the only
  maximal triple repeat of length `e ≥ L - 1 = 2` is the one at starts
  `0, 1, 2`, and every copy of it is bridged; clause 3 is vacuous, there being
  no interleaved repeat pair.
* `wraparound_all_windows_observed`: every length-`3` window of the truth is one
  of the realized reads, so the truth's window support is the observed read set.
  By `genuine62_support_eq` this is the honest content of "the truth is a
  genuine §6.2 candidate"; it is recorded here in the directly checkable form
  rather than as a `§6.2` certificate, which would require instantiating the
  whole `Section62Flow` layer at this instance.
* `wraparound_has_long_triple_repeat`: the truth carries a maximal triple repeat
  of length `2 = L - 1` at starts `0, 1, 2`. The three length-`2` windows there
  are all `AA`; the preceding symbols are `B, A, A` and the following symbols are
  `A, A, B`, so the three-copy maximality conditions both hold.

Consequently `informationFeasible_62_maximizer`'s premise is genuinely
residual, and the note `docs/same-length-62-maximizer.md` §4 is correct to leave
it visible rather than claim it away.

In this particular instance the truth nevertheless *is* a maximiser over every
same-support length-`5` competitor (both the truth and the best competitor score
`4/3125` in the exact objective), so the regime contains no counterexample
*here*. No theorem is claimed about the regime in general.
-/

namespace AssemblyP1.WraparoundTripleRepeat

open SourceFaithfulIs

noncomputable section

/-- The three-symbol alphabet. -/
inductive Sym where
  | A | B | C
  deriving DecidableEq, BEq, Repr, Inhabited

/-- The truth: the circular genome `AAAAB` of length `5`. -/
abbrev truth : Genome Sym where
  len := 5
  len_pos := by norm_num
  sym := ![Sym.A, Sym.A, Sym.A, Sym.A, Sym.B]

/-- The realized start set: all five positions. -/
def readStarts : Finset (Fin 5) := {0, 1, 2, 3, 4}

/-- The observed read multiset, as the list the objective consumes: one read at
each of the five starts. -/
def observedReads : Finset (Fin 3 → Sym) :=
  {truth.window 3 0, truth.window 3 1, truth.window 3 2,
    truth.window 3 3, truth.window 3 4}

/-- **Full source-faithful information feasibility at `L = 3`.** A single
`decide` on `InformationFeasible` itself, over every admissible repeat length
and every selection of starts. -/
theorem wraparound_information_feasible :
    InformationFeasible truth 3 readStarts := by
  unfold InformationFeasible
  decide

/-- **The truth's length-`3` windows are all observed reads.** Its window
support is therefore exactly the observed read set, which by
`AssemblyP1.SameLength62Maximizer.genuine62_support_eq` is the honest content of
"the truth is a genuine §6.2 candidate". -/
theorem wraparound_all_windows_observed :
    ∀ r : Fin 5, truth.window 3 r ∈ observedReads := by
  intro r
  fin_cases r <;> simp [observedReads] <;> decide

/-- **And yet the truth carries a long Bresler triple repeat**, of length
`2 = L - 1`, at starts `0, 1, 2`: the three length-`2` windows are all `AA`, the
preceding symbols are `B, A, A`, and the following symbols are `A, A, B`, so
three-copy maximality holds on both sides. -/
theorem wraparound_has_long_triple_repeat :
    RepeatAdapter.HasLongTripleRepeat truth.len_pos truth.sym 3 := by
  refine ⟨0, 1, 2, 2, by omega, by norm_num, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · intro d hd
    interval_cases d <;> decide
  · intro h
    rcases h with ⟨h1, h2⟩
    have hB : OrientedRigidity.cyc truth.len_pos truth.sym (0 + truth.len - 1) = Sym.B := by
      decide
    have hA : OrientedRigidity.cyc truth.len_pos truth.sym (1 + truth.len - 1) = Sym.A := by
      decide
    rw [hB] at h1
    rw [hA] at h1
    exact absurd h1 (by decide)
  · intro h
    rcases h with ⟨h1, h2⟩
    have hA : OrientedRigidity.cyc truth.len_pos truth.sym (0 + 2) = Sym.A := by decide
    have hB : OrientedRigidity.cyc truth.len_pos truth.sym (2 + 2) = Sym.B := by decide
    rw [hA] at h1
    rw [hB] at h2
    exact absurd (h1.symm.trans h2) (by decide)

/-- **The three facts together.** A realization that satisfies full
source-faithful `I_s`, whose truth has all of its length-`L` windows observed,
and which nevertheless carries a long Bresler triple repeat. This is the
explicit counterexample to discharging the premise of
`AssemblyP1.SameLength62Maximizer.informationFeasible_62_maximizer`. -/
theorem informationFeasible_does_not_exclude_long_triple_repeat :
    InformationFeasible truth 3 readStarts ∧
      (∀ r : Fin 5, truth.window 3 r ∈ observedReads) ∧
      RepeatAdapter.HasLongTripleRepeat truth.len_pos truth.sym 3 :=
  ⟨wraparound_information_feasible, wraparound_all_windows_observed,
    wraparound_has_long_triple_repeat⟩

end

end AssemblyP1.WraparoundTripleRepeat
