import AssemblyP1.SameLength62Maximizer

/-!
# The "wraparound regime" was an artifact of a wrong `BridgesCopy`

This module used to be a small, self-contained witness for the single most
important negative fact about
`AssemblyP1.SameLength62Maximizer.informationFeasible_62_maximizer`: that the
premise `¬ RepeatAdapter.HasLongTripleRepeat` **could not** be discharged from
source-faithful `InformationFeasible`. The instance was the circular genome
`AAAAB` of length `5`, read length `3`, read at all five starts, and it was
kernel-checked as

* `wraparound_information_feasible` — full source-faithful
  `AssemblyP1.SourceFaithfulIs.InformationFeasible`, all three clauses;
* `wraparound_has_long_triple_repeat` — a maximal triple repeat of length
  `2 = L - 1` at starts `0, 1, 2`.

## What changed

`SourceFaithfulIs.BridgesCopy` was, until this commit, the *endpoint-only*
condition

```
∃ r ∈ R, the read at r covers (t - 1) % G  and  the read at r covers (t + e) % G
```

which is **not** the source's condition. Bresler et al. (Fig. 5 and the
paragraph before Theorem 1) and Shomorony et al. (§3/Fig. 6) require one read to
*strictly straddle* the occurrence, i.e. on a suitable integer lift
`r < t'` and `t' + e < r + L`; see `docs/bridging-source-semantics.md`. The
endpoint-only reading lets a read of length `L` reach the two endpoints of a
**long** copy by travelling around the *complementary* circular arc, without ever
containing the copy. For `AAAAB` at `L = 3` that is exactly what happened: the
read at start `4` covers positions `4, 0, 1`, so it covers the predecessor `4`
of the copy at `0` and ... the endpoints of the length-`2` copy at `0` are
positions `4` and `2`, and no length-`3` read contains the copy at all.

`BridgesCopy` is now the source's straddling condition (one realized read, one
offset `d`, the copy at offset `d + 1`, with `d + e + 1 < L`). Its sharp
consequence is `SourceFaithfulIs.bridgesCopy_length : e + 2 ≤ L`, and hence

`BridgingBridge.informationFeasible_no_long_triple_repeat : 2 ≤ L → R ∈ I_s →
¬ HasLongTripleRepeat`,

so **no** genome in `I_s` carries a long triple repeat at all, and the
"wraparound regime" is empty.

## What this module records now

* `aaaab_not_information_feasible` — the former witness, kernel-checked as
  **not** `I_s`-feasible under the corrected semantics. This is the artifact,
  pinned down.
* `aaaab_has_long_triple_repeat` — the instance's long triple repeat, which is
  still a true fact about `AAAAB` and is exactly what clause 2 of `I_s` now
  forbids.
* `wraparound_all_windows_observed` — every length-`3` window of `AAAAB` is a
  realized read, so the instance is a genuine §6.2 candidate instance in the
  honest sense; it is only the `I_s` membership that fails.
* `informationFeasible_excludes_this_instance` — the pair, i.e. the explicit
  statement that this genome is excluded by the source's `I_s` precisely because
  of its long triple repeat.

The whole downstream research programme that the artifact supported —
`AssemblyP1.MLEscape`'s culprit statement `EscapeForcesMidRangeRepeat`, the
`HasWraparoundTripleRepeat` band, and the `G - L` escape route — is removed in
the same commit. `docs/issue88-wraparound-contrapositive.md` records what that
programme claimed and why it is void.
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

/-- **The former witness is not information-feasible any more.** A single
`decide` on `InformationFeasible` itself, over every admissible repeat length
and every selection of starts.

The refutation is clause 2. The only maximal triple repeat of length `e ≥ 1` is
the one at starts `0, 1, 2` with `e = 2`; a bridged copy must satisfy
`e + 2 ≤ L`, i.e. `4 ≤ 3`, so that copy cannot be bridged by any read of length
`3` at any start, and the triple repeat is not all-bridged. -/
theorem aaaab_not_information_feasible :
    ¬ InformationFeasible truth 3 readStarts := by
  unfold InformationFeasible
  decide

/-- **The truth's length-`3` windows are all observed reads.** Its window
support is therefore exactly the observed read set, which by
`AssemblyP1.SameLength62Maximizer.genuine62_support_eq` is the honest content of
"the truth is a genuine §6.2 candidate". The instance is a genuine candidate
instance; it is only the `I_s` membership that fails. -/
theorem wraparound_all_windows_observed :
    ∀ r : Fin 5, truth.window 3 r ∈ observedReads := by
  intro r
  fin_cases r <;> simp [observedReads] <;> decide

/-- **And yet the truth carries a long Bresler triple repeat**, of length
`2 = L - 1`, at starts `0, 1, 2`: the three length-`2` windows are all `AA`, the
preceding symbols are `B, A, A`, and the following symbols are `A, A, B`, so
three-copy maximality holds on both sides.

This is the fact that clause 2 of `I_s` forbids, and
`BridgingBridge.informationFeasible_no_long_triple_repeat` turns that
forbidding into a general theorem. -/
theorem aaaab_has_long_triple_repeat :
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

/-- **This genome is excluded by the source's `I_s` precisely because of its long
triple repeat.** The former counterexample to
`informationFeasible_62_maximizer`'s premise, restated in the corrected
semantics: there is no gap, because
`BridgingBridge.informationFeasible_no_long_triple_repeat` discharges the
premise from `I_s`. -/
theorem informationFeasible_excludes_this_instance :
    (¬ InformationFeasible truth 3 readStarts) ∧
      RepeatAdapter.HasLongTripleRepeat truth.len_pos truth.sym 3 ∧
      (∀ r : Fin 5, truth.window 3 r ∈ observedReads) :=
  ⟨aaaab_not_information_feasible, aaaab_has_long_triple_repeat,
    wraparound_all_windows_observed⟩

end

end AssemblyP1.WraparoundTripleRepeat
