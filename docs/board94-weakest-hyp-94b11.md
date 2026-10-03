# Board 94 — weakest hypothesis: dropping `IsPrimitive` from step 4

Front 94b11. Worktree `/workspace/assemblyp1-94-replacement`, branch `board/94-replacement`
at `666e849`. Status: **in progress** (this file is written incrementally).

## 0. Scope

94a09 (`078d2b7`) proved `selectedInterleaved_admissible`
(`SelectedInterleaved hG L S θ → AdmissibleObstruction hG L S`) under
`2 ≤ L ∧ IsPrimitive hG S ∧ ¬ LongObstruction hG L S`, and in §3 of its report
wrote that the *weakest form actually needed* is "only that the shift between
the two selected starts of the blocked constituent is not a period", while
explicitly **not** claiming that this weaker hypothesis is sufficient or
necessary. Closing that gap is this front's entire scope.

## 1. What the hypothesis is used for (analysis, from `078d2b7`)

`rightMax_of_doubled` (in `AssemblyP1/BBTInterleavedAdmissible.lean`) is the only
consumer of `hprim : IsPrimitive hG S`, in exactly two places:

1. deriving `L - 1 < G` via `RepeatAdapter.not_primitive_of_ge_G_agree`;
2. in the *blocked* case, ruling out `T.max' = G - 1`, i.e. the two copies
   agreeing on a **full turn**, again via `not_primitive_of_ge_G_agree`.

Both are the same underlying statement: agreement of `a` and `b` on `≥ G`
positions makes the shift between them a period of the circular word.
`not_primitive_of_ge_G_agree` produces that period as
`s = (b % G + G - a % G) % G`. So the hypothesis that is actually consumed is

```
H(a b) := ¬ ShiftInvariant hG S ((b.val + G - a.val) % G)
```

— the negation of *period-ness of that one shift*, exactly the weaker
hypothesis §3 of the 94a09 report names.

Further structural observation (this is the shape of the discharger):

* the *unblocked* case needs **no** hypothesis at all: `maximalRepeat_of_branch`
  already produces a maximal (hence right-maximal) repeat at the same starts;
* hence the minimal sufficient hypothesis per constituent pair `(a, b)` is the
  disjunction `Preceding a ≠ Preceding b ∨ H(a b)` — the weak hypothesis is
  needed **only for the blocked constituent**, which is precisely the form the
  report advertises.

`IsPrimitive hG S` implies `H(a b)` for every pair, so the new theorem strictly
subsumes `selectedInterleaved_admissible` (94a09) rather than merely resembling it.

## 2. Expected minimal statement (to be kernel-checked)

Planned module `AssemblyP1/BBTInterleavedWeak.lean`:

* `rightMax_of_doubled_weak`: for `a ≠ b`, doubled `(L-1)`-mer,
  `Preceding a ≠ Preceding b ∨ H(a b) ⟹ ∃ e < G, L - 1 ≤ e, IsRightRepeat e a b`;
* `selectedInterleaved_admissible_weak`: at general `G`, general `L`,
  `2 ≤ L ∧ SelectedInterleaved θ ∧ ¬ LongObstruction ∧ (one weak hypothesis per
  constituent pair) ⟹ AdmissibleObstruction`;
* non-vacuity: an explicit kernel-checked inhabitant (planned: `00101`, `G = 5`,
  `L = 3`, reusing `hypotheses_inhabited_00101` from 94a09);
* `#print axioms` for every claim.

## 3. Host/build notes

`AssemblyP1/BBTAdmissibleObstruction.lean` and
`AssemblyP1/BBTInterleavedAdmissible.lean` (from `b0de723` / `078d2b7` on
`board/94-chain`) are **not** on this branch; they were materialised locally,
untracked, purely as elaboration dependencies. `AssemblyP1/BBTReplacementInvariant.lean`
needed a fresh `-o` elaboration and is slow on this host (>600 s); being built now.

## 4. Falsification first (no counterexample found)

`scratch/94b11_census.py` transcribes the same definitions (`SelectedInterleaved`,
`InterleavedStarts`, `Preceding`, `IsRightRepeat`, `AdmissibleObstruction`,
`IsPeriod`, `IsPrimitive`) and searches **all** unary and binary circular words
`3 ≤ G ≤ 8`, `2 ≤ L ≤ 4`, all interleaved quadruples of doubled `(L-1)`-mers:

* selected interleavings at non-primitive genomes: 14512 quadruples;
* quadruples satisfying the weak hypothesis: 58256;
* quadruples satisfying the weak hypothesis at which `AdmissibleObstruction`
  **fails**: **0**.

So there is no counterexample to "the shift is not a period" on a
non-primitive genome, in this range. Census is evidence only; §3's theorem is
the proof. (One transcription bug was found and fixed en route: an inverted
blocking test in `admissible`, which initially reported 1088 spurious
counterexamples.)

## 5. The weak form (kernel-checked in progress)

New module `AssemblyP1/BBTInterleavedWeak.lean` (untracked dependency modules
`BBTAdmissibleObstruction.lean`, `BBTInterleavedAdmissible.lean` copied in from
`board/94-chain` for elaboration only):

* `NotPeriodShift hG S a b := ¬ ShiftInvariant hG S ((b.val + G - a.val) % G)`
  — the project's own notion of "the shift between the two starts is a period"
  (`RepeatAdapter.ShiftInvariant`), negated at exactly one shift.
* `shiftInvariant_of_agrees_G`: agreement on a full turn forces that shift to
  be a period. Together with `not_agrees_G_of_notPeriodShift` this shows the
  weak hypothesis is **exactly** "the two copies do not agree on a full turn":
  neither weaker nor stronger is meaningful here, since a full turn of
  agreement is precisely the `0101` obstruction (`no_rightRepeat_0101` in 94a09).
* `isPrimitive_notPeriodShift`: `IsPrimitive → NotPeriodShift` at every pair,
  so `selectedInterleaved_admissible_weak_of_primitive` **subsumes**
  `selectedInterleaved_admissible`; 94a09's theorem is a special case.
* `rightMax_of_doubled_weak`: per pair, the hypothesis is only
  `Preceding a ≠ Preceding b ∨ NotPeriodShift hG S a b`; the unblocked case
  consumes nothing (the library's `maximalRepeat_of_branch`), so the weak
  hypothesis is needed **for the blocked constituent only**, exactly as §3 of
  the 94a09 report advertises.
* `selectedInterleaved_admissible_weak`: the residual at general `G`, general
  `L`, with `SelectedInterleaved`, `¬ LongObstruction` and the per-quadruple
  `WeakInterleavingHyp`.
* Non-vacuity, kernel-checked: `weak_hypotheses_inhabited_00101` at
  `00101`, `G = 5`, `L = 3`, with witnessing quadruple `(1, 3, 2, 4)` at which
  the pair `(2, 4)` **is** preceding-blocked (`blocked_00101`) and **does** have
  a non-period shift (`notPeriodShift_2_4_00101`) — so the second disjunct is
  genuinely load-bearing, not decorative.

## 6. Answer to the brief's questions

* Is `IsPrimitive` genuinely necessary? **No.** The discharger uses it only to
  exclude a full turn of agreement between the two starts of a blocked
  constituent, and that is exactly `NotPeriodShift` at one shift. Proved above.
* Is the brief's advertised hypothesis sufficient? **Yes**, and the weaker
  per-pair disjunction is sufficient, which is strictly weaker still (nothing
  is required of unblocked pairs).
* Necessity: if the shift between the starts of a blocked pair **is** a period
  then the copies agree at every offset, so no right-maximal repeat exists at
  those starts at all and `AdmissibleObstruction` is unattainable — this is
  94a09's `no_rightRepeat_0101`, and it is why the weak hypothesis cannot be
  weakened further.

## 7. Kernel-checked results (`AssemblyP1/BBTInterleavedWeak.lean`, 0 errors 0 warnings)

```
cyc_congr_of_mod                  : congruence of `cyc` mod G
shiftInvariant_of_agrees_G         : full-turn agreement  ⟹  the shift is a period
not_agrees_G_of_notPeriodShift    : the converse reading of the weak hypothesis
isPrimitive_notPeriodShift        : IsPrimitive ⟹ NotPeriodShift   (94a09 subsumed)
shift_residue                     : congruence bookkeeping for the shift
no_rightRepeat_of_periodShift     : if the shift IS a period, no right-maximal repeat
                                    at those starts at all  (necessity)
rightMax_of_doubled_weak          : doubled (L-1)-mer, unblocked OR non-period shift
                                    ⟹ right-maximal repeat of length ≥ L-1 at the
                                    SAME two starts
selectedInterleaved_admissible_weak        : the residual at general G, general L
selectedInterleaved_admissible_weak_of_primitive : 94a09's theorem as a corollary
blocked_00101 / notPeriodShift_2_4_00101 /
weak_hypotheses_inhabited_00101   : non-vacuity
```

`#print axioms` (`docs/board94-weakest-hyp-94b11-axioms.txt`): every claim depends
only on `[propext, Classical.choice, Quot.sound]` (`blocked_00101` on `propext`
alone). No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`,
`@[implemented_by]`, `opaque`, and **no linter suppression** (0 warnings).

## 8. Answer to the brief's questions

* **Is `IsPrimitive` necessary?** No. The discharger consumes it in exactly two
  places, both being "the two starts of a blocked constituent do not agree on a
  full turn", i.e. `NotPeriodShift` at one shift. Proved.
* **Is the advertised weaker hypothesis sufficient?** Yes, and the minimal
  sufficient form is weaker still: per pair only
  `Preceding a ≠ Preceding b ∨ NotPeriodShift hG S a b`, since the unblocked
  case consumes nothing.
* **Can it be weakened further?** No: `no_rightRepeat_of_periodShift` shows that
  if the shift *is* a period then no right-maximal repeat exists at those starts
  at all, so no admissible obstruction can use them. Sufficient **and**
  necessary: the weak hypothesis is exactly right.
* **Is it non-vacuous?** Yes, kernel-checked. `weak_hypotheses_inhabited_00101`
  at `00101`, `G = 5`, `L = 3`: interleaved quadruple `(1, 3, 2, 4)`, the first
  pair unblocked, the second pair **blocked** (`blocked_00101`) **and** joined by
  a non-period shift (`notPeriodShift_2_4_00101`) --- so the second, non-period
  disjunct is genuinely load-bearing at a genuine instance, not vacuous.
* **Relation to 94a09.** `selectedInterleaved_admissible_weak_of_primitive`
  re-derives `selectedInterleaved_admissible` from the weak theorem, so nothing
  in 94a09 is lost or contradicted; the only content added is that primitivity
  of the whole word is more than the discharger needs.

## 9. Notes for integration

* `AssemblyP1/BBTAdmissibleObstruction.lean` and
  `AssemblyP1/BBTInterleavedAdmissible.lean` are **copies** from `board/94-chain`
  (`b0de723`, `078d2b7`), materialised untracked in this worktree purely so
  that `BBTInterleavedWeak.lean` elaborates. They are not committed here; when
  this branch is integrated those imports already exist upstream.
* Build facts on this host: `AssemblyP1/BBTReplacementInvariant.olean` was
  missing and had to be elaborated with
  `lake env lean AssemblyP1/BBTReplacementInvariant.lean -o .lake/build/lib/lean/AssemblyP1/BBTReplacementInvariant.olean`,
  which takes >35 min. `lake build` was never used and Mathlib was not rebuilt.
* The census script `scratch/94b11_census.py` is left in the worktree as
  evidence; its output is not a proof.

B94-WH-PROVED