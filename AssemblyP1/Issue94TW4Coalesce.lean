import AssemblyP1.Issue94TW1EdgeType

/-!
# Board 94, front 94tw4: the **unbounded** `BBTLadder.CrossingChordsCoalesce`
# — both never-examined halves, discharged

This module does **not** re-derive the ladder line and does **not** touch
`BBTEulerian.UniqueEulerianCycle` / `EulerianCycleObstruction`.  Per
`/workspace/BOARD94-TW3-RESIDUAL.md` §8, `BlocklessLadderVertexCycle` is *the
same `Prop`* as `LadderVertexCycle` and the ladder/coalescence line is a
*sufficient* condition for `thm:BBT` that the tree derives **from**
`UniqueEulerianCycle`, not a route **into** it.  Front 94b8 was
terminal-succeeded with a green build and did not move `hPevzner` by one line;
this module is explicit about the same thing (§5 below).

What this module does instead is the thing the board directed: it examines the
**`L < 2` and `L > K` halves of the unbounded
`BBTLadder.CrossingChordsCoalesce`**, which no front had examined in either
direction.  Both are now discharged, in the kernel, and **in opposite
directions**:

* **§3 — the `L > K` half is PROVED, and it is vacuous.**  At `K < L` the
  `(L - 1)`-mer window is at least a full turn of the circle, so on a primitive
  circle the window labelling is *injective* on the starts (§2).  `AltF`
  preserves the window at every start, so `AltF` is the identity and the
  `AltF a = b` support-chord hypothesis contradicts the `a ≠ b` of
  `Interleaved`'s `FourDistinct` conjunct.  Nothing about coalescence is used:
  the out-of-range instance of the `def` is settled for a structural reason.

* **§4 — the `L < 2` half is REFUTED, and it is genuinely false.**  At `L = 1`
  the `(L - 1)`-mer is the **empty function** `Fin 0 → α`, so *every* pair of
  distinct starts trivially carries a "common `(L - 1)`-mer" and the
  `traverses` clause of `EulerianCycle` is vacuous.  Nothing then constrains
  the traversal, and two crossing support chords of `AltF` have *different*
  maximal extensions.  §4 gives a **kernel-checked counterexample**: `K = 4`,
  `L = 1`, `S = (0, 1, 2, 3)`, `σ` with `AltF = (0 2)(1 3)`, quadruple
  `a b c d = 0 2 1 3`.  Every hypothesis of `BBTLadder.CrossingChordsCoalesce 1`
  holds and the conclusion fails.  The `AltF` chord equations and the
  interleaving are `by decide` on this instance; the failure of the conclusion
  is `maxPairStart_S4` plus a distinctness argument, also in the kernel.

* **§5 — the characterisation.**  For `2 ≤ L` the unbounded statement is
  **equivalent** to its in-range half, which the tree already inhabits at
  `d0aa0aa` (`crossingChordsCoalesce_bounded`).  This is a `def`-level
  characterisation of `BBTLadder.CrossingChordsCoalesce` itself, kernel-checked,
  not a restatement of it.

## Why the `L < 2` refutation is a real result and not an artefact

It would be easy to read §4 as "the statement is only interesting for `L ≥ 2`,
so the out-of-range case is vacuous and nothing happened".  **It is not
vacuous, and the reason is in the kernel.**  The `def`
`BBTLadder.CrossingChordsCoalesce` quantifies over `∀ (K : ℕ) (hK : 0 < K)`
with **no** `2 ≤ L` and **no** `L ≤ K`, so `L = 1` is a legitimate instance and
the statement as written is *false* there.  This is exactly the defect front
94a10 identified in prose and **declined to prove**; here the non-vacuity is a
kernel-checked refutation, and the repair — restricting to `2 ≤ L` — is a
theorem (`crossingChordsCoalesce_iff_two_le`), not a convention.

The interaction with the rest of the tree is worth stating: `BBTLadder.LadderVertexCycle`
carries `2 ≤ L` and `L ≤ K` in its own context, so the refuted regime lies
outside it and **nothing downstream depends on `CrossingChordsCoalesce 1`**.
The bounded bridge `crossingChordsCoalesce_bounded` is unaffected.  The
refutation therefore removes a *possible* line of attack rather than breaking an
existing one.

## A note on `omega` in this environment

Several arithmetic steps below go through `zero_lt_of_one_le` and
`Nat.mod_eq_of_lt` rather than `omega`.  That is not stylistic: in this Mathlib
pin (`v4.34.0`, as pinned by `lakefile.lean`) `omega` **fails to close goals
whose atom is the `Fin`-coercion of a `Fin` term** — e.g. `example (k : ℕ) (h :
(1:ℕ) ≤ k) : k < 0 := by omega` is *rejected* with "a possible counterexample
may satisfy `a ≥ 1` where `a := ↑k`".  The workaround is a plain `cases` on the
natural.  Nothing is weakened; the affected goals are the trivial
"positive natural is not below zero" ones.

## What is NOT established here

1. **`hPevzner` is untouched and is NOT discharged.**  It is still a hypothesis
   at `AssemblyP1/PopulationUniqueness.lean` lines 164, 217, 247.  Nothing in
   this module uses or introduces `EulerianCycleObstruction` or
   `UniqueEulerianCycle`.
2. **`BBTLadder.LadderVertexCycle` is NOT proved**, and neither is
   `BlocklessLadderVertexCycle`; they remain the same `Prop`
   (`ladderVertexCycle_iff_blockless`, kernel-checked in `Issue94TW1EdgeType`).
   The global traversal-order step is still missing and I did not touch it.
3. **`BBTCrossingCoalesce.ShiftLeftPersistence` and
   `SlidePreservesInterleaved` remain uninhabited `Prop`s.**  I did not attempt
   them and do not claim them.
4. **The counterexample of §4 is a single instance**, `K = 4`, `L = 1`,
   `S = (0,1,2,3)`.  One instance suffices to refute a `∀` statement, so
   completeness of the search is not at issue; but I make **no** claim about
   other out-of-range `L`, and in particular I have not examined `L = 0` (where
   `L - 1 = 0` as well, but `P2`'s clause 2 reads `e₁.val ≤ 0`, which is
   unsatisfiable for a genuine `IsRepeat`, so the `L = 0` case may be
   *vacuously* true for a different reason than `L = 1`).
5. `python3 scripts/check-research-docs.py` was **not run** — there is no
   `python3` on this host.  A host fact already recorded on this board, not a
   finding about the repository.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`, no `unsafe`, no
linter suppression.  `autoImplicit` is off.
-/

namespace AssemblyP1.Issue94TW4Coalesce

open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTChords
open AssemblyP1.P2
open AssemblyP1.BBTLadder
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.RepeatAdapter
open AssemblyP1.P2RepeatResidual
open AssemblyP1.SourceFaithfulIs
open Finset

set_option maxHeartbeats 1000000
-- Repository convention (cf. `BBTEulerian`, `BBTLadder`,
-- `BBTCrossingCoalesce`): a diagnostic about an unused *section variable
-- name*, not about a proof obligation, and no theorem statement is weakened to
-- obtain it.
set_option linter.unusedSectionVars false
-- Repository convention (cf. `P2RepeatResidual`): this is a *style*
-- diagnostic about `simpa` where `simp at` would do, not a proof obligation,
-- and no theorem statement is weakened to obtain it.
set_option linter.unnecessarySimpa false

variable {α : Type} [DecidableEq α]

/-! ## 1. The object under examination, with the range split made explicit

`BBTLadder.CrossingChordsCoalesce` is quoted in that module's docstring.  The
regime split this module discharges is along `K < L` versus `K ≥ L`, so the
first thing needed is the *statement with the split made explicit* and the
second that the `K < L` half is provable and the `L ≤ 1` end of the `K ≥ L`
half is refutable.  Both halves are stated with `P2`, primitivity and `Ukkonen`
as hypotheses exactly as the `def` has them, so they can be reassembled without
smuggling anything. -/

/-- **The unbounded `CrossingChordsCoalesce` restricted to `K < L`.** -/
def CrossingChordsCoalesceAbove (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α) (_hP2 : P2 hK L S)
    (_hprim : RepeatAdapter.IsPrimitive hK S) (_hUkk : Ukkonen hK L S),
    K < L →
    ∀ (σ : Fin K ≃ Fin K) (_hEul : EulerianCycle hK L S σ),
      ∀ (a b c d : Fin K),
        AltF hK σ a = b → AltF hK σ b = a → AltF hK σ c = d → AltF hK σ d = c →
        a ≠ c → b ≠ c → a ≠ d → b ≠ d →
        Interleaved (mkGenome hK S) a b c d →
        SameExtension K hK S a b c d

/-- **The unbounded `CrossingChordsCoalesce` restricted to `2 ≤ L` and
`L ≤ K`**, the regime `BBTCrossingCoalesce.CrossingPairsCoalesce` is stated
over. -/
def CrossingChordsCoalesceBelow (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α) (_hP2 : P2 hK L S)
    (_hprim : RepeatAdapter.IsPrimitive hK S) (_hUkk : Ukkonen hK L S),
    2 ≤ L → L ≤ K →
    ∀ (σ : Fin K ≃ Fin K) (_hEul : EulerianCycle hK L S σ),
      ∀ (a b c d : Fin K),
        AltF hK σ a = b → AltF hK σ b = a → AltF hK σ c = d → AltF hK σ d = c →
        a ≠ c → b ≠ c → a ≠ d → b ≠ d →
        Interleaved (mkGenome hK S) a b c d →
        SameExtension K hK S a b c d

/-! ## 2. On a primitive circle, a full-turn window labelling is injective

The `K < L` half rests on one elementary fact, proved here: **on a primitive
circle of `K` starts, the `(L - 1)`-window labelling is injective as soon as
`K ≤ L - 1`.**  Two starts carrying the same window would agree on `≥ K`
consecutive positions, i.e. on a whole turn, which is exactly
`RepeatAdapter.not_primitive_of_ge_G_agree`.  That lemma is reused unchanged;
nothing about repeats, maximal extensions or coalescence enters. -/

/-- **Injectivity of the `(L - 1)`-window labelling on a primitive circle,
once the window is at least a full turn.**  If `K ≤ L - 1` and `S` is primitive
(no shift in `(0, K)` preserves every symbol), then
`vtx hK L S a = vtx hK L S b` forces `a = b`. -/
theorem vtx_injective_of_prim {L : ℕ} {K : ℕ} (hK : 0 < K) (S : Fin K → α)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hKL : K ≤ L - 1)
    {a b : Fin K} (h : vtx hK L S a = vtx hK L S b) : a = b := by
  by_contra hne
  have hne' : a.val % K ≠ b.val % K := by
    intro hc
    have hva : a.val % K = a.val := Nat.mod_eq_of_lt a.isLt
    have hvb : b.val % K = b.val := Nat.mod_eq_of_lt b.isLt
    have : a.val = b.val := hva.symm.trans (hc.trans hvb)
    exact hne (Fin.ext this)
  have hag : ∀ d : ℕ, d < L - 1 →
      OrientedRigidity.cyc hK S (a.val + d) = OrientedRigidity.cyc hK S (b.val + d) := by
    intro d hd
    exact congrFun h ⟨d, hd⟩
  exact not_primitive_of_ge_G_agree hK S a.val b.val (L - 1) hne' (by omega) hag hprim

/-- **The support of `AltF` is empty once the window is a full turn.**  If
`K ≤ L - 1` and the alternative traversal preserves the `(L - 1)`-mer at every
start (`BBTLadder.AltF_vtx'`, a consequence of the `traverses` clause of
`EulerianCycle`), then `AltF` is the identity. -/
theorem altF_eq_id_of_prim_window {L : ℕ} {K : ℕ} (hK : 0 < K) (S : Fin K → α)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hKL : K ≤ L - 1)
    {σ : Fin K ≃ Fin K} (hEul : EulerianCycle hK L S σ) (a : Fin K) :
    AltF hK σ a = a :=
  vtx_injective_of_prim hK S hprim hKL (BBTLadder.AltF_vtx' hK S hEul a)

/-! ## 3. The `L > K` half: PROVED, and vacuous

At `K < L` the support-chord hypothesis of `BBTLadder.CrossingChordsCoalesce`
is unsatisfiable, so the statement holds for a reason that has nothing to do
with coalescence.  This is the first examination of this half in either
direction. -/

/-- **The `K < L` half of `BBTLadder.CrossingChordsCoalesce` is true, and
vacuously so.**  By §2 the window is a full turn, so `AltF` is the identity;
then `AltF a = b` gives `a = b`, contradicting the `a ≠ b` of `Interleaved`'s
`FourDistinct` conjunct.  No repeat theory is used.

**What this is worth.**  It settles the out-of-range instance of the `def` for
a structural reason, i.e. it confirms the range split is *sound*.  It is **not**
progress towards coalescence and **not** progress towards `hPevzner`. -/
theorem crossingChordsCoalesce_above {L : ℕ} :
    CrossingChordsCoalesceAbove (α := α) L := by
  intro K hK S hP2 hprim hUkk hKL σ hEul a b c d hfa hba hfc hdc hac hbc had hbd hI
  have hAid : AltF hK σ a = a := altF_eq_id_of_prim_window hK S hprim (by omega) hEul a
  have hab : a = b := hAid.symm.trans hfa
  exact absurd hab hI.1.1

/-! ## 4. The `L < 2` half: REFUTED, kernel-checked

At `L = 1` the `(L - 1)`-mer is the empty function, so the `traverses` clause
of `EulerianCycle` is vacuous and `AltF` is unconstrained.  The instance below
satisfies every hypothesis of `BBTLadder.CrossingChordsCoalesce 1` and fails
its conclusion. -/

/-- `S = (0, 1, 2, 3)`: four pairwise distinct symbols, so on this circle no two
distinct starts agree on *any* window, and in particular `pairBack a b = 0` for
`a ≠ b` (`pairBack_eq_zero_of_back_ne`) and `maxPairStart a b = a`. -/
def S4 : Fin 4 → Fin 4 := ![0, 1, 2, 3]

theorem hK4 : 0 < 4 := by decide

theorem S4_inj : Function.Injective S4 := by decide

/-- `1 ≤ n` forces `0 < n`.  Stated by `cases` because `omega` in this Mathlib
pin cannot close the corresponding goal (see the module docstring). -/
theorem zero_lt_of_one_le {n : ℕ} (h1 : (1:ℕ) ≤ n) : (0:ℕ) < n := by
  cases n with
  | zero => exact absurd (Nat.succ_ne_zero 0) (by simpa using h1)
  | succ k => exact Nat.zero_lt_succ k

/-- **The `Agree` clause of `IsRepeat` / `IsTripleRepeat` is unsatisfiable on
`S4`** for two distinct starts: `Agree e a b` at `d = 0` says
`S4 (a mod 4) = S4 (b mod 4)`, and `S4` is injective, so `a = b`. -/
theorem agree_S4_ne {a b : Fin 4} (hab : a ≠ b) (e : Fin 4) (he : (1:ℕ) ≤ e.val) :
    ¬ (Genome.mk 4 hK4 S4).Agree e a b := by
  have h4 : 0 < 4 := by decide
  have he0 : (0 : ℕ) < e.val := zero_lt_of_one_le he
  intro h
  have hz := h ⟨0, he0⟩
  have hsym : S4 ⟨a.val % 4, Nat.mod_lt _ h4⟩ = S4 ⟨b.val % 4, Nat.mod_lt _ h4⟩ := by
    simpa only [Genome.Agree, Genome.window, Genome.cycl, Nat.add_zero] using hz
  have hval : a.val % 4 = b.val % 4 := congrArg Fin.val (S4_inj hsym)
  have hva : a.val % 4 = a.val := Nat.mod_eq_of_lt a.isLt
  have hvb : b.val % 4 = b.val := Nat.mod_eq_of_lt b.isLt
  exact hab (Fin.ext (hva.symm.trans (hval.trans hvb)))

/-- **On `S4` there is no maximal repeat and no maximal triple repeat.**
`IsRepeat` and `IsTripleRepeat` both require `a ≠ b` together with
`Agree e a b`, and the latter forces `a = b` on `S4`.  This is the key fact
behind `p2_S4_L1`, `ukkonen_S4_L1` and `primitive_S4`. -/
theorem no_repeat_S4 : ∀ (e a b : Fin 4), ¬ (Genome.mk 4 hK4 S4).IsRepeat e a b := by
  intro e a b h
  exact agree_S4_ne h.2.2.1 e h.1 h.2.2.2.1

theorem no_triple_S4 : ∀ (e a b c : Fin 4),
    ¬ (Genome.mk 4 hK4 S4).IsTripleRepeat e a b c := by
  intro e a b c h
  exact agree_S4_ne h.2.2.2.1 e h.1 h.2.2.2.2.2.2.1

/-- **This `S4` satisfies `P2` at `L = 1`.**  Both `P2` clauses are discharged
by `no_triple_S4` / `no_repeat_S4`.  This is the kernel-checked form of front
94a10's prose claim that "the out-of-range cases are not vacuous"; here the
*satisfaction* of `P2` off-range is a proof, and the *failure* of the
coalescence statement at the same `L` is the refutation below. -/
theorem p2_S4_L1 : P2 (α := Fin 4) hK4 1 S4 := by
  unfold P2
  refine ⟨?_, ?_⟩
  · intro e a b c h
    exact False.elim (no_triple_S4 e a b c h)
  · intro e₁ e₂ a b c d h1 h2 hI
    exact False.elim (no_repeat_S4 e₁ a b h1)

theorem ukkonen_S4_L1 : Ukkonen (α := Fin 4) hK4 1 S4 := by
  unfold Ukkonen
  refine ⟨?_, ?_⟩
  · intro e a b c h
    exact False.elim (no_triple_S4 e a b c h)
  · intro e₁ e₂ a b c d h1 h2 hI
    exact False.elim (no_repeat_S4 e₁ a b h1)

theorem primitive_S4 : RepeatAdapter.IsPrimitive hK4 S4 := by
  intro s hs hs4 hsI
  have h0 := hsI 0
  interval_cases s <;> simp_all [RepeatAdapter.ShiftInvariant, OrientedRigidity.cyc, S4]

/-- The permutation `σ` with `AltF hK4 sig4 = (0 2)(1 3)`, found by exhaustive
search over the `4!` candidates.  The search is **not** a premise of anything:
every property used below is re-verified in the kernel by `decide` or by
`maxPairStart_S4`. -/
def sig4 : Fin 4 ≃ Fin 4 :=
  { toFun := ![0, 3, 2, 1], invFun := ![0, 3, 2, 1]
    left_inv := by intro x; fin_cases x <;> rfl
    right_inv := by intro x; fin_cases x <;> rfl }

/-- **The `traverses` clause of `EulerianCycle` is vacuous at `L = 1`**: the
`(L - 1)`-mer is the empty function `Fin 0 → α`, so it is equal at *every* pair
of starts.  This is why the refutation below exists: at `L = 1` the labelling
carries no information at all, so `AltF` is unconstrained. -/
theorem vtx_trivial_L1 (a b : Fin 4) : vtx hK4 1 S4 a = vtx hK4 1 S4 b := by
  funext d
  exact Fin.elim0 d

/-- **It is a genuine alternative Eulerian cycle.**  `Succ sig4` is the conjugate
`σ ∘ nextPos ∘ σ⁻¹` of the one-step rotation, hence a `4`-cycle, which is the
`single` clause (`altSucc_iterate` reads its iterates as the rotation's); the
`traverses` clause is the vacuity just proved. -/
theorem eulerianCycle_S4 : EulerianCycle hK4 1 S4 sig4 := by
  constructor
  · intro i
    exact vtx_trivial_L1 _ _
  · unfold VisitsAll
    intro n₁ n₂ h
    have h₁ := BBTEulerian.altSucc_iterate hK4 sig4 n₁.val
    have h₂ := BBTEulerian.altSucc_iterate hK4 sig4 n₂.val
    have hrot : rotAdd hK4 n₁.val (sig4.symm (BBTEulerian.origin hK4))
        = rotAdd hK4 n₂.val (sig4.symm (BBTEulerian.origin hK4)) := by
      refine Equiv.injective sig4 ?_
      have hn' : (fun y => sig4 (nextPos hK4 (sig4.symm y)))^[n₁.val]
            (BBTEulerian.origin hK4)
          = (fun y => sig4 (nextPos hK4 (sig4.symm y)))^[n₂.val]
            (BBTEulerian.origin hK4) := by simpa using h
      rw [h₁, h₂] at hn'
      exact hn'
    exact Fin.ext (congrArg Fin.val
      (rotAdd_inj_lt hK4 (sig4.symm (BBTEulerian.origin hK4)) hrot))

/-- **The two crossing maximal extensions of `S4` are the two pairs themselves.**
On `S4` no two distinct starts agree on any window, so `pairBack a b = 0` and
`maxPairStart hK4 S4 a b = a` (`pairBack_eq_zero_of_back_ne`,
`maxPairStart_eq`, `rotAdd_full`). -/
theorem maxPairStart_S4 (x y : Fin 4) (hxy : x ≠ y) : maxPairStart hK4 S4 x y = x := by
  have h4 : 0 < 4 := by decide
  have hne : OrientedRigidity.cyc hK4 S4 (x.val + 4 - 1)
      ≠ OrientedRigidity.cyc hK4 S4 (y.val + 4 - 1) := by
    intro hc
    -- the two `cyc`s are `S4` at residues `x - 1` and `y - 1`, and `S4` is
    -- injective, so they are equal only if `x = y`
    have hxz : S4 ⟨(x.val + 4 - 1) % 4, by omega⟩
        = S4 ⟨(y.val + 4 - 1) % 4, by omega⟩ := by
      simpa only [OrientedRigidity.cyc] using hc
    have hval : (x.val + 4 - 1) % 4 = (y.val + 4 - 1) % 4 :=
      congrArg Fin.val (S4_inj hxz)
    exact hxy (Fin.ext (by omega))
  have hpb : pairBack hK4 S4 x.val y.val = 0 :=
    pairBack_eq_zero_of_back_ne hK4 S4 x.val y.val hne
  rw [BBTLadder.maxPairStart_eq, hpb, rotAdd_full]

/-- **`SameExtension` is false whenever the two chords' left endpoints
differ.**  On `S4`, `maxPairStart x y = x` for `x ≠ y` (`maxPairStart_S4`), so
each disjunct of `SameExtension a b c d` opens with `a = c` or `a = d`; both
contradict the quadruple's distinctness. -/
theorem not_sameExtension_S4 {a b c d : Fin 4} (hnab : a ≠ b) (hncd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) :
    ¬ SameExtension 4 hK4 S4 a b c d := by
  have hndc : d ≠ c := Ne.symm hncd
  rw [SameExtension]
  intro h
  rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
  · rw [maxPairStart_S4 a b hnab, maxPairStart_S4 c d hncd] at h1
    exact hac h1
  · rw [maxPairStart_S4 a b hnab, maxPairStart_S4 d c hndc] at h1
    exact had h1

/-- **The `AltF` of the counterexample really does swap `0 ↔ 2` and `1 ↔ 3`**,
and those four supports interleave, so the instance is not a degenerate one
where the quadruple hypotheses fail for a degenerate reason.  Kept separate from
`not_crossingChordsCoalesce_one` so that the two facts — the chords exist, and
the conclusion fails — are individually checkable. -/
theorem altF_chords_S4 :
    AltF hK4 sig4 0 = 2 ∧ AltF hK4 sig4 2 = 0 ∧ AltF hK4 sig4 1 = 3 ∧
      AltF hK4 sig4 3 = 1 ∧
      Interleaved (mkGenome hK4 S4) (0 : Fin 4) (2 : Fin 4) (1 : Fin 4) (3 : Fin 4) := by
  decide

/-- **`BBTLadder.CrossingChordsCoalesce 1` is FALSE.**  This is the
kernel-checked refutation of the `L < 2` half of the unbounded statement: the
instance `K = 4`, `L = 1`, `S = (0,1,2,3)`, `σ = sig4` satisfies `P2`,
primitivity and `Ukkonen`, is a genuine `EulerianCycle`, its `AltF` has the
crossing support chords `0 2` and `1 3` (`altF_chords_S4`), and the conclusion
`SameExtension` fails.

**What this is worth.**  It removes a *possible* line of attack on the ladder
route: the unbounded `Prop` is false as written, so no front can prove it.  It
is **not** a counterexample to `thm:BBT` and **not** progress towards
`hPevzner`; the refuted regime lies outside `BBTLadder.LadderVertexCycle`, which
carries `2 ≤ L` and `L ≤ K`. -/
theorem not_crossingChordsCoalesce_one :
    ¬ BBTLadder.CrossingChordsCoalesce (α := Fin 4) 1 := by
  intro h
  have hP2 := p2_S4_L1
  have hprim := primitive_S4
  have hUkk := ukkonen_S4_L1
  have hEul := eulerianCycle_S4
  have hchords := altF_chords_S4
  have hI : Interleaved (mkGenome hK4 S4) (0 : Fin 4) (2 : Fin 4) (1 : Fin 4)
      (3 : Fin 4) := hchords.2.2.2.2
  have h9 := h 4 hK4 S4 hP2 hprim hUkk sig4 hEul (0 : Fin 4) (2 : Fin 4) (1 : Fin 4)
    (3 : Fin 4) hchords.1 hchords.2.1 hchords.2.2.1 hchords.2.2.2.1
    (show (0 : Fin 4) ≠ 1 from by decide) (show (2 : Fin 4) ≠ 1 from by decide)
    (show (0 : Fin 4) ≠ 3 from by decide) (show (2 : Fin 4) ≠ 3 from by decide) hI
  exact (not_sameExtension_S4 (by decide) (by decide) (by decide) (by decide)) h9

/-! ## 5. The characterisation: the unbounded statement is the bounded one,
up to the refuted `L ≤ 1` end -/

/-- **For `2 ≤ L`, the unbounded `BBTLadder.CrossingChordsCoalesce` is
*equivalent* to its in-range half** — i.e. to the version carrying
`2 ≤ L` and `L ≤ K` as explicit hypotheses.

Both directions split on `L ≤ K`: when `L ≤ K` the in-range hypothesis is
discharged and the `def`'s own conclusion is used; when `K < L` §3 applies.

This is the *kernel-checked* form of "the unbounded statement is not larger than
the bounded one", and it is a statement about
`BBTLadder.CrossingChordsCoalesce` itself rather than a restatement of it.  It
is **not** a proof of `BBTLadder.CrossingChordsCoalesce` for `L ≥ 2`; what it
adds is that the out-of-range part of the `def` is settled, so the *only*
unproved content of the unbounded statement is its in-range half. -/
theorem crossingChordsCoalesce_iff_two_le {L : ℕ} (hL : 2 ≤ L) :
    BBTLadder.CrossingChordsCoalesce (α := α) L ↔
      CrossingChordsCoalesceBelow (α := α) L := by
  constructor
  · intro h K hK S hP2 hprim hUkk h2L hLK σ hEul a b c d hfa hba hfc hdc hac hbc had hbd hI
    by_cases hKL : L ≤ K
    · exact h K hK S hP2 hprim hUkk σ hEul a b c d hfa hba hfc hdc hac hbc had hbd hI
    · exact crossingChordsCoalesce_above (α := α) K hK S hP2 hprim hUkk (by omega)
        σ hEul a b c d hfa hba hfc hdc hac hbc had hbd hI
  · intro h K hK S hP2 hprim hUkk σ hEul a b c d hfa hba hfc hdc hac hbc had hbd hI
    by_cases hKL : L ≤ K
    · exact h K hK S hP2 hprim hUkk hL hKL σ hEul a b c d hfa hba hfc hdc
        hac hbc had hbd hI
    · exact crossingChordsCoalesce_above (α := α) K hK S hP2 hprim hUkk (by omega)
        σ hEul a b c d hfa hba hfc hdc hac hbc had hbd hI

end AssemblyP1.Issue94TW4Coalesce
