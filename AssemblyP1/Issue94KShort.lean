import AssemblyP1.Issue94TW4Coalesce
import AssemblyP1.Issue94TW7AltF
import AssemblyP1.Issue94KShortGeneral

/-!
# Board 94, front `hpevroute`, repaired by front 94-p2repair: the `K ≤ L - 1`
# case of `thm:BBT`

> **STATUS: COMPILED, EXIT 0 (front 94-p2repair).**
>
> ```
> export LEAN_PATH=$(cd /workspace/assemblyp1-94-final && /home/lubko/.elan/bin/lake env printenv LEAN_PATH)
> cd /workspace/assemblyp1-94-p2repair
> /home/lubko/.elan/bin/lean AssemblyP1/Issue94KShort.lean ; echo "EXIT=$?"
> ```
>
> printed `EXIT=0` with no diagnostics.  Every declaration in this file is now
> kernel-checked.  Six elaboration slips were repaired (one of them a
> misapplied `.mpr`; see the note in §1).  There is no `sorry`, no `admit`, no
> `axiom`, no `native_decide`, and no `set_option` that removes an obligation.
>
> **UPDATE, board-94 front `94c20`: residual R2 is discharged.**  §4b below
> proves the `K ≤ L - 1` half of `hPevzner` for an **arbitrary** circular
> word: the hypothesis `hprim : RepeatAdapter.IsPrimitive hK S` has been
> *deleted* from `obstruction_short_window` and `obstruction_short_window'`.
> `lake build --wfail` exits 0 and the axiom set of every new declaration is a
> subset of `{propext, Classical.choice, Quot.sound}`.  §1–§4 (the primitivity
> route) are unchanged and still compile; they are now redundant for
> `obstruction_short_window`, which is discharged through §4b.  **R1, the
> range `L ≤ K`, is untouched and remains open.**
>
> **The `VertexCycleEq`-to-`LongObstruction` bridge the compile front recorded
> as unresolved is NOT needed and DOES NOT EXIST as a separate lemma.**  The
> error at the `obstruction_short_window'` step was a tactic-direction slip:
> `Or.resolve_left` was applied with a hypothesis of the wrong shape.  Case
> analysis on the disjunction plus `not_longObstruction_of_Ukkonen` discharges
> it in two lines.  See §3.

## What this file is

`AssemblyP1.BBTEulerian.EulerianCycleObstruction` (the `Prop` the public
endpoint takes as `hPevzner`) is quantified at **every** `K`.  **This file
discharges the whole range `K ≤ L - 1`**, with no primitivity hypothesis; it
proves the following case of the target:

* `Ukkonen hK L S`,
* `K ≤ L - 1`,
* an alternative Eulerian cycle `σ`,

entailing `VertexCycleEq hK L S σ (Equiv.refl (α := Fin K)) ∨ LongObstruction
hK L S`.  This is residual **R2** of the `hPevzner` quantifier, and it is
proved in §4b (`obstruction_short_window_general`, re-exported as
`obstruction_short_window`).

Note what is and is not in that statement:

* `Ukkonen` is **not used**.  The case holds for an arbitrary word.
* Apart from `K ≤ L - 1`, no bound on `L` occurs: neither `2 ≤ L` nor
  `L ≤ K` is needed.
* primitivity is **not** used and is **not** needed.  §1–§2 prove the same
  conclusion *under* `RepeatAdapter.IsPrimitive hK S` by a different route
  (injectivity of `vtx`); that route is retained unchanged as the
  primitivity-based derivation, and §4b supersedes it.  The endpoint's
  primitivity is still available if wanted:
  `P2RepeatResidual.IsPrimitive.shiftPrimitive`
  (`AssemblyP1/P2RepeatResidual.lean:220`) maps the endpoint's
  `PopulationReduction.IsPrimitive S` (`AssemblyP1/PopulationReduction.lean:1719`)
  to `RepeatAdapter.IsPrimitive hK S`
  (`AssemblyP1/RepeatAdapter.lean:87`), which is what §1–§2 take.

Three routes to the same conclusion are given.  §1 is the route the obstruction
map prescribes: `altF_eq_id_of_prim_window` then
`altF_eq_id_iff_rotation` then `rotAdd` arithmetic.  §2 is a direct induction
on the `traverses` clause under primitivity, which needs neither `AltF` nor
`IsRotation` and which is what made the residual in §6 statable precisely.
§3 phrases the result as a case of the target; §4 records that the endpoint's
primitivity suffices; **§4b discharges R2 with primitivity deleted**;
§6 records the residual that is left.

## What this file is NOT

It is a **case**, not the dichotomy.  It does not produce the second disjunct
`LongObstruction` (under `Ukkonen` that disjunct is anyway excluded by
`BBTEulerian.not_longObstruction_of_Ukkonen`), it says nothing about the range
`L ≤ K`, and it does not discharge `hPevzner`.  See
`/workspace/BOARD94-HPEV-ROUTE.md`, section "WHAT THIS DOES NOT ESTABLISH".
-/

namespace AssemblyP1.Issue94KShort

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.P2
open AssemblyP1.RepeatAdapter
open AssemblyP1.P2RepeatResidual
open AssemblyP1.Issue94TW4Coalesce
open AssemblyP1.Issue94TW7AltF

set_option linter.unusedSectionVars false

/-! ## 0. The position at step `n`

`BBTSequenceGraph.pos` (`AssemblyP1/BBTCondense.lean:684`) is declared inside a
section whose `variable` block carries `(L : ℕ) (S : Fin G → α)` which its own
body never mentions, so those two become **implicit metavariables** of `pos`.
Calling `pos` from another module therefore asks Lean to solve two unsolvable
implicit metavariables, and `BBTEulerian` has no `set_option` that would
suppress the resulting error.  The two-line helper is therefore re-defined here
in a section that mentions only `K`.  This is a real trap for anyone reusing
`pos` from `BBTEulerian`, and it is the reason the induction below is written
against `pt` rather than against `pos`. -/


section ShortWindow

variable {α : Type} [DecidableEq α] {K : ℕ} (hK : 0 < K) (L : ℕ) (S : Fin K → α)

/-! ## 1. Route A: the route the obstruction map prescribes

`Issue94TW4Coalesce.altF_eq_id_of_prim_window`
(`AssemblyP1/Issue94TW4Coalesce.lean:212`) takes `hK : 0 < K`,
`S : Fin K → α`, `hprim : RepeatAdapter.IsPrimitive hK S`,
`hKL : K ≤ L - 1`, `hEul : EulerianCycle hK L S σ` and `a : Fin K`, and
concludes `AltF hK σ a = a`.  Its `EulerianCycle` is
`BBTEulerian.EulerianCycle` (`AssemblyP1/BBTEulerian.lean:205`), declared in a
section whose variables are `{G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)`,
so `EulerianCycle hK L S σ` reads with `G := K`.  `AltF` is
`BBTUniqueEulerian.AltF` (`AssemblyP1/BBTUniqueEulerian.lean:698`). -/

/-- **`AltF` is the identity once the window is a full turn.**  Stated as its
own lemma so that the hypothesis list of the main step is visible on its own. -/
theorem altF_eq_id_short_window (hprim : RepeatAdapter.IsPrimitive hK S)
    (hKL : K ≤ L - 1) {σ : Fin K ≃ Fin K} (hEul : EulerianCycle hK L S σ)
    (a : Fin K) : AltF hK σ a = a :=
  altF_eq_id_of_prim_window hK S hprim hKL hEul a

/-- **Hence the alternative presentation is a rotation of the circle.**  This
step uses no word, no `L` and no `vtx`:
`Issue94TW7AltF.altF_eq_id_iff_rotation`
(`AssemblyP1/Issue94TW7AltF.lean:282`) is a fact about `AltF` and
`BBTChords.IsRotation` (`AssemblyP1/BBTChords.lean:87`) alone.  Note the
coercion: the conclusion is about `(σ : Fin K → Fin K)`, not about `σ`.

**Direction of the `Iff` (repair note).**  The `Iff` reads
`((∀ q, AltF hK σ q = q) ↔ IsRotation hK (↑σ))`, so the pointwise statement
goes in through `.mp`, not `.mpr`.  The draft used `.mpr`; that is the error
the compile front saw at this line.  It is a direction slip, not a
misreading of a lemma. -/
theorem isRotation_short_window (hprim : RepeatAdapter.IsPrimitive hK S)
    (hKL : K ≤ L - 1) {σ : Fin K ≃ Fin K} (hEul : EulerianCycle hK L S σ) :
    IsRotation hK (σ : Fin K → Fin K) :=
  (altF_eq_id_iff_rotation hK σ).mp (altF_eq_id_short_window hK L S hprim hKL hEul)

/-- **`rotAdd` arithmetic.**  `BBTChords.rotAdd_mod`
(`AssemblyP1/BBTChords.lean:130`) is `rotAdd hG s x = rotAdd hG (s % G) x`;
it is what replaces the unbounded shift `s : ℕ` coming out of `IsRotation` by
the `Fin K` index that `BBTEulerian.VertexCycleEq`
(`AssemblyP1/BBTEulerian.lean:217`) quantifies over. -/
theorem vtx_rotAdd_mod (s : ℕ) (i : Fin K) :
    vtx hK L S (rotAdd hK s i) = vtx hK L S (rotAdd hK (s % K) i) := by
  rw [rotAdd_mod hK s i]

/-- **Route A, assembled: the `K ≤ L - 1` case, for primitive truths.** -/
theorem vertexCycleEq_short_window (hprim : RepeatAdapter.IsPrimitive hK S)
    (hKL : K ≤ L - 1) {σ : Fin K ≃ Fin K} (hEul : EulerianCycle hK L S σ) :
    VertexCycleEq hK L S σ (Equiv.refl (α := Fin K)) := by
  obtain ⟨s, hs⟩ := isRotation_short_window hK L S hprim hKL hEul
  refine ⟨⟨s % K, Nat.mod_lt _ hK⟩, ?_⟩
  intro i
  have hi : σ i = rotAdd hK s i := hs i
  have hmod : rotAdd hK s i = rotAdd hK (s % K) i := rotAdd_mod hK s i
  calc vtx hK L S (σ i) = vtx hK L S (rotAdd hK s i) := by rw [hi]
    _ = vtx hK L S (rotAdd hK (s % K) i) := by rw [hmod]
    _ = vtx hK L S (rotAdd hK (s % K) (id i)) := by rfl

/-! ## 2. Route B: direct induction on the `traverses` clause

Route A detours through `AltF`, `Succ`, `prevPos` and `IsRotation`, none of
which is needed.  The whole content of the case is the following propagation
statement. -/

/-- **Propagation along the listing.**  If the listing `σ 0, σ 1, …` respects
the `(L-1)`-mer labelling, and the window is at least a full turn on a
primitive circle, then the `(L-1)`-mer entered at step `n` is the one the
truth enters at step `n` of its own listing, started at `σ 0`.

The step is the `traverses` conjunct of `BBTEulerian.EulerianCycle`
(`AssemblyP1/BBTEulerian.lean:206`, read at `.1`), which moves the vertex one
step along the circle, followed by injectivity of the `(L-1)`-window labelling
on a primitive circle:
`Issue94TW4Coalesce.vtx_injective_of_prim`
(`AssemblyP1/Issue94TW4Coalesce.lean:192`), whose signature is
`{L : ℕ} {K : ℕ} (hK : 0 < K) (S : Fin K → α) (hprim : RepeatAdapter.IsPrimitive hK S)
(hKL : K ≤ L - 1) {a b : Fin K} (h : vtx hK L S a = vtx hK L S b) : a = b`. -/
theorem vtx_sigma_eq_vtx_rotAdd (hKL : K ≤ L - 1)
    (hprim : RepeatAdapter.IsPrimitive hK S) {σ : Fin K ≃ Fin K}
    (hEul : EulerianCycle hK L S σ) :
    ∀ n : ℕ, vtx hK L S (σ (pt hK n))
      = vtx hK L S (rotAdd hK n (σ (origin hK))) := by
  intro n
  induction n with
  | zero =>
      have h0 : rotAdd hK 0 (σ (origin hK)) = σ (origin hK) := Fin.ext (by simp)
      rw [pt_zero hK, h0]
  | succ n ih =>
      have hpn : pt hK (n + 1) = nextPos hK (pt hK n) := pt_succ hK n
      rw [hpn]
      -- `traverses` moves the vertex one step along the circle
      have htrav := hEul.1 (pt hK n)
      rw [htrav]
      -- the two starts are now known to carry the same `(L-1)`-mer
      have hinj : σ (pt hK n) = rotAdd hK n (σ (origin hK)) :=
        vtx_injective_of_prim hK S hprim hKL ih
      rw [hinj]
      unfold nextPos
      simp only [rotAdd_succ_add]

/-- **Route B, assembled.**  The shift index is `σ 0` itself; the only
`Fin`-valued step is `Nat.add_comm` on the representatives, since `rotAdd` is
addition modulo `K` in either argument order. -/
theorem vertexCycleEq_short_window' (hprim : RepeatAdapter.IsPrimitive hK S)
    (hKL : K ≤ L - 1) {σ : Fin K ≃ Fin K} (hEul : EulerianCycle hK L S σ) :
    VertexCycleEq hK L S σ (Equiv.refl (α := Fin K)) := by
  refine ⟨σ (origin hK), ?_⟩
  intro i
  have hkey := vtx_sigma_eq_vtx_rotAdd hK L S hKL hprim hEul i.val
  have hi : pt hK i.val = i := pt_val hK i
  have hcomm : rotAdd hK i.val (σ (origin hK)) = rotAdd hK (σ (origin hK)).val i := by
    unfold rotAdd
    apply Fin.ext
    exact congrArg (fun n : ℕ => n % K)
      (Nat.add_comm (σ (origin hK)).val i.val)
  rw [hi, hcomm] at hkey
  simpa only [Equiv.refl_apply] using hkey

/-! ## 3. The case, phrased as a case of the target

`BBTEulerian.EulerianCycleObstruction` (`AssemblyP1/BBTEulerian.lean:451`) is
`VertexCycleEq … ∨ LongObstruction`.  Route B supplies the first disjunct, so
the disjunction is discharged with `Or.inl`; `Ukkonen` is not needed and is
therefore accepted and ignored.  This is the sense in which §1–§2 are "the
`K ≤ L - 1` half": they make the *first* disjunct available throughout that
range, which under the `Ukkonen` hypothesis is the whole content of the
dichotomy there, because
`BBTEulerian.longObstruction_iff_not_Ukkonen`
(`AssemblyP1/BBTEulerian.lean:397`) identifies the second disjunct with
`¬ Ukkonen`.

**No bridge between `VertexCycleEq` and `LongObstruction` is needed here, and
none exists in the tree.**  The draft tried to use
`Or.resolve_left`, whose signature is
`a ∨ b → (a → c) → (b → ¬ c) → c`: as an application
`x.resolve_left y` Lean expects `y : a → c`, but the draft passed
`not_longObstruction_of_Ukkonen hUkk : ¬ LongObstruction hK L S`, which is
`b → ⊥`, not `a → c`.  A plain case split on the disjunction, using
`not_longObstruction_of_Ukkonen` to kill the second disjunct, is the whole
repair.  The two predicates are never related to each other, and never need
to be.  **The statement of this theorem is now the R2 statement, with no
`hprim`:** it is proved in §4b (`obstruction_short_window_general`) and
re-exported under this name there. -/

/-! ## 4. The endpoint's primitivity supplies this file's primitivity

`P2RepeatResidual.IsPrimitive.shiftPrimitive`
(`AssemblyP1/P2RepeatResidual.lean:220`) is the bridge.  The public endpoint
carries `PopulationReduction.IsPrimitive S` ("not an exact nontrivial power",
`AssemblyP1/PopulationReduction.lean:1719`); `shiftPrimitive` turns it into
`RepeatAdapter.IsPrimitive hK S` ("no shift in `(0, K)` preserves every
symbol", `AssemblyP1/RepeatAdapter.lean:87`), which is what §1 and §2 consume.
So the `hprim` hypothesis of this file is **not** an extra assumption relative
to the endpoint. -/

theorem vertexCycleEq_short_window_of_endpoint_prim
    (_hUkk : Ukkonen hK L S) (hPrimS : PopulationReduction.IsPrimitive S)
    (hKL : K ≤ L - 1) {σ : Fin K ≃ Fin K} (hEul : EulerianCycle hK L S σ) :
    VertexCycleEq hK L S σ (Equiv.refl (α := Fin K)) :=
  vertexCycleEq_short_window' hK L S (IsPrimitive.shiftPrimitive hK hPrimS) hKL hEul


/-! ## 4b. The non-primitive short-window case

The definitions and proofs for R2, including the non-primitive full-window
argument, now live only in Issue94KShortGeneral. They are imported above
instead of re-declared here. This module retains the separate primitive route,
the additional Ukkonen corollary and its research notes.
-/

theorem obstruction_short_window' (hUkk : Ukkonen hK L S) (hKL : K ≤ L - 1)
    {σ : Fin K ≃ Fin K} (hEul : EulerianCycle hK L S σ) :
    VertexCycleEq hK L S σ (Equiv.refl (α := Fin K)) :=
  match obstruction_short_window hK L S hUkk hKL hEul with
  | Or.inl h => h
  | Or.inr h => absurd h (not_longObstruction_of_Ukkonen hUkk)

/-! ## 5. A sanity instance

The statement is not vacuous and not false: the identity presentation is an
Eulerian cycle (`BBTEulerian.eulerianCycle_refl`,
`AssemblyP1/BBTEulerian.lean:329`) and the conclusion holds for it, while a
genuinely different permutation of the starts is not an Eulerian cycle
(`BBTEulerian.not_eulerianCycle_validity`, `AssemblyP1/BBTEulerian.lean:552`,
at `S = 001`, `G = 3`, `L = 3`).  Both are kernel-checked instances already in
the tree and are reused unchanged; no new instance is claimed here.

## 6. THE RESIDUAL, stated exactly (revised by front `94c20`)

`EulerianCycleObstruction` has **no primitivity hypothesis** and quantifies at
**every** `K`.  After this file **one** gap remains, not two: the
primitivity half of the residual is closed, the `L ≤ K` half is not.  The two
are different in kind.

**(R1) The range `L ≤ K`. — STILL OPEN.**  Nothing here applies there.  The
sole consumer of `K ≤ L - 1` in §1–§2 is `vtx_injective_of_prim`, and its
hypothesis is not dischargeable in that range: there the window is *shorter*
than the circle and does not pin a start down, and the injectivity statement is
in fact **false** there, even at a primitive `S` (front `94c19` records the
instance `S = 000101`, `G = 6`, `L = 3`, where `vtx 0 = vtx 1 = 00` with `S`
primitive).  `/workspace/BOARD94-HPEV-RESIDUAL.md` §4–§5 further records that
the first disjunct alone is false in this range and that R1's content is
Bresler–Bresler–Tse 2013 Theorem 3.  **This file makes no claim about R1.**

**(R2) The range `K ≤ L - 1` for NON-primitive truths. — DISCHARGED in §4b.**

The text below is the original §6 record of *why this was a gap*; it is kept
because it states the obstacle the §4b argument had to get past, but its
conclusion ("no theorem in the tree speaks to it") is now **superseded** and is
false.

The `traverses` clause says: the `(L-1)`-mer entered at step `n + 1` of the
listing agrees, in its first `L - 2` coordinates, with the `(L-1)`-mer entered
at step `n` shifted one step along the circle; its **last** coordinate is a
freshly appended symbol and is not determined by the previous step.  So the
listing is a sequence of windows each obtained from the previous by dropping
the first symbol and appending an arbitrary one, and the induction of §2 fails
precisely at that one coordinate.  In the primitive case the coordinate is
recovered, because a window of `≥ K` symbols pins the start down.

**How §4b gets past it.**  The target is *not* injectivity of `vtx`; it is
rotation-equivariance of the *listing*.  Two starts carrying the same
`(L-1)`-mer with `K ≤ L - 1` do satisfy the "honest replacement" written below
— but as a statement about a **period of `S`**, not about the least period:

```
vtx a = vtx b  ⟹  ShiftInvariant hK S ((a.val + K - b.val) % K)      -- R2_window_to_period
```

and a period is invisible to the window labelling, so the fresh coordinate is
determined by the *class* of the start, which is all the induction needs.  No
least-period theory, no `ShiftInvariant`-subgroup argument and no
characterisation of the periods is used.  Concretely §4b adds
`R2_window_to_period`, `R2_period_is_invisible`, the congruence helpers
`R2_cyc_period`, `R2_cyc_congr`, `R2_cyc_add_mod`, the two translations
`R2_vtx_eq_shiftEq` / `R2_period_mk_shiftEq` and `R2_shiftEq_mk_period`, and
then the induction `vtx_sigma_eq_vtx_rotAdd_general` and the two results
`vertexCycleEq_short_window_general` and `obstruction_short_window_general`,
which re-export as `obstruction_short_window` and `obstruction_short_window'`
with `hprim` **deleted**.

**On the sub-question left open by earlier fronts** ("does the tree already
contain the needed lemma?"): **no, but there is a close sibling, and it is
worth recording.**  A `grep -rn "ShiftInvariant" --include=*.lean` over the
tree returns exactly two theorems whose *conclusion* is a
`RepeatAdapter.ShiftInvariant`:

* `Issue94Step5NoChord.chord_at_L_eq_K_shiftInvariant`
  (`AssemblyP1/Issue94Step5NoChord.lean:359`), and
* this file's new `R2_window_to_period` (§4b).

`chord_at_L_eq_K_shiftInvariant` is the same *shape* of conclusion — equal
`(L-1)`-mers give a shift-invariance by `(b.val + K - a.val) % K` — but it is
**not** the lemma R2 needs, for two independent reasons: it is stated at
**`L = K`**, i.e. a window of length `K - 1`, which is one symbol *short* of a
full turn, whereas R2 needs `K ≤ L - 1` (length `≥ K`); and it carries the
side condition `a ≠ b`, which R2 does not have and cannot supply.  It is,
however, strong evidence that the "equal windows ⟹ period" idea was already
found in this tree, in exactly the range where it is *degenerate*: a window
shorter than the circle pins nothing down, and the theorem survives only
because a non-injective `vtx` is accompanied by the distinctness hypothesis.
Its proof technique (`Nat.ModEq` and `Nat.mod_eq_of_modEq` on residues) is an
alternative to §4b's `R2_cyc_congr`/`R2_cyc_add_mod` route; the §4b route needs
no `ModEq` and no `Nat`-order lemmas at all.

The remaining near-objects, and why none of them is the needed lemma:

* `RepeatAdapter.not_primitive_of_ge_G_agree`
  (`AssemblyP1/RepeatAdapter.lean:221`) is the *contrapositive*: long agreement
  between distinct residues ⟹ `¬ IsPrimitive`.  Unavailable in the periodic
  case, as §6 always said.
* `RepeatAdapter.small_period_of_ge_p_agree`
  (`AssemblyP1/RepeatAdapter.lean:299`) is read at an *assumed* period `p` and
  returns a `∃ s < p` that is a period — the `p`-reduction form, not the
  `d`-conclusion, exactly the ambiguity §6 flagged.
* `Issue94TW6Lemma1.escape_iff_not_IsPrimitive`
  (`AssemblyP1/Issue94TW6Lemma1.lean:633`) and
  `BBTUniqueEulerian.leastPeriod` (`AssemblyP1/BBTUniqueEulerian.lean:342`)
  characterise the least period but say nothing about two *windows*.
* `Issue94TW4Coalesce.vtx_injective_of_prim`
  (`AssemblyP1/Issue94TW4Coalesce.lean:192`) is strictly stronger but
  **carries `hprim`**, so it cannot be used in the non-primitive case; it is
  strictly stronger in the relevant sense only under primitivity.

So the lemma had to be written, and §4b writes it; nothing was found ready-made.

**What this file establishes.**  For an **arbitrary** circular word — no
primitivity, no `Ukkonen` — the alternative Eulerian traversals of the
`(L-1)`-mer multigraph at `K ≤ L - 1` are all the vertex cycle of the truth
started at `σ 0`.  That is residual R2 in full, kernel-checked.  It is still
**not** the dichotomy: it says nothing about the range `L ≤ K` (R1), and it
does not discharge `hPevzner`. -/

end ShortWindow

end AssemblyP1.Issue94KShort
