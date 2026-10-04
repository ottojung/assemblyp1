import AssemblyP1.Issue94KShort

/-!
# Board 94, front `94r1long`: residual **R1** in the range `L ≤ K`

> **STATUS: COMPILED, EXIT 0.  Every declaration in this file is
> kernel-checked.**  There is no `sorry`, no `admit`, no `axiom`, no
> `native_decide`, no `unsafe` and no linter suppression.  The axiom set of
> every declaration is printed by the aggregator `AssemblyP1.lean`.

> **Port note (board 94, packet 94f03, branch
> `integration/94-le-one-obstruction`, base `deffdbeb` = tip of
> `origin/antonina/issue-89-final`).**  This file is the port of
> `fix/94-r1-shiftstep` (`385ba35`) onto `deffdbeb`, which is a *superset* of
> the file on `fix/94-r1-longwindow` (`1eccb46`): that branch dropped §7 when
> it forked off `711a23d` and moved the refutation into
> `AssemblyP1/Issue94R1ShiftStepOnSearch.lean`, which is **not** part of this
> port.  So §7 (`instance3_not_shift_step`, the kernel-checked refutation of
> `R1_shift_step`) and `scripts/audit_shift_step.mjs` come from `385ba35`.
> The port needed **no textual repair**: `deffdbeb` only adds
> `AssemblyP1/Issue94GcdOneP2.lean`, and this file's single import,
> `AssemblyP1.Issue94KShort`, is untouched by it.  The one addition made by
> this port is `eulerianCycleObstruction_of_le_one` (§2), which closes the
> outer quantifier of `obstruction_of_le_one` and so inhabits
> `BBTEulerian.EulerianCycleObstruction` **at `L ≤ 1` only** — `L = 0` and
> `L = 1`, i.e. outside the regime `2 ≤ L` in which `BBTEulerian` states
> `thm:BBT` and in which `bbtCompleteSpec_of_obstruction` consumes it.
> **Nothing here is established at `2 ≤ L`.**

## What R1 is

`BBTEulerian.EulerianCycleObstruction L` (`AssemblyP1/BBTEulerian.lean:451`)
is

```
∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α), Ukkonen hK L S →
  ∀ (σ : Fin K ≃ Fin K), EulerianCycle hK L S σ →
    VertexCycleEq hK L S σ (Equiv.refl (α := Fin K)) ∨ LongObstruction hK L S
```

`AssemblyP1/Issue94KShort.lean` §4b discharges the whole range `K ≤ L - 1`
(residual R2), with no primitivity hypothesis.  **This file works on the
complementary range `L ≤ K`, i.e. residual R1**, where the window has length
`L - 1 ≤ K - 1`, shorter than the circle, and where nothing in the tree
applies.

`LongObstruction` is the negation of `Ukkonen` clause by clause
(`BBTEulerian.longObstruction_iff_not_Ukkonen`,
`AssemblyP1/BBTEulerian.lean:397`), so **under the `Ukkonen` hypothesis the
disjunction R1 asks for is equivalent to its first disjunct alone**.  R1 is
therefore the statement that an `Ukkonen` circular word whose window is no
longer than its circle has a unique Eulerian cycle up to rotation: the content
of Bresler–Bresler–Tse 2013, Theorem 3, which this project does **not** assume
(§7).

## What this file establishes

1. **§2 — the degenerate sub-range `L ≤ 1` of R1 is discharged,
   kernel-checked, and with no hypotheses at all.**  At `L ≤ 1` the window has
   length `0`, so the vertex cycle is a single constant vertex and *every*
   presentation is a vertex cycle of the truth.  This part of R1 does not need
   BBT.  Three theorems: `vtx_eq_of_le_one`, `vertexCycleEq_of_le_one`,
   `obstruction_of_le_one` (per instance), and, added by this port,
   `eulerianCycleObstruction_of_le_one`, which is the whole of
   `BBTEulerian.EulerianCycleObstruction` at `L ≤ 1`.  **The `Ukkonen`
   hypothesis is not needed anywhere in §2.**
2. **§3 — the honest partial induction.**  The overlap identity
   `BBTCondense.window_next` (`AssemblyP1/BBTCondense.lean:212`) alone carries
   the R2 induction into the range `L ≤ K` for the first `L - 1 - n`
   coordinates at step `n` of the listing, and nothing more: the reach shrinks
   by exactly one coordinate per step.  `R1_reach` is this statement,
   kernel-checked, with **no** `Ukkonen`, no primitivity and no range
   hypothesis.  The bound `n + d.val < L - 1` is exactly what survives; the
   *unbounded* version (`d.val + 1 < L - 1`, "every coordinate but the last",
   at every step) is **false**, and the naive induction that would prove it
   dies at the second coordinate — see the note after `R1_reach`.
3. **§4 — the residual, isolated.**  `R1_shift_step`: *in the range `L ≤ K`,
   on an `Ukkonen` word, equality of `(L-1)`-mers is preserved by shifting one
   step along the circle.*  `obstruction_of_shift_step` shows that this single
   lemma, together with `EulerianCycle`, **discharges R1** — kernel-checked.
   `R1_shift_step` is stated as a `Prop` and is **not proved**; per `AGENTS.md`
   a conjecture is a `Prop` until it is actually proved.  Nothing below depends
   on it.
3'. **§7 — and `R1_shift_step` is in fact FALSE, kernel-checked.**  At
   `K = 3`, `L = 2`, `S = 001` the word *is* `Ukkonen` and the shift step
   nevertheless fails (`instance3_not_shift_step`).  `Ukkonen` constrains
   triple repeats and interleaved pairs, not a lone maximal pair of starts, and
   a lone maximal pair of length `L - 1` is exactly what the shift step needs to
   exclude.  **The §4 reduction is therefore vacuous and R1 is still open.**
   `K = 3` is the minimum size at which the residual fails (`shift_step_K2`),
   and `scripts/audit_shift_step.mjs` shows the failure is systematic: it occurs
   at every `K ≥ 3` and every `2 ≤ L ≤ K - 1`, and only there.
4. **§5 — the residual is false without `Ukkonen`**, kernel-checked at the
   instance the search scripts report (§6).
5. **§6 — the instance `G = 6`, `L = 2`, `S = 000101`, listing `0 2 3 1 4 5`**:
   `EulerianCycle` holds, `VertexCycleEq … refl` **fails**, and
   `LongObstruction` **holds** (a maximal triple repeat of length `1 = L - 1`
   at starts `0, 1, 4`).  Three small kernel-checked facts about one instance,
   plus the statement that this instance is **not** a counterexample to R1
   because `S` is not `Ukkonen` there.
6. **§7 — the residual of §4 is refuted, at the smallest possible size.**
   See above.
-/

namespace AssemblyP1.Issue94R1LongWindow

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian
open AssemblyP1.P2
open AssemblyP1.RepeatAdapter
open AssemblyP1.Issue94KShort

set_option linter.unusedSectionVars false

/-! ## 1. Setup -/

section LongWindow

variable {α : Type} [DecidableEq α] {K : ℕ} (hK : 0 < K) (L : ℕ) (S : Fin K → α)

/-! ## 2. The degenerate sub-range `L ≤ 1` of R1: discharged

`vtx hK L S r : Fin (L - 1) → α` is `BBTCondense.vtx`
(`AssemblyP1/BBTCondense.lean:224`), verbatim `OrientedRigidity.nodeWindow`
(`AssemblyP1/OrientedRigidity.lean:621`), i.e. `fun d => cyc hK S (r.val + d.val)`.
When `L ≤ 1` the index type is `Fin 0`, the `(L-1)`-mer graph has one edgeless
vertex, and the "vertex cycle" carries no information at all.  Every
presentation is therefore the truth's vertex cycle.  No `Ukkonen`, no
`EulerianCycle`, no range hypothesis, no `2 ≤ L`: this is pure degeneracy. -/

/-- **At `L ≤ 1` every vertex label is the empty function.**  All functions
`Fin 0 → α` are equal, so the `(L-1)`-mer labelling cannot distinguish two
starts. -/
theorem vtx_eq_of_le_one (hL : L ≤ 1) (r r' : Fin K) :
    vtx hK L S r = vtx hK L S r' := by
  have hsub : L - 1 = 0 := by omega
  funext d
  exact Fin.elim0 (Fin.cast hsub d)

/-- **R1, degenerate sub-range: every presentation is the truth's vertex
cycle.**  No `Ukkonen`, no `EulerianCycle`, no `L ≤ K`, no `2 ≤ L`. -/
theorem vertexCycleEq_of_le_one (hL : L ≤ 1) (σ : Fin K ≃ Fin K) :
    VertexCycleEq hK L S σ (Equiv.refl (α := Fin K)) :=
  ⟨σ (origin hK), fun _ => vtx_eq_of_le_one hK L S hL _ _⟩

/-- The same, as a case of the public endpoint `EulerianCycleObstruction`. -/
theorem obstruction_of_le_one (_hUkk : Ukkonen hK L S) (hL : L ≤ 1) (_hKL : L ≤ K)
    {σ : Fin K ≃ Fin K} (_hEul : EulerianCycle hK L S σ) :
    VertexCycleEq hK L S σ (Equiv.refl (α := Fin K)) ∨ LongObstruction hK L S :=
  Or.inl (vertexCycleEq_of_le_one hK L S hL σ)

/-- **The WHOLE of `BBTEulerian.EulerianCycleObstruction`, at `L ≤ 1`.**
`obstruction_of_le_one` is per instance; this closes the outer quantifier over
`K` and over `S`, so for `L = 0` and for `L = 1` the `hPevzner` residual
(`BBTEulerian.lean:451`) is an inhabitant of this module and not a premise.

The hypothesis `Ukkonen` is *unused*: at `L ≤ 1` the `(L-1)`-mer graph has a
single edgeless vertex, so every presentation of it is the truth's own vertex
cycle and the long obstruction is irrelevant.

**This is degeneracy, not progress on `thm:BBT`.**  The bridge
`BBTEulerian.bbtCompleteSpec_of_obstruction` (`AssemblyP1/BBTEulerian.lean:492`)
needs `2 ≤ L`, and `BBTEulerian` states the whole of `EulerianCycleObstruction`
for `L ≥ 2`; so the instances proved here lie outside the regime the theorem is
about.  In the range `2 ≤ L` this module proves nothing about
`EulerianCycleObstruction`: it isolates residual R1 there (§4) and shows the
§4 route is vacuous (§7). -/
theorem eulerianCycleObstruction_of_le_one {L : ℕ} (hL : L ≤ 1) :
    EulerianCycleObstruction (α := α) L :=
  fun _K hK S _hUkk _σ hEul =>
    obstruction_of_le_one hK L S _hUkk hL
      (Nat.le_trans hL (Nat.succ_le_of_lt hK)) hEul

/-! ## 3. What survives in the range `L ≤ K`: the honest partial induction

The induction that discharges R2 in `Issue94KShort.vtx_sigma_eq_vtx_rotAdd_general`
(`AssemblyP1/Issue94KShort.lean:479`) has one step which needs `K ≤ L - 1`: it
turns two equal `(L-1)`-mers into a period of `S` (`R2_window_to_period`,
`AssemblyP1/Issue94KShort.lean:449`).  In the range `L ≤ K` that step is
unavailable.

What *is* available, with no hypothesis beyond the definitions, is the plain
overlap identity of a window with itself shifted one step: coordinate `d` of
`vtx (nextPos r)` is coordinate `d + 1` of `vtx r`
(`BBTCondense.window_next`, `AssemblyP1/BBTCondense.lean:212`).  Combined with
the `traverses` conjunct of `BBTEulerian.EulerianCycle`
(`AssemblyP1/BBTEulerian.lean:206`) — the listing's window at step `n + 1` is
the listing's window at step `n`, shifted one step along the circle — this
carries the truth's window from step `n` to step `n + 1` **only in the
coordinates that were already known at `n` minus the last one**.  Formally, the
reach shrinks by exactly one coordinate per step. -/

/-- **The last index of a window of length `L - 1`, for `2 ≤ L`.**  Named
because `L - 2 < L - 1` is *not* true for `L ≤ 1` and needs `2 ≤ L`. -/
def lastIdx (hL : 2 ≤ L) : Fin (L - 1) := ⟨L - 2, by omega⟩

/-- **One step of the window, shifted.**  `window_next` at `L`, read through
`vtx`: the shift drops the window's first symbol and appends a fresh one, so
coordinate `j` of `vtx (nextPos r)` is coordinate `j + 1` of `vtx r`. -/
theorem vtx_nextPos (r : Fin K) (d : Fin (L - 1)) (hd : d.val + 1 < L - 1) :
    vtx hK L S r ⟨d.val + 1, by omega⟩ = vtx hK L S (nextPos hK r) ⟨d.val, by omega⟩ := by
  have hw := window_next hK (W := S) (j := d.val) r (by omega)
  simpa only [vtx, nodeWindow, window] using hw

/-- The same, with `nextPos` written as `rotAdd`. -/
theorem vtx_rotAdd_apply (_hL : 2 ≤ L) (r : Fin K) (d : Fin (L - 1)) (hd : d.val + 1 < L - 1) :
    vtx hK L S (rotAdd hK 1 r) d = vtx hK L S r (⟨d.val + 1, by omega⟩ : Fin (L - 1)) := by
  rw [show rotAdd hK 1 r = nextPos hK r from rfl, vtx_nextPos hK L S r d hd]

/-- **`R1_reach`: what the overlap identity alone gives in the range
`L ≤ K`.**  At step `n` of the listing, the first `L - 1 - n` coordinates of
the listing's `(L-1)`-mer agree with the truth's own, started at `σ 0`.  No
`Ukkonen`, no primitivity, no range hypothesis, no `K ≤ L - 1`.

The bound is `n + d.val < L - 1` and **not** `d.val + 1 < L - 1`.  The reach
shrinks by one coordinate at every step, because each step of the induction
replaces coordinate `d` of the shifted window by coordinate `d + 1` of the
unshifted one, so the set of coordinates known at step `n` has to be read at
step `n - 1`.  A front of this issue can lose an afternoon to the stronger
statement; it is false.  Concretely, at `K = 6`, `L = 3`, the listing
`0 2 3 1 4 5` of `S = 000101` has `EulerianCycle` failing, and that is *not*
the reason: the reason is visible in the reach bound itself, and
`instance_not_shift_step_raw` (§6.3) is the kernel-checked refutation of the
one-step form of the same mistake on the same word at `L = 2`. -/
theorem R1_reach (hL : 2 ≤ L) {σ : Fin K ≃ Fin K} (hEul : EulerianCycle hK L S σ) :
    ∀ (n : ℕ) (d : Fin (L - 1)), n + d.val < L - 1 →
      vtx hK L S (σ (pt hK n)) d = vtx hK L S (rotAdd hK n (σ (origin hK))) d := by
  intro n
  induction n with
  | zero =>
      intro d _
      have hp : pt hK 0 = origin hK := pt_zero hK
      have hr : rotAdd hK 0 (σ (origin hK)) = σ (origin hK) := by
        apply Fin.ext
        simp
      rw [hp, hr]
  | succ n ih =>
      intro d hd
      have hpn : pt hK (n + 1) = nextPos hK (pt hK n) := pt_succ hK n
      rw [hpn]
      -- the `traverses` clause, read at step `n` of the listing
      have htrav := hEul.1 (pt hK n)
      rw [htrav]
      simp only [nextPos]
      -- both windows are shifted one step along the circle, which costs one
      -- coordinate of reach
      have hdd : d.val + 1 < L - 1 := Nat.lt_of_le_of_lt (by omega) hd
      rw [vtx_rotAdd_apply hK L S hL (σ (pt hK n)) d hdd,
        ← rotAdd_succ_add hK n (σ (origin hK)),
        vtx_rotAdd_apply hK L S hL (rotAdd hK n (σ (origin hK))) d hdd]
      refine ih ⟨d.val + 1, hdd⟩ ?_
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hd

/-! ## 4. THE RESIDUAL: shifting equality of windows, as a `Prop`

`R1_shift_step` below is the single missing lemma for R1.  It is stated as a
`Prop` and **is not proved**; per `AGENTS.md` a conjecture is a `Prop` until it
is actually proved, and nothing below depends on it.

Its content, in words: *in the range `L ≤ K`, if `S` is `Ukkonen` at `L` and
the `(L-1)`-mers at two starts agree, then the `(L-1)`-mers one step later
agree too.*  Equivalently: **on an `Ukkonen` word whose window is no longer
than the circle, equality of windows is preserved by the shift.**  This is the
statement R2 gets for free from `R2_window_to_period` (there, equality of
windows *is* a period); here the window is too short to pin a start down, and
`Ukkonen` has to do the work.  §5 shows the `Ukkonen` hypothesis cannot be
dropped, kernel-checked.

`obstruction_of_shift_step` is the sharp part: **R1 follows from
`R1_shift_step` alone**, in two lines of induction, with `R1_reach` unused.
So R1 is reduced to this one lemma, and nothing else is missing. -/

/-- **THE RESIDUAL R1, as a `Prop`.**  Not proved; see §4. -/
def R1_shift_step (hK : 0 < K) (L : ℕ) (S : Fin K → α) : Prop :=
  2 ≤ L → L ≤ K → Ukkonen hK L S →
    ∀ x y : Fin K, vtx hK L S x = vtx hK L S y →
      vtx hK L S (nextPos hK x) = vtx hK L S (nextPos hK y)

/-- **R1, conditional on `R1_shift_step`.**  The induction: the listing's
window at step `0` is the truth's own window at `σ 0`; `traverses` says the
listing's window at step `n + 1` is the listing's window at step `n` shifted
one step; `R1_shift_step` says the shift propagates equality of windows; and
`rotAdd_succ_add` says the truth's own start is shifted one step too. -/
theorem vertexCycleEq_of_shift_step {σ : Fin K ≃ Fin K} (hEul : EulerianCycle hK L S σ)
    (hStep : ∀ x y : Fin K, vtx hK L S x = vtx hK L S y →
      vtx hK L S (nextPos hK x) = vtx hK L S (nextPos hK y)) :
    ∀ n : ℕ, vtx hK L S (σ (pt hK n)) = vtx hK L S (rotAdd hK n (σ (origin hK))) := by
  intro n
  induction n with
  | zero =>
      have hp : pt hK 0 = origin hK := pt_zero hK
      have hr : rotAdd hK 0 (σ (origin hK)) = σ (origin hK) := by
        apply Fin.ext
        simp
      rw [hp, hr]
  | succ n ih =>
      have hpn : pt hK (n + 1) = nextPos hK (pt hK n) := pt_succ hK n
      rw [hpn]
      have htrav := hEul.1 (pt hK n)
      rw [htrav, hStep _ _ ih]
      exact congrArg (vtx hK L S) (rotAdd_succ_add hK n (σ (origin hK)))

/-- **R1, conditional on the residual, in the range `L ≤ K`.**  `R1_reach` is
not used; `R1_shift_step` is the whole residual.

**§7 supersedes the usefulness of this theorem, not its correctness.**  Its
hypothesis `R1_shift_step` is false (`instance3_not_shift_step`), so it is
vacuous: it proves R1 from a statement that cannot hold.  It is left in place
because it is correct and kernel-checked, and because it records exactly what
the §4 reduction would have needed. -/
theorem obstruction_of_shift_step (_hUkk : Ukkonen hK L S) (hL : 2 ≤ L) (hKL : L ≤ K)
    {σ : Fin K ≃ Fin K} (hEul : EulerianCycle hK L S σ)
    (hShift : R1_shift_step hK L S) :
    VertexCycleEq hK L S σ (Equiv.refl (α := Fin K)) ∨ LongObstruction hK L S := by
  refine Or.inl ?_
  have h := vertexCycleEq_of_shift_step hK L S hEul
    (fun x y hxy => hShift hL hKL _hUkk x y hxy)
  refine ⟨σ (origin hK), ?_⟩
  intro i
  have hkey := h i.val
  have hi : pt hK i.val = i := pt_val hK i
  have hcomm : rotAdd hK i.val (σ (origin hK)) = rotAdd hK (σ (origin hK)).val i := by
    unfold rotAdd
    apply Fin.ext
    exact congrArg (fun n : ℕ => n % K)
      (Nat.add_comm (σ (origin hK)).val i.val)
  rw [hi, hcomm] at hkey
  simpa only [Equiv.refl_apply] using hkey

/-! ## 5. The residual is false without `Ukkonen`, kernel-checked

`R1_shift_step` is refuted below at `K = 6`, `L = 2`, `S = 000101`, with
`x = 1` and `y = 2`: both length-`1` windows are `0`, but the shifted windows
are `S6 2 = 0` and `S6 3 = 1`.  So the range hypotheses `2 ≤ L` and `L ≤ K`
are satisfiable and the conclusion still fails: **`Ukkonen` is genuinely
load-bearing** in the residual, and the residual is not a formal artefact.

`R1_shift_step` with the `Ukkonen` hypothesis deleted is what fails.  Stated
as a `Prop` so that the refutation is of the project's own object. -/

/-- **`R1_shift_step` with `Ukkonen` deleted.**  Refuted in §6.3. -/
def R1_shift_step_raw (hK : 0 < K) (L : ℕ) (S : Fin K → α) : Prop :=
  ∀ x y : Fin K, vtx hK L S x = vtx hK L S y →
    vtx hK L S (nextPos hK x) = vtx hK L S (nextPos hK y)

end LongWindow

/-! ## 6. The instance `G = 6`, `L = 2`, `S = 000101`, listing `0 2 3 1 4 5`

This is the instance that `audit_r1.mjs` and `audit_hpev.mjs` report, at head
`d854047`, as the global minimum counterexample to the **first disjunct** in
the range `L ≤ K`.  The listing is read as in the scripts, i.e.
`σ 0 = 0, σ 1 = 2, σ 2 = 3, σ 3 = 1, σ 4 = 4, σ 5 = 5`. -/

section Instance


/-- The circular word `S = 0 0 0 1 0 1`, i.e. `S = 000101`. -/
def S6 : Fin 6 → ℕ := fun i => if i.val = 3 ∨ i.val = 5 then 1 else 0

/-- The listing `0 2 3 1 4 5`, as a function. -/
def f6 : Fin 6 → Fin 6
  | 0 => 0
  | 1 => 2
  | 2 => 3
  | 3 => 1
  | 4 => 4
  | 5 => 5

theorem f6_injective : Function.Injective f6 := by decide

theorem f6_surjective : Function.Surjective f6 := by decide

/-- The inverse listing `0 3 1 2 4 5`. -/
def g6 : Fin 6 → Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 1
  | 3 => 2
  | 4 => 4
  | 5 => 5

theorem g6_f6 : ∀ i : Fin 6, g6 (f6 i) = i := by decide

theorem f6_g6 : ∀ i : Fin 6, f6 (g6 i) = i := by decide

/-- **The listing `0 2 3 1 4 5` as an `Equiv`.**  Spelled out with an explicit
inverse rather than via `Equiv.ofBijective`, which is `noncomputable` and
would make the `decide` proofs of §6 below impossible. -/
def e6 : Fin 6 ≃ Fin 6 where
  toFun := f6
  invFun := g6
  left_inv := g6_f6
  right_inv := f6_g6

/-! ### 6.1 `EulerianCycle` holds, and the first disjunct fails

At `L = 2` the window has length `1`, so `vtx h6 2 S6 r` is the constant
function with value `S6 r` and the `traverses` clause of
`BBTEulerian.EulerianCycle` (`AssemblyP1/BBTEulerian.lean:206`) reads
`S6 (σ (i + 1)) = S6 (σ i + 1)`.  The listing reads
`0 → 2 → 3 → 1 → 4 → 5 → 0`, whose symbol values are `0, 0, 1, 0, 0, 1`; the
truth's, entered at `σ 0, σ 0 + 1, …`, are `0, 1, 0, 0, 1, 0`.  Each entry of
the first is followed by the next entry of the second.  The `single` clause is
`σ ∘ rot₁ ∘ σ⁻¹`, a conjugate of the `6`-cycle `rot₁`, hence injective on
iterates for every bijection `σ`; the tree records that in
`AssemblyP1.Issue94TW5Single`, and it is discharged here by direct
computation regardless.

The vertex cycle of `σ` is the symbol string `0, 0, 1, 0, 0, 1`; the truth's,
read from shift `k`, is `0,0,0,1,0,1` (`k = 0`), `0,0,1,0,1,0` (`k = 1`),
`0,1,0,1,0,0` (`k = 2`), `1,0,1,0,0,0` (`k = 3`), `0,1,0,0,0,1` (`k = 4`),
`1,0,0,0,1,0` (`k = 5`).  None of the six is `0,0,1,0,0,1`, so no shift of the
truth carries this vertex cycle. -/

/-- `0 < 6`, as a closed term, so that the `decide` proofs below apply to a
closed goal. -/
theorem h6z : (0:ℕ) < 6 := by omega

/-- `S = 000101` as a `Genome`.  An `abbrev`, so that `G6.len` unfolds to `6`
for instance resolution; `mkGenome h6z S6` is the same term. -/
abbrev G6 : Genome ℕ := ⟨6, h6z, S6⟩

theorem instance_eulerian : EulerianCycle h6z 2 S6 e6 := by decide

theorem instance_sigma_eq_rotAdd : ∀ k : Fin 6, ∃ i : Fin 6,
    vtx h6z 2 S6 (e6 i) ≠ vtx h6z 2 S6 (rotAdd h6z k i) := by decide

theorem instance_not_vertexCycleEq :
    ¬ VertexCycleEq h6z 2 S6 e6 (Equiv.refl (α := Fin 6)) := by decide

/-! ### 6.2 The second disjunct holds, and `S` is *not* `Ukkonen`

`S = 000101` has a maximal triple repeat of length `e = 1` at starts
`a = 0`, `b = 1`, `c = 4`: the three length-`1` substrings are all `0`; the
preceding symbols are `1, 0, 1`, not all equal; the following symbols are
`0, 0, 1`, not all equal.  Since `1 = L - 1` at `L = 2`, this is a
`LongObstruction`, and by `BBTEulerian.longObstruction_iff_not_Ukkonen`
(`AssemblyP1/BBTEulerian.lean:397`) it is exactly the failure of `Ukkonen`.
This is why the search scripts' minimum is not a counterexample to R1. -/

theorem instance_triple : G6.IsTripleRepeat 1 ⟨0, by decide⟩
    ⟨1, by decide⟩ ⟨4, by decide⟩ := by
  have hpa : G6.Preceding ⟨0, by decide⟩ = 1 := by decide
  have hpb : G6.Preceding ⟨1, by decide⟩ = 0  := by decide
  have hpc : G6.Preceding ⟨4, by decide⟩ = 1  := by decide
  have hfa : G6.Following 1 ⟨0, by decide⟩ = 0  := by decide
  have hfb : G6.Following 1 ⟨1, by decide⟩ = 0  := by decide
  have hfc : G6.Following 1 ⟨4, by decide⟩ = 1  := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro d; simp [Genome.window, Genome.cycl, S6]
  · intro d; simp [Genome.window, Genome.cycl, S6]
  · intro d; simp [Genome.window, Genome.cycl, S6]
  · rintro ⟨h1, h2⟩; rw [hpa, hpb] at h1; omega
  · rintro ⟨h1, h2⟩; rw [hfb, hfc] at h2; omega

theorem instance_longObstruction : LongObstruction h6z 2 S6 :=
  Or.inl ⟨⟨1, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨4, by decide⟩,
    instance_triple, by decide⟩

theorem instance_not_Ukkonen : ¬ Ukkonen h6z 2 S6 :=
  (BBTEulerian.longObstruction_iff_not_Ukkonen (hG := h6z) (L := 2) (S := S6)).mp
    instance_longObstruction

/-! ### 6.3 The residual of §4–§5, refuted at this instance

At `L = 2`, `K = 6`, with `x = 1` and `y = 2`: both length-`1` windows are `0`,
so `vtx x = vtx y`; but `vtx (nextPos x)` is `S6 2 = 0` and `vtx (nextPos y)`
is `S6 3 = 1`.  Both range hypotheses of `R1_shift_step` hold.  So
`R1_shift_step_raw` is false here, and `Ukkonen` cannot be dropped. -/

theorem instance_vtx_one_two : vtx h6z 2 S6 ⟨1, by decide⟩ = vtx h6z 2 S6 ⟨2, by decide⟩ := by
  decide

theorem instance_shift_not_raw :
    ¬ vtx h6z 2 S6 (nextPos h6z ⟨1, by decide⟩) = vtx h6z 2 S6 (nextPos h6z ⟨2, by decide⟩) := by
  intro h
  have c1 : vtx h6z 2 S6 (nextPos h6z ⟨1, by decide⟩) = 0  := by decide
  have c2 : vtx h6z 2 S6 (nextPos h6z ⟨2, by decide⟩) = 1  := by decide
  rw [c1, c2] at h
  exact absurd h (by decide)

theorem instance_not_shift_step_raw : ¬ R1_shift_step_raw h6z 2 S6 := by
  intro h
  exact instance_shift_not_raw (h ⟨1, by decide⟩ ⟨2, by decide⟩ instance_vtx_one_two)

/-! ### 6.4 The three facts about the search minimum, all confirmed

* `EulerianCycle` holds — `instance_eulerian`.
* the first disjunct fails — `instance_not_vertexCycleEq`.
* the second disjunct holds — `instance_longObstruction`, and `S` is **not**
  `Ukkonen` — `instance_not_Ukkonen`.

Hence this instance is a genuine *first-disjunct* counterexample and a
genuine *second-disjunct* witness, and **not** a counterexample to R1.  The
search scripts `audit_r1.mjs` and `audit_hpev.mjs` report the first two of
these three facts and not the third, because they drop the `Ukkonen`
hypothesis from the statement of R1 (`audit_hpev.mjs:24-29` tests `traverses`
and `VertexCycleEq` only; `audit_dichotomy.mjs:81` is the script that tests
`Ukkonen`, and at head `d854047` it reports zero violations of the full
dichotomy in this range: binary `K ≤ 6`, 768 `(K, L, S)` of which 416 `Ukkonen`,
18 098 Eulerian listings, 0 violations; ternary `K ≤ 6`, 7107 of which 4431
`Ukkonen`, 181 104 listings, 0 violations).

**Correction to the framing in the front brief and in
`/workspace/BOARD94-HPEV-RESIDUAL.md` §5.1.**  Those documents present
`G = 6, L = 2, S = 000101, listing = 023145` as *the* minimum counterexample
to the first disjunct in the range `L ≤ K`, which is right, and the same
document's §5.1 table reports zero violations of the full dichotomy, which is
also right.  What is worth recording explicitly, and is proved here, is *why*
the two are compatible: this instance is discharged by the **second**
disjunct, because `S = 000101` is not `Ukkonen` at `L = 2`.  The minimum of the
first-disjunct search is therefore not a candidate refutation of R1 and cannot
be turned into one. -/


end Instance

/-! ## 7. **THE RESIDUAL `R1_shift_step` IS FALSE: `K = 3`, `L = 2`, `S = 001`**

This section is the front's result, and it is a **refutation**, kernel-checked.

`R1_shift_step` (§4) says that on an `Ukkonen` word with `2 ≤ L ≤ K`,
**equality of two `(L-1)`-mers survives the shift**.  In symbols, with
`e = L - 1`: if `S[x … x+e-1] = S[y … y+e-1]` then `S[x+e] = S[y+e]`.  That is,
**every length-`L-1` repeat of a circular word is right-maximal.**

`Ukkonen` (`P2.lean:91`) constrains only *triple* repeats (`IsTripleRepeat`,
i.e. **three** selected starts) and *interleaved pairs of repeats*.  It says
nothing about a **lone pair** of starts agreeing on `L - 1 ≥ 1` symbols whose two
occurrences are maximal.  Such a lone pair is exactly what defeats the lemma,
and it occurs at `K = 3`, `L = 2`, `S = 001`:

* `S = 001` is `Ukkonen` at `L = 2` (`instance3_ukkonen`).  There is no triple
  repeat at all: a triple repeat needs three pairwise distinct starts carrying
  the same symbol, and no symbol occurs three times in `001`, while the clause-1
  threshold is `e < L - 1 = 1`, i.e. no triple repeat of any length (`IsRepeat`
  forces `1 ≤ e`).  The interleaved clause is vacuous, because `Interleaved`
  needs four pairwise distinct starts and `K = 3`.
* `vtx h3z 2 S001 0 = vtx h3z 2 S001 1` — both windows are the constant `0`,
  since `L - 1 = 1`;
* but `vtx h3z 2 S001 (nextPos h3z 0) = vtx h3z 2 S001 1 = 0` while
  `vtx h3z 2 S001 (nextPos h3z 1) = vtx h3z 2 S001 2 = 1`;
* and both range hypotheses hold: `2 ≤ 2` and `2 ≤ 3`.

So the §4 route **R1 from `R1_shift_step` is vacuous**: its hypothesis is
false, and `obstruction_of_shift_step` therefore proves nothing about R1.  §7.1
records that this is not an artefact of `L = 2` or of `K = 3`, and makes the
minimum size kernel-checked.  §7.2 records the sharp statement that *is* true.

**This does not refute R1.**  `R1` (`EulerianCycleObstruction L`, range
`L ≤ K`) is much weaker than `R1_shift_step`: it only asks about the vertices of
an `EulerianCycle` listing, which is a strong extra hypothesis that this section
does not use and does not need.  Nothing below touches R1, and `R1_reach`,
`vertexCycleEq_of_shift_step` and `obstruction_of_shift_step` are left as they
were. -/

section Refutation

variable {α : Type} [DecidableEq α] {K : ℕ}

/-- The circular word `S = 001` on `K = 3`, over the two-letter alphabet, as
the de Bruijn labels.  (The two-letter alphabet is what makes the finite
instances of `Decidable` below go through: `Genome.Agree` decides equality of
functions `Fin e → α`, which needs `Fintype α`.) -/
def S001 : Fin 3 → Fin 2 := fun i => if i.val = 2 then 1 else 0

/-- `0 < 3`, as a closed term, so that the instances below are closed. -/
theorem h3z : (0:ℕ) < 3 := by omega

/-- **In `001` no three pairwise distinct starts carry the same symbol**: the
symbol `1` occurs once and the symbol `0` twice.  Exhaustive, `3³` cases,
kernel-checked. -/
theorem three_distinct_ne_all (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : ¬ (S001 a = S001 b ∧ S001 b = S001 c) := by decide +revert

/-- The first coordinate of two agreeing copies of length `e`, at `e ≥ 1`. -/
theorem agree0 {e a b : Fin 3} (he : 0 < e.val)
    (h : (mkGenome h3z S001).Agree e.val a b) : S001 a = S001 b := by
  have h' := h ⟨0, by omega⟩
  simp only [mkGenome, Genome.window, Genome.cycl] at h'
  have ea : S001 ⟨a.val % 3, Nat.mod_lt _ (by omega)⟩ = S001 a := by
    congr 2
    exact Nat.mod_eq_of_lt (by omega)
  have eb : S001 ⟨b.val % 3, Nat.mod_lt _ (by omega)⟩ = S001 b := by
    congr 2
    exact Nat.mod_eq_of_lt (by omega)
  exact ea.symm.trans (h'.trans eb)

/-- **There is no maximal triple repeat anywhere in `001`, at any length.**
This is what makes `001` `Ukkonen` at every `L`. -/
theorem no_triple (e a b c : Fin 3) : ¬ (mkGenome h3z S001).IsTripleRepeat e a b c := by
  intro h
  rcases h with ⟨he, hlt, hab, hac, hbc, habR, hacR, hbcR, hp, hf⟩
  exact three_distinct_ne_all a b c hab hac hbc
    ⟨agree0 he habR, agree0 he hbcR⟩

/-- Four pairwise distinct starts do not exist on a three-element circle.
Exhaustive, `3⁴` cases, kernel-checked. -/
theorem no_four_distinct (a b c d : Fin 3) :
    ¬ (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) := by decide +revert

/-- ... hence `S = 001` has no interleaved repeat pair. -/
theorem no_interleaved (a b c d : Fin 3) : ¬ Interleaved (mkGenome h3z S001) a b c d := by
  intro h
  exact no_four_distinct a b c d h.1

/-- **`S = 001` on `K = 3` is `Ukkonen` at `L = 2`.**  Proved, not `decide`d as
a black box: the two clauses of `P2.Ukkonen` (`P2.lean:91`) are discharged by
`no_triple` and `no_interleaved` above.  (Instance search will not synthesise
`Decidable (Ukkonen …)` — the conjunction in the definition is too large for the
instance search — so the clauses are discharged by hand, as above.) -/
theorem instance3_ukkonen : Ukkonen h3z 2 S001 := by
  refine ⟨?_, ?_⟩
  · intro e a b c h
    exact absurd h (no_triple e a b c)
  · intro e₁ e₂ a b c d h1 h2 h3
    exact absurd h3 (no_interleaved a b c d)

theorem instance3_vtx_zero_one : vtx h3z 2 S001 (0 : Fin 3) = vtx h3z 2 S001 (1 : Fin 3) := by
  decide

theorem instance3_vtx_next_ne :
    vtx h3z 2 S001 (nextPos h3z (0 : Fin 3)) ≠ vtx h3z 2 S001 (nextPos h3z (1 : Fin 3)) := by
  decide

/-- **THE RESIDUAL `R1_shift_step` OF §4 IS FALSE, kernel-checked, at
`K = 3`, `L = 2`, `S = 001`, with `x = 0`, `y = 1`, on a word that *is*
`Ukkonen` there.**  This is a refutation of `R1_shift_step`, not of
`EulerianCycleObstruction`: it says the §4 route (R1 from a shift-propagation
lemma) cannot work, because the lemma it rests on is false.  R1 itself is
untouched by this file. -/
theorem instance3_not_shift_step : ¬ R1_shift_step h3z 2 S001 := by
  intro h
  exact instance3_vtx_next_ne
    (h (by omega) (by omega) instance3_ukkonen (0 : Fin 3) (1 : Fin 3)
      instance3_vtx_zero_one)

/-! ### 7.1 The failure is systematic, and `K = 3` is the minimum

The failure is not an artefact of the smallest window.  A search over all binary
circular words and all `L` with `2 ≤ L ≤ K`
(`scripts/audit_shift_step.mjs`, whose transcription of `vtx`, `Ukkonen`,
`IsRepeat`, `IsTripleRepeat` and `Interleaved` is the one of
`audit_dichotomy.mjs`) gives, for every `K ≥ 3` and every `2 ≤ L ≤ K - 1`, an
`Ukkonen` word at which the shift step fails, and gives none at `L = K` and none
at `K ≤ 2`:

```
K=3  L=2:  6 of   8 Ukkonen words fail        e.g. 001,   x=0 y=1
K=4  L=2:  4 of   8 Ukkonen words fail        e.g. 0011,  x=0 y=1
K=4  L=3:  8 of  16 Ukkonen words fail        e.g. 0001,  x=0 y=1
K=5  L=3: 20 of  22 Ukkonen words fail        e.g. 00011, x=0 y=1
K=5  L=4: 20 of  32 Ukkonen words fail        e.g. 00001, x=0 y=1
K=7  L=5: 56 of 114 Ukkonen words fail        e.g. 0000011, x=0 y=1
K=8  L=6: 64 of 240 Ukkonen words fail        e.g. 00000011, x=0 y=1
L=K:      0 failures at every K <= 8
K<=2:     0 failures at every L
```

The `L = K` row is the regime where the window has length `K - 1`, all but one
symbol of the circle: there the lemma does hold, and that regime is where the
`K ≤ L - 1` argument of `Issue94KShort` is one step away.  **The failure is
confined to `L < K` and occurs at every `K ≥ 3`.**  None of these search
figures is a proof; the refutation is `instance3_not_shift_step` alone, which
needs no search.

The `K ≤ 2` row *is* discharged in the kernel, and with no search: at `K = L = 2`
the raw shift step holds for **every** circular word over **every** alphabet,
`Ukkonen` or not (`shift_step_K2` below, proved abstractly).  Together with
`instance3_not_shift_step` this makes `K = 3`, `L = 2`, `S = 001` the minimum
instance at which `R1_shift_step` fails: minimum `K = 3` and minimum `L = 2`. -/

theorem h2z : (0:ℕ) < 2 := by omega

/-- At `K = L = 2` the window has length `1`, so it is the constant function with
value `S x`. -/
theorem vtx_of_L_two (S : Fin 2 → α) (x : Fin 2) : vtx h2z 2 S x = fun _ => S x := by
  funext d
  have hd : d.val = 0 := by
    have h := d.isLt
    omega
  simp only [vtx, nodeWindow, cyc]
  rw [hd, Nat.add_zero]
  congr 1
  apply Fin.ext
  exact Nat.mod_eq_of_lt (by omega)

/-- **`K = L = 2`: the shift step holds for every word over every alphabet.**
If the two length-`1` windows agree then `S x = S y`; if `x ≠ y` the two starts
are the whole circle and the shift swaps them, so the shifted symbols agree as
well.  This is the only regime in the neighbourhood where no `Ukkonen`
hypothesis is needed, and it shows that `K = 3` really is the smallest circle on
which the residual fails. -/
theorem shift_step_K2 (S : Fin 2 → α) (x y : Fin 2) (h : vtx h2z 2 S x = vtx h2z 2 S y) :
    vtx h2z 2 S (nextPos h2z x) = vtx h2z 2 S (nextPos h2z y) := by
  have hxy : S x = S y := by
    rw [vtx_of_L_two, vtx_of_L_two] at h
    exact congrFun h ⟨0, by omega⟩
  rw [vtx_of_L_two, vtx_of_L_two]
  funext _
  by_cases hx : x = y
  · exact hx ▸ rfl
  · have hv : x.val ≠ y.val := fun hv => hx (Fin.ext hv)
    have hnx : (nextPos h2z x).val = (x.val + 1) % 2 := rfl
    have hny : (nextPos h2z y).val = (y.val + 1) % 2 := rfl
    have hn : nextPos h2z x = y ∧ nextPos h2z y = x :=
      ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
    rw [hn.1, hn.2]
    exact hxy.symm

end Refutation

end AssemblyP1.Issue94R1LongWindow
