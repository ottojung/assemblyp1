import AssemblyP1.Issue94TW4Coalesce
import AssemblyP1.Issue94TW7AltF

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

section Circle

variable {K : ℕ}

/-- The start of the circle at step `n`, read as an element of `Fin K`. -/
def pt (hK : 0 < K) (n : ℕ) : Fin K := ⟨n % K, Nat.mod_lt _ hK⟩

theorem pt_zero (hK : 0 < K) : pt hK 0 = origin hK := Fin.ext (Nat.zero_mod _)

/-- One step of `pt` is `nextPos`; this is `BBTEulerian.rotAdd_succ_add`
(`AssemblyP1/BBTEulerian.lean:246`) in the other shape. -/
theorem pt_succ (hK : 0 < K) (n : ℕ) : pt hK (n + 1) = nextPos hK (pt hK n) := by
  unfold nextPos
  apply Fin.ext
  show (n + 1) % K = (n % K + 1) % K
  exact (Nat.mod_add_mod n K 1).symm

theorem pt_val (hK : 0 < K) (i : Fin K) : pt hK i.val = i :=
  Fin.ext (Nat.mod_eq_of_lt i.isLt)

end Circle

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

/-! ## 4b. R2 discharged: the `K ≤ L - 1` half with **no** primitivity

Added by board-94 front `94c20`.  This subsection discharges residual **R2**
of `hPevzner`: the range `K ≤ L - 1` with the hypothesis
`hprim : RepeatAdapter.IsPrimitive hK S` **deleted**.  §1–§2 above (the
primitivity route) are left untouched and still compile; they are now
redundant for `obstruction_short_window`, which is restated below in its
stronger form.

The three lemmas of `/workspace/BOARD94-HPEV-RESIDUAL.md` §4 are proved here
as `R2_cyc_period`, `R2_window_to_period` and `R2_period_is_invisible`, with
the signatures that report gives.  The induction consumes the first two
through the intermediate notion `R2ShiftEq` below, which is exactly
"the two starts differ by a period of the circular word" in the form the
induction needs.  **No** least-period theory, no `ShiftInvariant`-subgroup
argument and no injectivity of `vtx` is used anywhere: injectivity of `vtx`
is genuinely false for a periodic word, and correctly so, but the target only
asks for rotation-equivariance of the *listing*, and a period is invisible
to `vtx`. -/

/-- `cyc` depends only on the residue mod `K`.  This congruence step is
stated once, so that no proof below has to `unfold cyc` and abstract its own
index. -/
theorem R2_cyc_congr {x y : ℕ} (h : x % K = y % K) : cyc hK S x = cyc hK S y := by
  unfold cyc
  exact congrArg S (Fin.ext h)

/-- **`R2_cyc_period`.**  Sliding `cyc` by any number of full turns changes
nothing: `cyc hK S (i + t * K) = cyc hK S i`.  Immediate from
`cyc hK S i = S ⟨i % G, _⟩` (`OrientedRigidity.lean:611`) and `Nat.add_mod`. -/
theorem R2_cyc_period (i t : ℕ) : cyc hK S (i + t * K) = cyc hK S i := by
  induction t with
  | zero => simp
  | succ n ih =>
      have e1 : i + (n + 1) * K = (i + n * K) + K := by
        rw [Nat.succ_mul]
        omega
      have e2 : ((i + n * K) + K) % K = (i + n * K) % K :=
        (Nat.add_mod _ _ _).trans (by rw [Nat.mod_self, Nat.add_zero, Nat.mod_mod])
      exact (R2_cyc_congr hK S (e1.symm ▸ e2)).trans ih

/-- Reducing the offset of a `cyc` access changes nothing.  This is the only
place where a `% K` is removed, and it is used in the final assembly to read
`rotAdd`'s truncated index. -/
theorem R2_cyc_add_mod (x v : ℕ) : cyc hK S (x + v % K) = cyc hK S (x + v) := by
  have hA : (v % K + (v / K) * K) % K = v % K :=
    congrArg (fun n : ℕ => n % K) (Nat.mod_add_div' v K)
  have hkey : (x + (v % K + (v / K) * K)) % K = (x + v) % K := by
    calc (x + (v % K + (v / K) * K)) % K
        = ((x % K) + (v % K + (v / K) * K) % K) % K := Nat.add_mod _ _ _
      _ = ((x % K) + v % K) % K := by rw [hA]
      _ = (x + v) % K := (Nat.add_mod _ _ _).symm
  calc cyc hK S (x + v % K)
      = cyc hK S (x + v % K + (v / K) * K) :=
        (R2_cyc_period hK S (x + v % K) (v / K)).symm
    _ = cyc hK S (x + (v % K + (v / K) * K)) := by
        congr 1
        omega
    _ = cyc hK S (x + v) := R2_cyc_congr hK S hkey

/-- The `ℕ`-form of "the two starts differ by a period of `S`": every
access at offset `a.val` is the access at offset `b.val`, uniformly in the
base point.  This is `RepeatAdapter.ShiftInvariant`
(`AssemblyP1/RepeatAdapter.lean:83`) re-expressed so that the two
`ShiftInvariant` translations of it below compose by transitivity alone,
with no arithmetic at all. -/
def R2ShiftEq (S : Fin K → α) (a b : Fin K) : Prop :=
  ∀ x : ℕ, OrientedRigidity.cyc hK S (x + a.val) = OrientedRigidity.cyc hK S (x + b.val)

/-- **`R2_window_to_period`, step 1.**  Two starts carrying the same
`(L-1)`-mer, with `K ≤ L - 1`, differ by a period of the circular word —
**with no primitivity hypothesis**.  The `K`-truncation of the shift is
harmless because `cyc` only sees residues, which is why no `ℕ`-truncation
obligation arises here. -/
theorem R2_vtx_eq_shiftEq (hKL : K ≤ L - 1) {a b : Fin K}
    (h : vtx hK L S a = vtx hK L S b) : R2ShiftEq hK S a b := by
  intro x
  have hdK : x % K < K := Nat.mod_lt _ hK
  have hdL : x % K < L - 1 := lt_of_lt_of_le hdK hKL
  have h1 : cyc hK S (x + a.val) = cyc hK S (x % K + a.val) :=
    R2_cyc_congr hK S (by
      calc (x + a.val) % K = ((x % K) + (a.val % K)) % K := Nat.add_mod _ _ _
        _ = ((x % K) + a.val) % K := by rw [Nat.mod_eq_of_lt a.isLt])
  have h2 : cyc hK S (x + b.val) = cyc hK S (x % K + b.val) :=
    R2_cyc_congr hK S (by
      calc (x + b.val) % K = ((x % K) + (b.val % K)) % K := Nat.add_mod _ _ _
        _ = ((x % K) + b.val) % K := by rw [Nat.mod_eq_of_lt b.isLt])
  have hag : cyc hK S (a.val + x % K) = cyc hK S (b.val + x % K) :=
    congrFun h ⟨x % K, hdL⟩
  rw [h1, h2]
  have hk : ∀ (u w : ℕ), (u + w) % K = (w + u) % K := by
    intro u w
    calc (u + w) % K = (u % K + w % K) % K := Nat.add_mod _ _ _
      _ = (w % K + u % K) % K := by rw [Nat.add_comm]
      _ = (w + u) % K := (Nat.add_mod _ _ _).symm
  have e1 : cyc hK S (x % K + a.val) = cyc hK S (a.val + x % K) :=
    R2_cyc_congr hK S (hk (x % K) a.val)
  have e2 : cyc hK S (b.val + x % K) = cyc hK S (x % K + b.val) :=
    R2_cyc_congr hK S (hk b.val (x % K))
  exact e1.trans (hag.trans e2)

/-- **`R2_window_to_period`, step 2.**  Conversely, being offset by
`p = (a.val + K - b.val) % K` is the same as being a `ShiftInvariant` by
`p`.  Only `Nat.mod_add_div` is used; no residue congruence is needed,
because the two `ℕ` indices are compared *after* sliding by a whole number
of turns. -/
theorem R2_period_mk_shiftEq {a b : Fin K}
    (hper : ShiftInvariant hK S ((a.val + K - b.val) % K)) : R2ShiftEq hK S a b := by
  intro x
  have e1 : (x + b.val) + (a.val + K - b.val) = x + a.val + K := by omega
  have hq := R2_cyc_period hK S (x + a.val) 1
  have hq' : cyc hK S (x + a.val + K) = cyc hK S (x + a.val) := by
    simpa only [Nat.one_mul] using hq
  calc cyc hK S (x + a.val) = cyc hK S (x + a.val + K) := hq'.symm
    _ = cyc hK S ((x + b.val) + (a.val + K - b.val)) :=
        congrArg (fun t : ℕ => cyc hK S t) e1.symm
    _ = cyc hK S ((x + b.val) + (a.val + K - b.val) % K) :=
        (R2_cyc_add_mod hK S (x + b.val) (a.val + K - b.val)).symm
    _ = cyc hK S (x + b.val) := (hper (x + b.val)).symm

/-- **`R2_window_to_period`, step 3.**  A uniform offset is a period.  The
base point is first slid a whole number of turns so that it clears
`b.val`; this is what makes the `ℕ` truncation `(a.val + K - b.val)` in the
statement a non-issue. -/
theorem R2_shiftEq_mk_period {a b : Fin K} (hse : R2ShiftEq hK S a b) :
    ShiftInvariant hK S ((a.val + K - b.val) % K) := by
  intro i
  have h1 := hse (i + K - b.val)
  have e1 : (i + K - b.val) + a.val = i + (a.val + K - b.val) := by omega
  have e2 : (i + K - b.val) + b.val = i + K := by omega
  have h2 : cyc hK S (i + (a.val + K - b.val)) = cyc hK S i := by
    calc cyc hK S (i + (a.val + K - b.val))
        = cyc hK S ((i + K - b.val) + a.val) := by rw [e1]
      _ = cyc hK S ((i + K - b.val) + b.val) := h1
      _ = cyc hK S (i + K) := by rw [e2]
      _ = cyc hK S i := by
          have hq := R2_cyc_period hK S i 1
          simpa only [Nat.one_mul] using hq
  exact ((R2_cyc_add_mod hK S i (a.val + K - b.val)).trans h2).symm

/-- **`R2_window_to_period`.**  The report's statement, verbatim in shape:
`K ≤ L - 1` and equal `(L-1)`-mers give a `ShiftInvariant` by
`p = (a.val + K - b.val) % K`, i.e. `∀ i, cyc hK S i = cyc hK S (i + p)`.
**No primitivity hypothesis.** -/
theorem R2_window_to_period (hKL : K ≤ L - 1) {a b : Fin K}
    (h : vtx hK L S a = vtx hK L S b) :
    ShiftInvariant hK S ((a.val + K - b.val) % K) :=
  R2_shiftEq_mk_period (S := S) (hse := R2_vtx_eq_shiftEq hK L S hKL h)

/-- **`R2_period_is_invisible`.**  A period is invisible to the window
labelling: `vtx hK L S (rotAdd hK p c) = vtx hK L S c` for every period `p`
and every start `c`.

Stated and proved as the report specifies.  **It is not consumed by the
induction below**, which works with the uniform form `R2ShiftEq` and so never
has to re-derive a `vtx` equality from a period; it is recorded here because it
is the sentence that makes the mathematics legible ("a period is invisible to
`vtx`"), and because it is a standalone fact about `vtx` and periods.  Front
`94c20` reports that honestly rather than wiring it in artificially. -/
theorem R2_period_is_invisible (p : ℕ) (hper : ShiftInvariant hK S p) (c : Fin K) :
    vtx hK L S (rotAdd hK p c) = vtx hK L S c := by
  funext d
  calc cyc hK S ((c.val + p) % K + d.val) = cyc hK S (c.val + d.val + p) := by
        exact R2_cyc_congr hK S ((Nat.mod_add_mod (c.val + p) K d.val).trans
          (congrArg (fun n : ℕ => n % K) (show c.val + p + d.val = c.val + d.val + p
            from by omega)))
    _ = cyc hK S (c.val + d.val) := (hper (c.val + d.val)).symm

/-- **The listing offset, `K ≤ L - 1`, no primitivity.**  If the listing
`σ` respects the `(L-1)`-mer labelling and the window covers a whole turn,
then every start of the listing carries the `(L-1)`-mer the truth carries at
that step of its own listing, started at `σ 0`.  This is
`vtx_sigma_eq_vtx_rotAdd` (§2) with `vtx_injective_of_prim` replaced by
`R2_window_to_period`; it is the whole content of R2. -/
theorem vtx_sigma_eq_vtx_rotAdd_general (hKL : K ≤ L - 1)
    {σ : Fin K ≃ Fin K} (hEul : EulerianCycle hK L S σ) :
    ∀ n : ℕ, vtx hK L S (σ (pt hK n))
      = vtx hK L S (rotAdd hK n (σ (origin hK))) := by
  have hinv : ∀ n : ℕ, ∀ x : ℕ,
      cyc hK S (x + (σ (pt hK n)).val)
        = cyc hK S (x + ((σ (origin hK)).val + n)) := by
    intro n
    induction n with
    | zero =>
        intro x
        rw [pt_zero hK, Nat.add_zero]
    | succ n ih =>
        intro x
        -- The `traverses` clause, read at step `n` of the listing: the
        -- starts `σ (nextPos (pt n))` and `nextPos (σ (pt n))` carry the
        -- same `(L-1)`-mer, so they differ by a period of `S`.
        have htrav := hEul.1 (pt hK n)
        rw [← pt_succ hK n] at htrav
        have hse : R2ShiftEq hK S (σ (pt hK (n + 1))) (nextPos hK (σ (pt hK n))) :=
          R2_period_mk_shiftEq (S := S)
            (hper := R2_window_to_period hK L S hKL htrav)
        -- Translate the period forward by one access and by one turn.
        have hbval : (nextPos hK (σ (pt hK n))).val
            = ((σ (pt hK n)).val + 1) % K := rfl
        calc cyc hK S (x + (σ (pt hK (n + 1))).val)
            = cyc hK S (x + (nextPos hK (σ (pt hK n))).val) := hse x
          _ = cyc hK S (x + (σ (pt hK n)).val + 1) := by
              rw [hbval, R2_cyc_add_mod hK S x ((σ (pt hK n)).val + 1),
                Nat.add_assoc]
          _ = cyc hK S (x + ((σ (origin hK)).val + n) + 1) := by
              have h := ih (x + 1)
              simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
          _ = cyc hK S (x + ((σ (origin hK)).val + (n + 1))) := by
              have e : x + ((σ (origin hK)).val + n) + 1
                  = x + ((σ (origin hK)).val + (n + 1)) := by omega
              rw [e]
  have hk : ∀ (u w : ℕ), (u + w) % K = (w + u) % K := by
    intro u w
    calc (u + w) % K = (u % K + w % K) % K := Nat.add_mod _ _ _
      _ = (w % K + u % K) % K := by rw [Nat.add_comm]
      _ = (w + u) % K := (Nat.add_mod _ _ _).symm
  intro n
  unfold vtx nodeWindow rotAdd
  funext d
  have h := hinv n d.val
  calc cyc hK S ((σ (pt hK n)).val + d.val)
      = cyc hK S (d.val + (σ (pt hK n)).val) :=
        R2_cyc_congr hK S (hk (σ (pt hK n)).val d.val)
    _ = cyc hK S (d.val + ((σ (origin hK)).val + n)) := h
    _ = cyc hK S (d.val + ((σ (origin hK)).val + n) % K) :=
        (R2_cyc_add_mod hK S d.val ((σ (origin hK)).val + n)).symm
    _ = cyc hK S (((σ (origin hK)).val + n) % K + d.val) :=
        R2_cyc_congr hK S (by rw [Nat.add_comm])

/-- **R2, discharged.**  `VertexCycleEq hK L S σ refl` at `K ≤ L - 1` for an
**arbitrary** circular word: no primitivity, no `Ukkonen`, no bound on `L`. -/
theorem vertexCycleEq_short_window_general (hKL : K ≤ L - 1)
    {σ : Fin K ≃ Fin K} (hEul : EulerianCycle hK L S σ) :
    VertexCycleEq hK L S σ (Equiv.refl (α := Fin K)) := by
  refine ⟨σ (origin hK), ?_⟩
  intro i
  have hkey := vtx_sigma_eq_vtx_rotAdd_general hK L S hKL hEul i.val
  have hi : pt hK i.val = i := pt_val hK i
  have hcomm : rotAdd hK i.val (σ (origin hK)) = rotAdd hK (σ (origin hK)).val i := by
    unfold rotAdd
    apply Fin.ext
    exact congrArg (fun n : ℕ => n % K)
      (Nat.add_comm (σ (origin hK)).val i.val)
  rw [hi, hcomm] at hkey
  simpa only [Equiv.refl_apply] using hkey

/-- **R2 phrased as a case of the target, with `hprim` deleted.**  This is
`obstruction_short_window` of §3 in its strengthened form. -/
theorem obstruction_short_window_general (_hUkk : Ukkonen hK L S)
    (hKL : K ≤ L - 1) {σ : Fin K ≃ Fin K} (hEul : EulerianCycle hK L S σ) :
    VertexCycleEq hK L S σ (Equiv.refl (α := Fin K)) ∨ LongObstruction hK L S :=
  Or.inl (vertexCycleEq_short_window_general hK L S hKL hEul)

/-- And under `Ukkonen` the second disjunct is absent, so R2 is exactly the
first disjunct. -/
theorem obstruction_short_window_general' (hUkk : Ukkonen hK L S)
    (hKL : K ≤ L - 1) {σ : Fin K ≃ Fin K} (hEul : EulerianCycle hK L S σ) :
    VertexCycleEq hK L S σ (Equiv.refl (α := Fin K)) :=
  match obstruction_short_window_general hK L S hUkk hKL hEul with
  | Or.inl h => h
  | Or.inr h => absurd h (not_longObstruction_of_Ukkonen hUkk)

/-- **R2 re-exported under the §3 name, with `hprim` deleted.**  This is
`obstruction_short_window`: the `K ≤ L - 1` half of `hPevzner`, with no
primitivity hypothesis anywhere.  (Front `94c20`: the hypothesis
`hprim : RepeatAdapter.IsPrimitive hK S` that earlier revisions of this file
carried at this point has been **deleted**; the conclusion is unchanged.) -/
theorem obstruction_short_window (_hUkk : Ukkonen hK L S) (hKL : K ≤ L - 1)
    {σ : Fin K ≃ Fin K} (hEul : EulerianCycle hK L S σ) :
    VertexCycleEq hK L S σ (Equiv.refl (α := Fin K)) ∨ LongObstruction hK L S :=
  obstruction_short_window_general hK L S _hUkk hKL hEul

/-- And under `Ukkonen` the second disjunct is *absent*, so R2 is exactly the
first disjunct. -/
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
