import AssemblyP1.BBTEulerian
import AssemblyP1.P2RepeatResidual

/-!
# Lightweight short-window R2 theorem

This module contains the general K ≤ L - 1 vertex-cycle argument used by the
Issue 94 endpoint, without importing the heavier TW/orbit-search development.
-/

namespace AssemblyP1.Issue94KShortGeneral

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian
open AssemblyP1.P2
open AssemblyP1.RepeatAdapter
open AssemblyP1.P2RepeatResidual

set_option linter.unusedSectionVars false

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

end ShortWindow

end AssemblyP1.Issue94KShortGeneral
