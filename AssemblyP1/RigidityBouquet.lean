import AssemblyP1.ExactRigidityCriterion

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Bouquet rigidity criterion (issue #257, scope §8.1)

This module advances open item **§8.1** of
`docs/source-notes/issue-257-rigid-read-graphs.md`: the search for a checkable
graph-theoretic / flow characterization of positive-circulation rigidity on the
oriented `L`-mer support graph. The exact algebraic criterion
(`AssemblyP1.ExactRigidityCriterion.nonrigid_iff_exists_delta`), the Graver form
(`AssemblyP1.GraverRigidity`), the two-closed-walk form
(`AssemblyP1.TwoWalkRigidity`) and the finite decider
(`AssemblyP1.FiniteRigidityDecider`) are already merged and are **not** redone
here.

## The bouquet family and the reduction

A **bouquet** is a strongly connected support consisting of `k` directed cycles
through one common vertex (the multi-cycle generalization of the figure-eight,
which is a genuine `L`-mer support: a circular word traverses each loop). Write
`len i ≥ 1` for the length of cycle `i` and `mult i ≥ 1` for the (constant)
multiplicity of every edge of cycle `i`; the slack is `mult i - 1`.

Every integer circulation of a bouquet is constant on each cycle (balance at the
internal vertices forces consecutive edges to be equal), so a circulation is a
vector `x : Fin k → ℤ`; its total is `∑ i, len i * x i`. Hence the exact
criterion collapses to a **bounded linear Diophantine condition**:

> `bouquet_nonrigid_iff`: the circulation `A` is **not** rigid **iff** there is
> a nonzero integer vector `x` with `∑ i, len i * x i = 0` and
> `x i ≥ 1 - mult i` for all `i`.

This is a sharp, checkable, purely graph-theoretic criterion for the whole
family, and it is *strictly stronger* than the rank-one (`k = 2`) form of §3.
It also shows that **no simple min-cut / max-flow closed form exists for the
general problem**: the bouquet family already encodes bounded linear Diophantine
feasibility (a numerical-semigroup / coin problem), so the general criterion is
an integer — not a fractional — feasibility problem. The kernel-checked
`len233_mult211_real_integer_gap` makes the fractional/integer gap explicit:
the rational relaxation has the nonzero solution `x = (-1, 0, 2/3)` while the
integer condition has none, so no LP/min-cut relaxation can decide rigidity.

## Main results

* `bouquet_nonrigid_iff`: the exact Diophantine criterion (iff).
* `len24_mult21_rigid`: a **rigid repetitive** instance (a `2`-cycle traversed
  twice) — rigid *despite* a repeated cycle.
* `len23_mult41_nonrigid`: an explicit **non-rigidity witness** `x = (-3, 2)`.
* `len233_mult211_real_integer_gap`: the **real/integer gap** witness.

## Epistemic status

All theorems are kernel-checked with only `[propext, Classical.choice,
Quot.sound]` (`AssemblyP1.RigidityBouquetAudit`); no `sorry`/`admit`/`axiom`/
`native_decide`. The residual — a *polynomial* min-cut/max-flow closed form for
the general support, or a proof that none exists — remains **OPEN** (§8.1/§8.2).
-/

namespace AssemblyP1.RigidityBouquet

open Finset BigOperators

variable {k : ℕ}

abbrev BEdge (len : Fin k → ℕ) (M : ℕ) := Fin k × Fin M

abbrev BVert (k : ℕ) := Option (Fin k × ℕ)

def btail {len : Fin k → ℕ} {M : ℕ} (e : BEdge len M) : BVert k :=
  if (e.2 : ℕ) = 0 then none
  else some (e.1, (e.2 : ℕ) - 1)

def bhead {len : Fin k → ℕ} {M : ℕ} (e : BEdge len M) : BVert k :=
  if (e.2 : ℕ) + 1 = len e.1 then none
  else some (e.1, (e.2 : ℕ))

variable (len : Fin k → ℕ) (M : ℕ)

def bedges : Finset (BEdge len M) :=
  Finset.univ.filter (fun e => (e.2 : ℕ) < len e.1)

def bnodes : Finset (BVert k) :=
  insert none ((Finset.univ : Finset (Fin k)).biUnion
    (fun i => (Finset.range (len i - 1)).image (fun j => some (i, j))))

lemma mem_bnodes_internal (i : Fin k) (j : ℕ) (hj : j < len i - 1) :
    (some (i, j) : BVert k) ∈ bnodes len := by
  unfold bnodes
  apply Finset.mem_insert.mpr
  right
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ i, ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨j, Finset.mem_range.mpr hj, rfl⟩

def boutF (v : BVert k) : Finset (BEdge len M) := (bedges len M).filter (fun e => btail e = v)

def binF (v : BVert k) : Finset (BEdge len M) := (bedges len M).filter (fun e => bhead e = v)

lemma boutF_internal (hM : ∀ i, len i ≤ M) (i : Fin k) (j : ℕ) (hj : j + 1 < len i) :
    boutF len M (some (i, j)) = {⟨i, ⟨j+1, by have := hM i; omega⟩⟩} := by
  unfold boutF bedges btail
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨hvalid, htail⟩
    obtain ⟨i', j'⟩ := e
    by_cases h0 : (j' : ℕ) = 0
    · rw [ite_eq_left h0] at htail; exact absurd htail (by simp)
    · rw [ite_eq_right h0] at htail
      simp only [Option.some.injEq, Prod.mk.injEq] at htail
      obtain ⟨hi, hk⟩ := htail
      subst hi
      apply Prod.ext
      · rfl
      · apply Fin.ext
        have : (j' : ℕ) = j + 1 := by omega
        simpa using this
  · intro he
    subst he
    constructor
    · simpa using hj
    · rw [ite_eq_right (by simp)]
      simp

lemma binF_internal (hM : ∀ i, len i ≤ M) (i : Fin k) (j : ℕ) (hj : j + 1 < len i) :
    binF len M (some (i, j)) = {⟨i, ⟨j, by have := hM i; omega⟩⟩} := by
  unfold binF bedges bhead
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨hvalid, hhead⟩
    obtain ⟨i', j'⟩ := e
    by_cases h1 : (j' : ℕ) + 1 = len i'
    · rw [ite_eq_left h1] at hhead; exact absurd hhead (by simp)
    · rw [ite_eq_right h1] at hhead
      simp only [Option.some.injEq, Prod.mk.injEq] at hhead
      obtain ⟨hi, hk⟩ := hhead
      subst hi
      apply Prod.ext
      · rfl
      · apply Fin.ext
        have : (j' : ℕ) = j := by omega
        simpa using this
  · intro he
    subst he
    constructor
    · show (j : ℕ) < len i
      omega
    · rw [ite_eq_right (by
        show ¬ ((j : ℕ) + 1 = len i)
        omega)]

end AssemblyP1.RigidityBouquet

namespace AssemblyP1.RigidityBouquet

open Finset BigOperators

variable {k : ℕ} (len : Fin k → ℕ) (M : ℕ)

lemma mem_bnodes_none : (none : BVert k) ∈ bnodes len := by
  unfold bnodes; exact Finset.mem_insert_self none _

lemma mem_bnodes_some_iff (i : Fin k) (j : ℕ) :
    (some (i, j) : BVert k) ∈ bnodes len ↔ j < len i - 1 := by
  constructor
  · intro h
    unfold bnodes at h
    rw [Finset.mem_insert] at h
    rcases h with h | h
    · exact absurd h (by simp)
    · rw [Finset.mem_biUnion] at h
      obtain ⟨i', _, h⟩ := h
      rw [Finset.mem_image] at h
      obtain ⟨j', hj', heq⟩ := h
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rw [Finset.mem_range] at hj'
      exact hj'
  · intro hj
    exact mem_bnodes_internal len i j hj

lemma mem_bedges_iff (e : BEdge len M) : e ∈ bedges len M ↔ (e.2 : ℕ) < len e.1 := by
  unfold bedges; simp

lemma mem_bedges_of_btail_mem (hlen : ∀ i, 1 ≤ len i) (e : BEdge len M)
    (h : btail e ∈ bnodes len) : e ∈ bedges len M := by
  rw [mem_bedges_iff]
  obtain ⟨i', j'⟩ := e
  simp only [btail] at h ⊢
  by_cases h0 : (j' : ℕ) = 0
  · rw [ite_eq_left h0] at h
    rw [h0]; exact hlen i'
  · rw [ite_eq_right h0] at h
    have := (mem_bnodes_some_iff len i' ((j' : ℕ) - 1)).mp h
    omega

lemma mem_bedges_of_bhead_mem (hlen : ∀ i, 1 ≤ len i) (e : BEdge len M)
    (h : bhead e ∈ bnodes len) : e ∈ bedges len M := by
  rw [mem_bedges_iff]
  obtain ⟨i', j'⟩ := e
  simp only [bhead] at h ⊢
  by_cases h1 : (j' : ℕ) + 1 = len i'
  · rw [ite_eq_left h1] at h
    omega
  · rw [ite_eq_right h1] at h
    have := (mem_bnodes_some_iff len i' (j' : ℕ)).mp h
    omega

lemma filter_btail_eq (hlen : ∀ i, 1 ≤ len i) (v : BVert k) (hv : v ∈ bnodes len) :
    (Finset.univ.filter (fun e => btail e = v)) = (bedges len M).filter (fun e => btail e = v) := by
  apply Finset.Subset.antisymm
  · intro e he
    rw [Finset.mem_filter] at he ⊢
    exact ⟨mem_bedges_of_btail_mem len M hlen e (by rw [he.2]; exact hv), he.2⟩
  · intro e he
    rw [Finset.mem_filter] at he ⊢
    exact ⟨Finset.mem_univ e, he.2⟩

lemma filter_bhead_eq (hlen : ∀ i, 1 ≤ len i) (v : BVert k) (hv : v ∈ bnodes len) :
    (Finset.univ.filter (fun e => bhead e = v)) = (bedges len M).filter (fun e => bhead e = v) := by
  apply Finset.Subset.antisymm
  · intro e he
    rw [Finset.mem_filter] at he ⊢
    exact ⟨mem_bedges_of_bhead_mem len M hlen e (by rw [he.2]; exact hv), he.2⟩
  · intro e he
    rw [Finset.mem_filter] at he ⊢
    exact ⟨Finset.mem_univ e, he.2⟩

/-- Explicit balance predicate on the valid edges. -/
def BalancedB (B : BEdge len M → ℤ) : Prop :=
  ∀ v ∈ bnodes len, (∑ e ∈ boutF len M v, B e) = (∑ e ∈ binF len M v, B e)

end AssemblyP1.RigidityBouquet

namespace AssemblyP1.RigidityBouquet

open Finset BigOperators

variable {k : ℕ} (len : Fin k → ℕ) (M : ℕ)

lemma boutF_none (hlen : ∀ i, 1 ≤ len i) (hM : ∀ i, len i ≤ M) :
    boutF len M none = (Finset.univ : Finset (Fin k)).image
      (fun i => (i, ⟨0, by have h1 := hlen i; have h2 := hM i; omega⟩)) := by
  unfold boutF bedges btail
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hvalid, htail⟩
    obtain ⟨i', j'⟩ := e
    by_cases h0 : (j' : ℕ) = 0
    · exact Finset.mem_image.mpr ⟨i', Finset.mem_univ _, by
        exact Prod.ext rfl (Fin.ext (by simp [h0]))⟩
    · rw [ite_eq_right h0] at htail
      simp at htail
  · intro he
    obtain ⟨i', _, heq⟩ := Finset.mem_image.mp he
    rw [← heq]
    constructor
    · show (0 : ℕ) < len i'; exact hlen i'
    · rw [ite_eq_left (by simp)]

lemma binF_none (hlen : ∀ i, 1 ≤ len i) (hM : ∀ i, len i ≤ M) :
    binF len M none = (Finset.univ : Finset (Fin k)).image
      (fun i => (i, ⟨len i - 1, by have h1 := hlen i; have h2 := hM i; omega⟩)) := by
  unfold binF bedges bhead
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hvalid, hhead⟩
    obtain ⟨i', j'⟩ := e
    by_cases h1 : (j' : ℕ) + 1 = len i'
    · refine Finset.mem_image.mpr ⟨i', Finset.mem_univ _, ?_⟩
      have hjeq : (j' : ℕ) = len i' - 1 := by omega
      exact Prod.ext rfl (Fin.ext hjeq.symm)
    · rw [ite_eq_right h1] at hhead
      simp at hhead
  · intro he
    obtain ⟨i', _, heq⟩ := Finset.mem_image.mp he
    rw [← heq]
    constructor
    · show (len i' - 1 : ℕ) < len i'
      exact Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one (hlen i')) Nat.one_pos
    · rw [ite_eq_left (Nat.sub_add_cancel (hlen i'))]

/-- A vector is constant on each cycle (on the valid edges). -/
def ConstCyc (B : BEdge len M → ℤ) (x : Fin k → ℤ) : Prop :=
  ∀ e, (e.2 : ℕ) < len e.1 → B e = x e.1

lemma const_balanced (hlen : ∀ i, 1 ≤ len i) (hM : ∀ i, len i ≤ M)
    (B : BEdge len M → ℤ) (x : Fin k → ℤ) (hconst : ConstCyc len M B x) :
    BalancedB len M B := by
  intro v hv
  rcases v with _ | ⟨i, j⟩
  · -- common vertex
    rw [boutF_none len M hlen hM, binF_none len M hlen hM]
    rw [Finset.sum_image (by intro a _ b _ h; exact congrArg Prod.fst h),
        Finset.sum_image (by intro a _ b _ h; exact congrArg Prod.fst h)]
    apply Finset.sum_congr rfl
    intro i _
    rw [hconst (i, ⟨0, by have h1 := hlen i; have h2 := hM i; omega⟩) (by exact hlen i),
        hconst (i, ⟨len i - 1, by have h1 := hlen i; have h2 := hM i; omega⟩)
          (by show len i - 1 < len i; exact Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one (hlen i)) Nat.one_pos)]
  · -- internal vertex
    have hj : j < len i - 1 := (mem_bnodes_some_iff len i j).mp hv
    rw [boutF_internal len M hM i j (by omega), binF_internal len M hM i j (by omega)]
    simp only [Finset.sum_singleton]
    rw [hconst (i, ⟨j+1, by have := hM i; omega⟩) (by show j + 1 < len i; omega),
        hconst (i, ⟨j, by have := hM i; omega⟩) (by show j < len i; omega)]

/-- `BalancedB` is exactly the support-domain `BalancedZ` of `ExactRigidityCriterion`. -/
lemma balancedB_iff_balancedZ (B : BEdge len M → ℤ) :
    BalancedB len M B ↔
      AssemblyP1.ExactRigidityCriterion.BalancedZ btail bhead (bnodes len) (bedges len M) B := by
  unfold BalancedB AssemblyP1.ExactRigidityCriterion.BalancedZ
  rfl

/-- Internal-vertex balance: consecutive edges of a cycle carry equal values. -/
lemma internal_balance (hM : ∀ i, len i ≤ M) (B : BEdge len M → ℤ)
    (hB : BalancedB len M B) (i : Fin k) (j : ℕ) (hj : j + 1 < len i) :
    B (i, ⟨j+1, by have := hM i; omega⟩) = B (i, ⟨j, by have := hM i; omega⟩) := by
  have hv : (some (i, j) : BVert k) ∈ bnodes len := mem_bnodes_internal len i j (by omega)
  have h := hB (some (i, j)) hv
  rw [boutF_internal len M hM i j hj, binF_internal len M hM i j hj] at h
  simpa using h

/-- A balanced vector is constant on each cycle. -/
lemma balanced_constcyc (hlen : ∀ i, 1 ≤ len i) (hM : ∀ i, len i ≤ M)
    (B : BEdge len M → ℤ) (hB : BalancedB len M B) :
    ConstCyc len M B (fun i => B (i, ⟨0, by have h1 := hlen i; have h2 := hM i; omega⟩)) := by
  intro e he
  obtain ⟨i, j⟩ := e
  have key : ∀ n (hn : n < len i),
      B (i, ⟨n, by have := hM i; omega⟩) = B (i, ⟨0, by have h1 := hlen i; have h2 := hM i; omega⟩) := by
    intro n
    induction n with
    | zero => intro hn; rfl
    | succ n ih =>
      intro hn
      have h1 := internal_balance len M hM B hB i n (by omega)
      have h2 := ih (by omega)
      rw [h1, h2]
  rw [show (i, j) = (i, ⟨(j : ℕ), by have := hM i; omega⟩) from Prod.ext rfl (Fin.ext rfl)]
  exact key (j : ℕ) he

/-- Total mass of a constant-on-cycles vector. -/
lemma sum_bedges_const (hlen : ∀ i, 1 ≤ len i) (hM : ∀ i, len i ≤ M)
    (B : BEdge len M → ℤ) (x : Fin k → ℤ) (hconst : ConstCyc len M B x) :
    ∑ e ∈ bedges len M, B e = ∑ i : Fin k, (len i : ℤ) * x i := by
  rw [← Finset.sum_fiberwise (bedges len M) (fun e => e.1) B]
  apply Finset.sum_congr rfl
  intro i _
  have hfiber : (bedges len M).filter (fun e => e.1 = i)
      = (Finset.univ : Finset (Fin (len i))).image
          (fun t => (i, ⟨t, by have := t.2; have := hM i; omega⟩)) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨he, hfirst⟩
      rw [mem_bedges_iff] at he
      obtain ⟨i', t⟩ := e
      have hi' : i' = i := hfirst
      subst hi'
      exact ⟨⟨t, he⟩, Prod.ext rfl (Fin.ext rfl)⟩
    · rintro ⟨t, heq⟩
      rw [← heq]
      constructor
      · rw [mem_bedges_iff]; exact t.2
      · rfl
  rw [hfiber]
  rw [Finset.sum_image (by
    intro a _ b _ h
    exact Fin.ext (by simpa using congrArg Fin.val (congrArg Prod.snd h)))]
  have h2 : (∑ t : Fin (len i), B (i, ⟨t, by have := t.2; have := hM i; omega⟩))
      = ∑ t : Fin (len i), x i :=
    Finset.sum_congr rfl (fun t _ =>
      hconst (i, ⟨t, by have := t.2; have := hM i; omega⟩) t.2)
  rw [h2]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The multiplicity vector `A` of the bouquet: every edge of cycle `i` carries `mult i`. -/
def bouquetA (mult : Fin k → ℤ) (e : BEdge len M) : ℤ := mult e.1

end AssemblyP1.RigidityBouquet

namespace AssemblyP1.RigidityBouquet

open Finset BigOperators

variable {k : ℕ} (len : Fin k → ℕ) (M : ℕ)

/-- **Bouquet rigidity criterion (exact).** For a bouquet of `k` directed cycles
through a common vertex, with cycle lengths `len i` and constant multiplicity
`mult i ≥ 1` on cycle `i`, the circulation `A` is **not** rigid iff there is a
nonzero integer vector `x` with `∑ len_i x_i = 0` (zero-sum) and
`x_i ≥ 1 - mult_i` (box). This is the exact reduction of the circulation
criterion to a bounded linear Diophantine condition on the cycle lengths and
multiplicities. -/
theorem bouquet_nonrigid_iff (hlen : ∀ i, 1 ≤ len i) (hM : ∀ i, len i ≤ M)
    (mult : Fin k → ℤ) (G : ℕ)
    (hAtot : ∑ e ∈ bedges len M, bouquetA len M mult e = (G : ℤ)) :
    (¬ AssemblyP1.ExactRigidityCriterion.Rigid btail bhead (bnodes len) (bedges len M)
        (bouquetA len M mult) G) ↔
      ∃ x : Fin k → ℤ, x ≠ 0 ∧ (∑ i : Fin k, (len i : ℤ) * x i = 0) ∧
        ∀ i, -((mult i) - 1) ≤ x i := by
  have hAbal : AssemblyP1.ExactRigidityCriterion.BalancedZ btail bhead (bnodes len)
      (bedges len M) (bouquetA len M mult) :=
    (balancedB_iff_balancedZ len M _).mp
      (const_balanced len M hlen hM _ mult (fun e he => rfl))
  rw [AssemblyP1.ExactRigidityCriterion.nonrigid_iff_exists_delta btail bhead
        (bnodes len) (bedges len M) (bouquetA len M mult) G hAbal hAtot]
  constructor
  · rintro ⟨δ, ⟨e0, he0, hδne⟩, hδbal, hδsum, hδbox⟩
    have hδB : BalancedB len M δ := (balancedB_iff_balancedZ len M δ).mpr hδbal
    have hconst : ConstCyc len M δ
        (fun i => δ (i, ⟨0, by have h1 := hlen i; have h2 := hM i; omega⟩)) :=
      balanced_constcyc len M hlen hM δ hδB
    refine ⟨fun i => δ (i, ⟨0, by have h1 := hlen i; have h2 := hM i; omega⟩),
      ?_, ?_, ?_⟩
    · intro hx0
      have h1 : δ e0 = (fun i => δ (i, ⟨0, by have h1 := hlen i; have h2 := hM i; omega⟩)) e0.1 :=
        hconst e0 (by simpa [bedges] using he0)
      rw [h1] at hδne
      exact hδne (congrFun hx0 e0.1)
    · change ∑ e ∈ bedges len M, δ e = 0 at hδsum
      rw [sum_bedges_const len M hlen hM δ
        (fun i => δ (i, ⟨0, by have h1 := hlen i; have h2 := hM i; omega⟩)) hconst] at hδsum
      exact hδsum
    · intro i
      have hbox := hδbox (i, ⟨0, by have h1 := hlen i; have h2 := hM i; omega⟩)
        (by rw [mem_bedges_iff]; show (0 : ℕ) < len i; have := hlen i; omega)
      show -((mult i) - 1) ≤ δ (i, ⟨0, by have h1 := hlen i; have h2 := hM i; omega⟩)
      have : bouquetA len M mult (i, ⟨0, by have h1 := hlen i; have h2 := hM i; omega⟩)
          = mult i := rfl
      rw [this] at hbox
      linarith
  · rintro ⟨x, hxne, hxsum, hxbox⟩
    obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hxne
    refine ⟨fun e => x e.1, ⟨(i0, ⟨0, by have h1 := hlen i0; have h2 := hM i0; omega⟩),
      (by rw [mem_bedges_iff]; show (0 : ℕ) < len i0; have := hlen i0; omega), hi0⟩, ?_, ?_, ?_⟩
    · exact (balancedB_iff_balancedZ len M _).mp
        (const_balanced len M hlen hM _ x (fun e he => rfl))
    · change ∑ e ∈ bedges len M, x e.1 = 0
      rw [sum_bedges_const len M hlen hM _ x (fun e he => rfl)]
      exact hxsum
    · intro e he
      show (1 : ℤ) - bouquetA len M mult e ≤ x e.1
      have h1 : bouquetA len M mult e = mult e.1 := rfl
      rw [h1]
      have := hxbox e.1
      linarith

end AssemblyP1.RigidityBouquet

namespace AssemblyP1.RigidityBouquet

open Finset BigOperators

/-! ## Kernel-checked worked instances -/

/-- Bouquet of a `2`-cycle and a `4`-cycle. -/
def len24 : Fin 2 → ℕ := fun i => if i = 0 then 2 else 4
/-- Cycle `0` (length `2`) is traversed `2` times, cycle `1` (length `4`) once. -/
def mult21 : Fin 2 → ℤ := fun i => if i = 0 then 2 else 1

/-- **Rigid despite repetition.** The bouquet of a `2`-cycle and a `4`-cycle with
the `2`-cycle traversed twice is rigid: the box `x₀ ≥ -1`, `x₁ ≥ 0` together with
`2x₀ + 4x₁ = 0` forces `x = 0`. -/
theorem len24_mult21_rigid :
    AssemblyP1.ExactRigidityCriterion.Rigid btail bhead (bnodes len24) (bedges len24 6)
      (bouquetA len24 6 mult21) 8 := by
  by_contra hnr
  rw [bouquet_nonrigid_iff len24 6 (by decide) (by decide) mult21 8 (by decide)] at hnr
  obtain ⟨x, hxne, hxsum, hxbox⟩ := hnr
  apply hxne
  have h0 : (-1 : ℤ) ≤ x 0 := by simpa [mult21] using hxbox 0
  have h1 : (0 : ℤ) ≤ x 1 := by simpa [mult21] using hxbox 1
  have hs : 2 * x 0 + 4 * x 1 = 0 := by
    have hh := hxsum
    simp only [Fin.sum_univ_two] at hh
    simpa [len24] using hh
  have hx0 : x 0 = 0 := by omega
  have hx1 : x 1 = 0 := by omega
  funext i
  fin_cases i
  · exact hx0
  · exact hx1

/-- Bouquet of a `2`-cycle and a `3`-cycle. -/
def len23 : Fin 2 → ℕ := fun i => if i = 0 then 2 else 3
/-- Cycle `0` (length `2`) traversed `4` times, cycle `1` (length `3`) once. -/
def mult41 : Fin 2 → ℤ := fun i => if i = 0 then 4 else 1

/-- **Non-rigid witness.** The bouquet of a `2`-cycle and a `3`-cycle with the
`2`-cycle traversed four times is non-rigid, witnessed by `x = (-3, 2)`
(`2·(-3) + 3·2 = 0`, `-3 ≥ -3`, `2 ≥ 0`). -/
theorem len23_mult41_nonrigid :
    ¬ AssemblyP1.ExactRigidityCriterion.Rigid btail bhead (bnodes len23) (bedges len23 5)
      (bouquetA len23 5 mult41) 11 := by
  rw [bouquet_nonrigid_iff len23 5 (by decide) (by decide) mult41 11 (by decide)]
  refine ⟨fun i => if i = 0 then -3 else 2, ?_, ?_, ?_⟩
  · intro h0
    have := congrFun h0 0
    simp at this
  · have : (∑ i : Fin 2, (len23 i : ℤ) * (if i = 0 then (-3 : ℤ) else 2)) = 0 := by
      simp only [Fin.sum_univ_two]
      norm_num [len23]
    exact this
  · intro i
    have : -((mult41 i) - 1) ≤ (if i = 0 then (-3 : ℤ) else 2) := by
      fin_cases i <;> norm_num [mult41]
    exact this

/-- Bouquet of a `2`-cycle and two `3`-cycles. -/
def len233 : Fin 3 → ℕ := fun i => if i = 0 then 2 else 3
/-- Cycle `0` traversed `2` times, cycles `1`, `2` once. -/
def mult211 : Fin 3 → ℤ := fun i => if i = 0 then 2 else 1

/-- **Real/integer gap on a bouquet.** The rational relaxation has a nonzero
solution `x = (-1, 0, 2/3)` (so the LP relaxation reports non-rigidity), but the
integer condition has none (the circulation is rigid). Hence no purely
fractional / LP min-cut condition can decide rigidity: the criterion is genuinely
integer. -/
theorem len233_mult211_real_integer_gap :
    (∃ x : Fin 3 → ℚ, x ≠ 0 ∧ (∑ i : Fin 3, (len233 i : ℚ) * x i = 0) ∧
        ∀ i, -((mult211 i : ℚ) - 1) ≤ x i) ∧
      ¬ (∃ x : Fin 3 → ℤ, x ≠ 0 ∧ (∑ i : Fin 3, (len233 i : ℤ) * x i = 0) ∧
        ∀ i, -((mult211 i) - 1) ≤ x i) := by
  constructor
  · refine ⟨fun i => if i = 0 then -1 else if i = 1 then 0 else 2/3, ?_, ?_, ?_⟩
    · intro h0
      have := congrFun h0 0
      simp at this
    · have : (∑ i : Fin 3, (len233 i : ℚ) * (if i = 0 then (-1 : ℚ) else if i = 1 then 0 else 2/3)) = 0 := by
        simp only [Fin.sum_univ_three]
        norm_num [len233]
      exact this
    · intro i
      have : -((mult211 i : ℚ) - 1) ≤ (if i = 0 then (-1 : ℚ) else if i = 1 then 0 else 2/3) := by
        fin_cases i <;> norm_num [mult211]
      exact this
  · rintro ⟨x, hxne, hxsum, hxbox⟩
    apply hxne
    have h0 : (-1 : ℤ) ≤ x 0 := by simpa [mult211] using hxbox 0
    have h1 : (0 : ℤ) ≤ x 1 := by simpa [mult211] using hxbox 1
    have h2 : (0 : ℤ) ≤ x 2 := by simpa [mult211] using hxbox 2
    have hs : 2 * x 0 + 3 * x 1 + 3 * x 2 = 0 := by
      have hh := hxsum
      simp only [Fin.sum_univ_three] at hh
      simpa [len233] using hh
    have hx0 : x 0 = 0 := by omega
    have hx1 : x 1 = 0 := by omega
    have hx2 : x 2 = 0 := by omega
    funext i
    fin_cases i
    · exact hx0
    · exact hx1
    · exact hx2

end AssemblyP1.RigidityBouquet
