import AssemblyP1.ExactRigidityCriterion

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The general `p,q` long bridge: the exact circulation-rigidity criterion
(issue #257, §8.1)

This module advances open item **§8.1** of
`docs/source-notes/issue-257-rigid-read-graphs.md` past both the merged
antiparallel bridge (`AssemblyP1/RigidityBridge.lean`, two `2`-cycles) and the
length-3 bridge (`AssemblyP1/RigidityLength3Bridge.lean`, two `3`-cycles). It
does **not** redefine or re-prove any merged result: it imports
`AssemblyP1.ExactRigidityCriterion` (Theorem 1, `nonrigid_iff_exists_delta`) and
is a new, strictly larger topology.

## The topology

The *general `p,q` long bridge* replaces the two cycles by cycles of arbitrary
lengths `p, q ≥ 2`:

```
C1 : v → x → a₂ → … → a_{p-1} → v        (a `p`-cycle, `p` arcs)
C2 : v → y → b₂ → … → b_{q-1} → v        (a `q`-cycle, `q` arcs)
bridge : x → y , y → x                    (antiparallel arc pair)
```

on the `1 + (p-1) + (q-1)` vertices, with `p + q + 2` arcs. The base
circulation `gA` has multiplicity `m1` on every `C1` arc, `m2` on every `C2`
arc, and `f` on each bridge arc; its total mass is `gG = p·m1 + q·m2 + 2·f`.

## Main results

* `phi_of_balanced`: every balanced integral circulation is the four-parameter
  form `phi a c u w` (the balance equations at the interior vertices force
  constancy along each cycle, and the hub balance is a consequence).
* `generalBridge_nonrigid_iff`: the exact four-variable criterion. The base
  circulation is non-rigid **iff** there is a nonzero `(a,c,u,w)` with
  `p·a + q·c + (q-p+1)·u + (p-q+1)·w = 0` and the six coupled box inequalities
  `a ≥ 1-m1`, `a-u+w ≥ 1-m1`, `c ≥ 1-m2`, `c-w+u ≥ 1-m2`, `u ≥ 1-f`,
  `w ≥ 1-f`. This specialises to the merged `2`-cycle criterion at `p = q = 2`
  (coefficients `2,2,1,1`) and to the length-3 criterion at `p = q = 3`
  (coefficients `3,3,1,1`).
* `generalBridge_nonrigid_m2_large` / `generalBridge_nonrigid_m1_large`: general
  non-rigidity witnesses `(q,-p,0,0)` and `(-q,p,0,0)`.
* `generalBridge_nonrigid_eq_m1` / `generalBridge_nonrigid_eq_m2`: for `p = q`,
  the witnesses `(-1,1,0,0)` and `(1,-1,0,0)`.
* `generalBridge_nonrigid_q3_f`: for `q = 3`, the bridge-repetition witness
  `(1,0,-1,-2)`, generalising `length3Bridge_nonrigid_f` to arbitrary `p`.
* `generalBridge_rigid_repetitive`: the `p,q`-dependent **rigid repetitive**
  instance `(p,q) = (3,4)`, `(m1,m2,f) = (2,1,1)`: the first cycle is traversed
  twice, yet the support is rigid. This refutes any claim that `m1 ≥ 2` alone
  forces non-rigidity — the classification is genuinely `p,q`-dependent.

## Epistemic status

All theorems are kernel-checked with only `[propext, Classical.choice,
Quot.sound]` (`AssemblyP1.RigidityGeneralBridgeAudit`); no `sorry`/`admit`/
`axiom`/`native_decide`. The topology is an *abstract* oriented support graph;
realizability as a de Bruijn read-support is not claimed. The residual — a
*polynomial* min-cut/max-flow closed form for arbitrary supports, or a proof
that none exists — remains **OPEN** (§8.1/§8.2).
-/
namespace AssemblyP1.RigidityGeneralBridge
open Finset BigOperators

def cnext (n : ℕ) (hn : 0 < n) (i : Fin n) : Fin n :=
  if h : i.val + 1 < n then ⟨i.val + 1, h⟩ else ⟨0, hn⟩

abbrev Vtx (p q : ℕ) := Fin p ⊕ Fin (q - 1)
abbrev Arc (p q : ℕ) := Fin p ⊕ (Fin q ⊕ Fin 2)

def c2v (p q : ℕ) (hp : 0 < p) (j : Fin q) : Vtx p q :=
  if h : j.val = 0 then Sum.inl ⟨0, hp⟩
  else Sum.inr ⟨j.val - 1, by have := j.isLt; omega⟩

def gtail (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) : Arc p q → Vtx p q
  | Sum.inl i => Sum.inl i
  | Sum.inr (Sum.inl j) => c2v p q (by omega) j
  | Sum.inr (Sum.inr 0) => Sum.inl ⟨1, h1p⟩
  | Sum.inr (Sum.inr 1) => c2v p q (by omega) ⟨1, h1q⟩

def ghead (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) : Arc p q → Vtx p q
  | Sum.inl i => Sum.inl (cnext p (by omega) i)
  | Sum.inr (Sum.inl j) => c2v p q (by omega) (cnext q (by omega) j)
  | Sum.inr (Sum.inr 0) => c2v p q (by omega) ⟨1, h1q⟩
  | Sum.inr (Sum.inr 1) => Sum.inl ⟨1, h1p⟩

@[simp] lemma gtail_inl (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (i : Fin p) :
    gtail p q h1p h1q (Sum.inl i) = Sum.inl i := rfl
@[simp] lemma gtail_inr_inl (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (j : Fin q) :
    gtail p q h1p h1q (Sum.inr (Sum.inl j)) = c2v p q (by omega) j := rfl
@[simp] lemma gtail_inr_inr_zero (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) :
    gtail p q h1p h1q (Sum.inr (Sum.inr 0)) = Sum.inl ⟨1, h1p⟩ := rfl
@[simp] lemma gtail_inr_inr_one (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) :
    gtail p q h1p h1q (Sum.inr (Sum.inr 1)) = c2v p q (by omega) ⟨1, h1q⟩ := rfl
@[simp] lemma ghead_inl (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (i : Fin p) :
    ghead p q h1p h1q (Sum.inl i) = Sum.inl (cnext p (by omega) i) := rfl
@[simp] lemma ghead_inr_inl (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (j : Fin q) :
    ghead p q h1p h1q (Sum.inr (Sum.inl j)) = c2v p q (by omega) (cnext q (by omega) j) := rfl
@[simp] lemma ghead_inr_inr_zero (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) :
    ghead p q h1p h1q (Sum.inr (Sum.inr 0)) = c2v p q (by omega) ⟨1, h1q⟩ := rfl
@[simp] lemma ghead_inr_inr_one (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) :
    ghead p q h1p h1q (Sum.inr (Sum.inr 1)) = Sum.inl ⟨1, h1p⟩ := rfl

@[simp] lemma cnext_val_of (n : ℕ) (hn : 0 < n) (i : Fin n) (h : i.val + 1 < n) :
    cnext n hn i = ⟨i.val + 1, h⟩ := by unfold cnext; rw [dite_eq_left h]
@[simp] lemma cnext_val_last (n : ℕ) (hn : 0 < n) (i : Fin n) (h : ¬ i.val + 1 < n) :
    cnext n hn i = ⟨0, hn⟩ := by unfold cnext; rw [dite_eq_right h]

@[simp] lemma c2v_val_zero (p q : ℕ) (hp : 0 < p) (j : Fin q) (h : j.val = 0) :
    c2v p q hp j = Sum.inl ⟨0, hp⟩ := by unfold c2v; rw [dite_eq_left h]
@[simp] lemma c2v_val_ne_zero (p q : ℕ) (hp : 0 < p) (j : Fin q) (h : j.val ≠ 0) :
    c2v p q hp j = Sum.inr ⟨j.val - 1, by have := j.isLt; omega⟩ := by
  unfold c2v; rw [dite_eq_right h]

@[simp] lemma c2v_eq_inl (p q : ℕ) (hp : 0 < p) (j : Fin q) (i : Fin p) :
    c2v p q hp j = Sum.inl i ↔ j.val = 0 ∧ i.val = 0 := by
  by_cases hj : j.val = 0
  · rw [c2v_val_zero p q hp j hj]
    constructor
    · intro h
      exact ⟨hj, by simpa using (congrArg Fin.val (Sum.inl.inj h)).symm⟩
    · rintro ⟨_, hi⟩
      rw [show i = ⟨0, hp⟩ from Fin.ext (by simpa using hi)]
  · rw [c2v_val_ne_zero p q hp j hj]
    exact ⟨fun h => absurd h (by simp), fun h => absurd h.1 (by omega)⟩

@[simp] lemma c2v_eq_inr (p q : ℕ) (hp : 0 < p) (j : Fin q) (k : Fin (q - 1)) :
    c2v p q hp j = Sum.inr k ↔ j.val ≠ 0 ∧ j.val - 1 = k.val := by
  by_cases hj : j.val = 0
  · rw [c2v_val_zero p q hp j hj]
    exact ⟨fun h => absurd h (by simp), fun h => absurd h.1 (by omega)⟩
  · rw [c2v_val_ne_zero p q hp j hj]
    constructor
    · intro h
      exact ⟨hj, by have := congrArg Fin.val (Sum.inr.inj h); simpa using this⟩
    · rintro ⟨_, hk⟩
      rw [show (⟨j.val - 1, by have := j.isLt; omega⟩ : Fin (q-1)) = k from Fin.ext hk]

@[simp] lemma cnext_eq_zero_iff (n : ℕ) (hn : 0 < n) (i : Fin n) :
    cnext n hn i = ⟨0, hn⟩ ↔ i.val + 1 = n := by
  constructor
  · intro h
    by_cases hi : i.val + 1 < n
    · rw [cnext_val_of n hn i hi] at h
      have h2 := congrArg Fin.val h
      simp only [Fin.val_mk, Fin.val_zero] at h2
      omega
    · rw [cnext_val_last n hn i hi] at h
      omega
  · intro h
    have hi : ¬ (i.val + 1 < n) := by omega
    rw [cnext_val_last n hn i hi]

@[simp] lemma cnext_val_eq_zero_iff (n : ℕ) (hn : 0 < n) (i : Fin n) :
    (cnext n hn i).val = 0 ↔ i.val + 1 = n := by
  have h : (cnext n hn i).val = 0 ↔ cnext n hn i = ⟨0, hn⟩ := by
    constructor
    · intro hv; exact Fin.ext (by simpa using hv)
    · intro he; rw [he]
  rw [h, cnext_eq_zero_iff]

lemma cnext_eq_of_ne_zero (n : ℕ) (hn : 0 < n) (i j : Fin n) (hj : j.val ≠ 0) :
    cnext n hn i = j ↔ i.val + 1 = j.val := by
  constructor
  · intro h
    have := congrArg Fin.val h
    by_cases hi : i.val + 1 < n
    · rw [cnext_val_of n hn i hi] at this; simpa using this
    · rw [cnext_val_last n hn i hi] at this; simp at this; omega
  · intro h
    have hi : i.val + 1 < n := by have := j.isLt; omega
    rw [cnext_val_of n hn i hi]
    exact Fin.ext (by simpa using h)

lemma sum_fin_ite_val_eq {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k < n) (f : Fin n → ℤ) :
    (∑ i : Fin n, if i.val = k then f i else 0) = f ⟨k, hk⟩ := by
  rw [show (∑ i : Fin n, if i.val = k then f i else 0)
        = ∑ i : Fin n, if i = ⟨k,hk⟩ then f i else 0 by
      apply Finset.sum_congr rfl; intro i _
      congr 1
      exact propext ((Fin.eq_mk_iff_val_eq (a:=i) (k:=k) (hk:=hk)).symm)]
  rw [Finset.sum_ite_eq']; simp

lemma sum_fin_ite_of_val {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k < n)
    (P : Fin n → Prop) [DecidablePred P] (hP : ∀ i, P i ↔ i.val = k) (f : Fin n → ℤ) :
    (∑ i : Fin n, if P i then f i else 0) = f ⟨k, hk⟩ := by
  rw [show (∑ i : Fin n, if P i then f i else 0)
        = ∑ i : Fin n, if i.val = k then f i else 0 by
      apply Finset.sum_congr rfl; intro i _
      by_cases hp : P i
      · rw [ite_eq_left hp, ite_eq_left ((hP i).mp hp)]
      · rw [ite_eq_right hp, ite_eq_right (fun h => hp ((hP i).mpr h))]]
  exact sum_fin_ite_val_eq hn k hk f

lemma sum_fin_ite_of_false {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (hP : ∀ i, ¬ P i) (f : Fin n → ℤ) :
    (∑ i : Fin n, if P i then f i else 0) = 0 := by
  apply Finset.sum_eq_zero; intro i _; rw [ite_eq_right (hP i)]

lemma sum_c1_out_inl (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (f : Fin p → ℤ) (i : Fin p) :
    (∑ i' : Fin p, if gtail p q h1p h1q (Sum.inl i') = Sum.inl i then f i' else 0) = f i := by
  simp only [gtail_inl, Sum.inl.injEq]
  rw [Finset.sum_ite_eq']; simp

lemma sum_c2_out_inl (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (f : Fin q → ℤ) (i : Fin p) :
    (∑ j : Fin q, if gtail p q h1p h1q (Sum.inr (Sum.inl j)) = Sum.inl i then f j else 0)
      = if i.val = 0 then f ⟨0, by omega⟩ else 0 := by
  simp only [gtail_inr_inl, c2v_eq_inl]
  by_cases hi : i.val = 0
  · rw [sum_fin_ite_of_val (n:=q) (by omega) 0 (by omega)
        (fun j => j.val = 0 ∧ i.val = 0) (fun j => by simp [hi])]
    simp [hi]
  · rw [sum_fin_ite_of_false (n:=q) (fun j => j.val = 0 ∧ i.val = 0) (fun j => by simp [hi])]
    simp [hi]

lemma sum_bridge_out_inl (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (f : Fin 2 → ℤ) (i : Fin p) :
    (∑ k : Fin 2, if gtail p q h1p h1q (Sum.inr (Sum.inr k)) = Sum.inl i then f k else 0)
      = if i.val = 1 then f 0 else 0 := by
  rw [Fin.sum_univ_two]
  simp only [gtail_inr_inr_zero, gtail_inr_inr_one, c2v_eq_inl, Sum.inl.injEq]
  by_cases hi : i.val = 1
  · have h1 : (⟨1, h1p⟩ : Fin p) = i := Fin.ext (by simpa using hi.symm)
    rw [ite_eq_left h1]
    rw [ite_eq_right (show ¬ ((⟨1, h1q⟩ : Fin q).val = 0 ∧ i.val = 0) from by simp)]
    rw [add_zero, ite_eq_left hi]
  · have h1 : ¬ ((⟨1, h1p⟩ : Fin p) = i) := fun h => hi (by rw [← h])
    rw [ite_eq_right h1]
    rw [ite_eq_right (show ¬ ((⟨1, h1q⟩ : Fin q).val = 0 ∧ i.val = 0) from by simp)]
    rw [zero_add, ite_eq_right hi]

lemma sum_c1_in_inl (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (f : Fin p → ℤ) (i : Fin p) :
    (∑ i' : Fin p, if ghead p q h1p h1q (Sum.inl i') = Sum.inl i then f i' else 0)
      = if i.val = 0 then f ⟨p - 1, by omega⟩ else f ⟨i.val - 1, by omega⟩ := by
  simp only [ghead_inl, Sum.inl.injEq]
  by_cases hi : i.val = 0
  · have hiz : i = ⟨0, by omega⟩ := Fin.ext (by simpa using hi)
    rw [hiz]
    rw [sum_fin_ite_of_val (n:=p) (by omega) (p-1) (by omega)
          (fun i' => cnext p (by omega) i' = ⟨0, by omega⟩)
          (fun i' => by rw [cnext_eq_zero_iff]; omega)]
    simp [hi]
  · rw [sum_fin_ite_of_val (n:=p) (by omega) (i.val-1) (by omega)
          (fun i' => cnext p (by omega) i' = i)
          (fun i' => by rw [cnext_eq_of_ne_zero p (by omega) i' i hi]; omega)]
    simp [hi]

lemma sum_c2_in_inl (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (f : Fin q → ℤ) (i : Fin p) :
    (∑ j : Fin q, if ghead p q h1p h1q (Sum.inr (Sum.inl j)) = Sum.inl i then f j else 0)
      = if i.val = 0 then f ⟨q - 1, by omega⟩ else 0 := by
  simp only [ghead_inr_inl, c2v_eq_inl]
  by_cases hi : i.val = 0
  · rw [sum_fin_ite_of_val (n:=q) (by omega) (q-1) (by omega)
        (fun j => (cnext q (by omega) j).val = 0 ∧ i.val = 0)
        (fun j => by
          rw [hi]
          constructor
          · rintro ⟨h1, _⟩; rw [cnext_val_eq_zero_iff] at h1; omega
          · intro h; exact ⟨(cnext_val_eq_zero_iff q (by omega) j).mpr (by omega), rfl⟩)]
    simp [hi]
  · rw [sum_fin_ite_of_false (n:=q) (fun j => (cnext q (by omega) j).val = 0 ∧ i.val = 0)
        (fun j => by simp [hi])]
    simp [hi]

lemma sum_bridge_in_inl (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (f : Fin 2 → ℤ) (i : Fin p) :
    (∑ k : Fin 2, if ghead p q h1p h1q (Sum.inr (Sum.inr k)) = Sum.inl i then f k else 0)
      = if i.val = 1 then f 1 else 0 := by
  rw [Fin.sum_univ_two]
  simp only [ghead_inr_inr_zero, ghead_inr_inr_one, c2v_eq_inl, Sum.inl.injEq]
  by_cases hi : i.val = 1
  · rw [ite_eq_right (show ¬ ((⟨1, h1q⟩ : Fin q).val = 0 ∧ i.val = 0) from by simp)]
    have h1 : (⟨1, h1p⟩ : Fin p) = i := Fin.ext (by simpa using hi.symm)
    rw [ite_eq_left h1, zero_add, ite_eq_left hi]
  · rw [ite_eq_right (show ¬ ((⟨1, h1q⟩ : Fin q).val = 0 ∧ i.val = 0) from by simp)]
    have h1 : ¬ ((⟨1, h1p⟩ : Fin p) = i) := fun h => hi (by rw [← h])
    rw [ite_eq_right h1, zero_add, ite_eq_right hi]

lemma sum_c1_out_inr (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (f : Fin p → ℤ) (k : Fin (q-1)) :
    (∑ i' : Fin p, if gtail p q h1p h1q (Sum.inl i') = Sum.inr k then f i' else 0) = 0 := by
  simp only [gtail_inl]
  exact Finset.sum_eq_zero (fun i _ => by simp)

lemma sum_c2_out_inr (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (f : Fin q → ℤ) (k : Fin (q-1)) :
    (∑ j : Fin q, if gtail p q h1p h1q (Sum.inr (Sum.inl j)) = Sum.inr k then f j else 0)
      = f ⟨k.val + 1, by have := k.isLt; omega⟩ := by
  simp only [gtail_inr_inl, c2v_eq_inr]
  rw [sum_fin_ite_of_val (n:=q) (by omega) (k.val+1) (by have := k.isLt; omega)
        (fun j => j.val ≠ 0 ∧ j.val - 1 = k.val)
        (fun j => by
          constructor
          · rintro ⟨h1, h2⟩
            have h1' : 1 ≤ j.val := Nat.one_le_iff_ne_zero.mpr h1
            rw [← h2]; exact (Nat.sub_add_cancel h1').symm
          · intro h
            exact ⟨by omega, by omega⟩)]

lemma sum_bridge_out_inr (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (f : Fin 2 → ℤ) (k : Fin (q-1)) :
    (∑ k' : Fin 2, if gtail p q h1p h1q (Sum.inr (Sum.inr k')) = Sum.inr k then f k' else 0)
      = if k.val = 0 then f 1 else 0 := by
  rw [Fin.sum_univ_two]
  simp only [gtail_inr_inr_zero, gtail_inr_inr_one, c2v_eq_inr]
  split_ifs with h1 h2 h3 <;> simp_all <;> omega

lemma sum_c1_in_inr (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (f : Fin p → ℤ) (k : Fin (q-1)) :
    (∑ i' : Fin p, if ghead p q h1p h1q (Sum.inl i') = Sum.inr k then f i' else 0) = 0 := by
  simp only [ghead_inl]
  exact Finset.sum_eq_zero (fun i _ => by simp)

lemma sum_c2_in_inr (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (f : Fin q → ℤ) (k : Fin (q-1)) :
    (∑ j : Fin q, if ghead p q h1p h1q (Sum.inr (Sum.inl j)) = Sum.inr k then f j else 0)
      = f ⟨k.val, by have := k.isLt; omega⟩ := by
  simp only [ghead_inr_inl, c2v_eq_inr]
  rw [sum_fin_ite_of_val (n:=q) (by omega) k.val (by have := k.isLt; omega)
        (fun j => (cnext q (by omega) j).val ≠ 0 ∧ (cnext q (by omega) j).val - 1 = k.val)
        (fun j => by
          have hk := k.isLt
          constructor
          · rintro ⟨h1, h2⟩
            by_cases hjc : j.val + 1 < q
            · rw [cnext_val_of q (by omega) j hjc] at h2
              rw [Nat.add_sub_cancel] at h2; exact h2
            · rw [cnext_val_last q (by omega) j hjc] at h1; simp at h1
          · intro h
            have hjc : j.val + 1 < q := by omega
            rw [cnext_val_of q (by omega) j hjc]
            exact ⟨Nat.succ_ne_zero j.val, by rw [Nat.add_sub_cancel]; exact h⟩)]

lemma sum_bridge_in_inr (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (f : Fin 2 → ℤ) (k : Fin (q-1)) :
    (∑ k' : Fin 2, if ghead p q h1p h1q (Sum.inr (Sum.inr k')) = Sum.inr k then f k' else 0)
      = if k.val = 0 then f 0 else 0 := by
  rw [Fin.sum_univ_two]
  simp only [ghead_inr_inr_zero, ghead_inr_inr_one, c2v_eq_inr]
  split_ifs with h1 h2 h3 <;> simp_all <;> omega

end AssemblyP1.RigidityGeneralBridge

namespace AssemblyP1.RigidityGeneralBridge

def gA (p q : ℕ) (m1 m2 f : ℕ) : Arc p q → ℤ
  | Sum.inl _ => m1
  | Sum.inr (Sum.inl _) => m2
  | Sum.inr (Sum.inr 0) => f
  | Sum.inr (Sum.inr 1) => f

def gG (p q : ℕ) (m1 m2 f : ℕ) : ℕ := p * m1 + q * m2 + 2 * f

def phi (p q : ℕ) (a c u w : ℤ) : Arc p q → ℤ :=
  Sum.elim (fun i : Fin p => if i.val = 0 then a else a - u + w)
    (Sum.elim (fun j : Fin q => if j.val = 0 then c else c + u - w) ![u, w])

lemma phi_inl_zero (p q : ℕ) (a c u w : ℤ) (i : Fin p) (h : i.val = 0) :
    phi p q a c u w (Sum.inl i) = a := by
  show (if i.val = 0 then a else a - u + w) = a
  rw [ite_eq_left h]
lemma phi_inl_ne (p q : ℕ) (a c u w : ℤ) (i : Fin p) (h : i.val ≠ 0) :
    phi p q a c u w (Sum.inl i) = a - u + w := by
  show (if i.val = 0 then a else a - u + w) = a - u + w
  rw [ite_eq_right h]
lemma phi_inr_inl_zero (p q : ℕ) (a c u w : ℤ) (j : Fin q) (h : j.val = 0) :
    phi p q a c u w (Sum.inr (Sum.inl j)) = c := by
  show (if j.val = 0 then c else c + u - w) = c
  rw [ite_eq_left h]
lemma phi_inr_inl_ne (p q : ℕ) (a c u w : ℤ) (j : Fin q) (h : j.val ≠ 0) :
    phi p q a c u w (Sum.inr (Sum.inl j)) = c + u - w := by
  show (if j.val = 0 then c else c + u - w) = c + u - w
  rw [ite_eq_right h]
lemma phi_bridge_zero (p q : ℕ) (a c u w : ℤ) : phi p q a c u w (Sum.inr (Sum.inr 0)) = u := rfl
lemma phi_bridge_one (p q : ℕ) (a c u w : ℤ) : phi p q a c u w (Sum.inr (Sum.inr 1)) = w := rfl

def goutF (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (v : Vtx p q) : Finset (Arc p q) :=
  Finset.univ.filter (fun e => gtail p q h1p h1q e = v)
def ginF (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (v : Vtx p q) : Finset (Arc p q) :=
  Finset.univ.filter (fun e => ghead p q h1p h1q e = v)

lemma sum_goutF (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (v : Vtx p q) (F : Arc p q → ℤ) :
    ∑ e ∈ goutF p q h1p h1q v, F e =
      (∑ i : Fin p, if gtail p q h1p h1q (Sum.inl i) = v then F (Sum.inl i) else 0)
    + (∑ j : Fin q, if gtail p q h1p h1q (Sum.inr (Sum.inl j)) = v then F (Sum.inr (Sum.inl j)) else 0)
    + (∑ k : Fin 2, if gtail p q h1p h1q (Sum.inr (Sum.inr k)) = v then F (Sum.inr (Sum.inr k)) else 0) := by
  rw [goutF, Finset.sum_filter, Fintype.sum_sum_type, Fintype.sum_sum_type]
  ring

lemma sum_ginF (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (v : Vtx p q) (F : Arc p q → ℤ) :
    ∑ e ∈ ginF p q h1p h1q v, F e =
      (∑ i : Fin p, if ghead p q h1p h1q (Sum.inl i) = v then F (Sum.inl i) else 0)
    + (∑ j : Fin q, if ghead p q h1p h1q (Sum.inr (Sum.inl j)) = v then F (Sum.inr (Sum.inl j)) else 0)
    + (∑ k : Fin 2, if ghead p q h1p h1q (Sum.inr (Sum.inr k)) = v then F (Sum.inr (Sum.inr k)) else 0) := by
  rw [ginF, Finset.sum_filter, Fintype.sum_sum_type, Fintype.sum_sum_type]
  ring

lemma balanced_iff (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (δ : Arc p q → ℤ) :
    AssemblyP1.ExactRigidityCriterion.BalancedZ (gtail p q h1p h1q) (ghead p q h1p h1q)
        Finset.univ Finset.univ δ ↔
      ∀ v : Vtx p q, ∑ e ∈ goutF p q h1p h1q v, δ e = ∑ e ∈ ginF p q h1p h1q v, δ e := by
  constructor
  · intro h v; exact h v (Finset.mem_univ v)
  · intro h v _; exact h v

end AssemblyP1.RigidityGeneralBridge

namespace AssemblyP1.RigidityGeneralBridge

lemma phi_balanced_inl (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (a c u w : ℤ) (i : Fin p) :
    ∑ e ∈ goutF p q h1p h1q (Sum.inl i), phi p q a c u w e
  = ∑ e ∈ ginF p q h1p h1q (Sum.inl i), phi p q a c u w e := by
  rw [sum_goutF, sum_ginF]
  rw [sum_c1_out_inl p q h1p h1q (fun i' => phi p q a c u w (Sum.inl i')) i,
      sum_c2_out_inl p q h1p h1q (fun j => phi p q a c u w (Sum.inr (Sum.inl j))) i,
      sum_bridge_out_inl p q h1p h1q (fun k => phi p q a c u w (Sum.inr (Sum.inr k))) i,
      sum_c1_in_inl p q h1p h1q (fun i' => phi p q a c u w (Sum.inl i')) i,
      sum_c2_in_inl p q h1p h1q (fun j => phi p q a c u w (Sum.inr (Sum.inl j))) i,
      sum_bridge_in_inl p q h1p h1q (fun k => phi p q a c u w (Sum.inr (Sum.inr k))) i]
  have hp0 : (⟨p - 1, by omega⟩ : Fin p).val ≠ 0 := by simp; omega
  have hq0 : (⟨q - 1, by omega⟩ : Fin q).val ≠ 0 := by simp; omega
  by_cases hi0 : i.val = 0
  · have hi1 : ¬ (i.val = 1) := by omega
    simp only [hi0, hi1, ite_true, ite_false, phi, Sum.elim_inl, Sum.elim_inr, hp0, hq0,
      Nat.reduceEqDiff, Matrix.cons_val_zero, Matrix.cons_val_one]
    try ring
  · by_cases hi1 : i.val = 1
    · have hi2 : (⟨i.val - 1, by omega⟩ : Fin p).val = 0 := by simp; omega
      simp only [hi0, hi1, hi2, ite_true, ite_false, phi, Sum.elim_inl, Sum.elim_inr,
        Nat.reduceEqDiff, Matrix.cons_val_zero, Matrix.cons_val_one]
      try ring
    · have hi2 : (⟨i.val - 1, by omega⟩ : Fin p).val ≠ 0 := by simp; omega
      simp only [hi0, hi1, hi2, ite_true, ite_false, phi, Sum.elim_inl, Sum.elim_inr,
        Nat.reduceEqDiff, Matrix.cons_val_zero, Matrix.cons_val_one]
      try ring

lemma phi_balanced_inr (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (a c u w : ℤ) (k : Fin (q-1)) :
    ∑ e ∈ goutF p q h1p h1q (Sum.inr k), phi p q a c u w e
  = ∑ e ∈ ginF p q h1p h1q (Sum.inr k), phi p q a c u w e := by
  rw [sum_goutF, sum_ginF]
  rw [sum_c1_out_inr p q h1p h1q (fun i' => phi p q a c u w (Sum.inl i')) k,
      sum_c2_out_inr p q h1p h1q (fun j => phi p q a c u w (Sum.inr (Sum.inl j))) k,
      sum_bridge_out_inr p q h1p h1q (fun k' => phi p q a c u w (Sum.inr (Sum.inr k'))) k,
      sum_c1_in_inr p q h1p h1q (fun i' => phi p q a c u w (Sum.inl i')) k,
      sum_c2_in_inr p q h1p h1q (fun j => phi p q a c u w (Sum.inr (Sum.inl j))) k,
      sum_bridge_in_inr p q h1p h1q (fun k' => phi p q a c u w (Sum.inr (Sum.inr k'))) k]
  by_cases hk0 : k.val = 0
  · simp only [hk0, ite_true, ite_false, phi, Sum.elim_inl, Sum.elim_inr,
      Nat.reduceEqDiff, Matrix.cons_val_zero, Matrix.cons_val_one]
    try ring
  · have hk1 : (⟨k.val + 1, by omega⟩ : Fin q).val ≠ 0 := by simp
    have hk2 : (⟨k.val, by omega⟩ : Fin q).val ≠ 0 := by simp; omega
    simp only [hk0, hk1, hk2, ite_true, ite_false, phi, Sum.elim_inl, Sum.elim_inr,
      Nat.reduceEqDiff, Matrix.cons_val_zero, Matrix.cons_val_one]
    try ring

theorem phi_balanced (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (a c u w : ℤ) :
    AssemblyP1.ExactRigidityCriterion.BalancedZ (gtail p q h1p h1q) (ghead p q h1p h1q)
      Finset.univ Finset.univ (phi p q a c u w) := by
  rw [balanced_iff]
  intro v
  rcases v with i | k
  · exact phi_balanced_inl p q h1p h1q a c u w i
  · exact phi_balanced_inr p q h1p h1q a c u w k

end AssemblyP1.RigidityGeneralBridge

namespace AssemblyP1.RigidityGeneralBridge

lemma sum_fin_ite_zero (n : ℕ) (hn : 1 ≤ n) (x y : ℤ) :
    (∑ i : Fin n, if i.val = 0 then x else y) = x + (n - 1) * y := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [Fin.sum_univ_succ]
  have h1 : (if (0 : Fin (m+1)).val = 0 then x else y) = x := by simp
  have h2 : ∀ i : Fin m, (if (i.succ).val = 0 then x else y) = y := by
    intro i
    have hne : (i.succ).val ≠ 0 := by
      intro hc; exact Fin.succ_ne_zero i (Fin.ext hc)
    rw [ite_eq_right hne]
  rw [h1, Finset.sum_congr rfl (fun i _ => h2 i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  simp

lemma phi_eq_zero_iff (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (a c u w : ℤ) :
    phi p q a c u w = 0 ↔ a = 0 ∧ c = 0 ∧ u = 0 ∧ w = 0 := by
  constructor
  · intro h
    have h0 : a = 0 := by
      have := congrFun h (Sum.inl ⟨0, by omega⟩)
      rw [phi_inl_zero p q a c u w ⟨0, by omega⟩ rfl] at this
      simpa using this
    have hc : c = 0 := by
      have := congrFun h (Sum.inr (Sum.inl ⟨0, by omega⟩))
      rw [phi_inr_inl_zero p q a c u w ⟨0, by omega⟩ rfl] at this
      simpa using this
    have hu : u = 0 := by
      have := congrFun h (Sum.inr (Sum.inr 0))
      rw [phi_bridge_zero] at this; simpa using this
    have hw : w = 0 := by
      have := congrFun h (Sum.inr (Sum.inr 1))
      rw [phi_bridge_one] at this; simpa using this
    exact ⟨h0, hc, hu, hw⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    funext e
    rcases e with i | (j | k)
    · by_cases hi : i.val = 0
      · rw [phi_inl_zero p q 0 0 0 0 i hi]; simp
      · rw [phi_inl_ne p q 0 0 0 0 i hi]; simp
    · by_cases hj : j.val = 0
      · rw [phi_inr_inl_zero p q 0 0 0 0 j hj]; simp
      · rw [phi_inr_inl_ne p q 0 0 0 0 j hj]; simp
    · fin_cases k <;> simp [phi_bridge_zero, phi_bridge_one]

lemma phi_sum (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (a c u w : ℤ) :
    ∑ e ∈ (Finset.univ : Finset (Arc p q)), phi p q a c u w e =
      (p : ℤ) * a + (q : ℤ) * c + ((q : ℤ) - (p : ℤ) + 1) * u
        + ((p : ℤ) - (q : ℤ) + 1) * w := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h1 : (∑ i : Fin p, phi p q a c u w (Sum.inl i)) = a + ((p : ℤ) - 1) * (a - u + w) := by
    simpa only [phi, Sum.elim_inl] using sum_fin_ite_zero p (by omega) a (a - u + w)
  have h2 : (∑ j : Fin q, phi p q a c u w (Sum.inr (Sum.inl j)))
      = c + ((q : ℤ) - 1) * (c + u - w) := by
    simpa only [phi, Sum.elim_inr, Sum.elim_inl] using sum_fin_ite_zero q (by omega) c (c + u - w)
  have h3 : (∑ k : Fin 2, phi p q a c u w (Sum.inr (Sum.inr k))) = u + w := by
    rw [Fin.sum_univ_two]; simp [phi_bridge_zero, phi_bridge_one]
  rw [h1, h2, h3]
  push_cast
  ring

end AssemblyP1.RigidityGeneralBridge

namespace AssemblyP1.RigidityGeneralBridge

lemma c1_const (p q : ℕ) (h1p : 1 < p) (δ : Arc p q → ℤ) (a u w : ℤ)
    (hx : δ (Sum.inl ⟨1, h1p⟩) = a - u + w)
    (hstep : ∀ i : Fin p, 2 ≤ i.val →
      δ (Sum.inl i) = δ (Sum.inl ⟨i.val - 1, by have := i.isLt; omega⟩)) :
    ∀ i : Fin p, 1 ≤ i.val → δ (Sum.inl i) = a - u + w := by
  have key : ∀ k (hkp : k < p), 1 ≤ k → δ (Sum.inl ⟨k, hkp⟩) = a - u + w := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
    intro hkp hk1
    rcases Nat.eq_or_lt_of_le hk1 with hk1' | hk1'
    · subst hk1'
      rw [show (⟨1, hkp⟩ : Fin p) = ⟨1, h1p⟩ from Fin.ext rfl]
      exact hx
    · have hstepk := hstep ⟨k, hkp⟩ (Nat.succ_le_of_lt hk1')
      rw [hstepk]
      have h1 : k - 1 < k := Nat.sub_lt (by omega : 0 < k) (by norm_num)
      have h2 : k - 1 < p := Nat.lt_of_le_of_lt (Nat.sub_le k 1) hkp
      have h3 : 1 ≤ k - 1 := Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hk1')
      exact ih (k - 1) h1 h2 h3
  intro i hi
  exact key i.val i.isLt hi

lemma c2_const (p q : ℕ) (h1q : 1 < q) (δ : Arc p q → ℤ) (c u w : ℤ)
    (hy : δ (Sum.inr (Sum.inl ⟨1, h1q⟩)) = c + u - w)
    (hstep : ∀ j : Fin q, 2 ≤ j.val →
      δ (Sum.inr (Sum.inl j)) = δ (Sum.inr (Sum.inl ⟨j.val - 1, by have := j.isLt; omega⟩))) :
    ∀ j : Fin q, 1 ≤ j.val → δ (Sum.inr (Sum.inl j)) = c + u - w := by
  have key : ∀ k (hkq : k < q), 1 ≤ k → δ (Sum.inr (Sum.inl ⟨k, hkq⟩)) = c + u - w := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
    intro hkq hk1
    rcases Nat.eq_or_lt_of_le hk1 with hk1' | hk1'
    · subst hk1'
      rw [show (⟨1, hkq⟩ : Fin q) = ⟨1, h1q⟩ from Fin.ext rfl]
      exact hy
    · have hstepk := hstep ⟨k, hkq⟩ (Nat.succ_le_of_lt hk1')
      rw [hstepk]
      have h1 : k - 1 < k := Nat.sub_lt (by omega : 0 < k) (by norm_num)
      have h2 : k - 1 < q := Nat.lt_of_le_of_lt (Nat.sub_le k 1) hkq
      have h3 : 1 ≤ k - 1 := Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hk1')
      exact ih (k - 1) h1 h2 h3
  intro j hj
  exact key j.val j.isLt hj

theorem phi_of_balanced (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (δ : Arc p q → ℤ)
    (hδ : AssemblyP1.ExactRigidityCriterion.BalancedZ (gtail p q h1p h1q) (ghead p q h1p h1q)
      Finset.univ Finset.univ δ) :
    δ = phi p q (δ (Sum.inl ⟨0, by omega⟩)) (δ (Sum.inr (Sum.inl ⟨0, by omega⟩)))
        (δ (Sum.inr (Sum.inr 0))) (δ (Sum.inr (Sum.inr 1))) := by
  have hbal := (balanced_iff p q h1p h1q δ).mp hδ
  have hx : δ (Sum.inl ⟨1, h1p⟩)
      = δ (Sum.inl ⟨0, by omega⟩) - δ (Sum.inr (Sum.inr 0)) + δ (Sum.inr (Sum.inr 1)) := by
    have hh := hbal (Sum.inl ⟨1, h1p⟩)
    rw [sum_goutF, sum_ginF] at hh
    rw [sum_c1_out_inl p q h1p h1q (fun i' => δ (Sum.inl i')) ⟨1, h1p⟩,
        sum_c2_out_inl p q h1p h1q (fun j' => δ (Sum.inr (Sum.inl j'))) ⟨1, h1p⟩,
        sum_bridge_out_inl p q h1p h1q (fun k' => δ (Sum.inr (Sum.inr k'))) ⟨1, h1p⟩,
        sum_c1_in_inl p q h1p h1q (fun i' => δ (Sum.inl i')) ⟨1, h1p⟩,
        sum_c2_in_inl p q h1p h1q (fun j' => δ (Sum.inr (Sum.inl j'))) ⟨1, h1p⟩,
        sum_bridge_in_inl p q h1p h1q (fun k' => δ (Sum.inr (Sum.inr k'))) ⟨1, h1p⟩] at hh
    simp at hh
    linarith
  have hy : δ (Sum.inr (Sum.inl ⟨1, h1q⟩))
      = δ (Sum.inr (Sum.inl ⟨0, by omega⟩)) + δ (Sum.inr (Sum.inr 0)) - δ (Sum.inr (Sum.inr 1)) := by
    have hh := hbal (Sum.inr ⟨0, by omega⟩)
    rw [sum_goutF, sum_ginF] at hh
    rw [sum_c1_out_inr p q h1p h1q (fun i' => δ (Sum.inl i')) ⟨0, by omega⟩,
        sum_c2_out_inr p q h1p h1q (fun j' => δ (Sum.inr (Sum.inl j'))) ⟨0, by omega⟩,
        sum_bridge_out_inr p q h1p h1q (fun k' => δ (Sum.inr (Sum.inr k'))) ⟨0, by omega⟩,
        sum_c1_in_inr p q h1p h1q (fun i' => δ (Sum.inl i')) ⟨0, by omega⟩,
        sum_c2_in_inr p q h1p h1q (fun j' => δ (Sum.inr (Sum.inl j'))) ⟨0, by omega⟩,
        sum_bridge_in_inr p q h1p h1q (fun k' => δ (Sum.inr (Sum.inr k'))) ⟨0, by omega⟩] at hh
    simp at hh
    linarith
  have hstep1 : ∀ i : Fin p, 2 ≤ i.val →
      δ (Sum.inl i) = δ (Sum.inl ⟨i.val - 1, by have := i.isLt; omega⟩) := by
    intro i hi
    have hh := hbal (Sum.inl i)
    rw [sum_goutF, sum_ginF] at hh
    rw [sum_c1_out_inl p q h1p h1q (fun i' => δ (Sum.inl i')) i,
        sum_c2_out_inl p q h1p h1q (fun j' => δ (Sum.inr (Sum.inl j'))) i,
        sum_bridge_out_inl p q h1p h1q (fun k' => δ (Sum.inr (Sum.inr k'))) i,
        sum_c1_in_inl p q h1p h1q (fun i' => δ (Sum.inl i')) i,
        sum_c2_in_inl p q h1p h1q (fun j' => δ (Sum.inr (Sum.inl j'))) i,
        sum_bridge_in_inl p q h1p h1q (fun k' => δ (Sum.inr (Sum.inr k'))) i] at hh
    simp only [show i.val ≠ 0 from by omega, show i.val ≠ 1 from by omega, ite_false,
      zero_add, add_zero] at hh
    exact hh
  have hstep2 : ∀ j : Fin q, 2 ≤ j.val →
      δ (Sum.inr (Sum.inl j)) = δ (Sum.inr (Sum.inl ⟨j.val - 1, by have := j.isLt; omega⟩)) := by
    intro j hj
    have hkq : j.val - 1 < q - 1 := by have := j.isLt; omega
    have hk0 : (⟨j.val - 1, hkq⟩ : Fin (q - 1)).val ≠ 0 := by simp; omega
    have hh := hbal (Sum.inr ⟨j.val - 1, hkq⟩)
    rw [sum_goutF, sum_ginF] at hh
    rw [sum_c1_out_inr p q h1p h1q (fun i' => δ (Sum.inl i')) ⟨j.val - 1, hkq⟩,
        sum_c2_out_inr p q h1p h1q (fun j' => δ (Sum.inr (Sum.inl j'))) ⟨j.val - 1, hkq⟩,
        sum_bridge_out_inr p q h1p h1q (fun k' => δ (Sum.inr (Sum.inr k'))) ⟨j.val - 1, hkq⟩,
        sum_c1_in_inr p q h1p h1q (fun i' => δ (Sum.inl i')) ⟨j.val - 1, hkq⟩,
        sum_c2_in_inr p q h1p h1q (fun j' => δ (Sum.inr (Sum.inl j'))) ⟨j.val - 1, hkq⟩,
        sum_bridge_in_inr p q h1p h1q (fun k' => δ (Sum.inr (Sum.inr k'))) ⟨j.val - 1, hkq⟩] at hh
    simp only [hk0, ite_false, zero_add, add_zero] at hh
    have hjeq : (⟨j.val - 1 + 1, by omega⟩ : Fin q) = j :=
      Fin.ext (Nat.sub_add_cancel (by omega : 1 ≤ j.val))
    rw [hjeq] at hh
    exact hh
  funext e
  rcases e with i | (j | k)
  · by_cases hi : i.val = 0
    · rw [phi_inl_zero p q _ _ _ _ i hi]
      have hiz : i = ⟨0, by omega⟩ := Fin.ext (by simpa using hi)
      rw [hiz]
    · rw [phi_inl_ne p q _ _ _ _ i hi]
      exact c1_const p q h1p δ _ _ _ hx hstep1 i (by omega)
  · by_cases hj : j.val = 0
    · rw [phi_inr_inl_zero p q _ _ _ _ j hj]
      have hjz : j = ⟨0, by omega⟩ := Fin.ext (by simpa using hj)
      rw [hjz]
    · rw [phi_inr_inl_ne p q _ _ _ _ j hj]
      exact c2_const p q h1q δ _ _ _ hy hstep2 j (by omega)
  · fin_cases k
    · exact (phi_bridge_zero p q _ _ _ _).symm
    · exact (phi_bridge_one p q _ _ _ _).symm

end AssemblyP1.RigidityGeneralBridge

namespace AssemblyP1.RigidityGeneralBridge

lemma gA_eq_phi (p q : ℕ) (m1 m2 f : ℕ) :
    gA p q m1 m2 f = phi p q (m1 : ℤ) (m2 : ℤ) (f : ℤ) (f : ℤ) := by
  funext e
  rcases e with i | (j | k)
  · by_cases hi : i.val = 0
    · rw [phi_inl_zero p q _ _ _ _ i hi]; rfl
    · rw [phi_inl_ne p q _ _ _ _ i hi]; simp [gA]
  · by_cases hj : j.val = 0
    · rw [phi_inr_inl_zero p q _ _ _ _ j hj]; rfl
    · rw [phi_inr_inl_ne p q _ _ _ _ j hj]; simp [gA]
  · fin_cases k <;> rfl

lemma gA_balanced (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (m1 m2 f : ℕ) :
    AssemblyP1.ExactRigidityCriterion.BalancedZ (gtail p q h1p h1q) (ghead p q h1p h1q)
      Finset.univ Finset.univ (gA p q m1 m2 f) := by
  rw [gA_eq_phi]
  exact phi_balanced p q h1p h1q (m1 : ℤ) (m2 : ℤ) (f : ℤ) (f : ℤ)

lemma gA_total (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (m1 m2 f : ℕ) :
    ∑ e ∈ (Finset.univ : Finset (Arc p q)), gA p q m1 m2 f e = (gG p q m1 m2 f : ℤ) := by
  rw [gA_eq_phi, phi_sum p q h1p h1q]
  simp only [gG]
  push_cast
  ring

theorem generalBridge_nonrigid_iff (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q)
    (m1 m2 f : ℕ) (hm1 : 1 ≤ m1) (hm2 : 1 ≤ m2) (hf : 1 ≤ f) :
    (¬ AssemblyP1.ExactRigidityCriterion.Rigid (gtail p q h1p h1q) (ghead p q h1p h1q)
        Finset.univ Finset.univ (gA p q m1 m2 f) (gG p q m1 m2 f)) ↔
      ∃ a c u w : ℤ, (a ≠ 0 ∨ c ≠ 0 ∨ u ≠ 0 ∨ w ≠ 0) ∧
        (p : ℤ) * a + (q : ℤ) * c + ((q : ℤ) - (p : ℤ) + 1) * u
          + ((p : ℤ) - (q : ℤ) + 1) * w = 0 ∧
        (1 - (m1 : ℤ) ≤ a) ∧ (1 - (m1 : ℤ) ≤ a - u + w) ∧
        (1 - (m2 : ℤ) ≤ c) ∧ (1 - (m2 : ℤ) ≤ c - w + u) ∧
        (1 - (f : ℤ) ≤ u) ∧ (1 - (f : ℤ) ≤ w) := by
  rw [AssemblyP1.ExactRigidityCriterion.nonrigid_iff_exists_delta (gtail p q h1p h1q)
      (ghead p q h1p h1q) Finset.univ Finset.univ (gA p q m1 m2 f) (gG p q m1 m2 f)
      (gA_balanced p q h1p h1q m1 m2 f) (gA_total p q h1p h1q m1 m2 f)]
  have hp0 : 0 < p := by omega
  have hq0 : 0 < q := by omega
  constructor
  · rintro ⟨δ, ⟨e0, he0, hne⟩, hδbal, hδsum, hδbox⟩
    have hphi := phi_of_balanced p q h1p h1q δ hδbal
    have hz := hδsum
    rw [AssemblyP1.ExactRigidityCriterion.ZeroSum] at hz
    rw [hphi, phi_sum p q h1p h1q] at hz
    refine ⟨δ (Sum.inl ⟨0, hp0⟩), δ (Sum.inr (Sum.inl ⟨0, hq0⟩)),
      δ (Sum.inr (Sum.inr 0)), δ (Sum.inr (Sum.inr 1)), ?_, hz, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · by_contra hcon
      push Not at hcon
      obtain ⟨h0, h2, h4, h5⟩ := hcon
      apply hne
      rw [hphi, h0, h2, h4, h5]
      exact congrFun (phi_eq_zero_iff p q h1p h1q 0 0 0 0 |>.mpr ⟨rfl, rfl, rfl, rfl⟩) e0
    · have hb := hδbox (Sum.inl ⟨0, hp0⟩) (Finset.mem_univ _)
      simp only [gA] at hb
      exact hb
    · have hb := hδbox (Sum.inl ⟨1, h1p⟩) (Finset.mem_univ _)
      rw [hphi] at hb
      rw [phi_inl_ne p q _ _ _ _ ⟨1, h1p⟩ (by norm_num)] at hb
      simp only [gA] at hb
      linarith
    · have hb := hδbox (Sum.inr (Sum.inl ⟨0, hq0⟩)) (Finset.mem_univ _)
      simp only [gA] at hb
      exact hb
    · have hb := hδbox (Sum.inr (Sum.inl ⟨1, h1q⟩)) (Finset.mem_univ _)
      rw [hphi] at hb
      rw [phi_inr_inl_ne p q _ _ _ _ ⟨1, h1q⟩ (by norm_num)] at hb
      simp only [gA] at hb
      linarith
    · have hb := hδbox (Sum.inr (Sum.inr 0)) (Finset.mem_univ _)
      simp only [gA] at hb
      exact hb
    · have hb := hδbox (Sum.inr (Sum.inr 1)) (Finset.mem_univ _)
      simp only [gA] at hb
      exact hb
  · rintro ⟨a, c, u, w, hne, hsum, ha, hb, hc, hd, hu, hw⟩
    refine ⟨phi p q a c u w, ?_, phi_balanced p q h1p h1q a c u w, ?_, ?_⟩
    · by_contra h
      push Not at h
      have hz : phi p q a c u w = 0 := funext (fun e => h e (Finset.mem_univ e))
      obtain ⟨ha0, hc0, hu0, hw0⟩ := (phi_eq_zero_iff p q h1p h1q a c u w).mp hz
      rcases hne with h' | h' | h' | h'
      · exact h' ha0
      · exact h' hc0
      · exact h' hu0
      · exact h' hw0
    · rw [AssemblyP1.ExactRigidityCriterion.ZeroSum, phi_sum p q h1p h1q]; exact hsum
    · intro e _
      rcases e with i | (j | k)
      · by_cases hi : i.val = 0
        · rw [phi_inl_zero p q a c u w i hi]; simp only [gA]; linarith
        · rw [phi_inl_ne p q a c u w i hi]; simp only [gA]; linarith
      · by_cases hj : j.val = 0
        · rw [phi_inr_inl_zero p q a c u w j hj]; simp only [gA]; linarith
        · rw [phi_inr_inl_ne p q a c u w j hj]; simp only [gA]; linarith
      · fin_cases k
        · show (1 - (f : ℤ) ≤ phi p q a c u w (Sum.inr (Sum.inr 0))); rw [phi_bridge_zero]; linarith
        · show (1 - (f : ℤ) ≤ phi p q a c u w (Sum.inr (Sum.inr 1))); rw [phi_bridge_one]; linarith

end AssemblyP1.RigidityGeneralBridge

namespace AssemblyP1.RigidityGeneralBridge

/-- Non-rigidity when the second cycle is heavily repeated (`m2 ≥ p+1`), with
witness `(a,c,u,w) = (q, -p, 0, 0)`: the relation `q·C1 - p·C2` has zero total
mass. -/
theorem generalBridge_nonrigid_m2_large (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q)
    (m1 m2 f : ℕ) (hm1 : 1 ≤ m1) (hm2 : p + 1 ≤ m2) (hf : 1 ≤ f) :
    ¬ AssemblyP1.ExactRigidityCriterion.Rigid (gtail p q h1p h1q) (ghead p q h1p h1q)
        Finset.univ Finset.univ (gA p q m1 m2 f) (gG p q m1 m2 f) := by
  rw [generalBridge_nonrigid_iff p q h1p h1q m1 m2 f hm1 (by omega) hf]
  refine ⟨(q : ℤ), -(p : ℤ), 0, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Or.inl (Nat.cast_ne_zero.mpr (by omega : q ≠ 0))
  · ring
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

/-- Non-rigidity when the first cycle is heavily repeated (`m1 ≥ q+1`), with
witness `(a,c,u,w) = (-q, p, 0, 0)`. -/
theorem generalBridge_nonrigid_m1_large (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q)
    (m1 m2 f : ℕ) (hm1 : q + 1 ≤ m1) (hm2 : 1 ≤ m2) (hf : 1 ≤ f) :
    ¬ AssemblyP1.ExactRigidityCriterion.Rigid (gtail p q h1p h1q) (ghead p q h1p h1q)
        Finset.univ Finset.univ (gA p q m1 m2 f) (gG p q m1 m2 f) := by
  rw [generalBridge_nonrigid_iff p q h1p h1q m1 m2 f (by omega) hm2 hf]
  refine ⟨-(q : ℤ), (p : ℤ), 0, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Or.inl (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega : q ≠ 0)))
  · ring
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

/-- For equal cycle lengths `p = q`, repeating the first cycle (`m1 ≥ 2`) is
non-rigid, with witness `(-1, 1, 0, 0)`. -/
theorem generalBridge_nonrigid_eq_m1 (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (hpq : p = q)
    (m1 m2 f : ℕ) (hm1 : 2 ≤ m1) (hm2 : 1 ≤ m2) (hf : 1 ≤ f) :
    ¬ AssemblyP1.ExactRigidityCriterion.Rigid (gtail p q h1p h1q) (ghead p q h1p h1q)
        Finset.univ Finset.univ (gA p q m1 m2 f) (gG p q m1 m2 f) := by
  subst hpq
  rw [generalBridge_nonrigid_iff p p h1p h1q m1 m2 f (by omega) hm2 hf]
  refine ⟨-1, 1, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Or.inl (by norm_num)
  · ring
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

/-- For equal cycle lengths `p = q`, repeating the second cycle (`m2 ≥ 2`) is
non-rigid, with witness `(1, -1, 0, 0)`. -/
theorem generalBridge_nonrigid_eq_m2 (p q : ℕ) (h1p : 1 < p) (h1q : 1 < q) (hpq : p = q)
    (m1 m2 f : ℕ) (hm1 : 1 ≤ m1) (hm2 : 2 ≤ m2) (hf : 1 ≤ f) :
    ¬ AssemblyP1.ExactRigidityCriterion.Rigid (gtail p q h1p h1q) (ghead p q h1p h1q)
        Finset.univ Finset.univ (gA p q m1 m2 f) (gG p q m1 m2 f) := by
  subst hpq
  rw [generalBridge_nonrigid_iff p p h1p h1q m1 m2 f hm1 (by omega) hf]
  refine ⟨1, -1, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Or.inl (by norm_num)
  · ring
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

/-- For second cycle length `q = 3`, repeating the bridge (`f ≥ 3`) with trivial
cycle multiplicities is non-rigid, with witness `(1, 0, -1, -2)`. This
generalises the length-3 witness `length3Bridge_nonrigid_f` to arbitrary `p`. -/
theorem generalBridge_nonrigid_q3_f (p : ℕ) (h1p : 1 < p) (m1 m2 f : ℕ)
    (hm1 : m1 = 1) (hm2 : m2 = 1) (hf : 3 ≤ f) :
    ¬ AssemblyP1.ExactRigidityCriterion.Rigid (gtail p 3 h1p (by norm_num)) (ghead p 3 h1p (by norm_num))
        Finset.univ Finset.univ (gA p 3 m1 m2 f) (gG p 3 m1 m2 f) := by
  subst hm1; subst hm2
  rw [generalBridge_nonrigid_iff p 3 h1p (by norm_num) 1 1 f (by norm_num) (by norm_num) (by omega)]
  refine ⟨1, 0, -1, -2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Or.inl (by norm_num)
  · ring
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

/-- A `p,q`-dependent **rigid repetitive** instance: the `(p,q) = (3,4)` bridge
with `(m1,m2,f) = (2,1,1)` is rigid even though the first cycle is traversed
twice. This refutes any claim that `m1 ≥ 2` alone forces non-rigidity. -/
theorem generalBridge_rigid_repetitive :
    AssemblyP1.ExactRigidityCriterion.Rigid (gtail 3 4 (by norm_num) (by norm_num))
        (ghead 3 4 (by norm_num) (by norm_num)) Finset.univ Finset.univ
        (gA 3 4 2 1 1) (gG 3 4 2 1 1) := by
  by_contra hnr
  rw [generalBridge_nonrigid_iff 3 4 (by norm_num) (by norm_num) 2 1 1
      (by norm_num) (by norm_num) (by norm_num)] at hnr
  obtain ⟨a, c, u, w, hne, hsum, ha, hb, hc, hd, hu, hw⟩ := hnr
  simp only [Nat.cast_ofNat, Nat.cast_one] at hsum ha hb hc hd hu hw
  have ha0 : a = 0 := by omega
  have hc0 : c = 0 := by omega
  have hu0 : u = 0 := by omega
  have hw0 : w = 0 := by omega
  rcases hne with h' | h' | h' | h'
  · exact h' ha0
  · exact h' hc0
  · exact h' hu0
  · exact h' hw0

end AssemblyP1.RigidityGeneralBridge
