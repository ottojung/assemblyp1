import AssemblyP1.ExactRigidityCriterion

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The triangular multi-hub family: a three-hub unbounded-cycle-rank family with a
# polynomial rigidity criterion (issue #257, §8.1/§8.2)

This module advances open items **§8.1** (a closed-form / polynomial criterion
for rigidity beyond bounded cycle rank) and **§8.2** (the exact complexity) of
`docs/source-notes/issue-257-rigid-read-graphs.md`. It imports only
`AssemblyP1.ExactRigidityCriterion` (Theorem 1) and is **not** a re-proof of any
merged front (finite decider, Graver, two-walk, bouquet, antiparallel bridge,
length-3 / general `p,q` bridge, double theta, two-hub multi-hub, coin/LP no-go).

## The topology

The *triangular multi-hub* family joins three hubs `u, v, w` in a directed cycle:
`a` internally vertex-disjoint `u → v` paths, `b` `v → w` paths and `c` `w → u`
paths, of **arbitrary lengths** `plen ≥ 1`. It has cycle rank `a + b + c - 2`,
which is **unbounded**, so this family is strictly larger than the bounded-cycle-
rank families for which a polynomial criterion was previously known, and it is a
genuinely *three-hub* topology (the merged two-hub multi-hub of `RigidityMultiHub`
is the degenerate case `c = 0`, i.e. a two-hub graph).

Internal vertices have in- and out-degree `1`, so every circulation is constant
on each path; writing `α, β, γ` for the path values in the three directions, the
three hubs give the two independent *hub-balance* equations

```
∑_{u→v} α = ∑_{v→w} β   and   ∑_{v→w} β = ∑_{w→u} γ,
```

and the total mass is `∑ plen · α + ∑ plen · β + ∑ plen · γ`.

## Main results

* `phi_of_balanced` / `balanced_of_phi`: a balanced integral circulation is
  exactly a path-constant function whose path values satisfy the two hub-balance
  equations.
* `triHub_nonrigid_iff`: the **exact criterion** — the base circulation is
  non-rigid **iff** there is a nonzero integer path-perturbation `(α, β, γ)` with
  hub balance, zero total mass `∑ plen · α + ∑ plen · β + ∑ plen · γ = 0`, and
  the boxes `α ≥ 1 - m`.
* `triHub_rigid_all_one`: all multiplicities `1` is rigid.
* `triHub_rigid_repetitive`: a **rigid repetitive** instance (lengths `(1,3)`
  each direction, multiplicities `(2,1)` each direction): the length-`1` path of
  each direction is traversed twice, yet the support is rigid.
* `triHub_relaxed_not_sound`: the naive independent-per-path (bouquet-style /
  single-cut) relaxation obtained by dropping the hub-balance equations is **not
  sound** — a committed counterexample to a tempting simpler hypothesis.

## §8.2 complexity (documented, cross-checked)

The criterion is a **three-equation** nonnegative-integer uniqueness problem.
Because the path lengths are encoded in unary (an explicit support), it is
decidable by a polynomial dynamic program in the input size, counting solutions
up to `2`; the companion script `scripts/verify_257_tri_hub.py` implements this
DP and cross-checks it against from-scratch enumeration. The general-support
case (arbitrary cycle rank) and any min-cut/max-flow closed form for it remain
**OPEN** (§8.1/§8.2).
-/

namespace AssemblyP1.RigidityTriHub

open Finset BigOperators

/-- Path index: `Sum.inl i` is the `i`-th `u → v` path, `Sum.inr (Sum.inl j)` the
`j`-th `v → w` path, and `Sum.inr (Sum.inr k)` the `k`-th `w → u` path. -/
abbrev PIdx (a b c : ℕ) : Type := Fin a ⊕ Fin b ⊕ Fin c

variable {a b c : ℕ}

/-- Source hub of a path: `u = 0` for a `u → v` path, `v = 1` for a `v → w` path,
`w = 2` for a `w → u` path. -/
def srcHub : PIdx a b c → Fin 3
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 2

/-- Target hub of a path. -/
def tgtHub : PIdx a b c → Fin 3
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl _) => 2
  | Sum.inr (Sum.inr _) => 0

/-- Vertices: the three hubs, plus the internal vertex of every path. A path of
length `plen s` has `plen s - 1` internal vertices. -/
abbrev Vtx (plen : PIdx a b c → ℕ) : Type := Fin 3 ⊕ (Σ s : PIdx a b c, Fin (plen s - 1))

/-- Arcs: for every path `s` of length `plen s`, arcs indexed `0 … plen s - 1`. -/
abbrev Arc (plen : PIdx a b c → ℕ) : Type := Σ s : PIdx a b c, Fin (plen s)

/-- Tail of an arc `(s, i)`: the source hub when `i = 0`, otherwise the internal
vertex `(s, i-1)`. -/
def mtail (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s) : Arc plen → Vtx plen
  | ⟨s, i⟩ =>
    if h : i.val = 0 then Sum.inl (srcHub s)
    else Sum.inr ⟨s, ⟨i.val - 1, by have := i.isLt; have := hpos s; omega⟩⟩

/-- Head of an arc `(s, i)`: the target hub on the last arc of a path, otherwise
the internal vertex `(s, i)`. -/
def mhead (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s) : Arc plen → Vtx plen
  | ⟨s, i⟩ =>
    if h : i.val + 1 = plen s then Sum.inl (tgtHub s)
    else Sum.inr ⟨s, ⟨i.val, by have := i.isLt; omega⟩⟩

@[simp] lemma mtail_mk (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (s : PIdx a b c) (i : Fin (plen s)) :
    mtail plen hpos ⟨s, i⟩ =
      (if h : i.val = 0 then Sum.inl (srcHub s)
       else Sum.inr ⟨s, ⟨i.val - 1, by have := i.isLt; have := hpos s; omega⟩⟩) := rfl

@[simp] lemma mhead_mk (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (s : PIdx a b c) (i : Fin (plen s)) :
    mhead plen hpos ⟨s, i⟩ =
      (if h : i.val + 1 = plen s then Sum.inl (tgtHub s)
       else Sum.inr ⟨s, ⟨i.val, by have := i.isLt; omega⟩⟩) := rfl

/-- The all-vertices node set. -/
def mnodes (plen : PIdx a b c → ℕ) : Finset (Vtx plen) := Finset.univ

/-- The all-arcs support. -/
def medges (plen : PIdx a b c → ℕ) : Finset (Arc plen) := Finset.univ

/-- The path-constant arc function `φ(q)`: every arc of path `s` carries `q s`. -/
def phi (plen : PIdx a b c → ℕ) (q : PIdx a b c → ℤ) : Arc plen → ℤ := fun x => q x.1

/-- The base circulation: every arc of path `s` carries multiplicity `m s`. -/
def mA (plen : PIdx a b c → ℕ) (m : PIdx a b c → ℕ) : Arc plen → ℤ := fun x => (m x.1 : ℤ)

/-- Total mass of the base circulation. -/
def mG (plen : PIdx a b c → ℕ) (m : PIdx a b c → ℕ) : ℕ := ∑ s, plen s * m s

@[simp] lemma phi_apply (plen : PIdx a b c → ℕ) (q : PIdx a b c → ℤ) (x : Arc plen) :
    phi plen q x = q x.1 := rfl

@[simp] lemma phi_mk (plen : PIdx a b c → ℕ) (q : PIdx a b c → ℤ) (s : PIdx a b c)
    (i : Fin (plen s)) : phi plen q ⟨s, i⟩ = q s := rfl

@[simp] lemma mA_mk (plen : PIdx a b c → ℕ) (m : PIdx a b c → ℕ) (s : PIdx a b c)
    (i : Fin (plen s)) : mA plen m ⟨s, i⟩ = (m s : ℤ) := rfl

end AssemblyP1.RigidityTriHub

namespace AssemblyP1.RigidityTriHub

open Finset BigOperators

variable {a b c : ℕ}

/-- Out-arcs of a vertex within the support. -/
def moutF (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s) (v : Vtx plen) :
    Finset (Arc plen) := (medges plen).filter (fun e => mtail plen hpos e = v)

/-- In-arcs of a vertex within the support. -/
def minF (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s) (v : Vtx plen) :
    Finset (Arc plen) := (medges plen).filter (fun e => mhead plen hpos e = v)

@[simp] lemma mem_moutF (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (v : Vtx plen) (e : Arc plen) : e ∈ moutF plen hpos v ↔ mtail plen hpos e = v := by
  simp [moutF, medges]

@[simp] lemma mem_minF (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (v : Vtx plen) (e : Arc plen) : e ∈ minF plen hpos v ↔ mhead plen hpos e = v := by
  simp [minF, medges]

/-- Characterization of the tail of an arc being an internal vertex. -/
lemma mtail_eq_inr_iff (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (s s' : PIdx a b c) (r : Fin (plen s - 1)) (i : Fin (plen s')) :
    mtail plen hpos ⟨s', i⟩ = Sum.inr ⟨s, r⟩ ↔ s' = s ∧ i.val = r.val + 1 := by
  rw [mtail_mk]
  split_ifs with h0
  · constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨rfl, hi⟩; omega
  · constructor
    · intro h
      have hfst : s' = s := by
        have := congrArg (fun x : Σ t : PIdx a b c, Fin (plen t - 1) => x.1) (Sum.inr.inj h)
        exact this
      have hsnd : i.val - 1 = r.val := by
        have := congrArg (fun x : Σ t : PIdx a b c, Fin (plen t - 1) => x.2.val) (Sum.inr.inj h)
        exact this
      exact ⟨hfst, by omega⟩
    · rintro ⟨hs', hi⟩
      cases hs'
      have hfin : (⟨i.val - 1, by have h1 := i.isLt; have h2 := hpos s; have h3 := h0; omega⟩ : Fin (plen s - 1)) = r := by
        apply Fin.ext; simp; omega
      rw [hfin]

/-- Characterization of the head of an arc being an internal vertex. -/
lemma mhead_eq_inr_iff (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (s s' : PIdx a b c) (r : Fin (plen s - 1)) (i : Fin (plen s')) :
    mhead plen hpos ⟨s', i⟩ = Sum.inr ⟨s, r⟩ ↔ s' = s ∧ i.val = r.val := by
  rw [mhead_mk]
  split_ifs with hlast
  · constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨rfl, hi⟩
      omega
  · constructor
    · intro h
      have hfst : s' = s := by
        have := congrArg (fun x : Σ t : PIdx a b c, Fin (plen t - 1) => x.1) (Sum.inr.inj h)
        exact this
      have hsnd : i.val = r.val := by
        have := congrArg (fun x : Σ t : PIdx a b c, Fin (plen t - 1) => x.2.val) (Sum.inr.inj h)
        exact this
      exact ⟨hfst, hsnd⟩
    · rintro ⟨hs', hi⟩
      cases hs'
      have hfin : (⟨i.val, by have h1 := i.isLt; omega⟩ : Fin (plen s - 1)) = r := by
        apply Fin.ext; simp; omega
      rw [hfin]

end AssemblyP1.RigidityTriHub

namespace AssemblyP1.RigidityTriHub

open Finset BigOperators

variable {a b c : ℕ}

/-- The out-arc of an internal vertex `(s, r)` is the single arc `(s, r+1)`. -/
lemma moutF_internal (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (s : PIdx a b c) (r : Fin (plen s - 1)) :
    moutF plen hpos (Sum.inr ⟨s, r⟩) =
      {⟨s, ⟨r.val + 1, by have := r.isLt; omega⟩⟩} := by
  apply Finset.eq_singleton_iff_unique_mem.mpr
  constructor
  · rw [mem_moutF]
    exact (mtail_eq_inr_iff plen hpos s s r
      ⟨r.val + 1, by have := r.isLt; omega⟩).mpr ⟨rfl, rfl⟩
  · intro e he
    rw [mem_moutF] at he
    obtain ⟨s', i⟩ := e
    obtain ⟨hs', hi⟩ := (mtail_eq_inr_iff plen hpos s s' r i).mp he
    cases hs'
    have hfin : i = (⟨r.val + 1, by have := r.isLt; omega⟩ : Fin (plen s)) := by
      apply Fin.ext; simp; omega
    rw [hfin]

/-- The in-arc of an internal vertex `(s, r)` is the single arc `(s, r)`. -/
lemma minF_internal (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (s : PIdx a b c) (r : Fin (plen s - 1)) :
    minF plen hpos (Sum.inr ⟨s, r⟩) =
      {⟨s, ⟨r.val, by have := r.isLt; omega⟩⟩} := by
  apply Finset.eq_singleton_iff_unique_mem.mpr
  constructor
  · rw [mem_minF]
    exact (mhead_eq_inr_iff plen hpos s s r
      ⟨r.val, by have := r.isLt; omega⟩).mpr ⟨rfl, rfl⟩
  · intro e he
    rw [mem_minF] at he
    obtain ⟨s', i⟩ := e
    obtain ⟨hs', hi⟩ := (mhead_eq_inr_iff plen hpos s s' r i).mp he
    cases hs'
    have hfin : i = (⟨r.val, by have := r.isLt; omega⟩ : Fin (plen s)) := by
      apply Fin.ext; simp; omega
    rw [hfin]

end AssemblyP1.RigidityTriHub

namespace AssemblyP1.RigidityTriHub

open Finset BigOperators

variable {a b c : ℕ}

/-- An arc's tail is a hub `Sum.inl h` iff it is the first arc of a path whose
source hub is `h`. -/
lemma mtail_eq_inl_iff (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (s' : PIdx a b c) (i : Fin (plen s')) (h : Fin 3) :
    mtail plen hpos ⟨s', i⟩ = Sum.inl h ↔ i.val = 0 ∧ srcHub s' = h := by
  rw [mtail_mk]
  by_cases h0 : i.val = 0
  · rw [dite_eq_left h0]; simp [Sum.inl.injEq, h0]
  · rw [dite_eq_right h0]; simp [h0]

/-- An arc's head is a hub `Sum.inl h` iff it is the last arc of a path whose
target hub is `h`. -/
lemma mhead_eq_inl_iff (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (s' : PIdx a b c) (i : Fin (plen s')) (h : Fin 3) :
    mhead plen hpos ⟨s', i⟩ = Sum.inl h ↔ i.val + 1 = plen s' ∧ tgtHub s' = h := by
  rw [mhead_mk]
  by_cases hlast : i.val + 1 = plen s'
  · rw [dite_eq_left hlast]; simp [Sum.inl.injEq, hlast]
  · rw [dite_eq_right hlast]; simp [hlast]

/-- Out-arcs of hub `u = Sum.inl 0` are the first arcs of the `u → v` paths. -/
lemma moutF_hub_zero (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s) :
    moutF plen hpos (Sum.inl (0 : Fin 3)) =
      Finset.univ.image (fun i : Fin a =>
        (⟨Sum.inl i, ⟨0, by have := hpos (Sum.inl i); omega⟩⟩ : Arc plen)) := by
  apply Finset.ext
  intro e
  obtain ⟨s', i⟩ := e
  rw [mem_moutF, Finset.mem_image]
  constructor
  · intro hh
    obtain ⟨h0, hsrc⟩ := (mtail_eq_inl_iff plen hpos s' i 0).mp hh
    cases s' with
    | inl i' =>
        refine ⟨i', Finset.mem_univ i', ?_⟩
        have hi : i = (⟨0, by have := hpos (Sum.inl i'); omega⟩ : Fin (plen (Sum.inl i'))) := by
          apply Fin.ext; simp; omega
        rw [hi]
    | inr s'' =>
        cases s'' with
        | inl j' => simp [srcHub] at hsrc
        | inr k' => simp [srcHub] at hsrc
  · rintro ⟨i', -, he⟩
    rw [← he]
    exact (mtail_eq_inl_iff plen hpos (Sum.inl i')
      ⟨0, by have := hpos (Sum.inl i'); omega⟩ 0).mpr ⟨rfl, rfl⟩

/-- In-arcs of hub `u = Sum.inl 0` are the last arcs of the `w → u` paths. -/
lemma minF_hub_zero (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s) :
    minF plen hpos (Sum.inl (0 : Fin 3)) =
      Finset.univ.image (fun k : Fin c =>
        (⟨Sum.inr (Sum.inr k), ⟨plen (Sum.inr (Sum.inr k)) - 1,
          by have := hpos (Sum.inr (Sum.inr k)); omega⟩⟩ : Arc plen)) := by
  apply Finset.ext
  intro e
  obtain ⟨s', i⟩ := e
  rw [mem_minF, Finset.mem_image]
  constructor
  · intro hh
    obtain ⟨hlast, htgt⟩ := (mhead_eq_inl_iff plen hpos s' i 0).mp hh
    cases s' with
    | inl i' => simp [tgtHub] at htgt
    | inr s'' =>
        cases s'' with
        | inl j' => simp [tgtHub] at htgt
        | inr k' =>
            refine ⟨k', Finset.mem_univ k', ?_⟩
            have hi : i = (⟨plen (Sum.inr (Sum.inr k')) - 1,
              by have := hpos (Sum.inr (Sum.inr k')); omega⟩ : Fin (plen (Sum.inr (Sum.inr k')))) := by
              apply Fin.ext; simp; omega
            rw [hi]
  · rintro ⟨k', -, he⟩
    rw [← he]
    exact (mhead_eq_inl_iff plen hpos (Sum.inr (Sum.inr k'))
      ⟨plen (Sum.inr (Sum.inr k')) - 1, by have := hpos (Sum.inr (Sum.inr k')); omega⟩ 0).mpr
      ⟨by show (plen (Sum.inr (Sum.inr k')) - 1) + 1 = plen (Sum.inr (Sum.inr k'));
          have := hpos (Sum.inr (Sum.inr k')); omega, rfl⟩

/-- Out-arcs of hub `v = Sum.inl 1` are the first arcs of the `v → w` paths. -/
lemma moutF_hub_one (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s) :
    moutF plen hpos (Sum.inl (1 : Fin 3)) =
      Finset.univ.image (fun j : Fin b =>
        (⟨Sum.inr (Sum.inl j), ⟨0, by have := hpos (Sum.inr (Sum.inl j)); omega⟩⟩ : Arc plen)) := by
  apply Finset.ext
  intro e
  obtain ⟨s', i⟩ := e
  rw [mem_moutF, Finset.mem_image]
  constructor
  · intro hh
    obtain ⟨h0, hsrc⟩ := (mtail_eq_inl_iff plen hpos s' i 1).mp hh
    cases s' with
    | inl i' => simp [srcHub] at hsrc
    | inr s'' =>
        cases s'' with
        | inl j' =>
            refine ⟨j', Finset.mem_univ j', ?_⟩
            have hi : i = (⟨0, by have := hpos (Sum.inr (Sum.inl j')); omega⟩ : Fin (plen (Sum.inr (Sum.inl j')))) := by
              apply Fin.ext; simp; omega
            rw [hi]
        | inr k' => simp [srcHub] at hsrc
  · rintro ⟨j', -, he⟩
    rw [← he]
    exact (mtail_eq_inl_iff plen hpos (Sum.inr (Sum.inl j'))
      ⟨0, by have := hpos (Sum.inr (Sum.inl j')); omega⟩ 1).mpr ⟨rfl, rfl⟩

/-- In-arcs of hub `v = Sum.inl 1` are the last arcs of the `u → v` paths. -/
lemma minF_hub_one (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s) :
    minF plen hpos (Sum.inl (1 : Fin 3)) =
      Finset.univ.image (fun i : Fin a =>
        (⟨Sum.inl i, ⟨plen (Sum.inl i) - 1,
          by have := hpos (Sum.inl i); omega⟩⟩ : Arc plen)) := by
  apply Finset.ext
  intro e
  obtain ⟨s', i⟩ := e
  rw [mem_minF, Finset.mem_image]
  constructor
  · intro hh
    obtain ⟨hlast, htgt⟩ := (mhead_eq_inl_iff plen hpos s' i 1).mp hh
    cases s' with
    | inl i' =>
        refine ⟨i', Finset.mem_univ i', ?_⟩
        have hi : i = (⟨plen (Sum.inl i') - 1,
          by have := hpos (Sum.inl i'); omega⟩ : Fin (plen (Sum.inl i'))) := by
          apply Fin.ext; simp; omega
        rw [hi]
    | inr s'' =>
        cases s'' with
        | inl j' => simp [tgtHub] at htgt
        | inr k' => simp [tgtHub] at htgt
  · rintro ⟨i', -, he⟩
    rw [← he]
    exact (mhead_eq_inl_iff plen hpos (Sum.inl i')
      ⟨plen (Sum.inl i') - 1, by have := hpos (Sum.inl i'); omega⟩ 1).mpr
      ⟨by show (plen (Sum.inl i') - 1) + 1 = plen (Sum.inl i');
          have := hpos (Sum.inl i'); omega, rfl⟩

/-- Out-arcs of hub `w = Sum.inl 2` are the first arcs of the `w → u` paths. -/
lemma moutF_hub_two (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s) :
    moutF plen hpos (Sum.inl (2 : Fin 3)) =
      Finset.univ.image (fun k : Fin c =>
        (⟨Sum.inr (Sum.inr k), ⟨0, by have := hpos (Sum.inr (Sum.inr k)); omega⟩⟩ : Arc plen)) := by
  apply Finset.ext
  intro e
  obtain ⟨s', i⟩ := e
  rw [mem_moutF, Finset.mem_image]
  constructor
  · intro hh
    obtain ⟨h0, hsrc⟩ := (mtail_eq_inl_iff plen hpos s' i 2).mp hh
    cases s' with
    | inl i' => simp [srcHub] at hsrc
    | inr s'' =>
        cases s'' with
        | inl j' => simp [srcHub] at hsrc
        | inr k' =>
            refine ⟨k', Finset.mem_univ k', ?_⟩
            have hi : i = (⟨0, by have := hpos (Sum.inr (Sum.inr k')); omega⟩ : Fin (plen (Sum.inr (Sum.inr k')))) := by
              apply Fin.ext; simp; omega
            rw [hi]
  · rintro ⟨k', -, he⟩
    rw [← he]
    exact (mtail_eq_inl_iff plen hpos (Sum.inr (Sum.inr k'))
      ⟨0, by have := hpos (Sum.inr (Sum.inr k')); omega⟩ 2).mpr ⟨rfl, rfl⟩

/-- In-arcs of hub `w = Sum.inl 2` are the last arcs of the `v → w` paths. -/
lemma minF_hub_two (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s) :
    minF plen hpos (Sum.inl (2 : Fin 3)) =
      Finset.univ.image (fun j : Fin b =>
        (⟨Sum.inr (Sum.inl j), ⟨plen (Sum.inr (Sum.inl j)) - 1,
          by have := hpos (Sum.inr (Sum.inl j)); omega⟩⟩ : Arc plen)) := by
  apply Finset.ext
  intro e
  obtain ⟨s', i⟩ := e
  rw [mem_minF, Finset.mem_image]
  constructor
  · intro hh
    obtain ⟨hlast, htgt⟩ := (mhead_eq_inl_iff plen hpos s' i 2).mp hh
    cases s' with
    | inl i' => simp [tgtHub] at htgt
    | inr s'' =>
        cases s'' with
        | inl j' =>
            refine ⟨j', Finset.mem_univ j', ?_⟩
            have hi : i = (⟨plen (Sum.inr (Sum.inl j')) - 1,
              by have := hpos (Sum.inr (Sum.inl j')); omega⟩ : Fin (plen (Sum.inr (Sum.inl j')))) := by
              apply Fin.ext; simp; omega
            rw [hi]
        | inr k' => simp [tgtHub] at htgt
  · rintro ⟨j', -, he⟩
    rw [← he]
    exact (mhead_eq_inl_iff plen hpos (Sum.inr (Sum.inl j'))
      ⟨plen (Sum.inr (Sum.inl j')) - 1, by have := hpos (Sum.inr (Sum.inl j')); omega⟩ 2).mpr
      ⟨by show (plen (Sum.inr (Sum.inl j')) - 1) + 1 = plen (Sum.inr (Sum.inl j'));
          have := hpos (Sum.inr (Sum.inl j')); omega, rfl⟩

end AssemblyP1.RigidityTriHub

namespace AssemblyP1.RigidityTriHub

open Finset BigOperators

variable {a b c : ℕ}

/-- Explicit balance predicate on the triangular multi-hub graph. -/
def BalancedB (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s) (δ : Arc plen → ℤ) : Prop :=
  ∀ v ∈ mnodes plen, (∑ e ∈ moutF plen hpos v, δ e) = (∑ e ∈ minF plen hpos v, δ e)

/-- `BalancedB` is exactly the support-domain `BalancedZ`. -/
lemma balancedB_iff_balancedZ (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (δ : Arc plen → ℤ) :
    BalancedB plen hpos δ ↔
      AssemblyP1.ExactRigidityCriterion.BalancedZ (mtail plen hpos) (mhead plen hpos)
        (mnodes plen) (medges plen) δ :=
  Iff.rfl

/-- The balance equation at an internal vertex `(s, r)` forces the two adjacent
path arcs to carry equal values. -/
lemma balanced_step (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (δ : Arc plen → ℤ) (hbal : BalancedB plen hpos δ)
    (s : PIdx a b c) (m : ℕ) (hm : m + 1 < plen s) :
    δ ⟨s, ⟨m + 1, hm⟩⟩ = δ ⟨s, ⟨m, by omega⟩⟩ := by
  have h := hbal (Sum.inr ⟨s, ⟨m, by omega⟩⟩) (Finset.mem_univ _)
  rw [moutF_internal, minF_internal] at h
  simpa using h

/-- Path constancy: a balanced arc function is constant on every path. -/
lemma path_const (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (δ : Arc plen → ℤ) (hbal : BalancedB plen hpos δ)
    (s : PIdx a b c) (i : Fin (plen s)) :
    δ ⟨s, i⟩ = δ ⟨s, ⟨0, by have := hpos s; omega⟩⟩ := by
  have key : ∀ m (hm : m < plen s),
      δ ⟨s, ⟨m, hm⟩⟩ = δ ⟨s, ⟨0, by have := hpos s; omega⟩⟩ := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
        intro hm
        have hstep : δ ⟨s, ⟨m + 1, hm⟩⟩ = δ ⟨s, ⟨m, by omega⟩⟩ :=
          balanced_step plen hpos δ hbal s m (by omega)
        rw [hstep]
        exact ih (by omega)
  exact key i.val i.isLt

end AssemblyP1.RigidityTriHub

namespace AssemblyP1.RigidityTriHub

open Finset BigOperators

variable {a b c : ℕ}

/-- Sum over the out-arcs of hub `u`, reindexed by the `u → v` paths. -/
lemma sum_moutF_hub_zero (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (g : Arc plen → ℤ) :
    (∑ e ∈ moutF plen hpos (Sum.inl (0 : Fin 3)), g e)
      = ∑ i : Fin a, g ⟨Sum.inl i, ⟨0, by have := hpos (Sum.inl i); omega⟩⟩ := by
  rw [moutF_hub_zero, Finset.sum_image]
  intro x _ y _ hxy
  exact Sum.inl.inj (α := Fin a) (β := Fin b ⊕ Fin c) (by simpa using congrArg (fun e : Arc plen => e.1) hxy)

/-- Sum over the in-arcs of hub `u`, reindexed by the `w → u` paths. -/
lemma sum_minF_hub_zero (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (g : Arc plen → ℤ) :
    (∑ e ∈ minF plen hpos (Sum.inl (0 : Fin 3)), g e)
      = ∑ k : Fin c, g ⟨Sum.inr (Sum.inr k), ⟨plen (Sum.inr (Sum.inr k)) - 1,
        by have := hpos (Sum.inr (Sum.inr k)); omega⟩⟩ := by
  rw [minF_hub_zero, Finset.sum_image]
  intro x _ y _ hxy
  exact Sum.inr.inj (α := Fin b) (β := Fin c)
    (Sum.inr.inj (α := Fin a) (β := Fin b ⊕ Fin c)
      (by simpa using congrArg (fun e : Arc plen => e.1) hxy))

/-- Sum over the out-arcs of hub `v`, reindexed by the `v → w` paths. -/
lemma sum_moutF_hub_one (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (g : Arc plen → ℤ) :
    (∑ e ∈ moutF plen hpos (Sum.inl (1 : Fin 3)), g e)
      = ∑ j : Fin b, g ⟨Sum.inr (Sum.inl j), ⟨0, by have := hpos (Sum.inr (Sum.inl j)); omega⟩⟩ := by
  rw [moutF_hub_one, Finset.sum_image]
  intro x _ y _ hxy
  exact Sum.inl.inj (α := Fin b) (β := Fin c)
    (Sum.inr.inj (α := Fin a) (β := Fin b ⊕ Fin c)
      (by simpa using congrArg (fun e : Arc plen => e.1) hxy))

/-- Sum over the in-arcs of hub `v`, reindexed by the `u → v` paths. -/
lemma sum_minF_hub_one (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (g : Arc plen → ℤ) :
    (∑ e ∈ minF plen hpos (Sum.inl (1 : Fin 3)), g e)
      = ∑ i : Fin a, g ⟨Sum.inl i, ⟨plen (Sum.inl i) - 1,
        by have := hpos (Sum.inl i); omega⟩⟩ := by
  rw [minF_hub_one, Finset.sum_image]
  intro x _ y _ hxy
  exact Sum.inl.inj (α := Fin a) (β := Fin b ⊕ Fin c) (by simpa using congrArg (fun e : Arc plen => e.1) hxy)

/-- Sum over the out-arcs of hub `w`, reindexed by the `w → u` paths. -/
lemma sum_moutF_hub_two (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (g : Arc plen → ℤ) :
    (∑ e ∈ moutF plen hpos (Sum.inl (2 : Fin 3)), g e)
      = ∑ k : Fin c, g ⟨Sum.inr (Sum.inr k), ⟨0, by have := hpos (Sum.inr (Sum.inr k)); omega⟩⟩ := by
  rw [moutF_hub_two, Finset.sum_image]
  intro x _ y _ hxy
  exact Sum.inr.inj (α := Fin b) (β := Fin c)
    (Sum.inr.inj (α := Fin a) (β := Fin b ⊕ Fin c)
      (by simpa using congrArg (fun e : Arc plen => e.1) hxy))

/-- Sum over the in-arcs of hub `w`, reindexed by the `v → w` paths. -/
lemma sum_minF_hub_two (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (g : Arc plen → ℤ) :
    (∑ e ∈ minF plen hpos (Sum.inl (2 : Fin 3)), g e)
      = ∑ j : Fin b, g ⟨Sum.inr (Sum.inl j), ⟨plen (Sum.inr (Sum.inl j)) - 1,
        by have := hpos (Sum.inr (Sum.inl j)); omega⟩⟩ := by
  rw [minF_hub_two, Finset.sum_image]
  intro x _ y _ hxy
  exact Sum.inl.inj (α := Fin b) (β := Fin c)
    (Sum.inr.inj (α := Fin a) (β := Fin b ⊕ Fin c)
      (by simpa using congrArg (fun e : Arc plen => e.1) hxy))

/-- Every balanced arc function is the path-constant function `φ` of its values
on the first arc of each path, and those values satisfy the two hub-balance
equations. -/
lemma phi_of_balanced (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (δ : Arc plen → ℤ) (hbal : BalancedB plen hpos δ) :
    δ = phi plen (fun s => δ ⟨s, ⟨0, by have := hpos s; omega⟩⟩) ∧
      (∑ i : Fin a, δ ⟨Sum.inl i, ⟨0, by have := hpos (Sum.inl i); omega⟩⟩)
        = ∑ j : Fin b, δ ⟨Sum.inr (Sum.inl j), ⟨0, by have := hpos (Sum.inr (Sum.inl j)); omega⟩⟩ ∧
      (∑ j : Fin b, δ ⟨Sum.inr (Sum.inl j), ⟨0, by have := hpos (Sum.inr (Sum.inl j)); omega⟩⟩)
        = ∑ k : Fin c, δ ⟨Sum.inr (Sum.inr k), ⟨0, by have := hpos (Sum.inr (Sum.inr k)); omega⟩⟩ := by
  have hphi : δ = phi plen (fun s => δ ⟨s, ⟨0, by have := hpos s; omega⟩⟩) := by
    funext x
    obtain ⟨s, i⟩ := x
    simp only [phi_mk]
    exact path_const plen hpos δ hbal s i
  have hab : (∑ i : Fin a, δ ⟨Sum.inl i, ⟨0, by have := hpos (Sum.inl i); omega⟩⟩)
        = ∑ j : Fin b, δ ⟨Sum.inr (Sum.inl j), ⟨0, by have := hpos (Sum.inr (Sum.inl j)); omega⟩⟩ := by
    have h0 := hbal (Sum.inl (1 : Fin 3)) (Finset.mem_univ _)
    rw [sum_moutF_hub_one, sum_minF_hub_one] at h0
    have hconst : ∀ i : Fin a,
        δ ⟨Sum.inl i, ⟨plen (Sum.inl i) - 1, by have := hpos (Sum.inl i); omega⟩⟩
          = δ ⟨Sum.inl i, ⟨0, by have := hpos (Sum.inl i); omega⟩⟩ := by
      intro i
      exact path_const plen hpos δ hbal (Sum.inl i)
        ⟨plen (Sum.inl i) - 1, by have := hpos (Sum.inl i); omega⟩
    rw [Finset.sum_congr rfl (fun i _ => hconst i)] at h0
    simpa using h0.symm
  have hbc : (∑ j : Fin b, δ ⟨Sum.inr (Sum.inl j), ⟨0, by have := hpos (Sum.inr (Sum.inl j)); omega⟩⟩)
        = ∑ k : Fin c, δ ⟨Sum.inr (Sum.inr k), ⟨0, by have := hpos (Sum.inr (Sum.inr k)); omega⟩⟩ := by
    have h0 := hbal (Sum.inl (2 : Fin 3)) (Finset.mem_univ _)
    rw [sum_moutF_hub_two, sum_minF_hub_two] at h0
    have hconst : ∀ j : Fin b,
        δ ⟨Sum.inr (Sum.inl j), ⟨plen (Sum.inr (Sum.inl j)) - 1,
          by have := hpos (Sum.inr (Sum.inl j)); omega⟩⟩
          = δ ⟨Sum.inr (Sum.inl j), ⟨0, by have := hpos (Sum.inr (Sum.inl j)); omega⟩⟩ := by
      intro j
      exact path_const plen hpos δ hbal (Sum.inr (Sum.inl j))
        ⟨plen (Sum.inr (Sum.inl j)) - 1, by have := hpos (Sum.inr (Sum.inl j)); omega⟩
    rw [Finset.sum_congr rfl (fun j _ => hconst j)] at h0
    simpa using h0.symm
  have hca : (∑ k : Fin c, δ ⟨Sum.inr (Sum.inr k), ⟨0, by have := hpos (Sum.inr (Sum.inr k)); omega⟩⟩)
        = ∑ i : Fin a, δ ⟨Sum.inl i, ⟨0, by have := hpos (Sum.inl i); omega⟩⟩ := by
    have h0 := hbal (Sum.inl (0 : Fin 3)) (Finset.mem_univ _)
    rw [sum_moutF_hub_zero, sum_minF_hub_zero] at h0
    have hconst : ∀ k : Fin c,
        δ ⟨Sum.inr (Sum.inr k), ⟨plen (Sum.inr (Sum.inr k)) - 1,
          by have := hpos (Sum.inr (Sum.inr k)); omega⟩⟩
          = δ ⟨Sum.inr (Sum.inr k), ⟨0, by have := hpos (Sum.inr (Sum.inr k)); omega⟩⟩ := by
      intro k
      exact path_const plen hpos δ hbal (Sum.inr (Sum.inr k))
        ⟨plen (Sum.inr (Sum.inr k)) - 1, by have := hpos (Sum.inr (Sum.inr k)); omega⟩
    rw [Finset.sum_congr rfl (fun k _ => hconst k)] at h0
    simpa using h0.symm
  exact ⟨hphi, hab, hbc⟩

/-- Conversely, a path-constant function with hub balance is balanced. -/
lemma balanced_of_phi (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (q : PIdx a b c → ℤ)
    (hab : (∑ i : Fin a, q (Sum.inl i))
        = ∑ j : Fin b, q (Sum.inr (Sum.inl j)))
    (hbc : (∑ j : Fin b, q (Sum.inr (Sum.inl j)))
        = ∑ k : Fin c, q (Sum.inr (Sum.inr k))) :
    BalancedB plen hpos (phi plen q) := by
  intro v _
  rcases v with h | h
  · fin_cases h
    · change (∑ e ∈ moutF plen hpos (Sum.inl (0 : Fin 3)), phi plen q e) =
        (∑ e ∈ minF plen hpos (Sum.inl (0 : Fin 3)), phi plen q e)
      rw [sum_moutF_hub_zero, sum_minF_hub_zero]
      simp only [phi_mk]
      exact hab.trans hbc
    · change (∑ e ∈ moutF plen hpos (Sum.inl (1 : Fin 3)), phi plen q e) =
        (∑ e ∈ minF plen hpos (Sum.inl (1 : Fin 3)), phi plen q e)
      rw [sum_moutF_hub_one, sum_minF_hub_one]
      simp only [phi_mk]
      exact hab.symm
    · change (∑ e ∈ moutF plen hpos (Sum.inl (2 : Fin 3)), phi plen q e) =
        (∑ e ∈ minF plen hpos (Sum.inl (2 : Fin 3)), phi plen q e)
      rw [sum_moutF_hub_two, sum_minF_hub_two]
      simp only [phi_mk]
      exact hbc.symm
  · obtain ⟨s, r⟩ := h
    rw [moutF_internal, minF_internal]
    simp [phi_mk]

end AssemblyP1.RigidityTriHub

namespace AssemblyP1.RigidityTriHub

open Finset BigOperators

variable {a b c : ℕ}

/-- Total mass of a path-constant arc function. -/
lemma phi_sum (plen : PIdx a b c → ℕ) (q : PIdx a b c → ℤ) :
    ∑ x : Arc plen, phi plen q x = ∑ s, (plen s : ℤ) * q s := by
  rw [Fintype.sum_sigma]
  simp only [phi_mk, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `mA` is the path-constant function of the multiplicities. -/
lemma mA_eq_phi (plen : PIdx a b c → ℕ) (m : PIdx a b c → ℕ) :
    mA plen m = phi plen (fun s => (m s : ℤ)) := rfl

/-- Total mass of the base circulation. -/
lemma mA_total (plen : PIdx a b c → ℕ) (m : PIdx a b c → ℕ) :
    ∑ x : Arc plen, mA plen m x = (mG plen m : ℤ) := by
  rw [mA_eq_phi, phi_sum, mG, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Nat.cast_mul]

/-- The base circulation is balanced provided the two hub-balance equations hold. -/
lemma mA_balanced (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (m : PIdx a b c → ℕ)
    (hab : (∑ i : Fin a, m (Sum.inl i)) = ∑ j : Fin b, m (Sum.inr (Sum.inl j)))
    (hbc : (∑ j : Fin b, m (Sum.inr (Sum.inl j))) = ∑ k : Fin c, m (Sum.inr (Sum.inr k))) :
    BalancedB plen hpos (mA plen m) := by
  rw [mA_eq_phi]
  apply balanced_of_phi
  · exact_mod_cast hab
  · exact_mod_cast hbc

/-- **The triangular multi-hub exact rigidity criterion.** For a triangular
multi-hub support with `a` `u → v` paths, `b` `v → w` paths and `c` `w → u` paths
of lengths `plen ≥ 1` and multiplicities `m ≥ 1` with
`∑ m(u→v) = ∑ m(v→w) = ∑ m(w→u)`, the base circulation is non-rigid **iff** there
is a nonzero integer path-perturbation `(α, β, γ)` with hub balance, zero total
mass, and the boxes. -/
theorem triHub_nonrigid_iff (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (m : PIdx a b c → ℕ) (hm : ∀ s, 1 ≤ m s)
    (hab : (∑ i : Fin a, m (Sum.inl i)) = ∑ j : Fin b, m (Sum.inr (Sum.inl j)))
    (hbc : (∑ j : Fin b, m (Sum.inr (Sum.inl j))) = ∑ k : Fin c, m (Sum.inr (Sum.inr k))) :
    (¬ AssemblyP1.ExactRigidityCriterion.Rigid (mtail plen hpos) (mhead plen hpos)
        (mnodes plen) (medges plen) (mA plen m) (mG plen m)) ↔
      ∃ α : Fin a → ℤ, ∃ β : Fin b → ℤ, ∃ γ : Fin c → ℤ,
        ((∃ i, α i ≠ 0) ∨ (∃ j, β j ≠ 0) ∨ (∃ k, γ k ≠ 0)) ∧
        ((∑ i : Fin a, α i = ∑ j : Fin b, β j) ∧
         (∑ j : Fin b, β j = ∑ k : Fin c, γ k)) ∧
        (∑ i : Fin a, (plen (Sum.inl i) : ℤ) * α i
           + ∑ j : Fin b, (plen (Sum.inr (Sum.inl j)) : ℤ) * β j
           + ∑ k : Fin c, (plen (Sum.inr (Sum.inr k)) : ℤ) * γ k = 0) ∧
        ((∀ i, 1 - (m (Sum.inl i) : ℤ) ≤ α i) ∧
         (∀ j, 1 - (m (Sum.inr (Sum.inl j)) : ℤ) ≤ β j) ∧
         (∀ k, 1 - (m (Sum.inr (Sum.inr k)) : ℤ) ≤ γ k)) := by
  have hAbal : AssemblyP1.ExactRigidityCriterion.BalancedZ (mtail plen hpos)
      (mhead plen hpos) (mnodes plen) (medges plen) (mA plen m) :=
    (balancedB_iff_balancedZ plen hpos (mA plen m)).mp (mA_balanced plen hpos m hab hbc)
  rw [AssemblyP1.ExactRigidityCriterion.nonrigid_iff_exists_delta (mtail plen hpos)
      (mhead plen hpos) (mnodes plen) (medges plen) (mA plen m) (mG plen m) hAbal
      (by simpa [medges] using mA_total plen m)]
  constructor
  · rintro ⟨δ, hne, hδbal, hδsum, hδbox⟩
    have hδbalB : BalancedB plen hpos δ :=
      (balancedB_iff_balancedZ plen hpos δ).mpr hδbal
    obtain ⟨hphi, hab', hbc'⟩ := phi_of_balanced plen hpos δ hδbalB
    refine ⟨fun i => δ ⟨Sum.inl i, ⟨0, by have := hpos (Sum.inl i); omega⟩⟩,
      fun j => δ ⟨Sum.inr (Sum.inl j), ⟨0, by have := hpos (Sum.inr (Sum.inl j)); omega⟩⟩,
      fun k => δ ⟨Sum.inr (Sum.inr k), ⟨0, by have := hpos (Sum.inr (Sum.inr k)); omega⟩⟩,
      ?_, ⟨hab', hbc'⟩, ?_, ?_⟩
    · obtain ⟨⟨s, i⟩, _, hde⟩ := hne
      rcases s with i' | s''
      · left; exact ⟨i', by intro h0; apply hde; rw [hphi, phi_mk]; exact h0⟩
      · cases s'' with
        | inl j' => right; left; exact ⟨j', by intro h0; apply hde; rw [hphi, phi_mk]; exact h0⟩
        | inr k' => right; right; exact ⟨k', by intro h0; apply hde; rw [hphi, phi_mk]; exact h0⟩
    · rw [AssemblyP1.ExactRigidityCriterion.ZeroSum] at hδsum
      simp only [medges] at hδsum
      rw [hphi, phi_sum] at hδsum
      -- convert the sigma sum to the three-group sum
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at hδsum
      rw [add_assoc]
      exact hδsum
    · refine ⟨?_, ?_, ?_⟩
      · intro i
        have := hδbox ⟨Sum.inl i, ⟨0, by have := hpos (Sum.inl i); omega⟩⟩ (Finset.mem_univ _)
        simpa [mA_mk] using this
      · intro j
        have := hδbox ⟨Sum.inr (Sum.inl j), ⟨0, by have := hpos (Sum.inr (Sum.inl j)); omega⟩⟩ (Finset.mem_univ _)
        simpa [mA_mk] using this
      · intro k
        have := hδbox ⟨Sum.inr (Sum.inr k), ⟨0, by have := hpos (Sum.inr (Sum.inr k)); omega⟩⟩ (Finset.mem_univ _)
        simpa [mA_mk] using this
  · rintro ⟨α, β, γ, hne, ⟨hab', hbc'⟩, hsum, ⟨hboxa, hboxb, hboxc⟩⟩
    refine ⟨phi plen (Sum.elim α (Sum.elim β γ)), ?_, ?_, ?_, ?_⟩
    · obtain hne' : (∃ s : PIdx a b c, Sum.elim α (Sum.elim β γ) s ≠ 0) := by
        rcases hne with h | h
        · rcases h with ⟨i, hi⟩; exact ⟨Sum.inl i, hi⟩
        · rcases h with h | h
          · rcases h with ⟨j, hj⟩; exact ⟨Sum.inr (Sum.inl j), hj⟩
          · rcases h with ⟨k, hk⟩; exact ⟨Sum.inr (Sum.inr k), hk⟩
      obtain ⟨s, hs⟩ := hne'
      exact ⟨⟨s, ⟨0, by have := hpos s; omega⟩⟩, Finset.mem_univ _, by simpa [phi_mk] using hs⟩
    · exact (balancedB_iff_balancedZ plen hpos _).mp (balanced_of_phi plen hpos _ hab' hbc')
    · rw [AssemblyP1.ExactRigidityCriterion.ZeroSum]
      have h : ∑ e ∈ medges plen, phi plen (Sum.elim α (Sum.elim β γ)) e
          = ∑ s, (plen s : ℤ) * Sum.elim α (Sum.elim β γ) s := by
        rw [medges]; exact phi_sum plen _
      rw [h, Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [← add_assoc]
      exact hsum
    · intro e _
      obtain ⟨s, i⟩ := e
      rcases s with i' | s''
      · simpa [mA_mk, phi_mk] using hboxa i'
      · cases s'' with
        | inl j' => simpa [mA_mk, phi_mk] using hboxb j'
        | inr k' => simpa [mA_mk, phi_mk] using hboxc k'

end AssemblyP1.RigidityTriHub

namespace AssemblyP1.RigidityTriHub

open Finset BigOperators

variable {a b c : ℕ}

/-- The rigidity predicate of the triangular multi-hub support at multiplicity `m`. -/
abbrev TRigid (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s) (m : PIdx a b c → ℕ) : Prop :=
  AssemblyP1.ExactRigidityCriterion.Rigid (mtail plen hpos) (mhead plen hpos)
    (mnodes plen) (medges plen) (mA plen m) (mG plen m)

/-- The three-group weighted sum equals the sigma sum over all paths. -/
lemma sum_elim_three (plen : PIdx a b c → ℕ) (α : Fin a → ℤ) (β : Fin b → ℤ) (γ : Fin c → ℤ) :
    (∑ i : Fin a, (plen (Sum.inl i) : ℤ) * α i
      + ∑ j : Fin b, (plen (Sum.inr (Sum.inl j)) : ℤ) * β j
      + ∑ k : Fin c, (plen (Sum.inr (Sum.inr k)) : ℤ) * γ k)
    = ∑ s : PIdx a b c, (plen s : ℤ) * Sum.elim α (Sum.elim β γ) s := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, add_assoc]
  simp only [Sum.elim_inl, Sum.elim_inr]

/-- **All multiplicities `1` is rigid.** With unit slack the box forces the
perturbation to be nonnegative, and the zero-mass equation with positive path
lengths forces it to be zero. -/
theorem triHub_rigid_all_one (plen : PIdx a b c → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (hab : (∑ i : Fin a, (1 : ℕ)) = ∑ j : Fin b, (1 : ℕ))
    (hbc : (∑ j : Fin b, (1 : ℕ)) = ∑ k : Fin c, (1 : ℕ)) :
    TRigid plen hpos (fun _ => 1) := by
  by_contra h
  rw [triHub_nonrigid_iff plen hpos (fun _ => 1) (fun _ => le_refl 1) hab hbc] at h
  obtain ⟨α, β, γ, hne, -, hsum, ⟨ha, hb, hc⟩⟩ := h
  have hnonneg : ∀ s : PIdx a b c,
      0 ≤ Sum.elim α (Sum.elim β γ) s := by
    intro s
    rcases s with i | s''
    · simpa using ha i
    · cases s'' with
      | inl j => simpa using hb j
      | inr k => simpa using hc k
  have hnonneg' : ∀ s ∈ (Finset.univ : Finset (PIdx a b c)),
      0 ≤ (plen s : ℤ) * Sum.elim α (Sum.elim β γ) s := by
    intro s _
    rcases s with i | s''
    · exact mul_nonneg (by have := hpos (Sum.inl i); omega) (hnonneg (Sum.inl i))
    · cases s'' with
      | inl j => exact mul_nonneg (by have := hpos (Sum.inr (Sum.inl j)); omega) (hnonneg (Sum.inr (Sum.inl j)))
      | inr k => exact mul_nonneg (by have := hpos (Sum.inr (Sum.inr k)); omega) (hnonneg (Sum.inr (Sum.inr k)))
  have hzero : ∀ s : PIdx a b c, Sum.elim α (Sum.elim β γ) s = 0 := by
    intro s
    have hterm := hnonneg' s (Finset.mem_univ s)
    have hsumeq : ∑ t, (plen t : ℤ) * Sum.elim α (Sum.elim β γ) t = 0 := by
      rw [← sum_elim_three]; exact hsum
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg').mp hsumeq s (Finset.mem_univ s)
    have hp : (0 : ℤ) < (plen s : ℤ) := by have := hpos s; omega
    exact (mul_eq_zero.mp hall).resolve_left (ne_of_gt hp)
  rcases hne with h | h
  · rcases h with ⟨i, hi⟩; exact hi (hzero (Sum.inl i))
  · rcases h with h | h
    · rcases h with ⟨j, hj⟩; exact hj (hzero (Sum.inr (Sum.inl j)))
    · rcases h with ⟨k, hk⟩; exact hk (hzero (Sum.inr (Sum.inr k)))

/-! ## Concrete instances -/

/-- The `2`-path-each-way instance with lengths `(1,3)` and multiplicities `(2,1)`
on each side. -/
def p3 : PIdx 2 2 2 → ℕ := Sum.elim ![1, 3] (Sum.elim ![1, 3] ![1, 3])

/-- The multiplicities of `p3`. -/
def m3 : PIdx 2 2 2 → ℕ := Sum.elim ![2, 1] (Sum.elim ![2, 1] ![2, 1])

lemma p3_pos : ∀ s, 1 ≤ p3 s := by
  intro s; rcases s with i | s''
  · fin_cases i <;> decide
  · cases s'' with
    | inl j => fin_cases j <;> decide
    | inr k => fin_cases k <;> decide

lemma m3_pos : ∀ s, 1 ≤ m3 s := by
  intro s; rcases s with i | s''
  · fin_cases i <;> decide
  · cases s'' with
    | inl j => fin_cases j <;> decide
    | inr k => fin_cases k <;> decide

lemma m3_bal_ab : (∑ i : Fin 2, m3 (Sum.inl i)) = ∑ j : Fin 2, m3 (Sum.inr (Sum.inl j)) := by
  decide

lemma m3_bal_bc : (∑ j : Fin 2, m3 (Sum.inr (Sum.inl j))) = ∑ k : Fin 2, m3 (Sum.inr (Sum.inr k)) := by
  decide

/-- **Rigid repetitive instance.** At `p3` with multiplicities `m3` the length-`1`
path of each direction is traversed twice, yet the instance is rigid. So no `m ≥ 2`
repeat bound is necessary for non-rigidity in this family. -/
theorem triHub_rigid_repetitive : TRigid p3 p3_pos m3 := by
  by_contra h
  rw [triHub_nonrigid_iff p3 p3_pos m3 m3_pos m3_bal_ab m3_bal_bc] at h
  obtain ⟨α, β, γ, hne, ⟨hab', hbc'⟩, hsum, ⟨ha, hb, hc⟩⟩ := h
  have hab'' : α 0 + α 1 = β 0 + β 1 := by simpa [Fin.sum_univ_two] using hab'
  have hbc'' : β 0 + β 1 = γ 0 + γ 1 := by simpa [Fin.sum_univ_two] using hbc'
  have hsum' : (1:ℤ) * α 0 + 3 * α 1 + 1 * β 0 + 3 * β 1 + 1 * γ 0 + 3 * γ 1 = 0 := by
    have hh := hsum
    simp only [Fin.sum_univ_two, p3, Sum.elim_inl, Sum.elim_inr] at hh
    norm_num at hh
    linarith [hh]
  have k0 : (1:ℤ) - 2 ≤ α 0 := by
    have h := ha 0; simp only [m3, Sum.elim_inl] at h; norm_num at h; exact h
  have k1 : (1:ℤ) - 1 ≤ α 1 := by
    have h := ha 1; simp only [m3, Sum.elim_inl] at h; norm_num at h; exact h
  have k2 : (1:ℤ) - 2 ≤ β 0 := by
    have h := hb 0; simp only [m3, Sum.elim_inr, Sum.elim_inl] at h; norm_num at h; exact h
  have k3 : (1:ℤ) - 1 ≤ β 1 := by
    have h := hb 1; simp only [m3, Sum.elim_inr, Sum.elim_inl] at h; norm_num at h; exact h
  have k4 : (1:ℤ) - 2 ≤ γ 0 := by
    have h := hc 0; simp only [m3, Sum.elim_inr, Sum.elim_inr] at h; norm_num at h; exact h
  have k5 : (1:ℤ) - 1 ≤ γ 1 := by
    have h := hc 1; simp only [m3, Sum.elim_inr, Sum.elim_inr] at h; norm_num at h; exact h
  have e0 : α 0 = 0 := by omega
  have e1 : α 1 = 0 := by omega
  have e2 : β 0 = 0 := by omega
  have e3 : β 1 = 0 := by omega
  have e4 : γ 0 = 0 := by omega
  have e5 : γ 1 = 0 := by omega
  rcases hne with h | h
  · rcases h with ⟨i, hi⟩; fin_cases i <;> simp_all [e0, e1]
  · rcases h with h | h
    · rcases h with ⟨j, hj⟩; fin_cases j <;> simp_all [e2, e3]
    · rcases h with ⟨k, hk⟩; fin_cases k <;> simp_all [e4, e5]

/-- The **relaxed** triangular multi-hub predicate: the exact criterion with the
hub-balance equations dropped (the naive independent-per-path / bouquet-style
relaxation). -/
def RelaxedTH (plen : PIdx a b c → ℕ) (m : PIdx a b c → ℕ) : Prop :=
  ∃ α : Fin a → ℤ, ∃ β : Fin b → ℤ, ∃ γ : Fin c → ℤ,
    ((∃ i, α i ≠ 0) ∨ (∃ j, β j ≠ 0) ∨ (∃ k, γ k ≠ 0)) ∧
    (∑ i : Fin a, (plen (Sum.inl i) : ℤ) * α i
       + ∑ j : Fin b, (plen (Sum.inr (Sum.inl j)) : ℤ) * β j
       + ∑ k : Fin c, (plen (Sum.inr (Sum.inr k)) : ℤ) * γ k = 0) ∧
    ((∀ i, 1 - (m (Sum.inl i) : ℤ) ≤ α i) ∧
     (∀ j, 1 - (m (Sum.inr (Sum.inl j)) : ℤ) ≤ β j) ∧
     (∀ k, 1 - (m (Sum.inr (Sum.inr k)) : ℤ) ≤ γ k))

/-- **The coupling equations are essential (failed simpler hypothesis).** At
`p3`, multiplicities `m3`, the relaxed predicate holds with witness
`(α, β, γ) = ((-1, 0), (1, 0), (0, 0))` while the instance is rigid. So the
hub-balance coupling cannot be dropped: no independent-per-path / single-cut
criterion decides the triangular multi-hub family. -/
theorem triHub_relaxed_not_sound : RelaxedTH p3 m3 ∧ TRigid p3 p3_pos m3 := by
  refine ⟨?_, triHub_rigid_repetitive⟩
  refine ⟨fun i : Fin 2 => if i = 0 then (-1 : ℤ) else 0,
    fun j : Fin 2 => if j = 0 then (1 : ℤ) else 0,
    fun _ => 0, ?_, ?_, ?_⟩
  · left; exact ⟨0, by simp⟩
  · simp only [Fin.sum_univ_two, p3, Sum.elim_inl, Sum.elim_inr, Fin.isValue,
      Fin.reduceFinMk]
    norm_num
  · refine ⟨?_, ?_, ?_⟩
    · intro i; fin_cases i <;> simp [m3, Sum.elim_inl]
    · intro j; fin_cases j <;> simp [m3, Sum.elim_inr, Sum.elim_inl]
    · intro k; fin_cases k <;> simp [m3, Sum.elim_inr, Sum.elim_inr]

end AssemblyP1.RigidityTriHub
