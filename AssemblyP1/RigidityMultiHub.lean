import AssemblyP1.ExactRigidityCriterion

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The multi-hub family: an unbounded-cycle-rank family with a polynomial
# rigidity criterion (issue #257, §8.1/§8.2)

This module advances open items **§8.1** (a closed-form / polynomial criterion
for rigidity beyond bounded cycle rank) and **§8.2** (the exact complexity) of
`docs/source-notes/issue-257-rigid-read-graphs.md`. It imports only
`AssemblyP1.ExactRigidityCriterion` (Theorem 1) and is **not** a re-proof of any
merged front (finite decider, Graver, two-walk, bouquet, antiparallel bridge,
length-3 / general `p,q` bridge, double theta, coin/LP no-go).

## The topology

The *multi-hub* family joins two hubs `u, v` by `k` internally vertex-disjoint
`u → v` paths and `l` internally vertex-disjoint `v → u` paths, of **arbitrary
lengths** `plen ≥ 1`. It has cycle rank `k + l - 1`, which is **unbounded**, so
this family is strictly larger than the bounded-cycle-rank families for which a
polynomial criterion was previously known. The bouquet (`k = l = 1`) and the
double theta / general two-hub (`k = l = 2`) are special cases.

Internal vertices have in- and out-degree `1`, so every circulation is constant
on each path; writing `α` for the path value on each path, the two hubs give the
single independent *hub-balance* equation `∑_{u→v} α = ∑_{v→u} α`, and the total
mass is `∑ plen · α`.

## Main results

* `phi_of_balanced` / `balanced_of_phi`: a balanced integral circulation is
  exactly a path-constant function whose path values satisfy the hub balance.
* `multiHub_nonrigid_iff`: the **exact criterion** — the base circulation is
  non-rigid **iff** there is a nonzero integer path-perturbation `α` with hub
  balance, zero total mass `∑ plen · α = 0`, and the box `α ≥ 1 - m`.
* `multiHub_rigid_all_one`: all multiplicities `1` is rigid.
* `multiHub_rigid_repetitive_2`: a **rigid repetitive** instance (`p2`, `m2`):
  the length-`1` path of each direction is traversed twice, yet the support is
  rigid.
* `multiHub_relaxed_not_sound`: the naive independent-per-path (bouquet-style /
  single-cut) relaxation obtained by dropping the hub-balance equation is **not
  sound** — a committed counterexample to a tempting simpler hypothesis.

## §8.2 complexity (documented, cross-checked)

The criterion is a **two-equation** nonnegative-integer uniqueness problem
(`∑ u - ∑ v = l - k`, `∑ plen · u + ∑ plen · v = C`). Because the path lengths
are encoded in unary (an explicit support), this is decidable by a polynomial
dynamic program in the input size, counting solutions up to `2`; the companion
script `scripts/verify_257_multi_hub.py` implements this DP and cross-checks it
against from-scratch enumeration. The general-support case (arbitrary cycle
rank) and any min-cut/max-flow closed form for it remain **OPEN** (§8.1/§8.2).
-/

namespace AssemblyP1.RigidityMultiHub

open Finset BigOperators

/-- Path index: `Sum.inl i` is the `i`-th `u → v` path, `Sum.inr j` the
`j`-th `v → u` path. -/
abbrev PIdx (k l : ℕ) : Type := Fin k ⊕ Fin l

variable {k l : ℕ}

/-- Source hub of a path: `u = 0` for a `u → v` path, `v = 1` for a `v → u`
path. -/
def srcHub : PIdx k l → Fin 2
  | Sum.inl _ => 0
  | Sum.inr _ => 1

/-- Target hub of a path. -/
def tgtHub : PIdx k l → Fin 2
  | Sum.inl _ => 1
  | Sum.inr _ => 0

/-- Vertices: the two hubs, plus the internal vertex of every path. A path of
length `plen s` has `plen s - 1` internal vertices. -/
abbrev Vtx (plen : PIdx k l → ℕ) : Type := Fin 2 ⊕ (Σ s : PIdx k l, Fin (plen s - 1))

/-- Arcs: for every path `s` of length `plen s`, arcs indexed `0 … plen s - 1`. -/
abbrev Arc (plen : PIdx k l → ℕ) : Type := Σ s : PIdx k l, Fin (plen s)

/-- Tail of an arc `(s, i)`: the source hub when `i = 0`, otherwise the
internal vertex `(s, i-1)`. -/
def mtail (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s) : Arc plen → Vtx plen
  | ⟨s, i⟩ =>
    if h : i.val = 0 then Sum.inl (srcHub s)
    else Sum.inr ⟨s, ⟨i.val - 1, by have := i.isLt; have := hpos s; omega⟩⟩

/-- Head of an arc `(s, i)`: the target hub on the last arc of a path,
otherwise the internal vertex `(s, i)`. -/
def mhead (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s) : Arc plen → Vtx plen
  | ⟨s, i⟩ =>
    if h : i.val + 1 = plen s then Sum.inl (tgtHub s)
    else Sum.inr ⟨s, ⟨i.val, by have := i.isLt; omega⟩⟩

@[simp] lemma mtail_mk (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (s : PIdx k l) (i : Fin (plen s)) :
    mtail plen hpos ⟨s, i⟩ =
      (if h : i.val = 0 then Sum.inl (srcHub s)
       else Sum.inr ⟨s, ⟨i.val - 1, by have := i.isLt; have := hpos s; omega⟩⟩) := rfl

@[simp] lemma mhead_mk (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (s : PIdx k l) (i : Fin (plen s)) :
    mhead plen hpos ⟨s, i⟩ =
      (if h : i.val + 1 = plen s then Sum.inl (tgtHub s)
       else Sum.inr ⟨s, ⟨i.val, by have := i.isLt; omega⟩⟩) := rfl

/-- The all-vertices node set. -/
def mnodes (plen : PIdx k l → ℕ) : Finset (Vtx plen) := Finset.univ

/-- The all-arcs support. -/
def medges (plen : PIdx k l → ℕ) : Finset (Arc plen) := Finset.univ

/-- The path-constant arc function `φ(c)`: every arc of path `s` carries `c s`. -/
def phi (plen : PIdx k l → ℕ) (c : PIdx k l → ℤ) : Arc plen → ℤ := fun a => c a.1

/-- The base circulation: every arc of path `s` carries multiplicity `m s`. -/
def mA (plen : PIdx k l → ℕ) (m : PIdx k l → ℕ) : Arc plen → ℤ := fun a => (m a.1 : ℤ)

/-- Total mass of the base circulation. -/
def mG (plen : PIdx k l → ℕ) (m : PIdx k l → ℕ) : ℕ := ∑ s, plen s * m s

@[simp] lemma phi_apply (plen : PIdx k l → ℕ) (c : PIdx k l → ℤ) (a : Arc plen) :
    phi plen c a = c a.1 := rfl

@[simp] lemma phi_mk (plen : PIdx k l → ℕ) (c : PIdx k l → ℤ) (s : PIdx k l)
    (i : Fin (plen s)) : phi plen c ⟨s, i⟩ = c s := rfl

@[simp] lemma mA_mk (plen : PIdx k l → ℕ) (m : PIdx k l → ℕ) (s : PIdx k l)
    (i : Fin (plen s)) : mA plen m ⟨s, i⟩ = (m s : ℤ) := rfl

end AssemblyP1.RigidityMultiHub

namespace AssemblyP1.RigidityMultiHub

open Finset BigOperators

variable {k l : ℕ}

/-- Out-arcs of a vertex within the support. -/
def moutF (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s) (v : Vtx plen) :
    Finset (Arc plen) := (medges plen).filter (fun e => mtail plen hpos e = v)

/-- In-arcs of a vertex within the support. -/
def minF (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s) (v : Vtx plen) :
    Finset (Arc plen) := (medges plen).filter (fun e => mhead plen hpos e = v)

@[simp] lemma mem_moutF (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (v : Vtx plen) (e : Arc plen) : e ∈ moutF plen hpos v ↔ mtail plen hpos e = v := by
  simp [moutF, medges]

@[simp] lemma mem_minF (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (v : Vtx plen) (e : Arc plen) : e ∈ minF plen hpos v ↔ mhead plen hpos e = v := by
  simp [minF, medges]

/-- Characterization of the tail of an arc being an internal vertex. -/
lemma mtail_eq_inr_iff (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (s s' : PIdx k l) (r : Fin (plen s - 1)) (i : Fin (plen s')) :
    mtail plen hpos ⟨s', i⟩ = Sum.inr ⟨s, r⟩ ↔ s' = s ∧ i.val = r.val + 1 := by
  rw [mtail_mk]
  split_ifs with h0
  · constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨rfl, hi⟩; omega
  · constructor
    · intro h
      have hfst : s' = s := by
        have := congrArg (fun x : Σ t : PIdx k l, Fin (plen t - 1) => x.1) (Sum.inr.inj h)
        exact this
      have hsnd : i.val - 1 = r.val := by
        have := congrArg (fun x : Σ t : PIdx k l, Fin (plen t - 1) => x.2.val) (Sum.inr.inj h)
        exact this
      exact ⟨hfst, by omega⟩
    · rintro ⟨hs', hi⟩
      cases hs'
      have hfin : (⟨i.val - 1, by have h1 := i.isLt; have h2 := hpos s; have h3 := h0; omega⟩ : Fin (plen s - 1)) = r := by
        apply Fin.ext; simp; omega
      rw [hfin]

/-- Characterization of the head of an arc being an internal vertex. -/
lemma mhead_eq_inr_iff (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (s s' : PIdx k l) (r : Fin (plen s - 1)) (i : Fin (plen s')) :
    mhead plen hpos ⟨s', i⟩ = Sum.inr ⟨s, r⟩ ↔ s' = s ∧ i.val = r.val := by
  rw [mhead_mk]
  split_ifs with hlast
  · constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨rfl, hi⟩
      -- hlast says i.val + 1 = plen s, but r.val < plen s - 1 gives r.val + 1 < plen s
      omega
  · constructor
    · intro h
      have hfst : s' = s := by
        have := congrArg (fun x : Σ t : PIdx k l, Fin (plen t - 1) => x.1) (Sum.inr.inj h)
        exact this
      have hsnd : i.val = r.val := by
        have := congrArg (fun x : Σ t : PIdx k l, Fin (plen t - 1) => x.2.val) (Sum.inr.inj h)
        exact this
      exact ⟨hfst, hsnd⟩
    · rintro ⟨hs', hi⟩
      cases hs'
      have hfin : (⟨i.val, by have h1 := i.isLt; omega⟩ : Fin (plen s - 1)) = r := by
        apply Fin.ext; simp; omega
      rw [hfin]

end AssemblyP1.RigidityMultiHub

namespace AssemblyP1.RigidityMultiHub

open Finset BigOperators

variable {k l : ℕ}

/-- The out-arc of an internal vertex `(s, r)` is the single arc `(s, r+1)`. -/
lemma moutF_internal (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (s : PIdx k l) (r : Fin (plen s - 1)) :
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
lemma minF_internal (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (s : PIdx k l) (r : Fin (plen s - 1)) :
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

end AssemblyP1.RigidityMultiHub

namespace AssemblyP1.RigidityMultiHub

open Finset BigOperators

variable {k l : ℕ}

/-- An arc's tail is a hub `Sum.inl h` iff it is the first arc of a path whose
source hub is `h`. -/
lemma mtail_eq_inl_iff (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (s' : PIdx k l) (i : Fin (plen s')) (h : Fin 2) :
    mtail plen hpos ⟨s', i⟩ = Sum.inl h ↔ i.val = 0 ∧ srcHub s' = h := by
  rw [mtail_mk]
  by_cases h0 : i.val = 0
  · rw [dite_eq_left h0]; simp [Sum.inl.injEq, h0]
  · rw [dite_eq_right h0]; simp [h0]

/-- An arc's head is a hub `Sum.inl h` iff it is the last arc of a path whose
target hub is `h`. -/
lemma mhead_eq_inl_iff (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (s' : PIdx k l) (i : Fin (plen s')) (h : Fin 2) :
    mhead plen hpos ⟨s', i⟩ = Sum.inl h ↔ i.val + 1 = plen s' ∧ tgtHub s' = h := by
  rw [mhead_mk]
  by_cases hlast : i.val + 1 = plen s'
  · rw [dite_eq_left hlast]; simp [Sum.inl.injEq, hlast]
  · rw [dite_eq_right hlast]; simp [hlast]

/-- Out-arcs of hub `u = Sum.inl 0` are the first arcs of the `u → v` paths. -/
lemma moutF_hub_zero (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s) :
    moutF plen hpos (Sum.inl (0 : Fin 2)) =
      Finset.univ.image (fun i : Fin k =>
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
    | inr j' => simp [srcHub] at hsrc
  · rintro ⟨i', -, he⟩
    rw [← he]
    exact (mtail_eq_inl_iff plen hpos (Sum.inl i')
      ⟨0, by have := hpos (Sum.inl i'); omega⟩ 0).mpr ⟨rfl, rfl⟩

/-- In-arcs of hub `u = Sum.inl 0` are the last arcs of the `v → u` paths. -/
lemma minF_hub_zero (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s) :
    minF plen hpos (Sum.inl (0 : Fin 2)) =
      Finset.univ.image (fun j : Fin l =>
        (⟨Sum.inr j, ⟨plen (Sum.inr j) - 1, by have := hpos (Sum.inr j); omega⟩⟩ : Arc plen)) := by
  apply Finset.ext
  intro e
  obtain ⟨s', i⟩ := e
  rw [mem_minF, Finset.mem_image]
  constructor
  · intro hh
    obtain ⟨hlast, htgt⟩ := (mhead_eq_inl_iff plen hpos s' i 0).mp hh
    cases s' with
    | inl i' => simp [tgtHub] at htgt
    | inr j' =>
        refine ⟨j', Finset.mem_univ j', ?_⟩
        have hi : i = (⟨plen (Sum.inr j') - 1, by have := hpos (Sum.inr j'); omega⟩ : Fin (plen (Sum.inr j'))) := by
          apply Fin.ext; simp; omega
        rw [hi]
  · rintro ⟨j', -, he⟩
    rw [← he]
    exact (mhead_eq_inl_iff plen hpos (Sum.inr j')
      ⟨plen (Sum.inr j') - 1, by have := hpos (Sum.inr j'); omega⟩ 0).mpr
      ⟨by show (plen (Sum.inr j') - 1) + 1 = plen (Sum.inr j'); have := hpos (Sum.inr j'); omega, rfl⟩

/-- Out-arcs of hub `v = Sum.inl 1` are the first arcs of the `v → u` paths. -/
lemma moutF_hub_one (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s) :
    moutF plen hpos (Sum.inl (1 : Fin 2)) =
      Finset.univ.image (fun j : Fin l =>
        (⟨Sum.inr j, ⟨0, by have := hpos (Sum.inr j); omega⟩⟩ : Arc plen)) := by
  apply Finset.ext
  intro e
  obtain ⟨s', i⟩ := e
  rw [mem_moutF, Finset.mem_image]
  constructor
  · intro hh
    obtain ⟨h0, hsrc⟩ := (mtail_eq_inl_iff plen hpos s' i 1).mp hh
    cases s' with
    | inl i' => simp [srcHub] at hsrc
    | inr j' =>
        refine ⟨j', Finset.mem_univ j', ?_⟩
        have hi : i = (⟨0, by have := hpos (Sum.inr j'); omega⟩ : Fin (plen (Sum.inr j'))) := by
          apply Fin.ext; simp; omega
        rw [hi]
  · rintro ⟨j', -, he⟩
    rw [← he]
    exact (mtail_eq_inl_iff plen hpos (Sum.inr j')
      ⟨0, by have := hpos (Sum.inr j'); omega⟩ 1).mpr ⟨rfl, rfl⟩

/-- In-arcs of hub `v = Sum.inl 1` are the last arcs of the `u → v` paths. -/
lemma minF_hub_one (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s) :
    minF plen hpos (Sum.inl (1 : Fin 2)) =
      Finset.univ.image (fun i : Fin k =>
        (⟨Sum.inl i, ⟨plen (Sum.inl i) - 1, by have := hpos (Sum.inl i); omega⟩⟩ : Arc plen)) := by
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
        have hi : i = (⟨plen (Sum.inl i') - 1, by have := hpos (Sum.inl i'); omega⟩ : Fin (plen (Sum.inl i'))) := by
          apply Fin.ext; simp; omega
        rw [hi]
    | inr j' => simp [tgtHub] at htgt
  · rintro ⟨i', -, he⟩
    rw [← he]
    exact (mhead_eq_inl_iff plen hpos (Sum.inl i')
      ⟨plen (Sum.inl i') - 1, by have := hpos (Sum.inl i'); omega⟩ 1).mpr
      ⟨by show (plen (Sum.inl i') - 1) + 1 = plen (Sum.inl i'); have := hpos (Sum.inl i'); omega, rfl⟩

end AssemblyP1.RigidityMultiHub

namespace AssemblyP1.RigidityMultiHub

open Finset BigOperators

variable {k l : ℕ}

/-- Explicit balance predicate on the multi-hub graph. -/
def BalancedB (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s) (δ : Arc plen → ℤ) : Prop :=
  ∀ v ∈ mnodes plen, (∑ e ∈ moutF plen hpos v, δ e) = (∑ e ∈ minF plen hpos v, δ e)

/-- `BalancedB` is exactly the support-domain `BalancedZ`. -/
lemma balancedB_iff_balancedZ (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (δ : Arc plen → ℤ) :
    BalancedB plen hpos δ ↔
      AssemblyP1.ExactRigidityCriterion.BalancedZ (mtail plen hpos) (mhead plen hpos)
        (mnodes plen) (medges plen) δ :=
  Iff.rfl

/-- The balance equation at an internal vertex `(s, r)` forces the two adjacent
path arcs to carry equal values. -/
lemma balanced_step (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (δ : Arc plen → ℤ) (hbal : BalancedB plen hpos δ)
    (s : PIdx k l) (m : ℕ) (hm : m + 1 < plen s) :
    δ ⟨s, ⟨m + 1, hm⟩⟩ = δ ⟨s, ⟨m, by omega⟩⟩ := by
  have h := hbal (Sum.inr ⟨s, ⟨m, by omega⟩⟩) (Finset.mem_univ _)
  rw [moutF_internal, minF_internal] at h
  simpa using h

/-- Path constancy: a balanced arc function is constant on every path. -/
lemma path_const (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (δ : Arc plen → ℤ) (hbal : BalancedB plen hpos δ)
    (s : PIdx k l) (i : Fin (plen s)) :
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

/-- Sum over the out-arcs of hub `u`, reindexed by the `u → v` paths. -/
lemma sum_moutF_hub_zero (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (g : Arc plen → ℤ) :
    (∑ e ∈ moutF plen hpos (Sum.inl (0 : Fin 2)), g e)
      = ∑ i : Fin k, g ⟨Sum.inl i, ⟨0, by have := hpos (Sum.inl i); omega⟩⟩ := by
  rw [moutF_hub_zero, Finset.sum_image]
  intro x _ y _ hxy
  exact Sum.inl.inj (α := Fin k) (β := Fin l) (by simpa using congrArg (fun e : Arc plen => e.1) hxy)

/-- Sum over the in-arcs of hub `u`, reindexed by the `v → u` paths. -/
lemma sum_minF_hub_zero (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (g : Arc plen → ℤ) :
    (∑ e ∈ minF plen hpos (Sum.inl (0 : Fin 2)), g e)
      = ∑ j : Fin l, g ⟨Sum.inr j, ⟨plen (Sum.inr j) - 1, by have := hpos (Sum.inr j); omega⟩⟩ := by
  rw [minF_hub_zero, Finset.sum_image]
  intro x _ y _ hxy
  exact Sum.inr.inj (α := Fin k) (β := Fin l) (by simpa using congrArg (fun e : Arc plen => e.1) hxy)

/-- Sum over the out-arcs of hub `v`, reindexed by the `v → u` paths. -/
lemma sum_moutF_hub_one (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (g : Arc plen → ℤ) :
    (∑ e ∈ moutF plen hpos (Sum.inl (1 : Fin 2)), g e)
      = ∑ j : Fin l, g ⟨Sum.inr j, ⟨0, by have := hpos (Sum.inr j); omega⟩⟩ := by
  rw [moutF_hub_one, Finset.sum_image]
  intro x _ y _ hxy
  exact Sum.inr.inj (α := Fin k) (β := Fin l) (by simpa using congrArg (fun e : Arc plen => e.1) hxy)

/-- Sum over the in-arcs of hub `v`, reindexed by the `u → v` paths. -/
lemma sum_minF_hub_one (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (g : Arc plen → ℤ) :
    (∑ e ∈ minF plen hpos (Sum.inl (1 : Fin 2)), g e)
      = ∑ i : Fin k, g ⟨Sum.inl i, ⟨plen (Sum.inl i) - 1, by have := hpos (Sum.inl i); omega⟩⟩ := by
  rw [minF_hub_one, Finset.sum_image]
  intro x _ y _ hxy
  exact Sum.inl.inj (α := Fin k) (β := Fin l) (by simpa using congrArg (fun e : Arc plen => e.1) hxy)

/-- Every balanced arc function is the path-constant function `φ` of its values
on the first arc of each path, and those values satisfy the hub balance. -/
lemma phi_of_balanced (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (δ : Arc plen → ℤ) (hbal : BalancedB plen hpos δ) :
    δ = phi plen (fun s => δ ⟨s, ⟨0, by have := hpos s; omega⟩⟩) ∧
      (∑ i : Fin k, δ ⟨Sum.inl i, ⟨0, by have := hpos (Sum.inl i); omega⟩⟩)
        = (∑ j : Fin l, δ ⟨Sum.inr j, ⟨0, by have := hpos (Sum.inr j); omega⟩⟩) := by
  have hphi : δ = phi plen (fun s => δ ⟨s, ⟨0, by have := hpos s; omega⟩⟩) := by
    funext a
    obtain ⟨s, i⟩ := a
    simp only [phi_mk]
    exact path_const plen hpos δ hbal s i
  refine ⟨hphi, ?_⟩
  have h0 := hbal (Sum.inl (0 : Fin 2)) (Finset.mem_univ _)
  rw [sum_moutF_hub_zero, sum_minF_hub_zero] at h0
  have hconst : ∀ j : Fin l,
      δ ⟨Sum.inr j, ⟨plen (Sum.inr j) - 1, by have := hpos (Sum.inr j); omega⟩⟩
        = δ ⟨Sum.inr j, ⟨0, by have := hpos (Sum.inr j); omega⟩⟩ := by
    intro j
    exact path_const plen hpos δ hbal (Sum.inr j)
      ⟨plen (Sum.inr j) - 1, by have := hpos (Sum.inr j); omega⟩
  rw [Finset.sum_congr rfl (fun j _ => hconst j)] at h0
  simpa using h0

/-- Conversely, a path-constant function with hub balance is balanced. -/
lemma balanced_of_phi (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (c : PIdx k l → ℤ)
    (hbal : (∑ i : Fin k, c (Sum.inl i)) = (∑ j : Fin l, c (Sum.inr j))) :
    BalancedB plen hpos (phi plen c) := by
  intro v _
  rcases v with h | h
  · fin_cases h
    · change (∑ e ∈ moutF plen hpos (Sum.inl (0 : Fin 2)), phi plen c e) =
        (∑ e ∈ minF plen hpos (Sum.inl (0 : Fin 2)), phi plen c e)
      rw [sum_moutF_hub_zero, sum_minF_hub_zero]
      simp only [phi_mk]
      exact hbal
    · change (∑ e ∈ moutF plen hpos (Sum.inl (1 : Fin 2)), phi plen c e) =
        (∑ e ∈ minF plen hpos (Sum.inl (1 : Fin 2)), phi plen c e)
      rw [sum_moutF_hub_one, sum_minF_hub_one]
      simp only [phi_mk]
      exact hbal.symm
  · obtain ⟨s, r⟩ := h
    rw [moutF_internal, minF_internal]
    simp [phi_mk]

end AssemblyP1.RigidityMultiHub

namespace AssemblyP1.RigidityMultiHub

open Finset BigOperators

variable {k l : ℕ}

/-- Total mass of a path-constant arc function. -/
lemma phi_sum (plen : PIdx k l → ℕ) (c : PIdx k l → ℤ) :
    ∑ a : Arc plen, phi plen c a = ∑ s, (plen s : ℤ) * c s := by
  rw [Fintype.sum_sigma]
  simp only [phi_mk, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `mA` is the path-constant function of the multiplicities. -/
lemma mA_eq_phi (plen : PIdx k l → ℕ) (m : PIdx k l → ℕ) :
    mA plen m = phi plen (fun s => (m s : ℤ)) := rfl

/-- Total mass of the base circulation. -/
lemma mA_total (plen : PIdx k l → ℕ) (m : PIdx k l → ℕ) :
    ∑ a : Arc plen, mA plen m a = (mG plen m : ℤ) := by
  rw [mA_eq_phi, phi_sum, mG, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Nat.cast_mul]

/-- The base circulation is balanced provided the hub balance
`∑ m(u→v) = ∑ m(v→u)` holds. -/
lemma mA_balanced (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (m : PIdx k l → ℕ)
    (hbal : (∑ i : Fin k, m (Sum.inl i)) = (∑ j : Fin l, m (Sum.inr j))) :
    BalancedB plen hpos (mA plen m) := by
  rw [mA_eq_phi]
  apply balanced_of_phi
  exact_mod_cast hbal

/-- **The multi-hub exact rigidity criterion.** For a multi-hub support with `k`
`u → v` paths and `l` `v → u` paths of lengths `plen ≥ 1` and multiplicities
`m ≥ 1` with `∑ m(u→v) = ∑ m(v→u)`, the base circulation is non-rigid **iff**
there is a nonzero integer path-perturbation `α` with hub balance, zero total
mass, and the four boxes. -/
theorem multiHub_nonrigid_iff (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (m : PIdx k l → ℕ) (hm : ∀ s, 1 ≤ m s)
    (hbal : (∑ i : Fin k, m (Sum.inl i)) = (∑ j : Fin l, m (Sum.inr j))) :
    (¬ AssemblyP1.ExactRigidityCriterion.Rigid (mtail plen hpos) (mhead plen hpos)
        (mnodes plen) (medges plen) (mA plen m) (mG plen m)) ↔
      ∃ α : PIdx k l → ℤ, (∃ s, α s ≠ 0) ∧
        (∑ i : Fin k, α (Sum.inl i) = ∑ j : Fin l, α (Sum.inr j)) ∧
        (∑ s, (plen s : ℤ) * α s = 0) ∧
        (∀ s, 1 - (m s : ℤ) ≤ α s) := by
  have hAbal : AssemblyP1.ExactRigidityCriterion.BalancedZ (mtail plen hpos)
      (mhead plen hpos) (mnodes plen) (medges plen) (mA plen m) :=
    (balancedB_iff_balancedZ plen hpos (mA plen m)).mp (mA_balanced plen hpos m hbal)
  rw [AssemblyP1.ExactRigidityCriterion.nonrigid_iff_exists_delta (mtail plen hpos)
      (mhead plen hpos) (mnodes plen) (medges plen) (mA plen m) (mG plen m) hAbal
      (by simpa [medges] using mA_total plen m)]
  constructor
  · rintro ⟨δ, hne, hδbal, hδsum, hδbox⟩
    have hδbalB : BalancedB plen hpos δ :=
      (balancedB_iff_balancedZ plen hpos δ).mpr hδbal
    obtain ⟨hphi, hhub⟩ := phi_of_balanced plen hpos δ hδbalB
    refine ⟨fun s => δ ⟨s, ⟨0, by have := hpos s; omega⟩⟩, ?_, hhub, ?_, ?_⟩
    · obtain ⟨⟨s, i⟩, _, hde⟩ := hne
      refine ⟨s, ?_⟩
      intro h0
      apply hde
      rw [hphi, phi_mk]
      exact h0
    · rw [AssemblyP1.ExactRigidityCriterion.ZeroSum] at hδsum
      simp only [medges] at hδsum
      rw [hphi, phi_sum] at hδsum
      simpa using hδsum
    · intro s
      have := hδbox ⟨s, ⟨0, by have := hpos s; omega⟩⟩ (Finset.mem_univ _)
      simpa [mA_mk] using this
  · rintro ⟨α, hne, hhub, hsum, hbox⟩
    refine ⟨phi plen α, ?_, ?_, ?_, ?_⟩
    · obtain ⟨s, hs⟩ := hne
      exact ⟨⟨s, ⟨0, by have := hpos s; omega⟩⟩, Finset.mem_univ _, by simpa [phi_mk] using hs⟩
    · exact (balancedB_iff_balancedZ plen hpos (phi plen α)).mp (balanced_of_phi plen hpos α hhub)
    · rw [AssemblyP1.ExactRigidityCriterion.ZeroSum]
      have : ∑ e ∈ medges plen, phi plen α e = ∑ s, (plen s : ℤ) * α s := by
        simpa [medges] using phi_sum plen α
      rw [this]; exact hsum
    · intro e _
      obtain ⟨s, i⟩ := e
      simpa [mA_mk, phi_mk] using hbox s

end AssemblyP1.RigidityMultiHub

namespace AssemblyP1.RigidityMultiHub

open Finset BigOperators

variable {k l : ℕ}

/-- The rigidity predicate of the multi-hub support at multiplicity `m`. -/
abbrev MRigid (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s) (m : PIdx k l → ℕ) : Prop :=
  AssemblyP1.ExactRigidityCriterion.Rigid (mtail plen hpos) (mhead plen hpos)
    (mnodes plen) (medges plen) (mA plen m) (mG plen m)

/-- **All multiplicities `1` is rigid.** With unit slack the box forces `α ≥ 0`,
and the zero-mass equation with positive path lengths forces `α = 0`. -/
theorem multiHub_rigid_all_one (plen : PIdx k l → ℕ) (hpos : ∀ s, 1 ≤ plen s)
    (hbal : (∑ i : Fin k, (1 : ℕ)) = (∑ j : Fin l, (1 : ℕ))) :
    MRigid plen hpos (fun _ => 1) := by
  by_contra h
  rw [multiHub_nonrigid_iff plen hpos (fun _ => 1) (fun _ => le_refl 1) hbal] at h
  obtain ⟨α, hne, hhub, hsum, hbox⟩ := h
  have hterm : ∀ s ∈ (Finset.univ : Finset (PIdx k l)), 0 ≤ (plen s : ℤ) * α s := by
    intro s _
    apply mul_nonneg
    · have := hpos s; omega
    · simpa using hbox s
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hsum
  have hα : ∀ s, α s = 0 := by
    intro s
    have hs := hzero s (Finset.mem_univ s)
    have hp : (0 : ℤ) < (plen s : ℤ) := by have := hpos s; omega
    exact (mul_eq_zero.mp hs).resolve_left (ne_of_gt hp)
  obtain ⟨s, hs⟩ := hne
  exact hs (hα s)

/-! ## Concrete instances -/

/-- The `2`-path-each-way instance with lengths `1,3` and multiplicities `2,1`
on each side. -/
def p2 : PIdx 2 2 → ℕ := Sum.elim ![1, 3] ![1, 3]

/-- The multiplicities of `p2`. -/
def m2 : PIdx 2 2 → ℕ := Sum.elim ![2, 1] ![2, 1]

lemma p2_pos : ∀ s, 1 ≤ p2 s := by
  intro s; rcases s with i | j
  · fin_cases i <;> decide
  · fin_cases j <;> decide

lemma m2_pos : ∀ s, 1 ≤ m2 s := by
  intro s; rcases s with i | j
  · fin_cases i <;> decide
  · fin_cases j <;> decide

lemma m2_bal : (∑ i : Fin 2, m2 (Sum.inl i)) = (∑ j : Fin 2, m2 (Sum.inr j)) := by
  decide

/-- **Rigid repetitive instance.** At `p2` with multiplicities `(2,1)` the first
(length-`1`) path of each direction is traversed twice, yet the instance is
rigid. So no `m ≥ 2` repeat bound is necessary for non-rigidity. -/
theorem multiHub_rigid_repetitive_2 : MRigid p2 p2_pos m2 := by
  by_contra h
  rw [multiHub_nonrigid_iff p2 p2_pos m2 m2_pos m2_bal] at h
  obtain ⟨α, hne, hhub, hsum, hbox⟩ := h
  have hhub' : α (Sum.inl 0) + α (Sum.inl 1) = α (Sum.inr 0) + α (Sum.inr 1) := by
    simpa [Fin.sum_univ_two] using hhub
  have hsum' : (1:ℤ) * α (Sum.inl 0) + 3 * α (Sum.inl 1)
      + 1 * α (Sum.inr 0) + 3 * α (Sum.inr 1) = 0 := by
    have hh := hsum
    rw [Fintype.sum_sum_type] at hh
    simp only [Fin.sum_univ_two] at hh
    simp only [p2, Sum.elim_inl, Sum.elim_inr] at hh
    norm_num at hh
    linarith [hh]
  have k0 : (1:ℤ) - 2 ≤ α (Sum.inl 0) := by
    have h := hbox (Sum.inl 0); simp only [m2, Sum.elim_inl] at h; norm_num at h; exact h
  have k1 : (1:ℤ) - 1 ≤ α (Sum.inl 1) := by
    have h := hbox (Sum.inl 1); simp only [m2, Sum.elim_inl] at h; norm_num at h; exact h
  have k2 : (1:ℤ) - 2 ≤ α (Sum.inr 0) := by
    have h := hbox (Sum.inr 0); simp only [m2, Sum.elim_inr] at h; norm_num at h; exact h
  have k3 : (1:ℤ) - 1 ≤ α (Sum.inr 1) := by
    have h := hbox (Sum.inr 1); simp only [m2, Sum.elim_inr] at h; norm_num at h; exact h
  have e0 : α (Sum.inl (0 : Fin 2)) = 0 := by omega
  have e1 : α (Sum.inl (1 : Fin 2)) = 0 := by omega
  have e2 : α (Sum.inr (0 : Fin 2)) = 0 := by omega
  have e3 : α (Sum.inr (1 : Fin 2)) = 0 := by omega
  obtain ⟨s, hs⟩ := hne
  rcases s with i | j
  · fin_cases i
    · exact hs (by simpa using e0)
    · exact hs (by simpa using e1)
  · fin_cases j
    · exact hs (by simpa using e2)
    · exact hs (by simpa using e3)

/-- The **relaxed** multi-hub predicate: the exact criterion with the hub-balance
equation dropped (the naive independent-per-path / bouquet-style relaxation). -/
def RelaxedMH (plen : PIdx k l → ℕ) (m : PIdx k l → ℕ) : Prop :=
  ∃ α : PIdx k l → ℤ, (∃ s, α s ≠ 0) ∧
    (∑ s, (plen s : ℤ) * α s = 0) ∧ (∀ s, 1 - (m s : ℤ) ≤ α s)

/-- **The coupling equation is essential (failed simpler hypothesis).** At `p2`,
multiplicities `m2`, the relaxed predicate holds with witness
`α = (-1, 0, 1, 0)` while the instance is rigid. So the hub-balance coupling
cannot be dropped: no independent-per-path (bouquet-style / single-cut)
criterion decides the multi-hub family. -/
theorem multiHub_relaxed_not_sound : RelaxedMH p2 m2 ∧ MRigid p2 p2_pos m2 := by
  refine ⟨?_, multiHub_rigid_repetitive_2⟩
  refine ⟨fun s => (if s = Sum.inl 0 then (-1 : ℤ) else if s = Sum.inr 0 then 1 else 0),
    ?_, ?_, ?_⟩
  · exact ⟨Sum.inl 0, by simp⟩
  · decide
  · intro s; rcases s with i | j
    · fin_cases i <;> simp [m2, Sum.elim_inl, Sum.elim_inr]
    · fin_cases j <;> simp [m2, Sum.elim_inr, Sum.elim_inl]

end AssemblyP1.RigidityMultiHub
