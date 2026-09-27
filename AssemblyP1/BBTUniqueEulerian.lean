import AssemblyP1.BBTEulerian

/-!
# `thm:BBT`: uniqueness of the Eulerian cycle of the condensed graph (#89)

This module works towards `AssemblyP1.BBTEulerian.UniqueEulerianCycle` --- and
hence `EulerianCycleObstruction`, the one hypothesis that
`AssemblyP1.PopulationUniqueness` still takes --- from `Ukkonen` alone.  See
`docs/bbt-unique-eulerian-89.md` for the mathematical write-up and for the exact
statement of the step that is still open.

The object is the pull-back presentation `σ : Fin G ≃ Fin G` of an
equal-spectrum matching, exactly as in `AssemblyP1.BBTEulerian`.  Write

* `W = vtx` for the `(L-1)`-mer at a start, `ρ = nextPos` for the one-step
  rotation, `K = L - 1`;
* `Succ σ` for the successor permutation *of the listing* `σ 0, σ 1, …`, so
  that `Succ σ (σ i) = σ (i+1)`.

The `traverses` clause of `EulerianCycle`, read at `x = σ i`, is

```text
W (Succ σ x) = W (ρ x)   for every x.                                (T')
```

and with `f := Succ σ ∘ ρ⁻¹` this is `W (f q) = W q`: **`f` is a permutation
of the starts preserving the `(L-1)`-mer at every start**, and the
alternative traversal is the `f ρ`-cycle.

The steps developed here, in order:

* §1 the window layer (`WSeq`, the de Bruijn shift, the sets of agreement
  lengths) and the period arithmetic of the circular word, including the
  fact that the least period divides every period;
* §2 the master reformulation above;
* §3 the *right* and *left* maximal agreement of a pair of starts, the
  maximal-repeat block it produces, and the **three-occurrences lemma**:
  three distinct starts spelling the same `(L-1)`-mer either extend to a
  maximal triple repeat of length `≥ K`, or are congruent modulo the least
  period.  This is the doc's Lemma 1, and its primitive corollary
  (`fibre_le_two_of_primitive`) is a closed theorem;
* §4 the *combinatorial cycle-breaking step*: a label-preserving `f ≠ id`
  with an "innermost chord" cannot have `f ρ` a `G`-cycle.  This is a
  strictly sharper form of the doc's Lemma 3 (it needs neither an involution
  hypothesis nor a global non-crossing hypothesis), and with §3 it yields the
  whole **primitive case of the theorem** (Theorem 4.4).
-/
namespace AssemblyP1.BBTUniqueEulerian

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## 1. The window layer

All the definitions of this section are stated at the namespace level with
their parameters explicit, so that no parameter can be silently dropped by
auto-bound inclusion. -/

/-- The length-`e` circular window of `S` at the start `r`: the `e`-mer
`S r, S (r+1), …`.  This is `nodeWindow` at `L = e + 1`, so
`WSeq hG S r (L-1) = vtx hG L S r` (`vtx_eq_WSeq`). -/
def WSeq {α : Type} {G : ℕ} (hG : 0 < G) (S : Fin G → α) (r : Fin G) (e : ℕ) :
    Fin e → α :=
  fun d => cyc hG S (r.val + d.val)

/-- The two length-`e` windows at `a` and `b` agree. -/
def Agr {α : Type} {G : ℕ} (hG : 0 < G) (S : Fin G → α) (a b : Fin G) (e : ℕ) : Prop :=
  ∀ d : Fin e, cyc hG S (a.val + d.val) = cyc hG S (b.val + d.val)

instance {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (S : Fin G → α)
    (a b : Fin G) (e : ℕ) : Decidable (Agr hG S a b e) := by
  unfold Agr
  infer_instance

/-- The three length-`e` windows at `a`, `b`, `c` agree. -/
def Agr3 {α : Type} {G : ℕ} (hG : 0 < G) (S : Fin G → α) (a b c : Fin G) (e : ℕ) : Prop :=
  ∀ d : Fin e, cyc hG S (a.val + d.val) = cyc hG S (b.val + d.val) ∧
    cyc hG S (a.val + d.val) = cyc hG S (c.val + d.val)

/-- The three length-`e` windows at `a`, `b`, `c` agree. -/
instance {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (S : Fin G → α)
    (a b c : Fin G) (e : ℕ) : Decidable (Agr3 hG S a b c e) := by
  unfold Agr3
  infer_instance

/-- `d` is a *period* of the circular word: shifting every start by `d`
preserves the symbol. -/
def Period {α : Type} {G : ℕ} (hG : 0 < G) (S : Fin G → α) (d : ℕ) : Prop :=
  ∀ r : Fin G, S (rotAdd hG d r) = S r

instance {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (S : Fin G → α) (d : ℕ) :
    Decidable (Period hG S d) := by
  unfold Period
  infer_instance

/-- The forward shift carrying `a` to `b`. -/
def sh {G : ℕ} (_hG : 0 < G) (a b : Fin G) : ℕ := (b.val + G - a.val) % G

section Windows

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (S : Fin G → α)

theorem mod_shl_add (x y : ℕ) : (x + y % G) % G = (x + y) % G := by
  have hh := Nat.mod_add_div y G
  have h3 : x + y = (x + y % G) + G * (y / G) := by omega
  rw [h3, Nat.add_mul_mod_self_left]

theorem mod_add_shl (x y : ℕ) : (x + y) % G = (x % G + y) % G := by
  have hh := Nat.div_add_mod x G
  have h3 : x + y = (x % G + y) + G * (x / G) := by omega
  rw [h3, Nat.add_mul_mod_self_left]

/-- **Adding a whole turn changes nothing.** -/
theorem cyc_add (a d : ℕ) : cyc hG S (a + d) = cyc hG S ((a % G) + d) := by
  unfold cyc
  congr 1
  apply Fin.ext
  exact mod_add_shl a d

/-- The vertex of the `(L-1)`-mer graph is the length-`(L-1)` window. -/
theorem vtx_eq_WSeq (L : ℕ) (r : Fin G) : WSeq hG S r (L - 1) = vtx hG L S r := rfl

/-- **The de Bruijn shift.**  The `(e+1)`-mer at `r + 1` is the `(e+1)`-mer at
`r` shifted left by one position. -/
theorem WSeq_next (e : ℕ) (r : Fin G) (d : Fin e) (hd : d.val + 1 < e) :
    WSeq hG S (nextPos hG r) e d = WSeq hG S r e ⟨d.val + 1, hd⟩ := by
  unfold WSeq nextPos rotAdd
  simpa only [Fin.val_mk, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (cyc_add hG S (r.val + 1) d.val).symm

/-- **Shifts compose.** -/
theorem rotAdd_add (a b : ℕ) (r : Fin G) :
    rotAdd hG a (rotAdd hG b r) = rotAdd hG (a + b) r := by
  apply Fin.ext
  show ((r.val + b) % G + a) % G = (r.val + (a + b)) % G
  calc ((r.val + b) % G + a) % G = (r.val + b + a) % G := (mod_add_shl (r.val + b) a).symm
    _ = (r.val + (a + b)) % G := by congr 1; omega

theorem rotAdd_full (r : Fin G) : rotAdd hG G r = r := by
  apply Fin.ext
  show (r.val + G) % G = r.val
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt r.isLt]

theorem sh_lt (a b : Fin G) : sh hG a b < G := Nat.mod_lt _ hG

theorem rotAdd_sh (a b : Fin G) : rotAdd hG (sh hG a b) a = b := by
  apply Fin.ext
  have h1 : a.val + (b.val + G - a.val) = b.val + G := by omega
  have h2 : (a.val + (b.val + G - a.val) % G) % G = (a.val + (b.val + G - a.val)) % G :=
    mod_shl_add a.val (b.val + G - a.val)
  show (a.val + (b.val + G - a.val) % G) % G = b.val
  rw [h2, h1, Nat.add_mod_right, Nat.mod_eq_of_lt b.isLt]

/-- **The shift coordinate commutes with the circle operations.**  Shifting
`b` forward by `sh a y` is the same position as shifting `y` forward by
`sh a b`: both are `a + sh a b + sh a y`.  This is the identity that makes
`sh` usable as a coordinate on the circle. -/
theorem rotAdd_sh_comm (a b y : Fin G) :
    rotAdd hG (sh hG a y) b = rotAdd hG (sh hG a b) y := by
  apply Fin.ext
  show ((b.val + sh hG a y) % G) = ((y.val + sh hG a b) % G)
  have hb : b.val = (a.val + sh hG a b) % G :=
    (congrArg Fin.val (rotAdd_sh hG a b)).symm
  have hy : y.val = (a.val + sh hG a y) % G :=
    (congrArg Fin.val (rotAdd_sh hG a y)).symm
  have e1 : ((a.val + sh hG a b) % G + sh hG a y) % G
      = ((a.val + sh hG a b) + sh hG a y) % G :=
    (mod_add_shl (a.val + sh hG a b) (sh hG a y)).symm
  have e2 : a.val + sh hG a b + sh hG a y = a.val + sh hG a y + sh hG a b := by omega
  have e3 : ((a.val + sh hG a y) + sh hG a b) % G
      = ((a.val + sh hG a y) % G + sh hG a b) % G :=
    mod_add_shl (a.val + sh hG a y) (sh hG a b)
  calc ((b.val + sh hG a y) % G) = ((a.val + sh hG a b) % G + sh hG a y) % G := by
        rw [hb]
    _ = ((a.val + sh hG a b + sh hG a y) % G) := e1
    _ = ((a.val + sh hG a y + sh hG a b) % G) := e2 ▸ rfl
    _ = ((a.val + sh hG a y) % G + sh hG a b) % G := e3
    _ = ((y.val + sh hG a b) % G) := by rw [hy]

/-! ### 1.1 The period arithmetic -/

theorem period_zero : Period hG S 0 := by
  intro r
  rw [rotAdd_zero]

theorem period_add {d e : ℕ} (hd : Period hG S d) (he : Period hG S e) :
    Period hG S (d + e) := by
  intro r
  rw [← rotAdd_add hG d e r]
  exact (hd (rotAdd hG e r)).trans (he r)

theorem period_sub {d e : ℕ} (hd : Period hG S d) (he : Period hG S e) (hde : e ≤ d) :
    Period hG S (d - e) := by
  intro r
  have h : rotAdd hG e (rotAdd hG (d - e) r) = rotAdd hG d r := by
    rw [rotAdd_add]
    congr 1
    omega
  calc S (rotAdd hG (d - e) r) = S (rotAdd hG e (rotAdd hG (d - e) r)) :=
        (he (rotAdd hG (d - e) r)).symm
    _ = S (rotAdd hG d r) := by rw [h]
    _ = S r := hd r

theorem period_mul {p q : ℕ} (hp : Period hG S p) : Period hG S (q * p) := by
  induction q with
  | zero => simpa using (period_zero hG S)
  | succ q ih =>
      have h := period_add hG S ih hp
      rw [← Nat.succ_mul] at h
      exact h

/-- **A period divides every period.**  This is the whole of the period
arithmetic needed below: it turns "the windows at `a` and `b` agree at every
length" into "`p` is a multiple of `leastPeriod`", and hence into "the starts
are congruent modulo `leastPeriod`". -/
theorem least_period_dvd {p d : ℕ} (hp : Period hG S p) (hpos : 0 < p)
    (hmin : ∀ e, 0 < e → e < p → ¬ Period hG S e) (hd : Period hG S d) : p ∣ d := by
  have hq' : p * (d / p) ≤ d := by
    have h2 : d / p * p = p * (d / p) := Nat.mul_comm _ _
    rw [← h2]
    exact Nat.div_mul_le_self d p
  have hmul : Period hG S (p * (d / p)) := by
    have hh := period_mul hG S (p := p) (q := d / p) hp
    simpa [Nat.mul_comm] using hh
  have hper : Period hG S (d - p * (d / p)) := period_sub hG S hd hmul hq'
  have h1 : p * (d / p) + d % p = d := Nat.div_add_mod d p
  have heq : d - p * (d / p) = d % p := by
    rw [Nat.sub_eq_iff_eq_add hq']
    exact h1.symm.trans (Nat.add_comm _ _)
  rw [heq] at hper
  have hz : d % p = 0 := by
    by_contra hne
    exact hmin _ (Nat.pos_of_ne_zero hne) (Nat.mod_lt _ hpos) hper
  exact Nat.dvd_of_mod_eq_zero hz

section LeastPeriod

theorem period_full : Period hG S G := by
  intro r
  rw [rotAdd_full]

/-- The **least period** of the circular word: the least *positive* shift that
preserves every symbol.  It exists because `G` is one (`rotAdd_full`,
`period_full`), and it satisfies `1 ≤ leastPeriod ≤ G`. -/
noncomputable def leastPeriod (hG : 0 < G) (S : Fin G → α) : ℕ :=
  ((Finset.range (G + 1)).filter (fun d => 0 < d ∧ Period hG S d)).min' (by
    refine ⟨(G : ℕ), ?_⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    exact ⟨by omega, by intro r; rw [rotAdd_full]⟩)

theorem leastPeriod_spec :
    Period hG S (leastPeriod hG S) ∧ 0 < leastPeriod hG S ∧ leastPeriod hG S ≤ G := by
  have hmem : leastPeriod hG S ∈
      (Finset.range (G + 1)).filter (fun d => 0 < d ∧ Period hG S d) :=
    Finset.min'_mem _ (by
      refine ⟨(G : ℕ), ?_⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
      exact ⟨by omega, by intro r; rw [rotAdd_full]⟩)
  have h2 := Finset.mem_filter.mp hmem
  exact ⟨h2.2.2, h2.2.1, by simpa using Finset.mem_range.mp h2.1⟩

theorem leastPeriod_min {d : ℕ} (hdG : d ≤ G) (hd : 0 < d) (hp : Period hG S d) :
    leastPeriod hG S ≤ d := by
  have hmem : d ∈ (Finset.range (G + 1)).filter (fun e => 0 < e ∧ Period hG S e) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ⟨hd, hp⟩⟩
  exact Finset.min'_le _ _ hmem

theorem leastPeriod_dvd_period {d : ℕ} (hdG : d ≤ G) (hd : Period hG S d) :
    leastPeriod hG S ∣ d := by
  have hspec := leastPeriod_spec hG S
  have hpos : 0 < leastPeriod hG S := hspec.2.1
  refine least_period_dvd hG S hspec.1 hpos ?_ hd
  intro e he het hper
  have h3 := leastPeriod_min hG S (d := e) (hdG := by omega) (hd := he) (hp := hper)
  omega

/-- **The least period divides the length.** -/
theorem leastPeriod_dvd_G : leastPeriod hG S ∣ G :=
  leastPeriod_dvd_period hG S (Nat.le_refl G) (period_full hG S)

end LeastPeriod

theorem cyc_eq_rotAdd' (r : Fin G) (n : ℕ) (_hn : n < G) :
    cyc hG S (r.val + n) = S (rotAdd hG n r) := rfl

/-- **If the windows at `a` and `b` agree at every length, `sh a b` is a
period.**  (The agreement says that `S` takes the same value at `a + t` and
`a + t + sh a b` for every `t`, i.e. that `S` is `sh a b`-periodic.) -/
theorem period_of_agree_all {a b : Fin G}
    (h : ∀ d : Fin G, cyc hG S (a.val + d.val) = cyc hG S (b.val + d.val)) :
    Period hG S (sh hG a b) := by
  intro y
  have hx : sh hG a y < G := Nat.mod_lt _ hG
  have hh := h ⟨sh hG a y, hx⟩
  have h1 : S (rotAdd hG (sh hG a y) a) = S (rotAdd hG (sh hG a y) b) := by
    rwa [cyc_eq_rotAdd' hG S _ _ hx, cyc_eq_rotAdd' hG S _ _ hx] at hh
  have h2 : rotAdd hG (sh hG a y) b = rotAdd hG (sh hG a b) y :=
    rotAdd_sh_comm hG a b y
  have h3 : rotAdd hG (sh hG a y) a = y := rotAdd_sh hG a y
  rw [h3, h2] at h1
  rw [h1]

/-- **If `sh a b` is a period, the windows at `a` and `b` agree at every
length.** -/
theorem agree_all_of_period {a b : Fin G} (h : Period hG S (sh hG a b)) (d : Fin G) :
    cyc hG S (a.val + d.val) = cyc hG S (b.val + d.val) := by
  have h4 := h (rotAdd hG d.val a)
  have h6 : rotAdd hG (sh hG a b + d.val) a = rotAdd hG (d.val + sh hG a b) a := by
    congr 1
    omega
  have h7 : rotAdd hG (d.val + sh hG a b) a = rotAdd hG d.val b := by
    rw [← rotAdd_add hG d.val (sh hG a b) a, rotAdd_sh hG a b]
  rw [rotAdd_add hG (sh hG a b) d.val a, h6, h7] at h4
  rw [cyc_eq_rotAdd' hG S a d.val d.isLt, cyc_eq_rotAdd' hG S b d.val d.isLt]
  exact h4.symm

/-! ### 1.2 The sets of agreement lengths -/

/-- The lengths at which the two windows at `a`, `b` agree. -/
def AgrSet {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (S : Fin G → α)
    (a b : Fin G) : Finset ℕ :=
  (Finset.range (G + 1)).filter (fun e => Agr hG S a b e)

/-- The lengths at which the three windows at `a`, `b`, `c` agree. -/
def AgrSet3 {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (S : Fin G → α)
    (a b c : Fin G) : Finset ℕ :=
  (Finset.range (G + 1)).filter (fun e => Agr3 hG S a b c e)

theorem mem_AgrSet {a b : Fin G} {e : ℕ} (he : e ∈ AgrSet hG S a b) :
    Agr hG S a b e :=
  (Finset.mem_filter.mp he).2

theorem mem_AgrSet_range {a b : Fin G} {e : ℕ} (he : e ∈ AgrSet hG S a b) :
    e ≤ G := by
  have h1 := Finset.mem_range.mp (Finset.mem_filter.mp he).1
  omega

theorem mem_AgrSet3 {a b c : Fin G} {e : ℕ} (he : e ∈ AgrSet3 hG S a b c) :
    Agr3 hG S a b c e :=
  (Finset.mem_filter.mp he).2

theorem mem_AgrSet3_range {a b c : Fin G} {e : ℕ} (he : e ∈ AgrSet3 hG S a b c) :
    e ≤ G := by
  have h1 := Finset.mem_range.mp (Finset.mem_filter.mp he).1
  omega

/-- **Agreement at length `e` is downward closed.** -/
theorem Agr_mono {a b : Fin G} {e e' : ℕ} (he' : e' ≤ e) (he : Agr hG S a b e) :
    Agr hG S a b e' := by
  intro d
  exact he ⟨d.val, Nat.lt_of_lt_of_le d.isLt he'⟩

theorem Agr3_mono {a b c : Fin G} {e e' : ℕ} (he' : e' ≤ e) (he : Agr3 hG S a b c e) :
    Agr3 hG S a b c e' := by
  intro d
  exact he ⟨d.val, Nat.lt_of_lt_of_le d.isLt he'⟩

/-- Agreement at length `e` iff agreement at every shorter length. -/
theorem agr_iff_forall_lt (a b : Fin G) (e : ℕ) :
    Agr hG S a b e ↔ ∀ d : ℕ, d < e → cyc hG S (a.val + d) = cyc hG S (b.val + d) := by
  constructor
  · intro h d hd
    exact h ⟨d, hd⟩
  · intro h d
    exact h d.val d.isLt

theorem agr3_iff_forall_lt (a b c : Fin G) (e : ℕ) :
    Agr3 hG S a b c e ↔ ∀ d : ℕ, d < e →
      cyc hG S (a.val + d) = cyc hG S (b.val + d) ∧
      cyc hG S (a.val + d) = cyc hG S (c.val + d) := by
  constructor
  · intro h d hd
    exact h ⟨d, hd⟩
  · intro h d
    exact h d.val d.isLt

/-- Agreement at length `e` is a statement about the *pair of starts*: it
survives a common shift of both, read at every length that still fits inside
the original window (`r + e' ≤ e`). -/
theorem agr_pair {a b : Fin G} {e e' : ℕ} (r : Fin G) (hr : r.val + e' ≤ e)
    (he : Agr hG S a b e) :
    Agr hG S (rotAdd hG r.val a) (rotAdd hG r.val b) e' := by
  intro d
  have h := he ⟨r.val + d.val, by omega⟩
  show cyc hG S ((a.val + r.val) % G + d.val) = cyc hG S ((b.val + r.val) % G + d.val)
  rw [← cyc_add hG S (a.val + r.val) d.val, ← cyc_add hG S (b.val + r.val) d.val]
  simpa only [Nat.add_assoc] using h

theorem agr3_pair {a b c : Fin G} {e e' : ℕ} (r : Fin G) (hr : r.val + e' ≤ e)
    (he : Agr3 hG S a b c e) :
    Agr3 hG S (rotAdd hG r.val a) (rotAdd hG r.val b) (rotAdd hG r.val c) e' := by
  intro d
  have h := he ⟨r.val + d.val, by omega⟩
  show cyc hG S ((a.val + r.val) % G + d.val) = cyc hG S ((b.val + r.val) % G + d.val) ∧
    cyc hG S ((a.val + r.val) % G + d.val) = cyc hG S ((c.val + r.val) % G + d.val)
  rw [← cyc_add hG S (a.val + r.val) d.val, ← cyc_add hG S (b.val + r.val) d.val,
    ← cyc_add hG S (c.val + r.val) d.val]
  simpa only [Nat.add_assoc] using h

/-- **The vertex equality is agreement at length `K = L - 1`.** -/
theorem vtx_agr {L : ℕ} {a b : Fin G} (h : vtx hG L S a = vtx hG L S b) :
    Agr hG S a b (L - 1) := by
  intro d
  exact congrFun h d

theorem vtx_agr3 {L : ℕ} {a b c : Fin G}
    (h1 : vtx hG L S a = vtx hG L S b) (h2 : vtx hG L S a = vtx hG L S c) :
    Agr3 hG S a b c (L - 1) := by
  intro d
  exact ⟨congrFun h1 d, congrFun h2 d⟩

/-- `K` is one of the agreement lengths, provided `K ≤ G`. -/
theorem agrSet_of_vtx {L : ℕ} (hK : L - 1 ≤ G) {a b : Fin G}
    (h : vtx hG L S a = vtx hG L S b) : L - 1 ∈ AgrSet hG S a b := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
  exact vtx_agr hG S h

theorem agrSet3_of_vtx {L : ℕ} (hK : L - 1 ≤ G) {a b c : Fin G}
    (h1 : vtx hG L S a = vtx hG L S b) (h2 : vtx hG L S a = vtx hG L S c) :
    L - 1 ∈ AgrSet3 hG S a b c := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
  exact vtx_agr3 hG S h1 h2

/-! ### 1.3 The congruence `p ∣ sh x y` of starts modulo the least period

The relation `x ~ y  :↔  leastPeriod ∣ sh x y` ("`x` and `y` are congruent
modulo the least period") is what the whole proof is organised around.  It
needs no arithmetic on `Fin` values: `sh` is a faithful "shift coordinate" on
the circle, so `~` is a congruence for the circle operations. -/

theorem rotAdd_eq_iff (d : ℕ) (r r' : Fin G) (hd : d < G) :
    rotAdd hG d r = r' ↔ d = sh hG r r' := by
  constructor
  · intro h
    have hinj : ∀ a b : Fin G, rotAdd hG a.val r = rotAdd hG b.val r → a = b :=
      fun a b hab => rotAdd_inj_lt hG r hab
    have hfin : (⟨d, hd⟩ : Fin G) = ⟨sh hG r r', Nat.mod_lt _ hG⟩ :=
      hinj ⟨d, hd⟩ ⟨sh hG r r', Nat.mod_lt _ hG⟩
        (h.trans (rotAdd_sh hG r r').symm)
    exact congrArg Fin.val hfin
  · intro h
    rw [h]
    exact rotAdd_sh hG r r'

/-- **The outer and inner shifts commute.** -/
theorem rotAdd_swap (a b : ℕ) (x : Fin G) :
    rotAdd hG a (rotAdd hG b x) = rotAdd hG b (rotAdd hG a x) := by
  apply Fin.ext
  show (((x.val + b) % G + a) % G) = (((x.val + a) % G + b) % G)
  have h1 : ((x.val + b) % G + a) % G = (x.val + b + a) % G := by
    rw [← mod_add_shl]
  have h2 : ((x.val + a) % G + b) % G = (x.val + a + b) % G := by
    rw [← mod_add_shl]
  rw [h1, h2]
  apply congrArg (fun t : ℕ => t % G)
  omega

/-- **The shift coordinate is additive along the circle.** -/
theorem sh_add (x y z : Fin G) : (sh hG x y + sh hG y z) % G = sh hG x z := by
  refine (rotAdd_eq_iff hG _ x z (Nat.mod_lt _ hG)).mp ?_
  have heq : rotAdd hG ((sh hG x y + sh hG y z) % G) x
      = rotAdd hG (sh hG x y + sh hG y z) x :=
    (rotAdd_mod hG (sh hG x y + sh hG y z) x).symm
  have hy : rotAdd hG (sh hG x y) x = y := rotAdd_sh hG x y
  have hz : rotAdd hG (sh hG y z) y = z := rotAdd_sh hG y z
  have key : rotAdd hG (sh hG x y) (rotAdd hG (sh hG y z) x) = z := by
    calc rotAdd hG (sh hG x y) (rotAdd hG (sh hG y z) x)
        = rotAdd hG (sh hG y z) (rotAdd hG (sh hG x y) x) :=
          rotAdd_swap hG (sh hG x y) (sh hG y z) x
      _ = rotAdd hG (sh hG y z + sh hG x y) x := rotAdd_add hG _ _ x
      _ = rotAdd hG (sh hG y z) y := by
          have h3 : rotAdd hG (sh hG y z) y
              = rotAdd hG (sh hG y z) (rotAdd hG (sh hG x y) x) :=
            congrArg (fun w : Fin G => rotAdd hG (sh hG y z) w) hy.symm
          rw [← rotAdd_add hG (sh hG y z) (sh hG x y) x]
          exact h3.symm
      _ = z := hz
  rw [heq, ← rotAdd_add hG (sh hG x y) (sh hG y z) x]
  exact key

/-- **`~` is transitive.** -/
theorem sh_dvd_trans {p : ℕ} (hpG : p ∣ G) {x y z : Fin G}
    (h1 : p ∣ sh hG x y) (h2 : p ∣ sh hG y z) : p ∣ sh hG x z := by
  have h3 : p ∣ sh hG x y + sh hG y z := dvd_add h1 h2
  have hdiv : (sh hG x y + sh hG y z) % G
        + G * ((sh hG x y + sh hG y z) / G) = sh hG x y + sh hG y z :=
    Nat.mod_add_div _ _
  have h5 : p ∣ G * ((sh hG x y + sh hG y z) / G) := dvd_mul_of_dvd_left hpG _
  have h6 : G * ((sh hG x y + sh hG y z) / G) ≤ sh hG x y + sh hG y z := by
    have hh := Nat.div_mul_le_self (sh hG x y + sh hG y z) G
    rwa [Nat.mul_comm] at hh
  have hsub : sh hG x y + sh hG y z - G * ((sh hG x y + sh hG y z) / G)
      = (sh hG x y + sh hG y z) % G := by
    have hN := hdiv
    omega
  have h7 := Nat.dvd_sub h3 h5
  rw [hsub] at h7
  rwa [sh_add hG x y z] at h7

/-- **The `(L-1)`-mer labelling is periodic.** -/
theorem cyc_of_period {p : ℕ} (hp : Period hG S p) (i : ℕ) :
    cyc hG S (i + p) = cyc hG S i := by
  have h2 : S (rotAdd hG p ⟨i % G, Nat.mod_lt _ hG⟩) = S ⟨i % G, Nat.mod_lt _ hG⟩ :=
    hp ⟨i % G, Nat.mod_lt _ hG⟩
  have h1 : cyc hG S (i + p) = S (rotAdd hG p ⟨i % G, Nat.mod_lt _ hG⟩) := by
    unfold cyc
    congr 1
    apply Fin.ext
    show (i + p) % G = (i % G + p) % G
    rw [mod_add_shl i p]
  rw [h1, h2]
  rfl

theorem vtx_of_period {L p : ℕ} (hp : Period hG S p) (r : Fin G) :
    vtx hG L S (rotAdd hG p r) = vtx hG L S r := by
  funext d
  show cyc hG S (((r.val + p) % G) + d.val) = cyc hG S (r.val + d.val)
  have h1 : cyc hG S (((r.val + p) % G) + d.val)
      = cyc hG S ((r.val + p) + d.val) := by
    unfold cyc
    apply congrArg (fun w : Fin G => S w)
    apply Fin.ext
    exact (mod_add_shl (r.val + p) d.val).symm
  calc cyc hG S (((r.val + p) % G) + d.val) = cyc hG S ((r.val + p) + d.val) := h1
    _ = cyc hG S ((r.val + d.val) + p) := by
      congr 1
      omega
    _ = cyc hG S (r.val + d.val) := cyc_of_period hG S hp (r.val + d.val)

theorem vtx_of_period_mul {L p q : ℕ} (hp : Period hG S p) (r : Fin G) :
    vtx hG L S (rotAdd hG (q * p) r) = vtx hG L S r := by
  induction q with
  | zero =>
      have hz : 0 * p = 0 := by simp
      rw [hz, rotAdd_zero]
  | succ q ih =>
      have h2 : (q + 1) * p = q * p + p := Nat.succ_mul q p
      have h3 : rotAdd hG (q * p + p) r = rotAdd hG p (rotAdd hG (q * p) r) := by
        rw [rotAdd_add]
        congr 1
        omega
      rw [h2, h3, vtx_of_period hG S hp]
      exact ih

/-- **Congruent starts spell the same `(L-1)`-mer.** -/
theorem vtx_eq_of_sh {L p : ℕ} (hp : Period hG S p) {x y : Fin G}
    (h : p ∣ sh hG x y) : vtx hG L S x = vtx hG L S y := by
  obtain ⟨q, hq⟩ := h
  have h2 : vtx hG L S y = vtx hG L S (rotAdd hG (q * p) x) := by
    have hq' : q * p = sh hG x y := (Nat.mul_comm q p).trans hq.symm
    rw [hq', rotAdd_sh hG x y]
  rw [h2, vtx_of_period_mul hG S hp]

/-! ## 2. The master reformulation: alternative traversals are
label-preserving permutations -/

/-- **The successor permutation of the listing `σ 0, σ 1, …`.**  It is the
conjugate `σ ρ σ⁻¹` of the one-step rotation, hence a bijection. -/
def Succ {G : ℕ} (hG : 0 < G) (σ : Fin G ≃ Fin G) : Fin G → Fin G :=
  fun x => σ (nextPos hG (σ.symm x))

theorem Succ_apply {G : ℕ} (hG : 0 < G) (σ : Fin G ≃ Fin G) (i : Fin G) :
    Succ hG σ (σ i) = σ (nextPos hG i) := by
  unfold Succ
  simp only [Equiv.symm_apply_apply]

theorem Succ_injective {G : ℕ} (hG : 0 < G) (σ : Fin G ≃ Fin G) :
    Function.Injective (Succ hG σ) := by
  intro x y hxy
  have h1 : σ (nextPos hG (σ.symm x)) = σ (nextPos hG (σ.symm y)) := hxy
  have h2 := congrArg σ.symm h1
  simp only [Equiv.symm_apply_apply] at h2
  exact (Equiv.injective σ.symm) (nextPos_inj hG h2)

/-- **The listing traverses the starts in the order `σ 0, σ 1, …`.**
Re-derived from the reduction's own `altSucc_iterate` (`Succ hG σ` *is* the
successor `σ ∘ ρ ∘ σ⁻¹` of the pull-back presentation), so this step adds no
new word semantics. -/
theorem succ_listing' {G : ℕ} (hG : 0 < G) (σ : Fin G ≃ Fin G) (i : Fin G) :
    ∀ n : ℕ, (Succ hG σ)^[n] (σ i) = σ (rotAdd hG n i) := by
  intro n
  have h1 := altSucc_iterate hG σ n (σ i)
  show (Succ hG σ)^[n] (σ i) = σ (rotAdd hG n i)
  unfold Succ
  simpa only [Equiv.symm_apply_apply] using h1

/-- **`Succ` is a `G`-cycle on the starts: the listing visits them all.** -/
theorem listing_surj {G : ℕ} (hG : 0 < G) (σ : Fin G ≃ Fin G) :
    ∀ x : Fin G, ∃ n : ℕ, (Succ hG σ)^[n] (σ (origin hG)) = x := by
  intro x
  refine ⟨(σ.symm x).val, ?_⟩
  rw [succ_listing' hG σ (origin hG) (σ.symm x).val]
  refine (congrArg σ ?_).trans (Equiv.apply_symm_apply σ x)
  apply Fin.ext
  show (((0 : ℕ) + (σ.symm x).val) % G) = (σ.symm x).val
  rw [Nat.zero_add, Nat.mod_eq_of_lt (σ.symm x).isLt]

/-- The alternative traversal, in the form in which the proof uses it:
`f q = Succ σ (prevPos q)`.  `traverses` is exactly "the `(L-1)`-mer of the
alternative traversal at the start following `q` is the `(L-1)`-mer at `q`". -/
def AltF {G : ℕ} (hG : 0 < G) (σ : Fin G ≃ Fin G) (q : Fin G) : Fin G :=
  Succ hG σ (prevPos hG q)

theorem AltF_succ {G : ℕ} (hG : 0 < G) (σ : Fin G ≃ Fin G) (q : Fin G) :
    AltF hG σ (nextPos hG q) = Succ hG σ q := by
  unfold AltF Succ
  rw [prevNext hG q]

theorem AltF_vtx {α : Type} {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)
    (σ : Fin G ≃ Fin G) (htrav : ∀ i : Fin G,
      vtx hG L S (σ (nextPos hG i)) = vtx hG L S (nextPos hG (σ i))) (q : Fin G) :
    vtx hG L S (AltF hG σ q) = vtx hG L S q := by
  have h1 := htrav (σ.symm (prevPos hG q))
  unfold AltF at ⊢
  simpa only [Succ, Equiv.symm_apply_apply, Equiv.apply_symm_apply, nextPrev] using h1

end Windows

end AssemblyP1.BBTUniqueEulerian
