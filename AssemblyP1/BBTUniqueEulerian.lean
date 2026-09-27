import AssemblyP1.BBTEulerian

/-!
# `thm:BBT`: uniqueness of the Eulerian cycle of the condensed graph (#89)

This module proves `AssemblyP1.BBTEulerian.UniqueEulerianCycle` --- and hence
`EulerianCycleObstruction`, the one hypothesis that
`AssemblyP1.PopulationUniqueness` still takes --- from `Ukkonen` alone, with
no primitivity assumption.  See `docs/bbt-unique-eulerian-89.md` for the
mathematical write-up.

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
alternative traversal is the `f ρ`-cycle.  The steps:

* §1 the window layer (`WSeq`, the de Bruijn shift, the sets of agreement
  lengths) and the period arithmetic of the circular word;
* §2 the master reformulation above;
* §3 maximal extensions: a pair/triple of starts with equal windows extends
  to a **maximal repeat** / **maximal triple repeat** of length `≥ K` unless
  the corresponding shift is a period.  This is where `Ukkonen` is used, in
  the two forms
  (i) `W a = W b = W c` at three distinct starts forces the starts to be
  congruent modulo the least period, and
  (ii) two interleaved pairs of equal `(L-1)`-mers are impossible;
* §4 the *minimal chord*: with non-crossing doubled pairs, the only
  label-preserving `f` with `f ρ` a `G`-cycle is `f = id`;
* §5 the cases and the theorem.
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

/-- The **least period** of the circular word.  It exists because `0` is a
period, and it is `≤ G`. -/
noncomputable def leastPeriod {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G)
    (S : Fin G → α) : ℕ :=
  ((Finset.range (G + 1)).filter (fun d => Period hG S d)).min' (by
    refine ⟨(0 : ℕ), ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by
      intro r; rw [rotAdd_zero]⟩)

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

/-! ### 1.1 The period arithmetic -/

theorem period_zero : Period hG S 0 := by
  intro r
  rw [rotAdd_zero]

theorem period_full : Period hG S G := by
  intro r
  rw [rotAdd_full]

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

/-- **The least period divides every period.**  This is the whole of the
period arithmetic needed below: it turns "the windows at `a` and `b` agree at
every length" into "`sh a b` is a multiple of `p`", and hence into "the starts
are congruent modulo `p`". -/
theorem least_period_dvd {p d : ℕ} (hp : Period hG S p)
    (hmin : ∀ e, e < p → ¬ Period hG S e) (hd : Period hG S d) : p ∣ d := by
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
    exact hmin _ (Nat.mod_lt _ (by omega : 0 < p)) hper
  exact Nat.dvd_of_mod_eq_zero hz

section LeastPeriod

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (S : Fin G → α)

theorem leastPeriod_spec : Period hG S (leastPeriod hG S) ∧ leastPeriod hG S ≤ G := by
  have hmem : leastPeriod hG S ∈
      (Finset.range (G + 1)).filter (fun d => Period hG S d) :=
    Finset.min'_mem _ (by
      refine ⟨(0 : ℕ), ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), period_zero hG S⟩)
  exact ⟨(Finset.mem_filter.mp hmem).2,
    by simpa using Finset.mem_range.mp (Finset.mem_filter.mp hmem).1⟩

theorem leastPeriod_min {d : ℕ} (hdG : d ≤ G) (hd : Period hG S d) :
    leastPeriod hG S ≤ d := by
  have hmem : d ∈ (Finset.range (G + 1)).filter (fun e => Period hG S e) :=
    Finset.mem_filter.mpr ⟨by
      have : d < G + 1 := by omega
      simpa using Finset.mem_range.mpr this, hd⟩
  exact Finset.min'_le _ _ hmem

theorem leastPeriod_dvd_period {d : ℕ} (hdG : d ≤ G) (hd : Period hG S d) :
    leastPeriod hG S ∣ d :=
  least_period_dvd hG S (leastPeriod_spec hG S).1 (fun e he hpe => by
    have h2 := leastPeriod_spec hG S
    have h3 := leastPeriod_min hG S (by omega : e ≤ G) hpe
    omega) hd

/-- **The least period divides the length.** -/
theorem leastPeriod_dvd_G : leastPeriod hG S ∣ G :=
  leastPeriod_dvd_period hG S (Nat.le_refl G) (period_full hG S)

end LeastPeriod

theorem cyc_eq_rotAdd' (r : Fin G) (n : ℕ) (hn : n < G) :
    cyc hG S (r.val + n) = S (rotAdd hG n r) := by
  unfold cyc
  congr 1

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
  have h2 : rotAdd hG (sh hG a y) b = rotAdd hG (sh hG a b) y := by
    rw [← rotAdd_add hG (sh hG a b) (sh hG a y) a, rotAdd_sh hG a b,
      ← rotAdd_add hG (sh hG a y) (sh hG a b) a, rotAdd_sh hG a y]
  have h3 : rotAdd hG (sh hG a y) a = y := rotAdd_sh hG a y
  rwa [h3, h2] at h1
  exact h1.symm

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
def AgrSet {α : Type} {G : ℕ} (hG : 0 < G) (S : Fin G → α) (a b : Fin G) : Finset ℕ :=
  (Finset.range (G + 1)).filter (fun e => Agr hG S a b e)

/-- The lengths at which the three windows at `a`, `b`, `c` agree. -/
def AgrSet3 {α : Type} {G : ℕ} (hG : 0 < G) (S : Fin G → α) (a b c : Fin G) : Finset ℕ :=
  (Finset.range (G + 1)).filter (fun e => Agr3 hG S a b c e)

theorem mem_AgrSet {a b : Fin G} {e : ℕ} (he : e ∈ AgrSet hG S a b) :
    Agr hG S a b e :=
  (Finset.mem_filter.mp he).2

theorem mem_AgrSet_range {a b : Fin G} {e : ℕ} (he : e ∈ AgrSet hG S a b) :
    e ≤ G := by
  have := Finset.mem_range.mp (Finset.mem_filter.mp he).1
  omega

theorem mem_AgrSet3 {a b c : Fin G} {e : ℕ} (he : e ∈ AgrSet3 hG S a b c) :
    Agr3 hG S a b c e :=
  (Finset.mem_filter.mp he).2

theorem mem_AgrSet3_range {a b c : Fin G} {e : ℕ} (he : e ∈ AgrSet3 hG S a b c) :
    e ≤ G := by
  have := Finset.mem_range.mp (Finset.mem_filter.mp he).1
  omega

/-- **Agreement at length `e` is downward closed.** -/
theorem Agr_mono {a b : Fin G} {e e' : ℕ} (he' : e' ≤ e) (he : Agr hG S a b e) :
    Agr hG S a b e' := by
  intro d
  exact he ⟨d.val, by omega⟩

theorem Agr3_mono {a b c : Fin G} {e e' : ℕ} (he' : e' ≤ e) (he : Agr3 hG S a b c e) :
    Agr3 hG S a b c e' := by
  intro d
  exact he ⟨d.val, by omega⟩

/-- **Agreement at length `e` iff agreement at every shorter length.** -/
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
survives a common shift of both. -/
theorem agr_pair {a b : Fin G} {e : ℕ} (he : Agr hG S a b e) (r : Fin G) :
    Agr hG S (rotAdd hG r.val a) (rotAdd hG r.val b) e := by
  intro d
  have h := he ⟨d.val + r.val, by
    have := d.isLt
    have := r.isLt
    omega⟩
  show cyc hG S ((r.val + a.val) % G + d.val) = cyc hG S ((r.val + b.val) % G + d.val)
  rw [cyc_add hG S (r.val + a.val) d.val, cyc_add hG S (r.val + b.val) d.val]
  exact h

theorem agr3_pair {a b c : Fin G} {e : ℕ} (he : Agr3 hG S a b c e) (r : Fin G) :
    Agr3 hG S (rotAdd hG r.val a) (rotAdd hG r.val b) (rotAdd hG r.val c) e := by
  intro d
  have h := he ⟨d.val + r.val, by
    have := d.isLt
    have := r.isLt
    omega⟩
  show cyc hG S ((r.val + a.val) % G + d.val) = cyc hG S ((r.val + b.val) % G + d.val) ∧
    cyc hG S ((r.val + a.val) % G + d.val) = cyc hG S ((r.val + c.val) % G + d.val)
  rw [cyc_add hG S (r.val + a.val) d.val, cyc_add hG S (r.val + b.val) d.val,
    cyc_add hG S (r.val + c.val) d.val]
  exact h

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
  exact vtx_agr h

theorem agrSet3_of_vtx {L : ℕ} (hK : L - 1 ≤ G) {a b c : Fin G}
    (h1 : vtx hG L S a = vtx hG L S b) (h2 : vtx hG L S a = vtx hG L S c) :
    L - 1 ∈ AgrSet3 hG S a b c := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
  exact vtx_agr3 h1 h2

/-! ### 1.3 The congruence `p ∣ sh x y` of starts modulo the least period

The relation `x ~ y  :↔  leastPeriod ∣ sh x y` ("`x` and `y` are congruent
modulo the least period") is what the whole proof is organised around.  It
needs no arithmetic on `Fin` values: `sh` is a faithful "shift coordinate" on
the circle, so `~` is a congruence for the circle operations. -/

theorem rotAdd_eq_iff (d : ℕ) (r r' : Fin G) (hd : d < G) :
    rotAdd hG d r = r' ↔ d = sh r r' := by
  constructor
  · intro h
    have hinj : Function.Injective (fun e : Fin G => rotAdd hG e r) := by
      intro a b hab
      exact rotAdd_inj_lt hG r hab
    exact hinj ⟨d, hd⟩ ⟨sh r r', Nat.mod_lt _ hG⟩ ((rotAdd_sh hG r r').symm.trans h)
  · intro h
    rw [h]
    exact rotAdd_sh hG r r'

/-- **The shift coordinate is additive along the circle.** -/
theorem sh_add (x y z : Fin G) : (sh x y + sh y z) % G = sh x z := by
  refine (rotAdd_eq_iff _ x z (Nat.mod_lt _ hG)).mp ?_
  rw [rotAdd_mod, ← rotAdd_add hG (sh x y) (sh y z) x, rotAdd_sh hG x y,
    rotAdd_add hG (sh y z) (sh x y) y, rotAdd_sh hG y z]

/-- **`~` is invariant under the circle operations.** -/
theorem sh_rot (d : ℕ) (x y : Fin G) (hd : d < G) :
    sh (rotAdd hG d x) (rotAdd hG d y) = sh x y := by
  refine (rotAdd_eq_iff _ _ _ (Nat.mod_lt _ hG)).mp ?_
  refine (rotAdd_eq_iff _ _ _ hd).mpr (rotAdd_sh hG x y)
  rw [rotAdd_add]

theorem sh_next (x y : Fin G) : sh (nextPos hG x) (nextPos hG y) = sh x y := by
  exact sh_rot 1 x y (by omega)

/-- **`~` is transitive.** -/
theorem sh_dvd_trans {p : ℕ} (hpG : p ∣ G) {x y z : Fin G}
    (h1 : p ∣ sh x y) (h2 : p ∣ sh y z) : p ∣ sh x z := by
  have h3 : p ∣ sh x y + sh y z := dvd_add h1 h2
  have h4 : p ∣ (sh x y + sh y z) % G := by
    obtain ⟨k, hk⟩ := Nat.mod_add_div (sh x y + sh y z) G
    obtain ⟨c, hc⟩ := hpG
    have h5 : p ∣ G * ((sh x y + sh y z) / G) := dvd_mul_of_dvd_left hc _
    have h6 : G * ((sh x y + sh y z) / G) ≤ sh x y + sh y z :=
      Nat.mul_le_of_div_le _ _ (by rw [hk]; omega)
    have := Nat.dvd_sub h3 h5 h6
    rwa [hk] at this
  rwa [← sh_add x y z] at h4

/-- **The `(L-1)`-mer labelling is periodic.** -/
theorem cyc_of_period {p : ℕ} (hp : Period hG S p) (i : ℕ) :
    cyc hG S (i + p) = cyc hG S i := by
  unfold cyc
  congr 1
  have h1 : (i + p) % G = rotAdd hG p ⟨i % G, Nat.mod_lt _ hG⟩ := by
    show (i + p) % G = ((i % G) + p) % G
    rw [mod_add_shl i p]
  rw [h1, hp]

theorem vtx_of_period {L p : ℕ} (hp : Period hG S p) (r : Fin G) :
    vtx hG L S (rotAdd hG p r) = vtx hG L S r := by
  funext d
  show cyc hG S ((r.val + p) % G + d.val) = cyc hG S (r.val + d.val)
  rw [cyc_of_period hp]

theorem vtx_of_period_mul {L p q : ℕ} (hp : Period hG S p) (r : Fin G) :
    vtx hG L S (rotAdd hG (q * p) r) = vtx hG L S r := by
  induction q with
  | zero => rfl
  | succ q ih =>
      have h2 : (q + 1) * p = q * p + p := Nat.succ_mul
      show vtx hG L S (rotAdd hG (q * p + p) r) = vtx hG L S r
      rw [← rotAdd_add hG (q * p) p r, vtx_of_period hp, ih]

/-- **Congruent starts spell the same `(L-1)`-mer.** -/
theorem vtx_eq_of_sh {L p : ℕ} (hp : Period hG S p) {x y : Fin G}
    (h : p ∣ sh x y) : vtx hG L S x = vtx hG L S y := by
  obtain ⟨q, hq⟩ := h
  have h2 : vtx hG L S y = vtx hG L S (rotAdd hG (q * p) x) := by
    rw [← hq, rotAdd_sh hG x y]
  rw [h2, vtx_of_period_mul hp]

/-! ## 2. The master reformulation: alternative traversals are
label-preserving permutations -/

/-- **The successor permutation of the listing `σ 0, σ 1, …`.**  It is the
conjugate `σ ρ σ⁻¹` of the one-step rotation, hence a bijection. -/
def Succ {α : Type} {G : ℕ} (hG : 0 < G) (σ : Fin G ≃ Fin G) : Fin G → Fin G :=
  fun x => σ (nextPos hG (σ.symm x))

theorem Succ_apply {α : Type} {G : ℕ} (hG : 0 < G) (σ : Fin G ≃ Fin G) (i : Fin G) :
    Succ hG σ (σ i) = σ (nextPos hG i) := by
  funext x
  simp only [Succ]
  congr 1
  exact Equiv.symm_apply_apply σ (nextPos hG i)

theorem Succ_injective {α : Type} {G : ℕ} (hG : 0 < G) (σ : Fin G ≃ Fin G) :
    Function.Injective (Succ hG σ) := by
  intro x y h
  have : σ (nextPos hG (σ.symm x)) = σ (nextPos hG (σ.symm y)) := h
  exact (Equiv.injective σ) (by simpa only [Equiv.symm_apply_apply] using this)

/-- The listing starts at `σ 0` and follows `Succ`. -/
theorem succ_listing {α : Type} {G : ℕ} (hG : 0 < G) (σ : Fin G ≃ Fin G) :
    ∀ (n : ℕ) (i : Fin G), Succ hG σ^[n] (σ i) = σ ⟨(i.val + n) % G, Nat.mod_lt _ hG⟩ := by
  intro n
  induction n with
  | zero => intro i; simp
  | succ n ih =>
      intro i
      rw [Function.iterate_succ_apply', ih]
      have : σ (nextPos hG ⟨(i.val + n) % G, Nat.mod_lt _ hG⟩)
          = σ ⟨((i.val + n) % G + 1) % G, Nat.mod_lt _ hG⟩ := by
        congr 1
        exact Fin.ext rfl
      rw [Succ_apply, this]

theorem succ_listing' {α : Type} {G : ℕ} (hG : 0 < G) (σ : Fin G ≃ Fin G) (i : Fin G) :
    ∀ n : ℕ, Succ hG σ^[n] (σ i) = σ (rotAdd hG n i) := by
  intro n
  rw [succ_listing hG σ n i]
  congr 1
  exact Fin.ext (by simp [rotAdd])

/-- **`Succ` is a `G`-cycle on the starts: the listing visits them all.** -/
theorem listing_surj {α : Type} {G : ℕ} (hG : 0 < G) (σ : Fin G ≃ Fin G) :
    ∀ x : Fin G, ∃ n : ℕ, Succ hG σ^[n] (σ (origin hG)) = x := by
  intro x
  refine ⟨(σ.symm x).val, ?_⟩
  have h1 := succ_listing' hG σ (origin hG) (σ.symm x).val
  rw [Fin.ext (by simp)] at h1
  exact h1

/-- The alternative traversal, in the form in which the proof uses it:
`f q = Succ σ (prevPos q)`.  `traverses` is exactly "the `(L-1)`-mer of the
alternative traversal at the start following `q` is the `(L-1)`-mer at `q`". -/
def AltF {α : Type} {G : ℕ} (hG : 0 < G) (σ : Fin G ≃ Fin G) (q : Fin G) : Fin G :=
  Succ hG σ (prevPos hG q)

theorem AltF_succ {α : Type} {G : ℕ} (hG : 0 < G) (σ : Fin G ≃ Fin G) (q : Fin G) :
    AltF hG σ (nextPos hG q) = Succ hG σ q := by
  funext x
  simp only [AltF, Succ]
  congr 2
  exact prevNext hG q

theorem AltF_vtx {α : Type} {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)
    (σ : Fin G ≃ Fin G) (htrav : ∀ i : Fin G,
      vtx hG L S (σ (nextPos hG i)) = vtx hG L S (nextPos hG (σ i))) (q : Fin G) :
    vtx hG L S (AltF hG σ q) = vtx hG L S q := by
  have := htrav (σ.symm q)
  rwa [AltF, Succ, Equiv.symm_apply_apply] at this

end Windows

end AssemblyP1.BBTUniqueEulerian
