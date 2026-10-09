import Mathlib
import AssemblyP1.SourceFaithfulIs
import AssemblyP1.Section62BidirectedFlow
import AssemblyP1.SameLengthSection62Counterexample

/-!
# A disconnected-support feasible optimum at full overlap (`o_min = L − 1`)

This module settles the open question that issue #214 asks about the
Medvedev–Brudno (2009) §6.2 flow domain at the full-overlap setting
`o_min = L − 1`:

> is every §6.1-optimal §6.2 flow positive-support connected?

The answer is **no**.  This module exhibits, from a truth that satisfies the
strict Shomorony `I_s` bridging predicate, an explicit §6.2-feasible flow whose
throughput is the *unique* global maximizer of the §6.1 separable binomial
objective over its whole domain `1 ≤ d ≤ N`, and whose positive support is
*disconnected*.  So a genuine optimum of the full flow optimizer need not be
positive-support connected, and "the optimum spells a single connected assembly"
fails at `o_min = L − 1` just as non-spellability fails at `o_min = 1`.

The instance is the same-length witness truth, reused:

```text
alphabet        {A, T}, reverse-complement involution A <-> T
truth           S = AAATAT  (G = 6)
read length     L = 3,  o_min = L − 1 = 2   (full overlap)
realized starts (0, 1, 3, 5), start 0 sampled twice   (n = 5)
external size   N = |S| = 6
observed        x = { AAA:2, AAT:1, ATA:1, TAA:1 }
support         { AAA, AAT, ATA, TAA }   (all four molecule classes)
```

The `I_s` certificate (`truth_information_feasible`) and the §6.2 graph
(`graphList`, the sixteen length-`2` bidirected overlap edges) are the ones
already kernel-checked in `AssemblyP1.SameLengthSection62Counterexample` for
this exact truth and realized start set; this module reuses them and adds the
disconnected optimum.

The disconnected optimal flow `d* = (AAA:2, AAT:1, ATA:1, TAA:1)`:

```text
component 1:  AAA.p -> AAA.p  (self-overlap "AA")  x2
component 2:  AAT.p -> ATA.p -> TAA.p -> AAT.p  (circuit)
positive support = { AAA } u { AAT, ATA, TAA }   -> two components
```

This is kept distinct from the `o_min = 1` non-spellable counterexample of
`AssemblyP1.Section62NonSpelledFlow`: here the optimal throughput `d*` *is* a
genome spectrum (the molecule `AAAAT`), so the phenomenon is disconnectedness of
the *flow*, not non-spellability of the *throughput*.  Indeed `d*` also has a
*connected* realization (the `AAAAT` window walk), so the optimum set contains
both a connected and a disconnected realization — which is exactly why "all
optima are positive-support connected" is false.

Everything is decidable and kernel-checked: the module contains no `sorry`,
`axiom`, `admit` or `native_decide`.

## Source correspondence

| Lean object | MB09 clause |
|---|---|
| `discFlow`, `dStar'` | §6.2: the flow is "a (non-contiguous) assembly"; §5.2: `dᵢ` is the flow through vertex `i` |
| `Feasible62` (reused) | §6.2 lower bounds + §3.4 balance + supersource/supersink |
| `PortBalanced` | §3.3/§3.4 read at strand (port) level (stronger than the class-level clause) |
| `supportDisconnected` | the positive-edge support of a flow, a project-level notion (see below) |
| `marginal`, `lik` (reused) | §6.1 separable binomial with external `N` |

The "positive-support connectedness" predicate is a **project-level
strengthening** used to state the question precisely; it is not an MB09 notion.
The §6.2 feasibility, the §6.1 objective and `I_s` are source facts.
-/

namespace AssemblyP1.Section62FullOverlapDisconnected

set_option maxHeartbeats 4000000

open AssemblyP1.Section62Flow
open AssemblyP1.SameLengthSection62Counterexample

/-! ## The disconnected optimal throughput and flow -/

/-- The throughput vector of the disconnected optimum, `d* = (AAA:2, AAT:1,
ATA:1, TAA:1)`, as a function on the `Fin 8` molecule-class labels. -/
def dStar (c : Fin 8) : Nat :=
  if c = (0 : Fin 8) then 2 else if c = (1 : Fin 8) then 1
    else if c = (2 : Fin 8) then 1 else if c = (4 : Fin 8) then 1 else 0

theorem dStar_0 : dStar 0 = 2 := rfl
theorem dStar_1 : dStar 1 = 1 := rfl
theorem dStar_2 : dStar 2 = 1 := rfl
theorem dStar_4 : dStar 4 = 1 := rfl

theorem dStar_off : ∀ c : Fin 8, c ∉ relevant → dStar c = 0 := by
  unfold relevant dStar
  decide

/-- The throughput vector of `discFlow`, relabelled by molecule class. -/
def dStar' (w : Strand3) : Nat := dStar (repCode w)

/-- **The disconnected optimal flow.**  Two bidirected components on the
`o_min = L − 1 = 2` graph: the `AAA.p → AAA.p` self-overlap (flow `2`) and the
`AAT.p → ATA.p → TAA.p → AAT.p` circuit (flow `1` each).  No edge joins the two
components, so the positive support is disconnected. -/
def discFlow : BdFlow Base Strand3 := fun e =>
  if ekey e = keyOf (m3 .A .A .A) (m3 .A .A .A) then 2 else
  if ekey e = keyOf (m3 .A .A .T) (m3 .A .T .A) then 1 else
  if ekey e = keyOf (m3 .A .T .A) (m3 .T .A .A) then 1 else
  if ekey e = keyOf (m3 .T .A .A) (m3 .A .A .T) then 1 else
  0

/-! ## §6.2 feasibility, clause by clause -/

theorem disc_edge_lower_bounds : ∀ e ∈ graphList, (0 : ℕ) ≤ discFlow e := by
  decide

theorem disc_vertex_lower_bounds :
    ∀ v ∈ readVerts, (1 : ℕ) ≤ throughput Base Strand3 rep3 discFlow graphList v := by
  decide

theorem disc_balance_zero :
    ∀ v ∈ readVerts,
      balance Base Strand3 rep3 discFlow noTerm graphList v = 0 := by
  decide

theorem disc_throughput :
    ∀ v ∈ readVerts,
      throughput Base Strand3 rep3 discFlow graphList v = dStar' v := by
  decide

/-- **The disconnected flow is a §6.2 admissible flow** on the full-overlap
graph: edge lower bounds `0`, the §6.2 vertex lower bound `1`, §3.4
signed-incidence balance `0` at every read vertex, no supersource/supersink
usage, and vertex throughput `dStar'`. -/
theorem disc_feasible62 :
    Feasible62 Base Strand3 rep3 readVerts graphList discFlow noTerm dStar' :=
  ⟨⟨disc_edge_lower_bounds, disc_vertex_lower_bounds, disc_balance_zero,
    disc_throughput⟩, noTerm_usage_zero⟩

/-! ### Port (strand-level) balance

MB09 §3.3 gives every molecule two strands; the §3.4 balance read at that level
asks for the departing and arriving flow to agree at every strand.  This is
*stronger* than the class-level balance of `Feasible62`; the disconnected flow
satisfies it too. -/

/-- Flow on the edges that depart from the strand `s`. -/
def portOut (f : BdFlow Base Strand3) (s : Strand3) : ℕ :=
  graphList.foldr (fun e acc => if e.sx = s then f e + acc else acc) 0

/-- Flow on the edges that arrive at the strand `s`. -/
def portIn (f : BdFlow Base Strand3) (s : Strand3) : ℕ :=
  graphList.foldr (fun e acc => if e.sy = s then f e + acc else acc) 0

/-- MB09 §3.4 balance at strand (port) level: the departing and arriving flow
agree at every strand of every observed molecule. -/
def PortBalanced (f : BdFlow Base Strand3) : Bool :=
  (strandsOf rc3 readVerts).all (fun s => decide (portOut f s = portIn f s))

theorem disc_port_balanced : PortBalanced discFlow = true := by
  decide

/-! ## The positive support of `discFlow` is disconnected

The positive support is the set of read vertices carrying positive throughput.
`discFlow` puts positive flow on exactly four edges, whose endpoints fall into
two classes with no edge between them: `{ AAA }` and `{ AAT, ATA, TAA }`.  The
predicate below is the project-level "positive-support connectedness" notion
that the question quantifies over. -/

/-- The positive support of a flow: a Boolean membership test for the read
vertices carrying positive throughput. -/
def inSupport (f : BdFlow Base Strand3) (v : Strand3) : Bool :=
  decide (0 < throughput Base Strand3 rep3 f graphList v)

/-- No positive edge of `f` crosses between the set `s` and its complement. -/
def noCross (f : BdFlow Base Strand3) (s : Strand3 → Bool) : Bool :=
  graphList.all (fun e => !decide (0 < f e) || (s (rep3 e.sx) == s (rep3 e.sy)))

/-- A flow's positive support is **disconnected** when it splits into two nonempty
parts joined by no positive edge. -/
def supportDisconnected (f : BdFlow Base Strand3) : Prop :=
  ∃ s : Strand3 → Bool,
    (∃ v, inSupport f v = true ∧ s v = true) ∧
    (∃ v, inSupport f v = true ∧ s v = false) ∧
    noCross f s = true

/-- The separating set: the isolated `AAA` component (true only at `AAA`). -/
def sSep : Strand3 → Bool := fun v => v == m3 .A .A .A

theorem inSupport_AAA : inSupport discFlow (m3 .A .A .A) = true := by
  decide

theorem inSupport_AAT : inSupport discFlow (m3 .A .A .T) = true := by
  decide

theorem sSep_AAA : sSep (m3 .A .A .A) = true := rfl

theorem sSep_AAT : sSep (m3 .A .A .T) = false := by
  decide

theorem noCross_disc : noCross discFlow sSep = true := by
  decide

/-- **The positive support of the disconnected optimum is disconnected.** -/
theorem disc_support_disconnected : supportDisconnected discFlow :=
  ⟨sSep, ⟨m3 .A .A .A, inSupport_AAA, sSep_AAA⟩,
    ⟨m3 .A .A .T, inSupport_AAT, sSep_AAT⟩, noCross_disc⟩

/-! ## The disconnected flow is §6.1-optimal

The §6.1 objective is separable, so its maximizer over the domain `1 ≤ d ≤ N` is
the coordinatewise maximizer.  With `x = (AAA:2, AAT:1, ATA:1, TAA:1)`, `n = 5`,
`N = 6`: the `AAA` marginal (observed count `2`) peaks uniquely at `d = 2`, and
the three marginals with observed count `1` peak uniquely at `d = 1`.  So the
unique global maximizer is `d* = (2,1,1,1)` — exactly the throughput of
`discFlow`. -/

theorem lik_obs_dStar :
    lik obs dStar = (marginal obs dStar 0) * ((marginal obs dStar 1) *
      ((marginal obs dStar 2) * (marginal obs dStar 4))) := by
  rw [lik_eq_relevant_prod obs dStar
    (fun c hc => ⟨(truth_zero_off c hc).1, dStar_off c hc⟩), relevant_prod_eq]

/-- The `AAA` marginal (observed count `2`) is maximized at `d = 2`. -/
theorem marg_AAA_le (d : Fin 8 → Nat) (hd : d 0 ≤ 6) :
    marginal obs d 0 ≤ marginal obs dStar 0 := by
  rw [marginal, marginal, obs_0, dStar_0]
  interval_cases d 0 <;> norm_num [Nat.choose]

/-- The `AAT` marginal (observed count `1`) is maximized at `d = 1`. -/
theorem marg_AAT_le (d : Fin 8 → Nat) (hd : d 1 ≤ 6) :
    marginal obs d 1 ≤ marginal obs dStar 1 := by
  rw [marginal, marginal, obs_1, dStar_1]
  interval_cases d 1 <;> norm_num [Nat.choose]

/-- The `ATA` marginal (observed count `1`) is maximized at `d = 1`. -/
theorem marg_ATA_le (d : Fin 8 → Nat) (hd : d 2 ≤ 6) :
    marginal obs d 2 ≤ marginal obs dStar 2 := by
  rw [marginal, marginal, obs_2, dStar_2]
  interval_cases d 2 <;> norm_num [Nat.choose]

/-- The `TAA` marginal (observed count `1`) is maximized at `d = 1`. -/
theorem marg_TAA_le (d : Fin 8 → Nat) (hd : d 4 ≤ 6) :
    marginal obs d 4 ≤ marginal obs dStar 4 := by
  rw [marginal, marginal, obs_4, dStar_4]
  interval_cases d 4 <;> norm_num [Nat.choose]

/-- Each marginal is nonnegative on the domain `0 ≤ d ≤ 6`. -/
theorem marginal_nonneg (d : Fin 8 → Nat) (hd : ∀ c : Fin 8, d c ≤ 6) (c : Fin 8) :
    0 ≤ marginal obs d c := by
  have hb := hd c
  rw [marginal]
  have h2 : (0 : ℚ) ≤ 1 - (d c : ℚ) / 6 := by interval_cases d c <;> norm_num
  positivity

theorem marginal_pos_dStar (c : Fin 8) (hc : c ∈ relevant) :
    0 < marginal obs dStar c := by
  rw [relevant, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
    Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · rw [marginal, obs_0, dStar_0]; norm_num [Nat.choose]
  · rw [marginal, obs_1, dStar_1]; norm_num [Nat.choose]
  · rw [marginal, obs_2, dStar_2]; norm_num [Nat.choose]
  · rw [marginal, obs_4, dStar_4]; norm_num [Nat.choose]

/-- **`d*` maximizes the §6.1 objective over its whole domain `1 ≤ d ≤ 6`,
restricted to throughput vectors that vanish off the observed support (as every
§6.2 flow's throughput vector does). -/
theorem lik_le_dStar (d : Fin 8 → Nat) (hd : ∀ c : Fin 8, d c ≤ 6)
    (hd0 : ∀ c : Fin 8, c ∉ relevant → d c = 0) :
    lik obs d ≤ lik obs dStar := by
  rw [lik_eq_relevant_prod obs d (fun c hc => ⟨(truth_zero_off c hc).1, hd0 c hc⟩),
    lik_obs_dStar, relevant_prod_eq]
  have h0 := marg_AAA_le d (hd 0)
  have h1 := marg_AAT_le d (hd 1)
  have h2 := marg_ATA_le d (hd 2)
  have h4 := marg_TAA_le d (hd 4)
  have p0 := marginal_pos_dStar 0 (by decide)
  have p1 := marginal_pos_dStar 1 (by decide)
  have p2 := marginal_pos_dStar 2 (by decide)
  have p4 := marginal_pos_dStar 4 (by decide)
  have n0 := marginal_nonneg d hd 0
  have n1 := marginal_nonneg d hd 1
  have n2 := marginal_nonneg d hd 2
  have n4 := marginal_nonneg d hd 4
  gcongr

/-- The `AAA` marginal equality forces `d 0 = 2`. -/
theorem marg_AAA_eq (d : Fin 8 → Nat) (hd : d 0 ≤ 6) :
    marginal obs d 0 = marginal obs dStar 0 → d 0 = 2 := by
  rw [marginal, marginal, obs_0, dStar_0]
  interval_cases d 0 <;> norm_num [Nat.choose]

/-- The `AAT` marginal equality forces `d 1 = 1`. -/
theorem marg_AAT_eq (d : Fin 8 → Nat) (hd : d 1 ≤ 6) :
    marginal obs d 1 = marginal obs dStar 1 → d 1 = 1 := by
  rw [marginal, marginal, obs_1, dStar_1]
  interval_cases d 1 <;> norm_num [Nat.choose]

/-- The `ATA` marginal equality forces `d 2 = 1`. -/
theorem marg_ATA_eq (d : Fin 8 → Nat) (hd : d 2 ≤ 6) :
    marginal obs d 2 = marginal obs dStar 2 → d 2 = 1 := by
  rw [marginal, marginal, obs_2, dStar_2]
  interval_cases d 2 <;> norm_num [Nat.choose]

/-- The `TAA` marginal equality forces `d 4 = 1`. -/
theorem marg_TAA_eq (d : Fin 8 → Nat) (hd : d 4 ≤ 6) :
    marginal obs d 4 = marginal obs dStar 4 → d 4 = 1 := by
  rw [marginal, marginal, obs_4, dStar_4]
  interval_cases d 4 <;> norm_num [Nat.choose]

/-! ### Uniqueness of the maximizer

If four nonnegative factors are each bounded by a positive factor and the two
products agree, then every factor equals its bound.  This is the engine behind
the uniqueness of `d*`: the §6.1 objective is a product of four marginals, each
maximized at the corresponding `d*` coordinate. -/

lemma eq_of_mul_eq_mul_right' {x X y : ℚ} (hy : 0 < y) (h : x * y = X * y) : x = X := by
  have hy' : y ≠ 0 := ne_of_gt hy
  field_simp [hy'] at h
  exact h

lemma eq_of_mul_eq_mul_left' {x X y : ℚ} (hx : 0 < x) (h : x * y = x * X) : y = X := by
  have hx' : x ≠ 0 := ne_of_gt hx
  field_simp [hx'] at h
  exact h

lemma prod4_eq_of_le {a A b B c C e E : ℚ}
    (_ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (he0 : 0 ≤ e)
    (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C) (he : e ≤ E)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hE : 0 < E)
    (h : a * (b * (c * e)) = A * (B * (C * E))) :
    a = A ∧ b = B ∧ c = C ∧ e = E := by
  have hpos : 0 < A * (B * (C * E)) := mul_pos hA (mul_pos hB (mul_pos hC hE))
  have bce_nn : 0 ≤ b * (c * e) := mul_nonneg hb0 (mul_nonneg hc0 he0)
  have htail : 0 < b * (c * e) := by
    by_contra hcon
    have hbce0 : b * (c * e) = 0 := le_antisymm (not_lt.mp hcon) bce_nn
    rw [hbce0, mul_zero] at h
    linarith [h, hpos]
  have bce_le : b * (c * e) ≤ B * (C * E) := by
    have h1 : b * (c * e) ≤ B * (c * e) := mul_le_mul_of_nonneg_right hb (mul_nonneg hc0 he0)
    have h2 : B * (c * e) ≤ B * (C * e) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc he0) (le_of_lt hB)
    have h3 : B * (C * e) ≤ B * (C * E) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (le_of_lt hC)) (le_of_lt hB)
    linarith [h1, h2, h3]
  have haA : a = A := by
    have hle : a * (b * (c * e)) ≤ A * (b * (c * e)) := mul_le_mul_of_nonneg_right ha bce_nn
    have hge : A * (b * (c * e)) ≤ a * (b * (c * e)) := by
      rw [h]; exact mul_le_mul_of_nonneg_left bce_le (le_of_lt hA)
    exact eq_of_mul_eq_mul_right' htail (le_antisymm hle hge)
  have hbce : b * (c * e) = B * (C * E) := by
    rw [haA] at h
    exact eq_of_mul_eq_mul_left' hA h
  have ce_nn : 0 ≤ c * e := mul_nonneg hc0 he0
  have hce : 0 < c * e := by
    by_contra hcon
    have hce0 : c * e = 0 := le_antisymm (not_lt.mp hcon) ce_nn
    have hA0 : A * (B * (C * E)) = 0 := by
      have h3 : B * (C * E) = 0 := by
        have h4 : b * (c * e) = 0 := by rw [hce0]; ring
        linarith [hbce, h4]
      rw [h3]; ring
    linarith [hA0, hpos]
  have hbB : b = B := by
    have hle : b * (c * e) ≤ B * (c * e) := mul_le_mul_of_nonneg_right hb ce_nn
    have hge : B * (c * e) ≤ b * (c * e) := by
      rw [hbce]
      apply mul_le_mul_of_nonneg_left
      · exact le_trans (mul_le_mul_of_nonneg_right hc he0)
          (mul_le_mul_of_nonneg_left he (le_of_lt hC))
      · exact le_of_lt hB
    exact eq_of_mul_eq_mul_right' hce (le_antisymm hle hge)
  have hce2 : c * e = C * E := by
    have h6 : B * (c * e) = B * (C * E) := by rw [hbB] at hbce; exact hbce
    exact eq_of_mul_eq_mul_left' hB h6
  have heE' : 0 < e := by
    by_contra hcon
    have he0' : e = 0 := le_antisymm (not_lt.mp hcon) he0
    have hA0 : A * (B * (C * E)) = 0 := by
      have h3 : B * (C * E) = 0 := by
        have h4 : c * e = 0 := by rw [he0']; ring
        have h5 : C * E = 0 := by linarith [hce2, h4]
        rw [h5]; ring
      rw [h3]; ring
    linarith [hA0, hpos]
  have hcC : c = C := by
    have hle : c * e ≤ C * e := mul_le_mul_of_nonneg_right hc he0
    have hge : C * e ≤ c * e := by
      rw [hce2]
      exact mul_le_mul_of_nonneg_left he (le_of_lt hC)
    exact eq_of_mul_eq_mul_right' heE' (le_antisymm hle hge)
  have heE'' : e = E := by
    rw [hcC] at hce2
    exact eq_of_mul_eq_mul_left' hC hce2
  exact ⟨haA, hbB, hcC, heE''⟩

/-- **`d*` is the *unique* global maximizer**: attaining the bound forces the
throughput to be exactly `d*` on the support. -/
theorem dStar_argmax (d : Fin 8 → Nat) (hd : ∀ c : Fin 8, d c ≤ 6)
    (hd0 : ∀ c : Fin 8, c ∉ relevant → d c = 0) :
    lik obs d = lik obs dStar → d 0 = 2 ∧ d 1 = 1 ∧ d 2 = 1 ∧ d 4 = 1 := by
  intro heq
  have h0 := marg_AAA_le d (hd 0)
  have h1 := marg_AAT_le d (hd 1)
  have h2 := marg_ATA_le d (hd 2)
  have h4 := marg_TAA_le d (hd 4)
  have p0 := marginal_pos_dStar 0 (by decide)
  have p1 := marginal_pos_dStar 1 (by decide)
  have p2 := marginal_pos_dStar 2 (by decide)
  have p4 := marginal_pos_dStar 4 (by decide)
  have n0 := marginal_nonneg d hd 0
  have n1 := marginal_nonneg d hd 1
  have n2 := marginal_nonneg d hd 2
  have n4 := marginal_nonneg d hd 4
  rw [lik_eq_relevant_prod obs d (fun c hc => ⟨(truth_zero_off c hc).1, hd0 c hc⟩),
    lik_obs_dStar, relevant_prod_eq] at heq
  have key := prod4_eq_of_le n0 n1 n2 n4 h0 h1 h2 h4 p0 p1 p2 p4 heq
  exact ⟨marg_AAA_eq d (hd 0) key.1,
    marg_AAT_eq d (hd 1) key.2.1,
    marg_ATA_eq d (hd 2) key.2.2.1,
    marg_TAA_eq d (hd 4) key.2.2.2⟩

/-! ## The truth is strictly beaten -/

theorem lik_dStar_over_truth : lik obs dStar / lik obs dS = (1280 : ℚ) / 243 := by
  rw [lik_truth, lik_obs_dStar]
  norm_num [marginal, obs_0, obs_1, obs_2, obs_4, dS_0, dS_1, dS_2, dS_4,
    dStar_0, dStar_1, dStar_2, dStar_4, Nat.choose]

theorem lik_truth_pos' : 0 < lik obs dS := by
  rw [lik_truth]
  norm_num [marginal, obs_0, obs_1, obs_2, obs_4, dS_0, dS_1, dS_2, dS_4, Nat.choose]

theorem star_better : lik obs dS < lik obs dStar := by
  have h := lik_dStar_over_truth
  have hpos := lik_truth_pos'
  rw [div_eq_iff (ne_of_gt hpos)] at h
  rw [h]
  nlinarith

/-! ## Main theorem -/

/-- **At full overlap `o_min = L − 1`, an explicit `I_s`-bridged disconnected
feasible optimum exists.**  Under the literal Medvedev–Brudno §6.2 object:

1. the bridging hypothesis `I_s` holds at full strength for the truth `AAATAT`
   with the realized placements `{0, 1, 3, 5}` (start `0` sampled twice, so the
   `n = 5` reads have multiplicities `x = (AAA:2, AAT:1, ATA:1, TAA:1)`);
2. the truth is an admissible §6.2 flow with the throughputs `d_S`;
3. another admissible §6.2 flow `discFlow` has throughputs `d* = (2,1,1,1)`,
   which is the *unique* global maximizer of the §6.1 objective over its whole
   domain `1 ≤ d ≤ N`, and whose positive support is **disconnected**;
4. the truth is strictly beaten (ratio `1280/243`).

So a genuine optimum of the full §6.2 flow optimizer need not be positive-support
connected: "positive-support connectedness of all optima" is **false** at
`o_min = L − 1`.  This is distinct from the `o_min = 1` non-spellable
counterexample, because here the optimal throughput `d*` *is* a genome spectrum
(`AAAAT`); the phenomenon is disconnectedness of the *flow*, not
non-spellability of the *throughput*. -/
theorem full_overlap_disconnected_optimum :
    SourceFaithfulIs.InformationFeasible truthGenome 3 realizedStarts ∧
      Feasible62 Base Strand3 rep3 readVerts graphList truthCircuitFlow noTerm dS' ∧
      Feasible62 Base Strand3 rep3 readVerts graphList discFlow noTerm dStar' ∧
      PortBalanced discFlow = true ∧
      supportDisconnected discFlow ∧
      (∀ d : Fin 8 → Nat, (∀ c : Fin 8, d c ≤ 6) →
        (∀ c : Fin 8, c ∉ relevant → d c = 0) → lik obs d ≤ lik obs dStar) ∧
      (∀ d : Fin 8 → Nat, (∀ c : Fin 8, d c ≤ 6) →
        (∀ c : Fin 8, c ∉ relevant → d c = 0) →
        lik obs d = lik obs dStar → d 0 = 2 ∧ d 1 = 1 ∧ d 2 = 1 ∧ d 4 = 1) ∧
      lik obs dS < lik obs dStar :=
  ⟨truth_information_feasible, truth_feasible62, disc_feasible62, disc_port_balanced,
    disc_support_disconnected, lik_le_dStar, dStar_argmax, star_better⟩

end AssemblyP1.Section62FullOverlapDisconnected
