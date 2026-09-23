import Mathlib
import AssemblyP1.OrientedRigidity

/-!
# Population normalized-to-ordinary spectrum reduction (primitive P2)

Mathematical source: `paper/sections/05-population.tex` and
`docs/maximum-likelihood-models-for-genome-assembly.md` §6.

This file kernel-checks the reusable arithmetic core of the population
reduction, the AssemblyP1-original primitive-P2 division–Eulerian
derivation of gcd-one (conditional on explicit spelling/uniqueness
premises), and a regression showing primitivity alone is insufficient.
External mathematical inputs are kept as **explicit hypotheses**,
never as axioms:

* **Gibbs/KL tie characterization** (Cover–Thomas): a population tie
  `ℓpop_S(D) = ℓpop_S(S)` holds iff the normalized spectra agree.
  Gibbs itself stays outside this file; theorems below take the
  resulting normalized equality (`NormalizedEqual`) as a premise.
* **Eulerian spelling of a divided balanced connected spectrum**
  (standard Eulerian-circuit existence applied to the paper's divided
  circulation `c/g`): stated as an explicit premise `hSpell`.
* **Bresler–Bresler–Tse (2013), Theorem 3** complete-spectrum
  uniqueness at `K = L - 1`: an explicit premise `hBBT`.

What is fully proved here:
* `normalized_to_ordinary`: proportional gcd-one integer spectrum
  vectors are equal (hence the two lengths agree).
* Circulation division (`divided_balanced`, `divided_sum`,
  `divided_support`): dividing a balanced integer circulation by a
  common divisor preserves balance, scales the total, and preserves
  support — the project-side division half of `lem:scaling`.
* Power lifting (`pow_spec_of_spell`): a spelling `W` of the quotient
  lifts to `spec (power W g) = spec S` via the explicit power-scale
  interface — the project-side repeated-spectrum identity.
* `gcd_one_of_primitive_P2`: from those project-side steps plus BBT
  uniqueness, primitivity, its rotation-invariance, and
  non-primitivity of nontrivial powers, derive `IsGcdOne`.
* `population_uniqueness_primitive_P2`: the end-to-end project-level
  reduction (normalized equality → ordinary equality → rotation
  equivalence) under the same premises.
The regression (`primitivity_insufficient`) shows the
gcd-one conclusion cannot be obtained from primitivity alone:
primitive `S = AAB` (`|S| = 3`) and `D = AAABAB` (`|D| = 6`) share
normalized 2-spectra but not ordinary 2-spectra.
-/

namespace AssemblyP1.PopulationReduction

variable {W : Type*} [Fintype W]

/-- Gcd-one over all entries (zeros contribute nothing: every `g`
divides `0`, so this is the gcd of the positive entries). -/
def IsGcdOne (c : W → ℕ) : Prop :=
  ∀ g : ℕ, (∀ w : W, g ∣ c w) → g = 1

/-- Normalized-spectrum equality, stated multiplicatively to avoid
division: `c(w)/n = d(w)/m` for every word `w`. -/
def NormalizedEqual (c d : W → ℕ) (n m : ℕ) : Prop :=
  ∀ w : W, c w * m = d w * n

theorem normalized_to_ordinary {c d : W → ℕ} {n m : ℕ}
    (hn : 0 < n) (_hm : 0 < m)
    (_hS : ∑ w : W, c w = n) (_hD : ∑ w : W, d w = m)
    (hNorm : NormalizedEqual c d n m)
    (hGcdC : IsGcdOne c) (hGcdD : IsGcdOne d) :
    n = m ∧ c = d := by
  -- Let `g = gcd n m`, `n₁ = n / g`, `m₁ = m / g` coprime.
  set g := Nat.gcd n m with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left m hn
  have hcop : Nat.Coprime (n / g) (m / g) :=
    Nat.coprime_div_gcd_div_gcd hgpos
  have hn_eq : g * (n / g) = n := Nat.mul_div_cancel' (Nat.gcd_dvd_left n m)
  have hm_eq : g * (m / g) = m := Nat.mul_div_cancel' (Nat.gcd_dvd_right n m)
  -- From `c w * m = d w * n` cancel `g`.
  have hcancel : ∀ w : W, c w * (m / g) = d w * (n / g) := by
    intro w
    have h := hNorm w
    rw [← hm_eq, ← hn_eq] at h
    have h2 : (c w * (m / g)) * g = (d w * (n / g)) * g := by
      linear_combination h
    exact Nat.mul_right_cancel hgpos h2
  -- `n/g ∣ c w` for every `w`, since `n/g ∣ d w * (n/g) = c w * (m/g)` and coprime.
  have hn₁_dvd : ∀ w : W, (n / g) ∣ c w := by
    intro w
    have h1 : (n / g) ∣ c w * (m / g) := by
      rw [hcancel w]
      exact dvd_mul_left _ _
    exact (Nat.Coprime.dvd_of_dvd_mul_right hcop h1)
  have hm₁_dvd : ∀ w : W, (m / g) ∣ d w := by
    intro w
    have h1 : (m / g) ∣ d w * (n / g) := by
      rw [← hcancel w]
      exact dvd_mul_left _ _
    exact (Nat.Coprime.dvd_of_dvd_mul_right hcop.symm h1)
  have hn₁ : n / g = 1 := hGcdC (n / g) hn₁_dvd
  have hm₁ : m / g = 1 := hGcdD (m / g) hm₁_dvd
  have hnm : n = m := by
    calc n = g * (n / g) := hn_eq.symm
    _ = g * (m / g) := by rw [hn₁, hm₁]
    _ = m := hm_eq
  refine ⟨hnm, ?_⟩
  funext w
  have h := hcancel w
  rw [hn₁, hm₁, mul_one, mul_one] at h
  exact h

/--
Explicit-hypothesis wrapper recording the paper's proof chain.
`hNormEq` is normalized-spectrum equality, the conclusion of the
external Gibbs/KL input (Cover–Thomas: tie iff normalized equality),
which itself stays outside this file; `hGcdS`/`hGcdD` are the
gcd-one facts discharged by `gcd_one_of_primitive_P2` via the
division–Eulerian argument under explicit Eulerian-spelling and BBT
premises (see below); `hBBT` in the uniqueness theorem is
Bresler–Bresler–Tse (2013) Theorem 3 at `K = L - 1`. No external fact
is hidden: each is a universally quantified hypothesis.
-/
theorem population_tie_reduction {cS cD : W → ℕ} {nS nD : ℕ}
    (hnS : 0 < nS) (hnD : 0 < nD)
    (hSumS : ∑ w : W, cS w = nS) (hSumD : ∑ w : W, cD w = nD)
    (hNormEq : NormalizedEqual cS cD nS nD)
    (hGcdS : IsGcdOne cS) (hGcdD : IsGcdOne cD) :
    nS = nD ∧ cS = cD :=
  normalized_to_ordinary hnS hnD hSumS hSumD hNormEq hGcdS hGcdD

/-- BBT uniqueness step with the external theorem explicit. -/
theorem population_uniqueness_of_ordinary {Genome V : Type*}
    (cS cD : V → ℕ)
    (hOrd : cS = cD)
    (rotEquiv : Genome → Genome → Prop)
    (S D : Genome)
    (hBBT : cS = cD → rotEquiv D S) :
    rotEquiv D S :=
  hBBT hOrd

-- ---------------------------------------------------------------------------
-- AssemblyP1-original primitive-P2 division–Eulerian gcd-one mechanism.
-- Paper source: `paper/sections/05-population.tex`, proof of
-- `lem:scaling`, via `thm:BBT` (Bresler–Bresler–Tse 2013, Theorem 3).
--
-- The Eulerian closed-trail theorem below (`eulerian_closed_trail`,
-- Hierholzer's theorem for finite balanced weakly-connected integer
-- circulations) is proved in Lean from scratch: Mathlib has no Eulerian
-- machinery, so the project-side division/Eulerian step is
-- kernel-checked rather than assumed. The circular power-word scaling
-- identity (`powerSpec`) is likewise proved from the circular-word
-- structure of issue #69's `WordLayer`. The only external mathematical
-- input remaining is complete-spectrum uniqueness `hBBT`
-- (Bresler–Bresler–Tse 2013, Theorem 3). Gcd-one itself is never assumed.
-- ---------------------------------------------------------------------------

section EulerianTrail

variable {V E : Type} [DecidableEq V] [DecidableEq E] [Fintype E]
variable (tail head : E → V)

/-- Out-edges of `v` (all of them; availability is tracked separately). -/
def eOut (v : V) : Finset E := Finset.univ.filter (fun e => tail e = v)

/-- In-edges of `v`. -/
def eIn (v : V) : Finset E := Finset.univ.filter (fun e => head e = v)

/-- Edge usage of a trail: multiplicity of `e` in `T`. -/
def edgeUse (T : List E) (e : E) : ℕ :=
  T.countP (fun x => decide (x = e))

/-- Out-usage at `v`: used out-edges counted with multiplicity. -/
def outUse (T : List E) (v : V) : ℕ :=
  ∑ e ∈ eOut tail v, edgeUse T e

/-- In-usage at `v`. -/
def inUse (T : List E) (v : V) : ℕ :=
  ∑ e ∈ eIn head v, edgeUse T e

/-- Balance of an availability function (integer circulation). -/
def CircBalanced (q : E → ℕ) : Prop :=
  ∀ v : V, ∑ e ∈ eOut tail v, q e = ∑ e ∈ eIn head v, q e

/-- Vertices visited by a trail. -/
def TVerts (T : List E) (u : V) : Prop :=
  ∃ e ∈ T, tail e = u ∨ head e = u

/-- Directed trails with endpoints. -/
inductive TrailEnds : List E → V → V → Prop
  | nil (s : V) : TrailEnds [] s s
  | cons (e : E) (T : List E) (s t : V) (hte : tail e = s)
      (hT : TrailEnds T (head e) t) : TrailEnds (e :: T) s t

/-- Undirected vertex paths inside a support edge set. -/
inductive UPath (supp : Finset E) : List E → V → V → Prop
  | nil (u : V) : UPath supp [] u u
  | fwd (f : E) (P : List E) (u v : V) (hf : f ∈ supp)
      (hte : tail f = u) (hP : UPath supp P (head f) v) :
      UPath supp (f :: P) u v
  | bwd (f : E) (P : List E) (u v : V) (hf : f ∈ supp)
      (hhe : head f = u) (hP : UPath supp P (tail f) v) :
      UPath supp (f :: P) u v

/-- Weak connectivity of a support edge set: any two incident vertices
are joined by an undirected path. -/
def WeakConn (supp : Finset E) : Prop :=
  ∀ u v : V, (∃ e ∈ supp, tail e = u ∨ head e = u) →
    (∃ e ∈ supp, tail e = v ∨ head e = v) → ∃ P, UPath tail head supp P u v

omit [Fintype E] in
theorem edgeUse_nil (e : E) : edgeUse ([] : List E) e = 0 := rfl

omit [Fintype E] in
theorem edgeUse_cons (a : E) (T' : List E) (e : E) :
    edgeUse (a :: T') e = edgeUse T' e + (if a = e then 1 else 0) := by
  unfold edgeUse
  rw [List.countP_cons]
  by_cases h : a = e <;> simp [h]

omit [Fintype E] in
/-- Indicator sum over a finset: only the given member contributes. -/
private theorem sum_ite_self (s : Finset E) (a : E) :
    ∑ x ∈ s, (if a = x then 1 else 0) = (if a ∈ s then 1 else 0) := by
  by_cases h : a ∈ s
  · have e1 : (if a ∈ s then (1 : ℕ) else 0) = 1 := by simp [h]
    rw [e1]
    calc ∑ x ∈ s, (if a = x then 1 else 0)
        = (if a = a then 1 else 0) :=
          Finset.sum_eq_single a
            (fun x _ hxa => by simp [Ne.symm hxa])
            (fun hcon => absurd h hcon)
      _ = 1 := by simp
  · have e0 : (if a ∈ s then (1 : ℕ) else 0) = 0 := by simp [h]
    rw [e0]
    apply Finset.sum_eq_zero
    intro x hx
    have hne : a ≠ x := fun he => h (he.symm ▸ hx)
    simp [hne]

theorem outUse_nil (v : V) : outUse tail ([] : List E) v = 0 := by
  unfold outUse
  simp [edgeUse]

theorem inUse_nil (v : V) : inUse head ([] : List E) v = 0 := by
  unfold inUse
  simp [edgeUse]

theorem outUse_cons (a : E) (T' : List E) (v : V) :
    outUse tail (a :: T') v
      = outUse tail T' v + (if tail a = v then 1 else 0) := by
  unfold outUse
  have h : ∀ x ∈ eOut tail v,
      edgeUse (a :: T') x = edgeUse T' x + (if a = x then 1 else 0) :=
    fun x _ => edgeUse_cons a T' x
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, sum_ite_self]
  congr 1
  by_cases hmv : tail a = v
  · have hm : a ∈ eOut tail v :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmv⟩
    simp [hm, hmv]
  · have hm : a ∉ eOut tail v :=
      fun hh => hmv (Finset.mem_filter.mp hh).2
    simp [hm, hmv]

theorem inUse_cons (a : E) (T' : List E) (v : V) :
    inUse head (a :: T') v
      = inUse head T' v + (if head a = v then 1 else 0) := by
  unfold inUse
  have h : ∀ x ∈ eIn head v,
      edgeUse (a :: T') x = edgeUse T' x + (if a = x then 1 else 0) :=
    fun x _ => edgeUse_cons a T' x
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, sum_ite_self]
  congr 1
  by_cases hmv : head a = v
  · have hm : a ∈ eIn head v :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmv⟩
    simp [hm, hmv]
  · have hm : a ∉ eIn head v :=
      fun hh => hmv (Finset.mem_filter.mp hh).2
    simp [hm, hmv]

omit [Fintype E] in
theorem edgeUse_append (A B : List E) (e : E) :
    edgeUse (A ++ B) e = edgeUse A e + edgeUse B e := by
  unfold edgeUse
  rw [List.countP_append]

theorem outUse_append (A B : List E) (v : V) :
    outUse tail (A ++ B) v = outUse tail A v + outUse tail B v := by
  unfold outUse
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  exact edgeUse_append A B x

theorem inUse_append (A B : List E) (v : V) :
    inUse head (A ++ B) v = inUse head A v + inUse head B v := by
  unfold inUse
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  exact edgeUse_append A B x

/-- A trail's length is the total edge usage. -/
theorem length_eq_sum_edgeUse (T : List E) :
    T.length = ∑ e ∈ Finset.univ, edgeUse T e := by
  induction T with
  | nil => simp [edgeUse]
  | cons a T' ih =>
    have h : ∀ x ∈ (Finset.univ : Finset E),
        edgeUse (a :: T') x = edgeUse T' x + (if a = x then 1 else 0) :=
      fun x _ => edgeUse_cons a T' x
    have h1 : ∑ x ∈ (Finset.univ : Finset E), (if a = x then 1 else 0) = 1 := by
      rw [sum_ite_self]
      simp only [Finset.mem_univ, ite_true]
    rw [List.length_cons, Finset.sum_congr rfl h,
      Finset.sum_add_distrib, ← ih, h1, add_comm]

/-- Endpoint flow balance of a trail: out-use minus in-use is `+1` at
the start, `-1` at the end, `0` elsewhere. -/
theorem trail_count {T : List E} {s t : V} (h : TrailEnds tail head T s t)
    (v : V) :
    (outUse tail T v : ℤ) - (inUse head T v : ℤ)
      = (if s = v then 1 else 0) - (if t = v then 1 else 0) := by
  induction h with
  | nil s => simp [outUse_nil, inUse_nil]
  | cons e T' s t hte _ ih =>
    rw [outUse_cons, inUse_cons]
    push_cast
    rw [hte]
    by_cases q1 : s = v <;> by_cases q2 : head e = v <;> by_cases q3 : t = v <;>
      simp only [q1, q2, q3, ite_true, ite_false] at ih ⊢ <;> omega

/-- A closed trail's usage is balanced at every vertex. -/
theorem trail_closed_balanced {T : List E} {s : V}
    (h : TrailEnds tail head T s s) (v : V) :
    outUse tail T v = inUse head T v := by
  have h := trail_count tail head h v
  have hz : (if s = v then (1 : ℤ) else 0) - (if s = v then 1 else 0) = 0 :=
    sub_self _
  rw [hz] at h
  omega

omit [DecidableEq V] [DecidableEq E] [Fintype E] in
/-- Appending consecutive trails. -/
theorem trail_append {A B : List E} {s u t : V}
    (hA : TrailEnds tail head A s u) (hB : TrailEnds tail head B u t) :
    TrailEnds tail head (A ++ B) s t := by
  revert hB
  induction hA with
  | nil s =>
    intro hB
    simpa using hB
  | cons e A' s u' hte _ ih =>
    intro hB
    exact .cons e (A' ++ B) s t hte (ih hB)

omit [DecidableEq V] [DecidableEq E] [Fintype E] in
/-- Appending a single edge at the end. -/
theorem trail_append_single {T : List E} {s t : V} {e : E}
    (hT : TrailEnds tail head T s t) (hte : tail e = t) :
    TrailEnds tail head (T ++ [e]) s (head e) :=
  trail_append tail head hT (.cons e [] t (head e) hte (.nil _))

omit [DecidableEq V] [DecidableEq E] [Fintype E] in
/-- A trail through `u` splits into `s ⇝ u` and `u ⇝ t`. -/
theorem trail_split_visit {T : List E} {s t u : V}
    (h : TrailEnds tail head T s t)
    (hvisit : ∃ e ∈ T, tail e = u ∨ head e = u) :
    ∃ A B, T = A ++ B ∧ TrailEnds tail head A s u ∧
      TrailEnds tail head B u t := by
  revert u
  induction h with
  | nil s =>
    intro u hvisit
    obtain ⟨f, hf, _⟩ := hvisit
    exact absurd hf List.not_mem_nil
  | cons e T' s t hte hT' ih =>
    intro u hvisit
    obtain ⟨f, hf, hfu⟩ := hvisit
    rw [List.mem_cons] at hf
    rcases hf with hfe | hfT'
    · subst hfe
      rcases hfu with htu | huu
      · have hsu : s = u := hte.symm.trans htu
        subst hsu
        exact ⟨[], f :: T', rfl, .nil _, .cons f T' _ _ hte hT'⟩
      · subst huu
        exact ⟨[f], T', rfl,
          .cons f [] s (head f) hte (.nil _), hT'⟩
    · obtain ⟨A', B', hAB', hA', hB'⟩ := ih ⟨f, hfT', hfu⟩
      exact ⟨e :: A', B', by rw [hAB', List.cons_append],
        .cons e A' s u hte hA', hB'⟩

omit [DecidableEq V] [DecidableEq E] [Fintype E] in
/-- Appending undirected paths. -/
theorem upath_append {supp : Finset E} {P Q : List E} {u w v : V}
    (hP : UPath tail head supp P u w) (hQ : UPath tail head supp Q w v) :
    UPath tail head supp (P ++ Q) u v := by
  revert hQ
  induction hP with
  | nil u =>
    intro hQ
    simpa using hQ
  | fwd f P' u w' hf hte _ ih =>
    intro hQ
    exact .fwd f (P' ++ Q) u v hf hte (ih hQ)
  | bwd f P' u w' hf hhe _ ih =>
    intro hQ
    exact .bwd f (P' ++ Q) u v hf hhe (ih hQ)

omit [DecidableEq V] [DecidableEq E] [Fintype E] in
/-- Directed reachability yields an undirected path. -/
theorem reachable_to_upath {edges supp : Finset E}
    (hsub : edges ⊆ supp)
    {u v : V} (h : OrientedRigidity.Reachable tail head edges u v) :
    ∃ P, UPath tail head supp P u v := by
  induction h with
  | refl => exact ⟨[], .nil _⟩
  | step f _ hmem htw hhw ih =>
    obtain ⟨P, hP⟩ := ih
    refine ⟨P ++ [f], hhw ▸ upath_append tail head hP ?_⟩
    exact .fwd f [] _ _ (hsub hmem) htw (.nil _)

/-- Maximal trails end at their start: if every out-edge of the end
is exhausted and availability is balanced, the end equals the start.
Otherwise out-use would exceed in-use at the end. -/
theorem maximal_end_start {q' : E → ℕ} (hbal : CircBalanced tail head q')
    {X : List E} {s' t : V} (hT : TrailEnds tail head X s' t)
    (hle : ∀ e, edgeUse X e ≤ q' e)
    (hstuck : ∀ e ∈ eOut tail t, edgeUse X e = q' e) :
    t = s' := by
  have hcount := trail_count tail head hT t
  have hOut : outUse tail X t = ∑ e ∈ eOut tail t, q' e :=
    Finset.sum_congr rfl (fun e he => hstuck e he)
  have hge : (inUse head X t : ℤ) ≤ (outUse tail X t : ℤ) := by
    have h1 : inUse head X t ≤ ∑ e ∈ eIn head t, q' e :=
      Finset.sum_le_sum (fun e _ => hle e)
    have h2 : ∑ e ∈ eOut tail t, q' e = ∑ e ∈ eIn head t, q' e := hbal t
    omega
  by_contra hne
  have hne' : s' ≠ t := fun h => hne h.symm
  have e1 : (if s' = t then (1 : ℤ) else 0) = 0 := by simp [hne']
  have e2 : (if t = t then (1 : ℤ) else 0) = 1 := by simp
  rw [e1, e2] at hcount
  omega

omit [DecidableEq E] in
/-- Subtracting a balanced sub-circulation preserves balance. -/
theorem balanced_sub {q u : E → ℕ} (hbal : CircBalanced tail head q)
    (hbalu : ∀ v : V, ∑ e ∈ eOut tail v, u e = ∑ e ∈ eIn head v, u e)
    (hle : ∀ e : E, u e ≤ q e) :
    CircBalanced tail head (fun e => q e - u e) := by
  intro v
  show ∑ e ∈ eOut tail v, (q e - u e) = ∑ e ∈ eIn head v, (q e - u e)
  have key : ∀ s : Finset E,
      ∑ e ∈ s, (q e - u e) + ∑ e ∈ s, u e = ∑ e ∈ s, q e := by
    intro s
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => Nat.sub_add_cancel (hle x))
  have h1 := key (eOut tail v)
  have h2 := key (eIn head v)
  have hq := hbal v
  have hu := hbalu v
  omega

/-- Find an available out-edge of `t` (one used strictly below quota). -/
noncomputable def findAvail (q : E → ℕ) (T : List E) (t : V) : Option E :=
  (eOut tail t).toList.find? (fun e => decide (edgeUse T e < q e))

theorem findAvail_some_mem {q : E → ℕ} {T : List E} {t : V}
    {ee : E} (h : findAvail tail q T t = some ee) :
    ee ∈ eOut tail t := by
  unfold findAvail at h
  exact Finset.mem_toList.mp (List.mem_of_find?_eq_some h)

theorem findAvail_some_lt {q : E → ℕ} {T : List E} {t : V} {ee : E}
    (h : findAvail tail q T t = some ee) : edgeUse T ee < q ee := by
  unfold findAvail at h
  have h2 := List.find?_some h
  exact of_decide_eq_true h2

theorem findAvail_none_le {q : E → ℕ} {T : List E} {t : V}
    (h : findAvail tail q T t = none) (x : E) (hx : x ∈ eOut tail t) :
    q x ≤ edgeUse T x := by
  unfold findAvail at h
  rw [List.find?_eq_none] at h
  have hx' : x ∈ (eOut tail t).toList := Finset.mem_toList.mpr hx
  have h2 := h x hx'
  by_contra hlt
  have hlt' : edgeUse T x < q x := Nat.not_le.mp hlt
  exact h2 (by simp [hlt'])

/-- Greedy maximal extension with fuel: extend while an available
out-edge exists at the current end. -/
noncomputable def grow (q : E → ℕ) : ℕ → List E → V → List E × V
  | 0, T, t => (T, t)
  | fuel + 1, T, t =>
    match findAvail tail q T t with
    | none => (T, t)
    | some e => grow q fuel (T ++ [e]) (head e)

theorem grow_succ (q : E → ℕ) (fuel : ℕ) (T : List E) (t : V) :
    grow tail head q (fuel + 1) T t =
      match findAvail tail q T t with
      | none => (T, t)
      | some e => grow tail head q fuel (T ++ [e]) (head e) := rfl

theorem grow_trail (q : E → ℕ) (fuel : ℕ) (X : List E) (s' t : V)
    (hT : TrailEnds tail head X s' t) :
    TrailEnds tail head (grow tail head q fuel X t).1 s'
      (grow tail head q fuel X t).2 := by
  induction fuel generalizing X t with
  | zero =>
    simpa [grow] using hT
  | succ fuel ih =>
    rw [grow_succ]
    cases hfind : findAvail tail q X t with
    | none =>
      simpa using hT
    | some e =>
      have he : tail e = t :=
        (Finset.mem_filter.mp (findAvail_some_mem tail hfind)).2
      show TrailEnds tail head (grow tail head q fuel (X ++ [e]) (head e)).1
        s' (grow tail head q fuel (X ++ [e]) (head e)).2
      exact ih (X ++ [e]) (head e) (trail_append_single tail head hT he)

theorem grow_le (q : E → ℕ) (fuel : ℕ) (X : List E) (t : V)
    (hle : ∀ e, edgeUse X e ≤ q e) :
    ∀ e, edgeUse (grow tail head q fuel X t).1 e ≤ q e := by
  induction fuel generalizing X t with
  | zero =>
    simpa [grow] using hle
  | succ fuel ih =>
    rw [grow_succ]
    cases hfind : findAvail tail q X t with
    | none =>
      simpa using hle
    | some e =>
      show ∀ e', edgeUse (grow tail head q fuel (X ++ [e]) (head e)).1 e' ≤ q e'
      apply ih
      intro x
      have hlt : edgeUse X e < q e := findAvail_some_lt tail hfind
      have hx := hle x
      rw [edgeUse_append]
      by_cases hxe : x = e
      · subst hxe
        have h1 : edgeUse [x] x = 1 := by simp [edgeUse]
        omega
      · have h0 : edgeUse [e] x = 0 := by simp [edgeUse, Ne.symm hxe]
        omega

/-- Growth outcome: either the end is stuck (all out-edges exhausted)
or the trail grew by the full fuel allowance. -/
theorem grow_outcome (q : E → ℕ) (fuel : ℕ) (X : List E) (s' t : V)
    (hT : TrailEnds tail head X s' t) :
    (∀ e ∈ eOut tail (grow tail head q fuel X t).2,
        q e ≤ edgeUse (grow tail head q fuel X t).1 e) ∨
      (grow tail head q fuel X t).1.length ≥ X.length + fuel := by
  induction fuel generalizing X t with
  | zero =>
    right
    simp [grow]
  | succ fuel ih =>
    rw [grow_succ]
    cases hfind : findAvail tail q X t with
    | none =>
      left
      show ∀ e ∈ eOut tail t, q e ≤ edgeUse X e
      intro e he
      exact findAvail_none_le tail hfind e he
    | some e =>
      have he : tail e = t :=
        (Finset.mem_filter.mp (findAvail_some_mem tail hfind)).2
      have hT' := trail_append_single tail head hT he
      have hih := ih (X ++ [e]) (head e) hT'
      rcases hih with hstuck | hlen
      · left
        show ∀ e' ∈ eOut tail
            (grow tail head q fuel (X ++ [e]) (head e)).2,
            q e' ≤ edgeUse (grow tail head q fuel (X ++ [e]) (head e)).1 e'
        exact hstuck
      · right
        show (grow tail head q fuel (X ++ [e]) (head e)).1.length ≥
          X.length + (fuel + 1)
        have hlen' : (grow tail head q fuel (X ++ [e]) (head e)).1.length ≥
            (X ++ [e]).length + fuel := hlen
        rw [List.length_append] at hlen'
        simp only [List.length_cons, List.length_nil] at hlen'
        omega

omit [DecidableEq V] in
/-- Connectivity search: if some edge is still unused, then some unused
edge touches a visited vertex. Paths ending in visited vertices start
in visited vertices (consumed edges lie on the trail), applied to a
path from the unused edge to the trail. -/
theorem search_incident {q : E → ℕ} {T : List E}
    (hle : ∀ e, edgeUse T e ≤ q e)
    (supp : Finset E) (hsupp : ∀ e ∈ supp, 0 < q e)
    (eStar : E) (hrem : edgeUse T eStar < q eStar)
    {P : List E} {u x : V} (hu : tail eStar = u)
    (hP : UPath tail head supp P u x) (hx : TVerts tail head T x) :
    ∃ e₁ u₁, edgeUse T e₁ < q e₁ ∧ (tail e₁ = u₁ ∨ head e₁ = u₁) ∧
      TVerts tail head T u₁ := by
  by_cases hC : ∃ e₁ u₁, edgeUse T e₁ < q e₁ ∧ (tail e₁ = u₁ ∨ head e₁ = u₁) ∧
      TVerts tail head T u₁
  · exact hC
  · exfalso
    have hclosed : ∀ (P : List E) (u x : V), UPath tail head supp P u x →
        TVerts tail head T x → TVerts tail head T u := by
      intro P u x hP
      induction hP with
      | nil u => exact id
      | fwd f P' u x hf hte _ ih =>
        intro hx
        have hmem : TVerts tail head T (head f) := ih hx
        by_cases hfrem : edgeUse T f < q f
        · exact absurd ⟨f, head f, hfrem, Or.inr rfl, hmem⟩ hC
        · have hqf : 0 < q f := hsupp f hf
          have hpos : 0 < edgeUse T f := by
            have := hle f
            omega
          have hfT : f ∈ T := by
            by_contra hc
            have hzero : edgeUse T f = 0 := by
              unfold edgeUse
              rw [List.countP_eq_zero]
              intro a ha hpa
              exact hc ((of_decide_eq_true hpa) ▸ ha)
            omega
          exact ⟨f, hfT, Or.inl hte⟩
      | bwd f P' u x hf hhe _ ih =>
        intro hx
        have hmem : TVerts tail head T (tail f) := ih hx
        by_cases hfrem : edgeUse T f < q f
        · exact absurd ⟨f, tail f, hfrem, Or.inl rfl, hmem⟩ hC
        · have hqf : 0 < q f := hsupp f hf
          have hpos : 0 < edgeUse T f := by
            have := hle f
            omega
          have hfT : f ∈ T := by
            by_contra hc
            have hzero : edgeUse T f = 0 := by
              unfold edgeUse
              rw [List.countP_eq_zero]
              intro a ha hpa
              exact hc ((of_decide_eq_true hpa) ▸ ha)
            omega
          exact ⟨f, hfT, Or.inr hhe⟩
    have huT := hclosed P u x hP hx
    rw [← hu] at huT
    exact hC ⟨eStar, tail eStar, hrem, Or.inl rfl, huT⟩

omit [DecidableEq V] [DecidableEq E] [Fintype E] in
/-- Trails from a fixed start have unique ends. -/
theorem trail_end_unique {T : List E} {s t₁ t₂ : V}
    (h₁ : TrailEnds tail head T s t₁) (h₂ : TrailEnds tail head T s t₂) :
    t₁ = t₂ := by
  induction h₁ with
  | nil s =>
    cases h₂ with
    | nil _ => rfl
  | cons e T' s t hte _ ih =>
    cases h₂ with
    | cons _ _ _ _ _ h₂' => exact ih h₂'

theorem grow_prefix (q : E → ℕ) (fuel : ℕ) (X : List E) (t : V) :
    ∃ S, (grow tail head q fuel X t).1 = X ++ S := by
  induction fuel generalizing X t with
  | zero => exact ⟨[], by simp [grow]⟩
  | succ fuel ih =>
    rw [grow_succ]
    cases hfind : findAvail tail q X t with
    | none => exact ⟨[], by simp⟩
    | some e =>
      show ∃ S, (grow tail head q fuel (X ++ [e]) (head e)).1 = X ++ S
      obtain ⟨S, hS⟩ := ih (X ++ [e]) (head e)
      exact ⟨[e] ++ S, by rw [hS, List.append_assoc]⟩

/-- A growth run with more fuel than total availability, restarted at a
vertex with an available out-edge, yields a closed trail plus progress:
the length-only outcome is impossible (pigeonhole), and the stuck
outcome closes at the start (maximality) with a forced first step. -/
theorem grow_closed_progress (q' : E → ℕ) (hbal' : CircBalanced tail head q')
    (fuel : ℕ) (X : List E) (s' t' : V) (hT : TrailEnds tail head X s' t')
    (hleX : ∀ e, edgeUse X e ≤ q' e)
    (hbig : X.length + fuel > ∑ e, q' e)
    (o : E) (ho_mem : o ∈ eOut tail t') (ho_lt : edgeUse X o < q' o) :
    TrailEnds tail head (grow tail head q' fuel X t').1 s' s' ∧
      X.length + 1 ≤ (grow tail head q' fuel X t').1.length := by
  have hRle : ∀ e, edgeUse (grow tail head q' fuel X t').1 e ≤ q' e :=
    grow_le tail head q' fuel X t' hleX
  have hbound : (grow tail head q' fuel X t').1.length ≤ ∑ e, q' e := by
    rw [length_eq_sum_edgeUse]
    exact Finset.sum_le_sum (fun e _ => hRle e)
  have hTR := grow_trail tail head q' fuel X s' t' hT
  rcases grow_outcome tail head q' fuel X s' t' hT with hstuck | hlen
  · have hEnd : (grow tail head q' fuel X t').2 = s' :=
      maximal_end_start tail head hbal' hTR hRle
        (fun e he => le_antisymm (hRle e) (hstuck e he))
    refine ⟨?_, ?_⟩
    · rw [hEnd] at hTR
      exact hTR
    · have hne : (grow tail head q' fuel X t').1 ≠ X := by
        intro hRX
        have hend : (grow tail head q' fuel X t').2 = t' := by
          have hTRX : TrailEnds tail head X s'
              (grow tail head q' fuel X t').2 := by
            rw [hRX] at hTR
            exact hTR
          exact trail_end_unique tail head hTRX hT
        have hstuck_t' : ∀ e ∈ eOut tail t',
            q' e ≤ edgeUse (grow tail head q' fuel X t').1 e := by
          intro e he
          have he' : e ∈ eOut tail (grow tail head q' fuel X t').2 := by
            rw [hend]
            exact he
          exact hstuck e he'
        have hcon := hstuck_t' o ho_mem
        rw [hRX] at hcon
        omega
      obtain ⟨S, hS⟩ := grow_prefix tail head q' fuel X t'
      have hSne : S ≠ [] := by
        intro h0
        apply hne
        rw [hS, h0, List.append_nil]
      have hSlen : 1 ≤ S.length := by
        have h0 : S.length ≠ 0 :=
          fun hz => hSne (List.eq_nil_of_length_eq_zero hz)
        omega
      rw [hS, List.length_append]
      omega
  · exfalso
    omega

/-- One Hierholzer step: if some support edge is unused, grow a closed
trail in the remaining circulation and splice it into the current
closed trail (or start fresh when empty). Returns `none` when done.
The returned trail carries its closedness, quota, and progress
proofs, so the outer loop needs no re-derivation. -/
noncomputable def eulerStep (q : E → ℕ) (supp : Finset E)
    (hbal : CircBalanced tail head q) (hconn : WeakConn tail head supp)
    (hsupp : ∀ e, e ∈ supp ↔ 0 < q e)
    (T : List E) (hleT : ∀ e, edgeUse T e ≤ q e)
    (hclosedT : ∃ s, TrailEnds tail head T s s) :
    Option { R : List E //
      (∃ s, TrailEnds tail head R s s) ∧ (∀ e, edgeUse R e ≤ q e) ∧
        T.length + 1 ≤ R.length } :=
  match hfind : supp.toList.find? (fun e => decide (edgeUse T e < q e)) with
  | none => none
  | some e₀ =>
    have hrem₀ : edgeUse T e₀ < q e₀ := by
      have h2 := List.find?_some hfind
      exact of_decide_eq_true h2
    have hmem₀ : e₀ ∈ supp :=
      Finset.mem_toList.mp (List.mem_of_find?_eq_some hfind)
    match T with
    | [] =>
      have hprog := grow_closed_progress tail head q hbal
        ((∑ e, q e) + 1) [] (tail e₀) (tail e₀) (.nil _)
        (fun e => by rw [edgeUse_nil]; exact Nat.zero_le _)
        (by simp only [List.length_nil, Nat.zero_add]; omega)
        e₀ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩) hrem₀
      have hle : ∀ e, edgeUse
          (grow tail head q ((∑ e, q e) + 1) [] (tail e₀)).1 e ≤ q e :=
        grow_le tail head q ((∑ e, q e) + 1) [] (tail e₀)
          (fun e => by rw [edgeUse_nil]; exact Nat.zero_le _)
      some ⟨(grow tail head q ((∑ e, q e) + 1) [] (tail e₀)).1,
        ⟨tail e₀, hprog.1⟩, hle, hprog.2⟩
    | f₀ :: T' =>
      have hf₀mem : f₀ ∈ f₀ :: T' := List.mem_cons.mpr (Or.inl rfl)
      have h1 : 1 ≤ edgeUse (f₀ :: T') f₀ := by
        unfold edgeUse
        by_contra hc
        have hz : (f₀ :: T').countP (fun x => decide (x = f₀)) = 0 := by omega
        rw [List.countP_eq_zero] at hz
        have h2 := hz f₀ hf₀mem
        simp at h2
      have hf₀supp : f₀ ∈ supp :=
        (hsupp f₀).mpr
          (Nat.lt_of_lt_of_le Nat.one_pos (le_trans h1 (hleT f₀)))
      have hP : ∃ P, UPath tail head supp P (tail e₀) (tail f₀) :=
        hconn (tail e₀) (tail f₀) ⟨e₀, hmem₀, Or.inl rfl⟩
          ⟨f₀, hf₀supp, Or.inl rfl⟩
      have hsearch : ∃ eu : E × V, edgeUse (f₀ :: T') eu.1 < q eu.1 ∧
          (tail eu.1 = eu.2 ∨ head eu.1 = eu.2) ∧
          TVerts tail head (f₀ :: T') eu.2 := by
        have hPc := Classical.choose_spec hP
        have hbase := search_incident tail head hleT supp
          (fun e he => (hsupp e).mp he) e₀ hrem₀ rfl hPc
          ⟨f₀, hf₀mem, Or.inl rfl⟩
        obtain ⟨e₁, u₁, hh1, hh2, hh3⟩ := hbase
        exact ⟨(e₁, u₁), hh1, hh2, hh3⟩
      have hbalT : ∀ v : V, outUse tail (f₀ :: T') v
          = inUse head (f₀ :: T') v := by
        obtain ⟨s, hs⟩ := hclosedT
        exact trail_closed_balanced tail head hs
      have hbalT' : ∀ v : V, ∑ e ∈ eOut tail v, edgeUse (f₀ :: T') e
          = ∑ e ∈ eIn head v, edgeUse (f₀ :: T') e := hbalT
      have hbalR : CircBalanced tail head
          (fun e => q e - edgeUse (f₀ :: T') e) :=
        balanced_sub tail head hbal hbalT' hleT
      have ho₁ : ∃ o₁, o₁ ∈ eOut tail (Classical.choose hsearch).2 ∧
          edgeUse (f₀ :: T') o₁ < q o₁ := by
        have heu := Classical.choose_spec hsearch
        rcases heu.2.1 with htail | hhead
        · exact ⟨(Classical.choose hsearch).1,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, htail⟩, heu.1⟩
        · have hrin : 0 < ∑ e ∈ eIn head (Classical.choose hsearch).2,
              (q e - edgeUse (f₀ :: T') e) := by
            have h1 : 0 < q (Classical.choose hsearch).1 -
                edgeUse (f₀ :: T') (Classical.choose hsearch).1 := by
              have hlt := heu.1
              have hle1 := hleT (Classical.choose hsearch).1
              omega
            have hmem : (Classical.choose hsearch).1 ∈
                eIn head (Classical.choose hsearch).2 :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhead⟩
            calc 0 < q (Classical.choose hsearch).1 -
                  edgeUse (f₀ :: T') (Classical.choose hsearch).1 := h1
              _ ≤ ∑ e ∈ eIn head (Classical.choose hsearch).2,
                    (q e - edgeUse (f₀ :: T') e) :=
                Finset.single_le_sum
                  (f := fun e => q e - edgeUse (f₀ :: T') e)
                  (fun _ _ => Nat.zero_le _) hmem
          have hbalR' : ∑ e ∈ eOut tail (Classical.choose hsearch).2,
                (q e - edgeUse (f₀ :: T') e)
              = ∑ e ∈ eIn head (Classical.choose hsearch).2,
                (q e - edgeUse (f₀ :: T') e) := hbalR _
          obtain ⟨o₁, ho₁mem, ho₁pos⟩ : ∃ o₁ ∈ eOut tail
              (Classical.choose hsearch).2,
              0 < q o₁ - edgeUse (f₀ :: T') o₁ := by
            by_contra hcon
            have hall : ∀ o₁ ∈ eOut tail (Classical.choose hsearch).2,
                q o₁ - edgeUse (f₀ :: T') o₁ = 0 := by
              intro o₁ ho₁
              by_contra hne
              exact hcon ⟨o₁, ho₁, Nat.pos_of_ne_zero hne⟩
            have hsum0 : ∑ e ∈ eOut tail (Classical.choose hsearch).2,
                (q e - edgeUse (f₀ :: T') e) = 0 :=
              Finset.sum_eq_zero (fun e he => hall e he)
            omega
          refine ⟨o₁, ho₁mem, ?_⟩
          have hle1 := hleT o₁
          omega
      have ho₁pos' : 0 < q (Classical.choose ho₁) -
          edgeUse (f₀ :: T') (Classical.choose ho₁) := by
        have hlt := (Classical.choose_spec ho₁).2
        have hle1 := hleT (Classical.choose ho₁)
        omega
      have hXprog := grow_closed_progress tail head
        (fun e => q e - edgeUse (f₀ :: T') e) hbalR
        ((∑ e, q e) + 1) [] (Classical.choose hsearch).2
        (Classical.choose hsearch).2 (.nil _)
        (fun e => by rw [edgeUse_nil]; exact Nat.zero_le _)
        (by
          show List.length [] + ((∑ e, q e) + 1) >
            ∑ e, (q e - edgeUse (f₀ :: T') e)
          have hle_sum : ∑ e, (q e - edgeUse (f₀ :: T') e) ≤ ∑ e, q e :=
            Finset.sum_le_sum (fun e _ => Nat.sub_le _ _)
          simp only [List.length_nil, Nat.zero_add]
          omega)
        (Classical.choose ho₁)
        (Classical.choose_spec ho₁).1
        (by
          show 0 < q (Classical.choose ho₁) -
            edgeUse (f₀ :: T') (Classical.choose ho₁)
          have h2 := (Classical.choose_spec ho₁).2
          have hle1 := hleT (Classical.choose ho₁)
          omega)
      let sT := Classical.choose hclosedT
      have hsT : TrailEnds tail head (f₀ :: T') sT sT :=
        Classical.choose_spec hclosedT
      have hsplit : ∃ AB : List E × List E, (f₀ :: T') = AB.1 ++ AB.2 ∧
          TrailEnds tail head AB.1 sT (Classical.choose hsearch).2 ∧
          TrailEnds tail head AB.2 (Classical.choose hsearch).2 sT := by
        have hvisit : TVerts tail head (f₀ :: T')
            (Classical.choose hsearch).2 :=
          (Classical.choose_spec hsearch).2.2
        obtain ⟨A, B, hAB, hA, hB⟩ :=
          trail_split_visit tail head hsT hvisit
        exact ⟨(A, B), hAB, hA, hB⟩
      let AB := Classical.choose hsplit
      have hAB : (f₀ :: T') = AB.1 ++ AB.2 :=
        (Classical.choose_spec hsplit).1
      have hA : TrailEnds tail head AB.1 sT (Classical.choose hsearch).2 :=
        (Classical.choose_spec hsplit).2.1
      have hB : TrailEnds tail head AB.2 (Classical.choose hsearch).2 sT :=
        (Classical.choose_spec hsplit).2.2
      have hXcl := hXprog.1
      have hXlen := hXprog.2
      have hclosed : ∃ s, TrailEnds tail head
          (AB.1 ++ (grow tail head (fun e => q e - edgeUse (f₀ :: T') e)
            ((∑ e, q e) + 1) [] (Classical.choose hsearch).2).1 ++ AB.2)
          s s :=
        ⟨sT, trail_append tail head (trail_append tail head hA hXcl) hB⟩
      have hleR : ∀ e, edgeUse
          (AB.1 ++ (grow tail head (fun e => q e - edgeUse (f₀ :: T') e)
            ((∑ e, q e) + 1) [] (Classical.choose hsearch).2).1 ++ AB.2)
          e ≤ q e := by
        intro e
        have hXle : ∀ x, edgeUse
            (grow tail head (fun e => q e - edgeUse (f₀ :: T') e)
              ((∑ e, q e) + 1) [] (Classical.choose hsearch).2).1 x
            ≤ q x - edgeUse (f₀ :: T') x :=
          grow_le tail head (fun e => q e - edgeUse (f₀ :: T') e)
            ((∑ e, q e) + 1) [] (Classical.choose hsearch).2
            (fun x => by rw [edgeUse_nil]; exact Nat.zero_le _)
        have hTe := hleT e
        have hXe := hXle e
        simp only [edgeUse_append]
        have e3 := edgeUse_append AB.1 AB.2 e
        rw [← hAB] at e3
        omega
      have hlenR : (f₀ :: T').length + 1 ≤
          (AB.1 ++ (grow tail head (fun e => q e - edgeUse (f₀ :: T') e)
            ((∑ e, q e) + 1) [] (Classical.choose hsearch).2).1
            ++ AB.2).length := by
        have hlenT : (f₀ :: T').length = (AB.1 ++ AB.2).length :=
          congrArg List.length hAB
        simp only [List.length_append, List.length_nil] at hXlen hlenT ⊢
        omega
      some ⟨AB.1 ++ (grow tail head (fun e => q e - edgeUse (f₀ :: T') e)
        ((∑ e, q e) + 1) [] (Classical.choose hsearch).2).1 ++ AB.2,
        hclosed, hleR, hlenR⟩

/-- Outer loop: iterate steps with fuel. -/
noncomputable def eulerLoop (q : E → ℕ) (supp : Finset E)
    (hbal : CircBalanced tail head q) (hconn : WeakConn tail head supp)
    (hsupp : ∀ e, e ∈ supp ↔ 0 < q e) :
    ∀ (_fuel : ℕ) (_T : List E), (∀ e, edgeUse _T e ≤ q e) →
      (∃ s, TrailEnds tail head _T s s) → List E
  | 0, T, _, _ => T
  | fuel + 1, T, hleT, hclosedT =>
    match eulerStep tail head q supp hbal hconn hsupp T hleT hclosedT with
    | none => T
    | some S => eulerLoop q supp hbal hconn hsupp fuel S.val S.property.2.1 S.property.1

theorem eulerLoop_succ (q : E → ℕ) (supp : Finset E)
    (hbal : CircBalanced tail head q) (hconn : WeakConn tail head supp)
    (hsupp : ∀ e, e ∈ supp ↔ 0 < q e)
    (fuel : ℕ) (T : List E) (hleT : ∀ e, edgeUse T e ≤ q e)
    (hclosedT : ∃ s, TrailEnds tail head T s s) :
    eulerLoop tail head q supp hbal hconn hsupp (fuel + 1) T hleT hclosedT =
      match eulerStep tail head q supp hbal hconn hsupp T hleT hclosedT with
      | none => T
      | some S => eulerLoop tail head q supp hbal hconn hsupp fuel S.val
          S.property.2.1 S.property.1 := rfl

/-- A `none` step means no support edge is unused. -/
theorem eulerStep_eq_none (q : E → ℕ) (supp : Finset E)
    (hbal : CircBalanced tail head q) (hconn : WeakConn tail head supp)
    (hsupp : ∀ e, e ∈ supp ↔ 0 < q e)
    (T : List E) (hleT : ∀ e, edgeUse T e ≤ q e)
    (hclosedT : ∃ s, TrailEnds tail head T s s)
    (hS : eulerStep tail head q supp hbal hconn hsupp T hleT hclosedT = none) :
    supp.toList.find? (fun e => decide (edgeUse T e < q e)) = none := by
  unfold eulerStep at hS
  split at hS
  case h_1 => assumption
  case h_2 =>
    revert hS
    cases T with
    | nil =>
      intro hS
      dsimp only at hS
      cases hS
    | cons f₀ T' =>
      intro hS
      dsimp only at hS
      cases hS

/-- Loop outcome: either every support edge is exhausted or the trail
grew by the full fuel allowance. -/
theorem eulerLoop_outcome (q : E → ℕ) (supp : Finset E)
    (hbal : CircBalanced tail head q) (hconn : WeakConn tail head supp)
    (hsupp : ∀ e, e ∈ supp ↔ 0 < q e)
    (fuel : ℕ) (T : List E) (hleT : ∀ e, edgeUse T e ≤ q e)
    (hclosedT : ∃ s, TrailEnds tail head T s s) :
    (∀ e ∈ supp, q e ≤
        edgeUse (eulerLoop tail head q supp hbal hconn hsupp fuel T hleT
          hclosedT) e) ∨
        (eulerLoop tail head q supp hbal hconn hsupp fuel T hleT
          hclosedT).length ≥ T.length + fuel := by
  induction fuel generalizing T hleT hclosedT with
  | zero =>
    right
    show T.length ≥ T.length + 0
    simp
  | succ fuel ih =>
    simp only [eulerLoop_succ]
    cases hS : eulerStep tail head q supp hbal hconn hsupp T hleT hclosedT with
    | none =>
      dsimp only
      left
      have hfind0 := eulerStep_eq_none tail head q supp hbal hconn hsupp T
        hleT hclosedT hS
      intro e he
      have hx' : e ∈ supp.toList := Finset.mem_toList.mpr he
      have h2 := (List.find?_eq_none.mp hfind0) e hx'
      by_contra hlt
      have hlt' : edgeUse T e < q e := Nat.not_le.mp hlt
      exact h2 (by simp [hlt'])
    | some S =>
      clear hS
      dsimp only
      have hih := ih S.val S.property.2.1 S.property.1
      rcases hih with hdone | hlen
      · exact Or.inl hdone
      · right
        have hprog := S.property.2.2
        omega

/-- The loop preserves closedness. -/
theorem eulerLoop_closed (q : E → ℕ) (supp : Finset E)
    (hbal : CircBalanced tail head q) (hconn : WeakConn tail head supp)
    (hsupp : ∀ e, e ∈ supp ↔ 0 < q e)
    (fuel : ℕ) (T : List E) (hleT : ∀ e, edgeUse T e ≤ q e)
    (hclosedT : ∃ s, TrailEnds tail head T s s) :
    ∃ s, TrailEnds tail head
        (eulerLoop tail head q supp hbal hconn hsupp fuel T hleT
          hclosedT) s s := by
  induction fuel generalizing T hleT hclosedT with
  | zero => exact hclosedT
  | succ fuel ih =>
    simp only [eulerLoop_succ]
    cases hS : eulerStep tail head q supp hbal hconn hsupp T hleT hclosedT with
    | none =>
      clear hS
      dsimp only
      exact hclosedT
    | some S =>
      clear hS
      dsimp only
      exact ih S.val S.property.2.1 S.property.1

/-- The loop preserves the quota. -/
theorem eulerLoop_le (q : E → ℕ) (supp : Finset E)
    (hbal : CircBalanced tail head q) (hconn : WeakConn tail head supp)
    (hsupp : ∀ e, e ∈ supp ↔ 0 < q e)
    (fuel : ℕ) (T : List E) (hleT : ∀ e, edgeUse T e ≤ q e)
    (hclosedT : ∃ s, TrailEnds tail head T s s) :
    ∀ e, edgeUse
        (eulerLoop tail head q supp hbal hconn hsupp fuel T hleT
          hclosedT) e ≤ q e := by
  induction fuel generalizing T hleT hclosedT with
  | zero => exact hleT
  | succ fuel ih =>
    simp only [eulerLoop_succ]
    cases hS : eulerStep tail head q supp hbal hconn hsupp T hleT hclosedT with
    | none =>
      clear hS
      dsimp only
      exact hleT
    | some S =>
      clear hS
      dsimp only
      exact ih S.val S.property.2.1 S.property.1

/-- **Hierholzer's theorem (issue #70).** A balanced integer circulation
on a nonempty weakly-connected support is spelled by a closed trail
using every edge exactly its multiplicity. -/
theorem eulerian_closed_trail (q : E → ℕ) (hbal : CircBalanced tail head q)
    (supp : Finset E) (hsupp : ∀ e, e ∈ supp ↔ 0 < q e)
    (hne : supp.Nonempty) (hconn : WeakConn tail head supp) :
    ∃ T s, TrailEnds tail head T s s ∧ ∀ e, edgeUse T e = q e := by
  obtain ⟨e₀, he₀⟩ := hne
  have hle0 : ∀ e, edgeUse ([] : List E) e ≤ q e := fun e => by
    rw [edgeUse_nil]
    exact Nat.zero_le _
  have hcl0 : ∃ s, TrailEnds tail head ([] : List E) s s :=
    ⟨tail e₀, .nil _⟩
  obtain ⟨R, hRdone⟩ : ∃ R,
      (((∀ e ∈ supp, q e ≤ edgeUse R e) ∨
        R.length ≥ ([] : List E).length + ((∑ e ∈ Finset.univ, q e) + 1)) ∧
      (∃ s, TrailEnds tail head R s s) ∧ (∀ e, edgeUse R e ≤ q e)) :=
    ⟨_, eulerLoop_outcome tail head q supp hbal hconn hsupp
        ((∑ e ∈ Finset.univ, q e) + 1) [] hle0 hcl0,
      eulerLoop_closed tail head q supp hbal hconn hsupp
        ((∑ e ∈ Finset.univ, q e) + 1) [] hle0 hcl0,
      eulerLoop_le tail head q supp hbal hconn hsupp
        ((∑ e ∈ Finset.univ, q e) + 1) [] hle0 hcl0⟩
  rcases hRdone with ⟨hout, hclR, hleR⟩
  rcases hout with hdone | hbig
  · obtain ⟨s, hs⟩ := hclR
    refine ⟨R, s, hs, fun e => ?_⟩
    by_cases he : e ∈ supp
    · have h1 := hdone e he
      have h2 := hleR e
      omega
    · have hq0 : q e = 0 := by
        by_contra hne0
        have hpos : 0 < q e := Nat.pos_of_ne_zero hne0
        exact he ((hsupp e).mpr hpos)
      have h2 := hleR e
      omega
  · exfalso
    have hbound : R.length ≤ ∑ e ∈ Finset.univ, q e := by
      rw [length_eq_sum_edgeUse]
      exact Finset.sum_le_sum (fun e _ => hleR e)
    simp only [List.length_nil, Nat.zero_add] at hbig
    omega

end EulerianTrail

/-- Every nonempty list splits off its last element. -/
theorem list_split_last {E : Type} {T : List E} (hne : T ≠ []) :
    ∃ A l, T = A ++ [l] := by
  induction T with
  | nil => exact absurd rfl hne
  | cons e T' ih =>
    cases T' with
    | nil => exact ⟨[], e, rfl⟩
    | cons f rest =>
      obtain ⟨A, l, h⟩ := ih (by simp)
      exact ⟨e :: A, l, by rw [h, List.cons_append]⟩

section TrailSpelling

variable {V E : Type} [DecidableEq V] [DecidableEq E]
variable (tail head : E → V)

omit [DecidableEq V] [DecidableEq E] in
/-- First edge of a nonempty trail starts at the start. -/
theorem trail_first_tail {e : E} {T' : List E} {s t : V}
    (h : TrailEnds tail head (e :: T') s t) : tail e = s := by
  cases h with
  | cons _ _ _ _ hte _ => exact hte

omit [DecidableEq V] [DecidableEq E] in
/-- Internal adjacency: consecutive edges of a trail match head/tail. -/
theorem trail_get_adj {T : List E} {s t : V}
    (h : TrailEnds tail head T s t) (i : ℕ) (hi : i + 1 < T.length) :
    head (T.get ⟨i, by omega⟩) = tail (T.get ⟨i + 1, hi⟩) := by
  revert i hi
  induction h with
  | nil s =>
    intro i hi
    simp at hi
  | cons e T' s t hte hT' ih =>
    intro i hi
    cases i with
    | zero =>
      show head e = tail ((e :: T').get ⟨0 + 1, hi⟩)
      rw [List.get_cons_succ]
      cases T' with
      | nil => simp at hi
      | cons f rest =>
        show head e = tail f
        cases hT' with
        | cons _ _ _ _ hte' _ => exact hte'.symm
    | succ j =>
      have hlen : (e :: T').length = T'.length + 1 := rfl
      have hj : j + 1 < T'.length := by omega
      simp only [List.get_cons_succ]
      exact ih j hj

omit [DecidableEq V] [DecidableEq E] in
/-- Last edge of a trail ends at the end (index-free: induct on the
init part). -/
theorem trail_last_head {A : List E} {l : E} {s t : V}
    (h : TrailEnds tail head (A ++ [l]) s t) : head l = t := by
  induction A generalizing s with
  | nil =>
    have h' : TrailEnds tail head [l] s t := h
    cases h' with
    | cons _ _ _ _ _ hT' =>
      cases hT' with
      | nil _ => rfl
  | cons a A' ih =>
    have h' : TrailEnds tail head (a :: (A' ++ [l])) s t := h
    cases h' with
    | cons _ _ _ _ _ hT' => exact ih hT'

section WordSpelling

variable {α : Type} [DecidableEq α]
variable {L : ℕ}

open OrientedRigidity

/-- Cyclic edge access into a trail. -/
def cycEdge (T : List (Fin L → α)) (hm : 0 < T.length) (n : ℕ) : Fin L → α :=
  T.get ⟨n % T.length, Nat.mod_lt _ hm⟩

omit [DecidableEq α] in
/-- Cyclic adjacency of a closed trail: consecutive edges (modulo the
length) match suffix/prefix. -/
theorem trail_cyc_adj {T : List (Fin L → α)} {s : Fin (L - 1) → α}
    (h : TrailEnds winPrefix winSuffix T s s) (hm : 0 < T.length)
    (j : ℕ) (hj : j < T.length) :
    winSuffix (cycEdge T hm j)
      = winPrefix (cycEdge T hm ((j + 1) % T.length)) := by
  by_cases hlt : j + 1 < T.length
  · have g1 : cycEdge T hm j = T.get ⟨j, hj⟩ := by
      unfold cycEdge
      congr 1
      exact Fin.ext (Nat.mod_eq_of_lt hj)
    have g2 : cycEdge T hm ((j + 1) % T.length) = T.get ⟨j + 1, hlt⟩ := by
      unfold cycEdge
      congr 1
      apply Fin.ext
      rw [Nat.mod_eq_of_lt hlt]
      exact Nat.mod_eq_of_lt hlt
    rw [g1, g2]
    exact trail_get_adj winPrefix winSuffix h j hlt
  · have hj1 : j + 1 = T.length := by omega
    have e0 : (j + 1) % T.length = 0 := by rw [hj1, Nat.mod_self]
    have hne : T ≠ [] := by
      intro h0
      rw [h0] at hj
      simp at hj
    obtain ⟨A, l, hAB⟩ := list_split_last hne
    subst hAB
    have hlen : (A ++ [l]).length = A.length + 1 := by
      rw [List.length_append]
      simp
    have hls : winSuffix l = s :=
      trail_last_head winPrefix winSuffix h
    have h3 : j - A.length = 0 := by omega
    have hlast : cycEdge (A ++ [l]) hm j = l := by
      have g1 : cycEdge (A ++ [l]) hm j = (A ++ [l]).get ⟨j, hj⟩ := by
        unfold cycEdge
        congr 1
        exact Fin.ext (Nat.mod_eq_of_lt hj)
      have hJ : (A ++ [l])[j] = l := by
        rw [List.getElem_append_right (by omega : A.length ≤ j)]
        exact List.getElem_singleton (by omega)
      rw [g1, List.get_eq_getElem]
      exact hJ
    have hfs : winPrefix (cycEdge (A ++ [l]) hm 0) = s := by
      cases A with
      | nil =>
        have g0 : cycEdge ([] ++ [l]) hm 0
            = ([] ++ [l]).get ⟨0, hm⟩ := by
          unfold cycEdge
          congr 1
        have hJ : ([] ++ [l])[0] = l := by
          rw [List.getElem_append_right (by simp : ([] : List (Fin L → α)).length ≤ 0)]
          exact List.getElem_singleton (by omega)
        have h2 : TrailEnds winPrefix winSuffix [l] s s := h
        have hW : winPrefix (([] ++ [l])[0]) = s := by
          rw [hJ]
          exact trail_first_tail winPrefix winSuffix h2
        rw [g0, List.get_eq_getElem]
        exact hW
      | cons a A' =>
        have g0 : cycEdge ((a :: A') ++ [l]) hm 0
            = ((a :: A') ++ [l]).get ⟨0, hm⟩ := by
          unfold cycEdge
          congr 1
        have hJ : ((a :: A') ++ [l])[0] = a := by
          rw [List.getElem_append_left (by simp : (0 : ℕ) < (a :: A').length)]
          exact List.getElem_cons_zero a A' (by simp)
        have h2 : TrailEnds winPrefix winSuffix (a :: (A' ++ [l])) s s := h
        have hW : winPrefix (((a :: A') ++ [l])[0]) = s := by
          rw [hJ]
          exact trail_first_tail winPrefix winSuffix h2
        rw [g0, List.get_eq_getElem]
        exact hW
    rw [e0, hlast, hfs]
    exact hls

/-- Spelling word: first letters of successive trail edges. -/
def spellWord {m : ℕ} (hL : 0 < L) (w : Fin m → Fin L → α) : Fin m → α :=
  fun j => w j ⟨0, hL⟩

omit [DecidableEq α] in
/-- One-letter shift along the trail spelling. -/
theorem spell_shift {m : ℕ} (w : Fin m → Fin L → α) (hm : 0 < m)
    (hadj : ∀ j : Fin m, winSuffix (w j)
      = winPrefix (w ⟨(j.val + 1) % m, Nat.mod_lt _ hm⟩))
    (j : Fin m) (k : ℕ) (hk1 : k + 1 < L) :
    w ⟨(j.val + 1) % m, Nat.mod_lt _ hm⟩ ⟨k, by omega⟩
      = w j ⟨k + 1, by omega⟩ := by
  have hk' : k < L - 1 := by omega
  have hc := congrFun (hadj j) ⟨k, hk'⟩
  exact hc.symm

omit [DecidableEq α] in
/-- Window identity core: the `d`-th letter window aligns by induction. -/
theorem spell_window_aux {m : ℕ} (w : Fin m → Fin L → α) (hm : 0 < m)
    (hadj : ∀ j : Fin m, winSuffix (w j)
      = winPrefix (w ⟨(j.val + 1) % m, Nat.mod_lt _ hm⟩))
    (n d k : ℕ) (hk : k < L) (hdk : d + k < L) :
    w ⟨(n + d) % m, Nat.mod_lt _ hm⟩ ⟨k, hk⟩
      = w ⟨n % m, Nat.mod_lt _ hm⟩ ⟨d + k, by omega⟩ := by
  revert k hk hdk
  induction d with
  | zero =>
    intro k hk hdk
    have e1 : (⟨(n + 0) % m, Nat.mod_lt _ hm⟩ : Fin m)
        = ⟨n % m, Nat.mod_lt _ hm⟩ :=
      Fin.ext (by rw [Nat.add_zero])
    have e2 : (⟨0 + k, by omega⟩ : Fin L) = ⟨k, hk⟩ :=
      Fin.ext (Nat.zero_add k)
    rw [e1, e2]
  | succ d ih =>
    intro k hk hdk
    have hmod : (n + (d + 1)) % m = ((n + d) % m + 1) % m := by
      have h1 : n + (d + 1) = (n + d) + 1 := by omega
      rw [h1, Nat.mod_add_mod]
    have estep : (⟨(n + (d + 1)) % m, Nat.mod_lt _ hm⟩ : Fin m)
        = ⟨((n + d) % m + 1) % m, Nat.mod_lt _ hm⟩ :=
      Fin.ext hmod
    rw [estep]
    have hsh := spell_shift w hm hadj ⟨(n + d) % m, Nat.mod_lt _ hm⟩ k
      (by omega : k + 1 < L)
    have hih := ih (k + 1) (by omega) (by omega)
    have hkv : d + (k + 1) = (d + 1) + k := by omega
    have e3 : (⟨d + (k + 1), by omega⟩ : Fin L) = ⟨(d + 1) + k, by omega⟩ :=
      Fin.ext hkv
    rw [← e3]
    exact hsh.trans hih

omit [DecidableEq α] in
/-- Windows of the spelling word are exactly the trail edges. -/
theorem spell_window {m : ℕ} (w : Fin m → Fin L → α) (hm : 0 < m)
    (hL0 : 0 < L)
    (hadj : ∀ j : Fin m, winSuffix (w j)
      = winPrefix (w ⟨(j.val + 1) % m, Nat.mod_lt _ hm⟩))
    (r : Fin m) :
    window hm (spellWord hL0 w) r = w r := by
  funext d
  have hd : d.val < L := d.isLt
  have hA := spell_window_aux w hm hadj r.val d.val 0
    (by omega : 0 < L) (by omega : d.val + 0 < L)
  have er : (⟨r.val % m, Nat.mod_lt _ hm⟩ : Fin m) = r :=
    Fin.ext (Nat.mod_eq_of_lt r.isLt)
  have ed : (⟨d.val + 0, by omega⟩ : Fin L) = d :=
    Fin.ext (Nat.add_zero _)
  simp only [window, spellWord, cyc]
  rw [er] at hA
  rw [ed] at hA
  exact hA

/-- Spectrum of the spelling word equals trail edge usage. -/
theorem count_bridge {E : Type} [DecidableEq E] (T : List E) (w : E) :
    (({j | T.get j = w} : Finset (Fin T.length))).card = edgeUse T w := by
  induction T with
  | nil =>
    simp only [edgeUse, List.countP_nil]
    rw [Finset.card_eq_zero]
    ext j
    exact Fin.elim0 j
  | cons a T' ih =>
    simp only [List.length_cons]
    rw [Fin.card_filter_univ_succ', List.get_cons_zero]
    have hfib : (({x | (a :: T').get x.succ = w} : Finset (Fin T'.length))).card
        = (({x | T'.get x = w} : Finset (Fin T'.length))).card := by
      congr 1
    rw [hfib, ih, edgeUse_cons]
    exact Nat.add_comm _ _

end WordSpelling

end TrailSpelling

section DividedSpelling

variable {α : Type} [DecidableEq α] [Fintype α]
variable {L : ℕ}

open OrientedRigidity

omit [Fintype α] in
/-- Support is exactly where the spectrum is positive. -/
theorem mem_support_iff {G : ℕ} (hG : 0 < G) (S : Fin G → α)
    (w : Fin L → α) :
    w ∈ support hG S ↔ 0 < specCount hG S w := by
  constructor
  · intro hw
    have h1 := truth_pos_on_support hG S w hw
    omega
  · intro hpos
    have hne : (Finset.univ.filter
        (fun r : Fin G => window hG S r = w)).Nonempty := by
      apply Finset.card_pos.mp
      simpa [specCount] using hpos
    obtain ⟨r, hr⟩ := hne
    simp only [support, Finset.mem_image]
    exact ⟨r, Finset.mem_univ r, (Finset.mem_filter.mp hr).2⟩

/-- **Eulerian spelling of a divided circulation (issue #70, discharging
`hSpell`).** If every `L`-window multiplicity of a circular genome is
divisible by `g > 1`, the divided circulation is spelled by a circular
word with exactly the quotient spectrum. Division preserves balance
(`balanced_div_univ`); support is unchanged so connectivity transfers
(`truth_strongly_connected`); `eulerian_closed_trail` gives the closed
trail; `spell_window` + `count_bridge` turn it into a word. -/
theorem spell_exists_divided {G : ℕ} (hG : 0 < G) (S : Fin G → α)
    (hL : 1 < L) (g : ℕ) (hg1 : 1 < g)
    (hdiv : ∀ w : Fin L → α, g ∣ specCount hG S w) :
    ∃ (m : ℕ) (hW : 0 < m) (W : Fin m → α),
      specCount hW W = (fun w : Fin L → α => specCount hG S w / g)
        ∧ m * g = G := by
  have hg0 : 0 < g := by omega
  -- The divided circulation vanishes off-support.
  have hcvan : ∀ w : Fin L → α, w ∉ support hG S → specCount hG S w = 0 := by
    intro w hw
    have h : ¬ 0 < specCount hG S w :=
      fun hpos => hw ((mem_support_iff hG S w).mpr hpos)
    omega
  have hqvan : ∀ w : Fin L → α, w ∉ support hG S →
      specCount hG S w / g = 0 := by
    intro w hw
    rw [hcvan w hw]
    exact Nat.zero_div g
  -- The divided circulation is balanced (on nodes, then everywhere).
  have hqBal : CircBalanced winPrefix winSuffix
      (fun w : Fin L → α => specCount hG S w / g) := by
    intro v
    by_cases hv : v ∈ genomeNodes hG S
    · unfold eOut eIn
      exact balanced_div_univ winPrefix winSuffix (genomeNodes hG S)
        (support hG S) (specCount hG S) g hg0 (fun e he => hdiv e)
        (truth_balanced hG S) hcvan v hv
    · have o0 : ∑ e ∈ Finset.univ.filter (fun e => winPrefix e = v),
          (fun w => specCount hG S w / g) e = 0 := by
        apply Finset.sum_eq_zero
        intro w hw
        have hwv : winPrefix w = v := (Finset.mem_filter.mp hw).2
        have hws : w ∉ support hG S := by
          intro hmem
          have hm := mem_nodes_of_mem_support hG S w hmem
          exact hv (hwv ▸ hm.1)
        exact hqvan w hws
      have i0 : ∑ e ∈ Finset.univ.filter (fun e => winSuffix e = v),
          (fun w => specCount hG S w / g) e = 0 := by
        apply Finset.sum_eq_zero
        intro w hw
        have hwv : winSuffix w = v := (Finset.mem_filter.mp hw).2
        have hws : w ∉ support hG S := by
          intro hmem
          have hm := mem_nodes_of_mem_support hG S w hmem
          exact hv (hwv ▸ hm.2)
        exact hqvan w hws
      unfold eOut eIn
      omega
  -- Support of the quotient = support of the truth.
  have hsupp : ∀ e : Fin L → α,
      e ∈ support hG S ↔ 0 < specCount hG S e / g := by
    intro e
    rw [mem_support_iff hG S e]
    constructor
    · intro hpos
      by_contra hneg
      have h0 : specCount hG S e / g = 0 := Nat.eq_zero_of_not_pos hneg
      have hmul := Nat.mul_div_cancel' (hdiv e)
      rw [h0, mul_zero] at hmul
      omega
    · intro hpos
      have hle : specCount hG S e / g ≤ specCount hG S e :=
        Nat.div_le_self _ _
      omega
  have hsupne : (support (L := L) hG S).Nonempty := by
    have h0 : (Finset.univ : Finset (Fin G)).Nonempty := by
      rw [Finset.univ_nonempty_iff]
      exact ⟨⟨0, hG⟩⟩
    exact h0.image _
  -- Weak connectivity transfers from strong connectivity.
  have hconn : WeakConn winPrefix winSuffix (support (L := L) hG S) := by
    intro u v hu hv
    obtain ⟨eu, heu, hue⟩ := hu
    obtain ⟨ev, hev, hve⟩ := hv
    have hmemu := mem_nodes_of_mem_support hG S eu heu
    have hmemv := mem_nodes_of_mem_support hG S ev hev
    have huN : u ∈ genomeNodes hG S := by
      rcases hue with h | h
      · rw [← h]; exact hmemu.1
      · rw [← h]; exact hmemu.2
    have hvN : v ∈ genomeNodes hG S := by
      rcases hve with h | h
      · rw [← h]; exact hmemv.1
      · rw [← h]; exact hmemv.2
    have hreach := truth_strongly_connected (L := L) hG S u huN v hvN
    exact reachable_to_upath winPrefix winSuffix Finset.Subset.rfl hreach
  -- The Eulerian closed trail with exact quotient multiplicities.
  obtain ⟨T, s, hTclosed, hTuse⟩ := eulerian_closed_trail winPrefix winSuffix
    (fun w => specCount hG S w / g) hqBal (support hG S) hsupp hsupne hconn
  -- Total mass is positive, so the trail is nonempty.
  have htot := truth_total (L := L) hG S
  have hGmul : G = g * ∑ w : Fin L → α, specCount hG S w / g := by
    have hsub : (∑ w ∈ support (L := L) hG S, specCount hG S w / g)
        = ∑ w : Fin L → α, specCount hG S w / g :=
      Finset.sum_subset (Finset.subset_univ _) (fun w _ hwN => hqvan w hwN)
    have h1 : (∑ w ∈ support (L := L) hG S, specCount hG S w)
        = g * ∑ w ∈ support (L := L) hG S, specCount hG S w / g := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun w _ => (Nat.mul_div_cancel' (hdiv w)).symm)
    exact htot.symm.trans (h1.trans (by rw [hsub]))
  have hQpos : 0 < ∑ w : Fin L → α, specCount hG S w / g := by
    by_contra hcon
    have hQ0 : ∑ w : Fin L → α, specCount hG S w / g = 0 := Nat.eq_zero_of_not_pos hcon
    rw [hQ0, mul_zero] at hGmul
    omega
  have hTeq := length_eq_sum_edgeUse T
  have hsum : ∑ e, edgeUse T e
      = ∑ w : Fin L → α, specCount hG S w / g :=
    Finset.sum_congr rfl (fun w _ => hTuse w)
  have hlenT : 0 < T.length := by omega
  have hmg : T.length * g = G := by
    rw [hTeq, hsum, mul_comm]
    exact hGmul.symm
  -- Spell the trail as a circular word with the quotient spectrum.
  have hL0 : 0 < L := by omega
  have hadj : ∀ j : Fin T.length, winSuffix (T.get j)
      = winPrefix (T.get ⟨(j.val + 1) % T.length, Nat.mod_lt _ hlenT⟩) := by
    intro j
    have hbase := trail_cyc_adj hTclosed hlenT j.val j.isLt
    have b1 : cycEdge T hlenT j.val = T.get j := by
      unfold cycEdge
      congr 1
      exact Fin.ext (Nat.mod_eq_of_lt j.isLt)
    have b2 : cycEdge T hlenT ((j.val + 1) % T.length)
        = T.get ⟨(j.val + 1) % T.length, Nat.mod_lt _ hlenT⟩ := by
      unfold cycEdge
      congr 1
      exact Fin.ext (Nat.mod_eq_of_lt (Nat.mod_lt _ hlenT))
    rw [b1, b2] at hbase
    exact hbase
  refine ⟨T.length, hlenT, spellWord hL0 T.get, ?_, hmg⟩
  funext w
  have hwin : ∀ r : Fin T.length,
      window hlenT (spellWord hL0 T.get) r = T.get r :=
    fun r => spell_window T.get hlenT hL0 hadj r
  have hspec : specCount hlenT (spellWord hL0 T.get) w = edgeUse T w := by
    have hset : Finset.univ.filter
        (fun r : Fin T.length => window hlenT (spellWord hL0 T.get) r = w)
        = Finset.univ.filter (fun r : Fin T.length => T.get r = w) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hwin r]
    have hsp : specCount hlenT (spellWord hL0 T.get) w
        = (Finset.univ.filter
          (fun r : Fin T.length => window hlenT (spellWord hL0 T.get) r = w)).card :=
      rfl
    rw [hsp, hset]
    exact count_bridge T w
  rw [hspec]
  exact hTuse w

end DividedSpelling

section PowerScaling

variable {α : Type} [DecidableEq α]
variable {L : ℕ}

open OrientedRigidity

/-- Power word: repeat `W` `g` times into length `G`. -/
def repWord {m : ℕ} (hm : 0 < m) (W : Fin m → α) (_g : ℕ) (G : ℕ) :
    Fin G → α :=
  fun i => W ⟨i.val % m, Nat.mod_lt _ hm⟩

omit [DecidableEq α] in
/-- Windows of a power word are windows of the base. -/
theorem window_repWord {m G : ℕ} (hm : 0 < m) (W : Fin m → α) (g : ℕ)
    (hG0 : 0 < G) (hG : m * g = G) (L : ℕ) (r : Fin G) :
    window (L := L) hG0 (repWord hm W g G) r
      = window (L := L) hm W ⟨r.val % m, Nat.mod_lt _ hm⟩ := by
  funext d
  have hdivG : m ∣ G := ⟨g, hG.symm⟩
  have e1 : ((r.val + d.val) % G) % m = (r.val + d.val) % m :=
    Nat.mod_mod_of_dvd _ hdivG
  have e2 : ((r.val % m) + d.val) % m = (r.val + d.val) % m :=
    Nat.mod_add_mod _ _ _
  have sL : window (L := L) hG0 (repWord hm W g G) r d
      = W ⟨((r.val + d.val) % G) % m, Nat.mod_lt _ hm⟩ := rfl
  have sR : window (L := L) hm W ⟨r.val % m, Nat.mod_lt _ hm⟩ d
      = W ⟨((r.val % m) + d.val) % m, Nat.mod_lt _ hm⟩ := rfl
  have f1 : (⟨((r.val + d.val) % G) % m, Nat.mod_lt _ hm⟩ : Fin m)
      = ⟨(r.val + d.val) % m, Nat.mod_lt _ hm⟩ :=
    Fin.ext e1
  have f2 : (⟨((r.val % m) + d.val) % m, Nat.mod_lt _ hm⟩ : Fin m)
      = ⟨(r.val + d.val) % m, Nat.mod_lt _ hm⟩ :=
    Fin.ext e2
  rw [sL, sR, f1, f2]

/-- Each base start lifts to exactly `g` power starts. -/
theorem fiber_card_rep {m G : ℕ} (hm : 0 < m) (g : ℕ) (hG : m * g = G)
    (b : Fin m) :
    (Finset.univ.filter (fun r : Fin G => r.val % m = b.val)).card = g := by
  have hbound : ∀ t : Fin g, b.val + t.val * m < m * g := by
    intro t
    have ht1 : t.val + 1 ≤ g := Nat.succ_le_of_lt t.isLt
    have hmul := mul_le_mul_of_nonneg_right ht1 (Nat.zero_le m)
    have hexpand : (t.val + 1) * m = t.val * m + m := by
      rw [Nat.add_mul, Nat.one_mul]
    have hb : b.val < m := b.isLt
    have hcomm : m * g = g * m := mul_comm _ _
    omega
  have hfin : ∀ t : Fin g, b.val + t.val * m < G := fun t => hG ▸ hbound t
  classical
  let φ : Fin g → Fin G := fun t => ⟨b.val + t.val * m, hfin t⟩
  have himg : Finset.image φ Finset.univ
      = Finset.univ.filter (fun r : Fin G => r.val % m = b.val) := by
    ext r
    simp only [Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨t, ht⟩
      have htv : (φ t).val = b.val + t.val * m := rfl
      rw [← ht, htv]
      have e : (b.val + t.val * m) % m = b.val := by
        have hb : b.val < m := b.isLt
        rw [Nat.add_mul_mod_self_right]
        exact Nat.mod_eq_of_lt hb
      exact e
    · intro hmod
      have hlt : r.val < g * m := by
        rw [mul_comm]
        omega
      have hdiv : r.val / m < g := (Nat.div_lt_iff_lt_mul hm).mpr hlt
      refine ⟨⟨r.val / m, hdiv⟩, ?_⟩
      apply Fin.ext
      have hdecomp : r.val % m + m * (r.val / m) = r.val :=
        Nat.mod_add_div _ _
      have h2 : b.val + r.val / m * m = r.val := by
        rw [← hmod]
        rw [mul_comm (r.val / m) m]
        exact hdecomp
      -- goal: b.val + (r.val / m) * m = r.val (from Fin.ext val equation)
      exact h2
  have hinj : Function.Injective φ := by
    intro t₁ t₂ h12
    have h12v : b.val + t₁.val * m = b.val + t₂.val * m := by
      have := congrArg Fin.val h12
      simpa only [Fin.val_mk] using this
    have hmul : t₁.val * m = t₂.val * m := by omega
    have hteq : t₁.val = t₂.val := Nat.mul_right_cancel hm hmul
    exact Fin.ext hteq
  rw [← himg, Finset.card_image_of_injective _ hinj, Finset.card_univ,
    Fintype.card_fin]

/-- Power spectrum scaling (issue #70, discharging `hPowScale`):
repeating a word `g` times scales every window count by `g`. -/
theorem power_spec_rep {m G : ℕ} (hm : 0 < m) (W : Fin m → α) (g : ℕ)
    (hG0 : 0 < G) (hG : m * g = G) (L : ℕ) :
    specCount (L := L) hG0 (repWord hm W g G)
      = fun w : Fin L → α => g * specCount (L := L) hm W w := by
  funext w
  have hMaps : Set.MapsTo (fun r : Fin G => (⟨r.val % m, Nat.mod_lt _ hm⟩ : Fin m))
      ↑(Finset.univ.filter
        (fun r : Fin G => window (L := L) hG0 (repWord hm W g G) r = w))
      ↑(Finset.univ.filter (fun s : Fin m => window (L := L) hm W s = w)) := by
    intro r hr
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
      true_and] at hr ⊢
    have hwr := window_repWord hm W g hG0 hG L r
    exact hwr ▸ hr
  have hcount := Finset.card_eq_sum_card_fiberwise hMaps
  have hsR : specCount (L := L) hG0 (repWord hm W g G) w
      = (Finset.univ.filter
        (fun r : Fin G => window (L := L) hG0 (repWord hm W g G) r = w)).card := rfl
  have hsW : specCount (L := L) hm W w
      = (Finset.univ.filter (fun s : Fin m => window (L := L) hm W s = w)).card := rfl
  have hfib_eq : ∀ b ∈ Finset.univ.filter
      (fun s : Fin m => window (L := L) hm W s = w),
      (Finset.univ.filter
        (fun r : Fin G => window (L := L) hG0 (repWord hm W g G) r = w)).filter
        (fun a => (⟨a.val % m, Nat.mod_lt _ hm⟩ : Fin m) = b)
      = Finset.univ.filter (fun r : Fin G => r.val % m = b.val) := by
    intro b hb
    have hwb : window (L := L) hm W b = w := (Finset.mem_filter.mp hb).2
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hmem
      obtain ⟨hrw, hfb⟩ := hmem
      have hfbv : r.val % m = b.val := by
        have hcc := congrArg Fin.val hfb
        simpa only [Fin.val_mk] using hcc
      exact hfbv
    · intro hmod
      have hfb : (⟨r.val % m, Nat.mod_lt _ hm⟩ : Fin m) = b :=
        Fin.ext hmod
      have hwR : window (L := L) hG0 (repWord hm W g G) r = window (L := L) hm W b := by
        have hwr := window_repWord hm W g hG0 hG L r
        rw [hfb] at hwr
        exact hwr
      refine ⟨?_, ?_⟩
      · rw [hwR]; exact hwb
      · exact hfb
  have hsum : (∑ b ∈ Finset.univ.filter (fun s : Fin m => window (L := L) hm W s = w),
      ((Finset.univ.filter
        (fun r : Fin G => window (L := L) hG0 (repWord hm W g G) r = w)).filter
        (fun a => (⟨a.val % m, Nat.mod_lt _ hm⟩ : Fin m) = b)).card)
      = ∑ _b ∈ Finset.univ.filter (fun s : Fin m => window (L := L) hm W s = w), g :=
    Finset.sum_congr rfl (fun b hb => by
      have hfc := fiber_card_rep hm g hG b
      have heq := hfib_eq b hb
      exact (congrArg Finset.card heq).trans hfc)
  have hfin : (∑ _b ∈ Finset.univ.filter
      (fun s : Fin m => window (L := L) hm W s = w), g)
      = g * specCount (L := L) hm W w := by
    have e1 : (∑ _b ∈ Finset.univ.filter
        (fun s : Fin m => window (L := L) hm W s = w), g)
        = (Finset.univ.filter
          (fun s : Fin m => window (L := L) hm W s = w)).card * g := by
      rw [Finset.sum_const]
      exact nsmul_eq_mul _ _
    rw [e1, hsW, mul_comm]
  exact hsR.trans (hcount.trans (hsum.trans hfin))

end PowerScaling

/-- Power lifting: a spelling `W` of the quotient `spec S / g` repeats
to the original spectrum, via the explicit power-scale interface
`hPowScale` (what `power W g`, i.e. `W^g`, means for spectra: each
cyclic window count scales by `g`, cf. `lem:scaling` "each cyclic
length-`L` window of `W` lifts to exactly `g` windows of `W^g`").
Lean checks the arithmetic lift `g * (c/g) = c`; only the Eulerian
existence of `W` (`hSpell`) and BBT below stay premises. -/
theorem pow_spec_of_spell {Genome V : Type*} [Fintype V]
    {spec : Genome → (V → ℕ)} {power : Genome → ℕ → Genome}
    {S W : Genome} {g : ℕ}
    (hdiv : ∀ v : V, g ∣ spec S v)
    (hSpell : spec W = fun v => spec S v / g)
    (hPowScale : spec (power W g) = fun v => g * spec W v) :
    spec (power W g) = spec S := by
  funext v
  rw [hPowScale]
  simp only
  rw [hSpell]
  simp only
  exact Nat.mul_div_cancel' (hdiv v)

/-- Primitive-P2 spectra have gcd one, conditional on the explicit
Eulerian-spelling and BBT premises of the paper proof. -/
theorem gcd_one_of_primitive_P2 {Genome V : Type*} [Fintype V]
    {spec : Genome → (V → ℕ)} {len : Genome → ℕ}
    {Primitive AdmP2 : Genome → Prop}
    {rotEquiv : Genome → Genome → Prop}
    {power : Genome → ℕ → Genome}
    (S : Genome)
    (hSum : ∑ v : V, spec S v = len S)
    (hlen : 0 < len S)
    (hPrim : Primitive S)
    (hP2S : AdmP2 S)
    (hSpell : ∀ g : ℕ, 1 < g → (∀ v : V, g ∣ spec S v) →
      ∃ W : Genome, spec W = fun v => spec S v / g)
    (hPowScale : ∀ W : Genome, ∀ g : ℕ,
      spec (power W g) = fun v => g * spec W v)
    (hPowerNonPrim : ∀ W : Genome, ∀ g : ℕ, 1 < g → ¬ Primitive (power W g))
    (hBBT : ∀ D : Genome, AdmP2 S → spec D = spec S → rotEquiv D S)
    (hRotPrim : ∀ D : Genome, rotEquiv D S → Primitive S → Primitive D) :
    IsGcdOne (spec S) := by
  intro g hg
  by_cases h1 : g = 1
  · exact h1
  · have hpos : 0 < g := by
      rcases Nat.eq_zero_or_pos g with rfl | hp
      · exfalso
        have hall : ∀ v : V, spec S v = 0 :=
          fun v => Nat.eq_zero_of_zero_dvd (hg v)
        have hzero : ∑ v : V, spec S v = 0 :=
          Finset.sum_eq_zero (fun v _ => hall v)
        omega
      · exact hp
    have hlt : 1 < g := by omega
    obtain ⟨W, hSpecW⟩ := hSpell g hlt hg
    have hLift : spec (power W g) = spec S :=
      pow_spec_of_spell hg hSpecW (hPowScale W g)
    have hRot := hBBT (power W g) hP2S hLift
    have hPrimW := hRotPrim (power W g) hRot hPrim
    exact absurd hPrimW (hPowerNonPrim W g hlt)

/-- End-to-end project-level reduction for primitive P2 genomes:
normalized equality forces ordinary equality and rotation
equivalence, under the same explicit Eulerian-spelling/BBT premises
for each genome plus one final BBT uniqueness application. -/
theorem population_uniqueness_primitive_P2 {Genome V : Type*} [Fintype V]
    {spec : Genome → (V → ℕ)} {len : Genome → ℕ}
    {Primitive AdmP2 : Genome → Prop}
    {rotEquiv : Genome → Genome → Prop}
    {power : Genome → ℕ → Genome}
    (S D : Genome)
    (hSumS : ∑ v : V, spec S v = len S)
    (hSumD : ∑ v : V, spec D v = len D)
    (hlenS : 0 < len S) (hlenD : 0 < len D)
    (hPrimS : Primitive S) (hPrimD : Primitive D)
    (hP2S : AdmP2 S) (hP2D : AdmP2 D)
    (hNormEq : NormalizedEqual (spec S) (spec D) (len S) (len D))
    (hSpellS : ∀ g : ℕ, 1 < g → (∀ v : V, g ∣ spec S v) →
      ∃ W : Genome, spec W = fun v => spec S v / g)
    (hSpellD : ∀ g : ℕ, 1 < g → (∀ v : V, g ∣ spec D v) →
      ∃ W : Genome, spec W = fun v => spec D v / g)
    (hPowScale : ∀ W : Genome, ∀ g : ℕ,
      spec (power W g) = fun v => g * spec W v)
    (hPowerNonPrim : ∀ W : Genome, ∀ g : ℕ, 1 < g → ¬ Primitive (power W g))
    (hBBTS : ∀ E : Genome, AdmP2 S → spec E = spec S → rotEquiv E S)
    (hBBTD : ∀ E : Genome, AdmP2 D → spec E = spec D → rotEquiv E D)
    (hRotPrimS : ∀ E : Genome, rotEquiv E S → Primitive S → Primitive E)
    (hRotPrimD : ∀ E : Genome, rotEquiv E D → Primitive D → Primitive E)
    (hBBTuniq : spec S = spec D → rotEquiv D S) :
    len S = len D ∧ spec S = spec D ∧ rotEquiv D S := by
  have hGcdS : IsGcdOne (spec S) :=
    gcd_one_of_primitive_P2 S hSumS hlenS hPrimS hP2S hSpellS
      hPowScale hPowerNonPrim hBBTS hRotPrimS
  have hGcdD : IsGcdOne (spec D) :=
    gcd_one_of_primitive_P2 D hSumD hlenD hPrimD hP2D hSpellD
      hPowScale hPowerNonPrim hBBTD hRotPrimD
  have hOrd := normalized_to_ordinary hlenS hlenD hSumS hSumD hNormEq hGcdS hGcdD
  exact ⟨hOrd.1, hOrd.2, hBBTuniq hOrd.2⟩

-- ---------------------------------------------------------------------------
-- Regression: primitivity alone does not imply the reduction.
-- ---------------------------------------------------------------------------

/-- Two-letter alphabet keeps the regression enumerations tiny. -/
inductive Bin where
  | A | B
  deriving DecidableEq, Repr, Inhabited, BEq

instance : Fintype Bin :=
  ⟨{.A, .B}, by intro x; cases x <;> simp⟩

abbrev Word3 := Fin 3 → Bin
abbrev Word6 := Fin 6 → Bin
abbrev DiBin := Fin 2 → Bin

def regS : Word3 := ![Bin.A, Bin.A, Bin.B]
def regD : Word6 := ![Bin.A, Bin.A, Bin.A, Bin.B, Bin.A, Bin.B]

def regSCyc (i : Nat) : Bin := regS ⟨i % 3, Nat.mod_lt _ (by norm_num)⟩
def regDCyc (i : Nat) : Bin := regD ⟨i % 6, Nat.mod_lt _ (by norm_num)⟩

def regSWin (r : Fin 3) : DiBin := fun d => regSCyc (r.val + d.val)
def regDWin (r : Fin 6) : DiBin := fun d => regDCyc (r.val + d.val)

def regSOcc (w : DiBin) : ℕ :=
  (Finset.univ.filter (fun r : Fin 3 => regSWin r = w)).card

def regDOcc (w : DiBin) : ℕ :=
  (Finset.univ.filter (fun r : Fin 6 => regDWin r = w)).card

def RegSPrimitive : Prop :=
  ∀ k : Fin 3, k ≠ 0 → ∃ i : Fin 3, regSCyc (i.val + k.val) ≠ regS i

def RegDPrimitive : Prop :=
  ∀ k : Fin 6, k ≠ 0 → ∃ i : Fin 6, regDCyc (i.val + k.val) ≠ regD i

theorem reg_S_primitive : RegSPrimitive := by unfold RegSPrimitive; decide

theorem reg_D_primitive : RegDPrimitive := by unfold RegDPrimitive; decide

/-- The two ordinary 2-spectra are proportional with factor two. -/
theorem reg_normalized_equal : NormalizedEqual regSOcc regDOcc 3 6 := by
  intro w
  fin_cases w <;> decide

theorem reg_sum_S : ∑ w : DiBin, regSOcc w = 3 := by decide

theorem reg_sum_D : ∑ w : DiBin, regDOcc w = 6 := by decide

private def diAA : DiBin := ![Bin.A, Bin.A]

theorem reg_ordinary_differ : regSOcc ≠ regDOcc := by
  intro h
  have h1 : regSOcc diAA = 1 := by decide
  have h2 : regDOcc diAA = 2 := by decide
  rw [h] at h1
  omega

/-- The competitor spectrum `(AA:2, AB:2, BA:2)` is divisible by two,
so the gcd-one hypothesis genuinely fails there. -/
theorem reg_competitor_not_gcd_one : ¬ IsGcdOne regDOcc := by
  intro h
  have h2 := h 2 (by intro w; fin_cases w <;> decide)
  norm_num at h2

/-- Regression: both words are primitive and share normalized spectra,
yet ordinary spectra differ — primitivity alone is insufficient and the
gcd-one hypothesis in `normalized_to_ordinary` cannot be dropped. -/
theorem primitivity_insufficient :
    RegSPrimitive ∧ RegDPrimitive ∧
      NormalizedEqual regSOcc regDOcc 3 6 ∧ regSOcc ≠ regDOcc ∧
      ¬ IsGcdOne regDOcc :=
  ⟨reg_S_primitive, reg_D_primitive, reg_normalized_equal,
    reg_ordinary_differ, reg_competitor_not_gcd_one⟩

end AssemblyP1.PopulationReduction
