import Mathlib

/-!
# Abstract short-repeat circulation rigidity (issue #66)

This file formalizes the source-independent combinatorial core of the
oriented same-length rigidity argument: Theorem A of
`docs/source-notes/oriented-se62-rigidity-theorem.md`, as scoped by
issue #66.

> For a finite directed support graph with edge set `E`, let `A : E → ℕ`
> be a positive balanced circulation. Assume the support graph is
> strongly connected, every vertex has truth vertex-throughput
> `out_A(v) = in_A(v) ≤ 2`, and `B : E → ℕ` is another positive balanced
> circulation with `∑ e, B e = ∑ e, A e`. Then `B = A`.

## What is proved in Lean

* `unique_positive_circulation`: the abstract uniqueness theorem above,
  via the difference circulation `δ = B - A` over `ℤ` (negative set is a
  union of incidence-closed components, hence empty or everything;
  strong connectivity plus zero total forces it empty).
* `strong_to_supportConnected`: directed strong connectivity implies the
  undirected incidence-connectivity consequence consumed by the proof.

## Explicit hypotheses (trust surface)

`hmem` (edges land in the node set), `hApos` / `hBpos` (positivity),
`hAbal` / `hBbal` (balance), `hAtot` / `hBtot` (equal totals),
`hcap` (truth vertex-throughput bound `out_A(v) ≤ 2`; together with
balance this is `out_A(v) = in_A(v) ≤ 2`), `hstrong` (directed strong
connectivity of the support).

## Deliberately not formalized here

Per issue #66 scope discipline: no genomes, reads, repeat predicates,
`I_s`, likelihoods, or BBT assumptions. The circular-spectrum adapter
and the repeat-theory / `I_s` multiplicity-bound adapter are separate
follow-up packets. The full word-layer development previously on this
branch is preserved on `agent/formal-rigidity-word-layer`.
-/

namespace AssemblyP1.OrientedRigidity

open Finset
open BigOperators

section AbstractCirculation

variable {V E : Type} [DecidableEq V] [DecidableEq E]
variable (tail head : E → V) (nodes : Finset V) (edges : Finset E)

/-- Out-edges of `v` within the support. -/
private def outF (v : V) : Finset E := edges.filter (fun e => tail e = v)

/-- In-edges of `v` within the support. -/
private def inF (v : V) : Finset E := edges.filter (fun e => head e = v)

/-- Balance at every node: a circulation. -/
def Balanced (f : E → ℕ) : Prop :=
  ∀ v ∈ nodes, ∑ e ∈ outF tail edges v, f e = ∑ e ∈ inF head edges v, f e

/-- Undirected connectivity of the support: no nonempty proper edge set is
closed under incidence. This is the exact connectivity consequence used by the
paper proof (note §2, Fact 2). -/
def SupportConnected : Prop :=
  ∀ N : Finset E, N ⊆ edges → N.Nonempty → N ≠ edges →
    ∃ e ∈ N, ∃ e' ∈ edges, e' ∉ N ∧
      (tail e = tail e' ∨ tail e = head e' ∨ head e = tail e' ∨
        head e = head e')

/-- Directed reachability inside the support edge set. -/
inductive Reachable : V → V → Prop
  | refl (u : V) : Reachable u u
  | step {u w v : V} (f : E) : Reachable u w → f ∈ edges →
      tail f = w → head f = v → Reachable u v

/-- Strong connectivity of the support (issue #66 hypothesis): every node
reaches every node by a directed path staying inside `edges`. -/
def StronglyConnected : Prop :=
  ∀ u ∈ nodes, ∀ v ∈ nodes, Reachable tail head edges u v

/-- Strong connectivity implies the undirected incidence consequence used by
the rigidity proof: a strongly connected support has no proper nonempty
edge set closed under incidence. -/
theorem strong_to_supportConnected
    (hmem : ∀ e ∈ edges, tail e ∈ nodes ∧ head e ∈ nodes)
    (hstrong : StronglyConnected tail head nodes edges) :
    SupportConnected tail head edges := by
  intro N hNsub hNe hNne
  by_contra hcon
  push Not at hcon
  -- `N` is closed under incidence: every support edge sharing a vertex
  -- with a member of `N` is itself in `N`.
  have hclosed : ∀ e ∈ N, ∀ e' ∈ edges,
      (tail e = tail e' ∨ tail e = head e' ∨ head e = tail e' ∨
        head e = head e') → e' ∈ N := by
    intro e he e' he' hshare
    by_contra habs
    obtain ⟨h1, h2, h3, h4⟩ := hcon e he e' he' habs
    rcases hshare with h | h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact absurd h h3
    · exact absurd h h4
  -- Closure spreads along directed paths: if `N` touches `u` and
  -- `u ⇝ v`, then every support edge incident to `v` lies in `N`.
  have spread : ∀ {u v : V}, Reachable tail head edges u v →
      (∃ e ∈ N, tail e = u ∨ head e = u) →
      ∀ f ∈ edges, tail f = v ∨ head f = v → f ∈ N := by
    intro u v h
    induction h with
    | refl =>
        intro ht f hf hinc
        obtain ⟨e, he, hue⟩ := ht
        rcases hue with h1 | h1 <;> rcases hinc with h2 | h2
        · exact hclosed e he f hf (Or.inl (h1.trans h2.symm))
        · exact hclosed e he f hf (Or.inr (Or.inl (h1.trans h2.symm)))
        · exact hclosed e he f hf (Or.inr (Or.inr (Or.inl (h1.trans h2.symm))))
        · exact hclosed e he f hf (Or.inr (Or.inr (Or.inr (h1.trans h2.symm))))
    | step g hpred hgf hgt hgv ih =>
        intro ht f hf hinc
        -- `g` joins `N` via the IH (it leaves the reached vertex `w`);
        -- `f` then joins via `g` (both touch `head g`).
        have hgN : g ∈ N := ih ht g hgf (Or.inl hgt)
        rcases hinc with h2 | h2
        · exact hclosed g hgN f hf
            (Or.inr (Or.inr (Or.inl (hgv.trans h2.symm))))
        · exact hclosed g hgN f hf
            (Or.inr (Or.inr (Or.inr (hgv.trans h2.symm))))
  -- Pick `e₀ ∈ N` and `e₁ ∈ edges ∖ N`; the path
  -- `tail e₀ ⇝ tail e₁` drags `e₁` into `N`. Contradiction.
  obtain ⟨e₀, he₀⟩ := hNe
  have he₀e := hNsub he₀
  have hne' : ∃ e₁ ∈ edges, e₁ ∉ N := by
    by_contra h
    rw [not_exists] at h
    have hsub : edges ⊆ N := fun x hx => by
      by_contra hc
      exact h x ⟨hx, hc⟩
    exact hNne (Finset.Subset.antisymm hNsub hsub)
  obtain ⟨e₁, he₁, habs⟩ := hne'
  have hu₀ : tail e₀ ∈ nodes := (hmem e₀ he₀e).1
  have hv₁ : tail e₁ ∈ nodes := (hmem e₁ he₁).1
  exact habs (spread (hstrong _ hu₀ _ hv₁) ⟨e₀, he₀, Or.inl rfl⟩
    e₁ he₁ (Or.inl rfl))

/-- Two distinct members contribute at most the whole sum. -/
private lemma pair_le_sum (s : Finset E) (f : E → ℕ) (a b : E)
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    f a + f b ≤ ∑ x ∈ s, f x := by
  have hsub : {a, b} ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  calc f a + f b = ∑ x ∈ {a, b}, f x := (Finset.sum_pair hab).symm
    _ ≤ ∑ x ∈ s, f x :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)

/-- Three distinct members contribute at most the whole sum. -/
private lemma triple_le_sum (s : Finset E) (f : E → ℕ) (a b c : E)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    f a + f b + f c ≤ ∑ x ∈ s, f x := by
  have hsub : {a, b, c} ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have hani : a ∉ ({b, c} : Finset E) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hab, hac⟩
  have htri : ∑ x ∈ {a, b, c}, f x = f a + f b + f c := by
    rw [show ({a, b, c} : Finset E) = insert a {b, c} from rfl,
      Finset.sum_insert hani, Finset.sum_pair hbc, ← add_assoc]
  rw [← htri]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)

/-- **Theorem A (short-repeat rigidity, issue #66).** A positive circulation `A`
whose vertex throughput is at most `2` (i.e. `out_A(v) = in_A(v) ≤ 2` at every
node: equality from `hAbal`, the bound from `hcap`) is the unique positive
circulation of the same total on a strongly connected support. This is the
Lean-checked core of note §3: with `δ = B - A`, the negative set `N = {δ < 0}`
is shown to be a union of connected components, hence empty (it cannot be
everything since `∑ δ = 0`). -/
theorem unique_positive_circulation
    (G : ℕ) (A B : E → ℕ)
    (hmem : ∀ e ∈ edges, tail e ∈ nodes ∧ head e ∈ nodes)
    (hApos : ∀ e ∈ edges, 1 ≤ A e)
    (hBpos : ∀ e ∈ edges, 1 ≤ B e)
    (hAbal : Balanced tail head nodes edges A)
    (hBbal : Balanced tail head nodes edges B)
    (hAtot : ∑ e ∈ edges, A e = G)
    (hBtot : ∑ e ∈ edges, B e = G)
    (hcap : ∀ v ∈ nodes, ∑ e ∈ outF tail edges v, A e ≤ 2)
    (hstrong : StronglyConnected tail head nodes edges)
    : ∀ e ∈ edges, B e = A e := by
  have hconn : SupportConnected tail head edges :=
    strong_to_supportConnected tail head nodes edges hmem hstrong
  -- The difference circulation `δ = B - A` over `ℤ`.
  set δ : E → ℤ := fun e => (B e : ℤ) - (A e : ℤ) with hδdef
  have hδbal : ∀ v ∈ nodes,
      ∑ e ∈ outF tail edges v, δ e = ∑ e ∈ inF head edges v, δ e := by
    intro v hv
    have h1 := hAbal v hv
    have h2 := hBbal v hv
    simp only [hδdef, Finset.sum_sub_distrib, ← Nat.cast_sum]
    rw [h1, h2]
  have hδtot : ∑ e ∈ edges, δ e = 0 := by
    simp only [hδdef, Finset.sum_sub_distrib, ← Nat.cast_sum, hAtot, hBtot,
      sub_self]
  -- Edge cap: each `A e ≤ out_A(tail e) ≤ 2`.
  have hA2 : ∀ e ∈ edges, A e ≤ 2 := by
    intro e he
    have hcapv := hcap (tail e) (hmem e he).1
    have hmemf : e ∈ outF tail edges (tail e) :=
      Finset.mem_filter.mpr ⟨he, rfl⟩
    have hle := Finset.single_le_sum (f := fun e' => A e')
      (fun _ _ => Nat.zero_le _) hmemf
    unfold outF at hle hcapv
    omega
  have hδlo : ∀ e ∈ edges, -1 ≤ δ e := by
    intro e he
    have h1 := hA2 e he
    have h2 := hBpos e he
    simp only [hδdef]
    omega
  -- The negative set `N = {δ < 0}`.
  set N : Finset E := edges.filter (fun e => δ e < 0) with hNdef
  have hNsub : N ⊆ edges := Finset.filter_subset _ _
  have hNmem : ∀ e : E, e ∈ N ↔ e ∈ edges ∧ δ e < 0 := by
    intro e
    simp only [hNdef, Finset.mem_filter]
  -- On `N`, the values are pinned: `δ = -1`, `A = 2`, `B = 1`.
  have hNchar : ∀ e ∈ N, δ e = -1 ∧ A e = 2 ∧ B e = 1 := by
    intro e he
    have ⟨hee, hlt⟩ := (hNmem e).mp he
    have h1 := hA2 e hee
    have h2 := hBpos e hee
    have h3 := hδlo e hee
    simp only [hδdef] at hlt h3 ⊢
    refine ⟨by omega, by omega, by omega⟩
  -- In-flow analysis at a node with `A`-inflow `2` and `δ`-inflow `-1`:
  -- there is a unique in-edge, it lies ∈ `N`.
  have inAnalysis : ∀ v ∈ nodes,
      ∑ e ∈ inF head edges v, A e = 2 →
      ∑ e ∈ inF head edges v, δ e = -1 →
      ∃ e0, e0 ∈ edges ∧ head e0 = v ∧ e0 ∈ N ∧
        ∀ e' ∈ edges, head e' = v → e' = e0 := by
    intro v hv hAin hδin
    have hsub1 : ∀ e1 ∈ inF head edges v, ∀ e2 ∈ inF head edges v, e1 = e2 := by
      intro e1 h1 e2 h2
      by_contra hne
      have hm1 := (Finset.mem_filter.mp h1).1
      have hm2 := (Finset.mem_filter.mp h2).1
      have g1 := hApos e1 hm1
      have g2 := hApos e2 hm2
      have hp := pair_le_sum (inF head edges v) A e1 e2 h1 h2 hne
      have e1eq : A e1 = 1 := by omega
      have e2eq : A e2 = 1 := by omega
      have h23 : ∀ e3 ∈ inF head edges v, e3 = e1 ∨ e3 = e2 := by
        intro e3 h3
        by_contra hc
        have hc1 : e3 ≠ e1 := fun h => hc (Or.inl h)
        have hc2 : e3 ≠ e2 := fun h => hc (Or.inr h)
        have hm3 := (Finset.mem_filter.mp h3).1
        have g3 := hApos e3 hm3
        have ht := triple_le_sum (inF head edges v) A e1 e2 e3
          h1 h2 h3 hne hc1.symm hc2.symm
        omega
      have hIFeq : inF head edges v = {e1, e2} := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun hx => h23 x hx, fun hx => hx.elim
          (fun h => h ▸ h1) (fun h => h ▸ h2)⟩
      have hsumδ : ∑ e' ∈ inF head edges v, δ e' = δ e1 + δ e2 := by
        rw [hIFeq, Finset.sum_pair hne]
      have d1 : 0 ≤ δ e1 := by
        have gB := hBpos e1 hm1
        simp only [hδdef]
        omega
      have d2 : 0 ≤ δ e2 := by
        have gB := hBpos e2 hm2
        simp only [hδdef]
        omega
      omega
    have hne0 : ∃ e0, e0 ∈ inF head edges v := by
      by_contra h
      rw [not_exists] at h
      have hempty : inF head edges v = ∅ :=
        Finset.eq_empty_iff_forall_notMem.mpr h
      rw [hempty, Finset.sum_empty] at hAin
      omega
    obtain ⟨e0, he0⟩ := hne0
    have hsing : inF head edges v = {e0} :=
      Finset.eq_singleton_iff_unique_mem.mpr
        ⟨he0, fun x hx => hsub1 x hx e0 he0⟩
    have hδ0 : δ e0 = -1 := by
      have h := hδin
      rw [hsing, Finset.sum_singleton] at h
      exact h
    have he0e := (Finset.mem_filter.mp he0).1
    have he0h := (Finset.mem_filter.mp he0).2
    refine ⟨e0, he0e, he0h, (hNmem e0).mpr ⟨he0e, by omega⟩, ?_⟩
    intro e' he' hhe'
    exact hsub1 e' (Finset.mem_filter.mpr ⟨he', hhe'⟩) e0 he0
  -- Out-flow analysis: symmetric statement for out-edges.
  have outAnalysis : ∀ v ∈ nodes,
      ∑ e ∈ outF tail edges v, A e = 2 →
      ∑ e ∈ outF tail edges v, δ e = -1 →
      ∃ e0, e0 ∈ edges ∧ tail e0 = v ∧ e0 ∈ N ∧
        ∀ e' ∈ edges, tail e' = v → e' = e0 := by
    intro v hv hAout hδout
    have hsub1 : ∀ e1 ∈ outF tail edges v, ∀ e2 ∈ outF tail edges v, e1 = e2 := by
      intro e1 h1 e2 h2
      by_contra hne
      have hm1 := (Finset.mem_filter.mp h1).1
      have hm2 := (Finset.mem_filter.mp h2).1
      have g1 := hApos e1 hm1
      have g2 := hApos e2 hm2
      have hp := pair_le_sum (outF tail edges v) A e1 e2 h1 h2 hne
      have e1eq : A e1 = 1 := by omega
      have e2eq : A e2 = 1 := by omega
      have h23 : ∀ e3 ∈ outF tail edges v, e3 = e1 ∨ e3 = e2 := by
        intro e3 h3
        by_contra hc
        have hc1 : e3 ≠ e1 := fun h => hc (Or.inl h)
        have hc2 : e3 ≠ e2 := fun h => hc (Or.inr h)
        have hm3 := (Finset.mem_filter.mp h3).1
        have g3 := hApos e3 hm3
        have ht := triple_le_sum (outF tail edges v) A e1 e2 e3
          h1 h2 h3 hne hc1.symm hc2.symm
        omega
      have hOF : outF tail edges v = {e1, e2} := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun hx => h23 x hx, fun hx => hx.elim
          (fun h => h ▸ h1) (fun h => h ▸ h2)⟩
      have hsumδ : ∑ e' ∈ outF tail edges v, δ e' = δ e1 + δ e2 := by
        rw [hOF, Finset.sum_pair hne]
      have d1 : 0 ≤ δ e1 := by
        have gB := hBpos e1 hm1
        simp only [hδdef]
        omega
      have d2 : 0 ≤ δ e2 := by
        have gB := hBpos e2 hm2
        simp only [hδdef]
        omega
      omega
    have hne0 : ∃ e0, e0 ∈ outF tail edges v := by
      by_contra h
      rw [not_exists] at h
      have hempty : outF tail edges v = ∅ :=
        Finset.eq_empty_iff_forall_notMem.mpr h
      rw [hempty, Finset.sum_empty] at hAout
      omega
    obtain ⟨e0, he0⟩ := hne0
    have hsing : outF tail edges v = {e0} :=
      Finset.eq_singleton_iff_unique_mem.mpr
        ⟨he0, fun x hx => hsub1 x hx e0 he0⟩
    have hδ0 : δ e0 = -1 := by
      have h := hδout
      rw [hsing, Finset.sum_singleton] at h
      exact h
    have he0e := (Finset.mem_filter.mp he0).1
    have he0t := (Finset.mem_filter.mp he0).2
    refine ⟨e0, he0e, he0t, (hNmem e0).mpr ⟨he0e, by omega⟩, ?_⟩
    intro e' he' hte'
    exact hsub1 e' (Finset.mem_filter.mpr ⟨he', hte'⟩) e0 he0
  -- Tail-side closure: every edge incident to `tail e` lies ∈ `N`.
  -- Since `A e = 2` meets the node cap, `e` is the unique out-edge, so
  -- `δ` sums to `-1` on both sides and the in-analysis closes the node.
  have tailClosed : ∀ e ∈ N, ∀ e' ∈ edges,
      (tail e' = tail e ∨ head e' = tail e) → e' ∈ N := by
    intro e he e' he' hinc
    have ⟨hδe, hAe, _⟩ := hNchar e he
    have hee := hNsub he
    have hv : tail e ∈ nodes := (hmem e hee).1
    have hcapv := hcap (tail e) hv
    have hAout2 : ∑ x ∈ outF tail edges (tail e), A x = 2 := by
      have hmemf : e ∈ outF tail edges (tail e) :=
        Finset.mem_filter.mpr ⟨hee, rfl⟩
      have hle := Finset.single_le_sum (f := fun x => A x)
        (fun _ _ => Nat.zero_le _) hmemf
      omega
    -- `e` is the unique out-edge at its tail.
    have houtU : ∀ x ∈ edges, tail x = tail e → x = e := by
      intro x hx htx
      by_contra hne
      have g := hApos x hx
      have h1 : e ∈ outF tail edges (tail e) :=
        Finset.mem_filter.mpr ⟨hee, rfl⟩
      have h2 : x ∈ outF tail edges (tail e) :=
        Finset.mem_filter.mpr ⟨hx, htx⟩
      have hp := pair_le_sum (outF tail edges (tail e)) A e x h1 h2
        (Ne.symm hne)
      omega
    have hOFsing : outF tail edges (tail e) = {e} :=
      Finset.eq_singleton_iff_unique_mem.mpr
        ⟨Finset.mem_filter.mpr ⟨hee, rfl⟩,
          fun x hx => houtU x (Finset.mem_filter.mp hx).1
            (Finset.mem_filter.mp hx).2⟩
    have hδoutm1 : ∑ x ∈ outF tail edges (tail e), δ x = -1 := by
      rw [hOFsing, Finset.sum_singleton]
      exact hδe
    have hδinm1 : ∑ x ∈ inF head edges (tail e), δ x = -1 := by
      rw [← hδbal (tail e) hv]
      exact hδoutm1
    have hAin2 : ∑ x ∈ inF head edges (tail e), A x = 2 := by
      have h := hAbal (tail e) hv
      omega
    obtain ⟨g0, _, _, hg0N, huniq⟩ := inAnalysis (tail e) hv hAin2 hδinm1
    rcases hinc with hte | hhe
    · rw [houtU e' he' hte]
      exact he
    · rw [huniq e' he' hhe]
      exact hg0N
  -- Head-side closure: every edge incident to `head e` lies ∈ `N`.
  -- Since `A e = 2`, the inflow cap (via balance) makes `e` the unique
  -- in-edge, so `δ` sums to `-1` on both sides and the out-analysis closes it.
  have headClosed : ∀ e ∈ N, ∀ e' ∈ edges,
      (tail e' = head e ∨ head e' = head e) → e' ∈ N := by
    intro e he e' he' hinc
    have ⟨hδe, hAe, _⟩ := hNchar e he
    have hee := hNsub he
    have hu : head e ∈ nodes := (hmem e hee).2
    have hAin2 : ∑ x ∈ inF head edges (head e), A x = 2 := by
      have hcapu := hcap (head e) hu
      have hbalu := hAbal (head e) hu
      have hmemf : e ∈ inF head edges (head e) :=
        Finset.mem_filter.mpr ⟨hee, rfl⟩
      have hle := Finset.single_le_sum (f := fun x => A x)
        (fun _ _ => Nat.zero_le _) hmemf
      omega
    -- `e` is the unique in-edge at its head.
    have hinU : ∀ x ∈ edges, head x = head e → x = e := by
      intro x hx hhx
      by_contra hne
      have g := hApos x hx
      have h1 : e ∈ inF head edges (head e) :=
        Finset.mem_filter.mpr ⟨hee, rfl⟩
      have h2 : x ∈ inF head edges (head e) :=
        Finset.mem_filter.mpr ⟨hx, hhx⟩
      have hp := pair_le_sum (inF head edges (head e)) A e x h1 h2
        (Ne.symm hne)
      omega
    have hIFsing : inF head edges (head e) = {e} :=
      Finset.eq_singleton_iff_unique_mem.mpr
        ⟨Finset.mem_filter.mpr ⟨hee, rfl⟩,
          fun x hx => hinU x (Finset.mem_filter.mp hx).1
            (Finset.mem_filter.mp hx).2⟩
    have hδinm1 : ∑ x ∈ inF head edges (head e), δ x = -1 := by
      rw [hIFsing, Finset.sum_singleton]
      exact hδe
    have hδoutm1 : ∑ x ∈ outF tail edges (head e), δ x = -1 := by
      have h := hδbal (head e) hu
      omega
    have hAout2 : ∑ x ∈ outF tail edges (head e), A x = 2 := by
      have h := hAbal (head e) hu
      omega
    obtain ⟨f0, _, _, hf0N, huniq⟩ := outAnalysis (head e) hu hAout2 hδoutm1
    rcases hinc with hte | hhe
    · rw [huniq e' he' hte]
      exact hf0N
    · rw [hinU e' he' hhe]
      exact he
  -- `N` is closed under incidence, hence empty or everything.
  have hclosed : ∀ e ∈ N, ∀ e' ∈ edges,
      (tail e = tail e' ∨ tail e = head e' ∨ head e = tail e' ∨
        head e = head e') → e' ∈ N := by
    intro e he e' he' hshare
    rcases hshare with h | h | h | h
    · exact tailClosed e he e' he' (Or.inl h.symm)
    · exact tailClosed e he e' he' (Or.inr h.symm)
    · exact headClosed e he e' he' (Or.inl h.symm)
    · exact headClosed e he e' he' (Or.inr h.symm)
  by_cases hNe : N.Nonempty
  · -- `N` cannot be proper: connectivity plus closure forces `N = edges`.
    have hNeq : N = edges := by
      by_contra hne
      obtain ⟨e, heN, e', he'e, he'N, hshare⟩ := hconn N hNsub hNe hne
      exact he'N (hclosed e heN e' he'e hshare)
    -- But then `∑ δ = -|edges| < 0`, contradicting `∑ δ = 0`.
    have h1 : ∑ e ∈ N, δ e = -(N.card : ℤ) := by
      have hsum : ∑ e ∈ N, δ e = ∑ _e ∈ N, (-1 : ℤ) :=
        Finset.sum_congr rfl (fun e he => (hNchar e he).1)
      rw [hsum, Finset.sum_const, nsmul_eq_mul]
      simp
    have hcard : N.card = 0 := by
      have h2 : (-(N.card : ℤ)) = 0 := by
        rw [← h1, hNeq]
        exact hδtot
      omega
    rw [Finset.card_eq_zero] at hcard
    exact absurd hcard (Finset.nonempty_iff_ne_empty.mp hNe)
  · -- `N` empty: `δ ≥ 0` everywhere with total `0`, so `δ = 0` and `B = A`.
    rw [Finset.not_nonempty_iff_eq_empty] at hNe
    have hnn : ∀ e ∈ edges, 0 ≤ δ e := by
      intro e he
      by_contra hlt
      replace hlt : δ e < 0 := lt_of_not_ge hlt
      have hmemN : e ∈ N := (hNmem e).mpr ⟨he, hlt⟩
      rw [hNe] at hmemN
      exact Finset.notMem_empty e hmemN
    have hall : ∀ e ∈ edges, δ e = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hδtot
    intro e he
    have h0 := hall e he
    have h2 := hBpos e he
    simp only [hδdef] at h0
    omega

end AbstractCirculation

end AssemblyP1.OrientedRigidity
