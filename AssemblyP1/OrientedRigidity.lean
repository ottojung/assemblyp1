import Mathlib

/-!
# Oriented same-length rigidity (strict single-strand Section 6.2)

This file formalizes the project's central positive finite theorem (issue #63,
Priority 1) ∈ the smallest clean abstraction faithful to the current paper
proof ∈ `docs/source-notes/oriented-se62-rigidity-theorem.md`:

> Under strict oriented read types, if the truth admits an `I_s` read
> realization, then its length-`L` spectrum is the unique positive circulation
> of total genome length on its window-support graph.

Consequently every same-length oriented §6.2 spelled candidate has the truth's
spectrum, every spectrum/count-based likelihood ratio is exactly `1`, and no
strict same-length counterexample exists — for any `G`, `L`, or alphabet.

## What is proved ∈ Lean vs. cited

* **Lean-checked:** the short-repeat rigidity core (`unique_positive_circulation`,
  Theorem A of the note: a node-outflow bound of `2` forces uniqueness of the
  positive circulation of fixed total on a connected support); its application
  to circular-word spectra (`rigidity_same_spectrum`); the likelihood-tie
  corollaries; rotation uniqueness **conditional** on an explicit
  complete-spectrum hypothesis (`rigidity_up_to_rotation`).
* **Explicit hypotheses (trust boundary), each citing the note:**
  - `hAbal`: the truth spectrum is balanced (note §2, Fact 1);
  - `hconn`: the window support is (undirectedly) connected (note §2, Fact 2);
  - `hcap`: every `(L-1)`-mer occurs at most twice. By note §3 (Fact D,
    Lemmas B and C) this follows from the triple-repeat clause of `I_s`, in
    both the primitive and the periodic cases. The word combinatorics of that
    implication is cited, not re-proved here;
  - `bbt`: the external Bresler–Bresler–Tse complete-spectrum uniqueness
    theorem, exposed as an explicit hypothesis per issue #63 (full
    formalization of BBT is out of scope).
* **Deliberately not formalized here:** the `I_s` bridging predicates
  themselves, the Medvedev–Brudno likelihood layers, tie/equivalence source
  semantics, and bounded-search minimality results.

The rigidity argument proves uniqueness on the full set of positive
circulations, so it covers the Eulerian single-circuit spelled candidates
a fortiori (note §2, Reduction R).
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

/-- **Theorem A (short-repeat rigidity).** A positive circulation `A` whose
node outflows are all at most `2` is the unique positive circulation of the
same total on a connected support. This is the Lean-checked core of note §3:
with `δ = B - A`, the negative set `N = {δ < 0}` is shown to be a union of
connected components, hence empty (it cannot be everything since `∑ δ = 0`). -/
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
    (hconn : SupportConnected tail head edges)
    : ∀ e ∈ edges, B e = A e := by
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

section WordLayer

/-- Circular symbol access for a length-`G` circular word. -/
def cyc {α : Type} {G : ℕ} (hG : 0 < G) (S : Fin G → α) (i : ℕ) : α :=
  S ⟨i % G, Nat.mod_lt _ hG⟩

/-- Oriented length-`L` circular window at start `r` (strict single-strand
read type: no reverse-complement collapse). -/
def window {α : Type} {G L : ℕ} (hG : 0 < G) (S : Fin G → α) (r : Fin G) :
    Fin L → α :=
  fun d => cyc hG S (r.val + d.val)

/-- Length-`(L-1)` circular window at start `r` (de Bruijn node). -/
def nodeWindow {α : Type} {G L : ℕ} (hG : 0 < G) (S : Fin G → α) (r : Fin G) :
    Fin (L - 1) → α :=
  fun d => cyc hG S (r.val + d.val)

/-- Length-`L` spectrum: occurrence counts of each window. -/
noncomputable def specCount {α : Type} [DecidableEq α] {G L : ℕ} (hG : 0 < G)
    (S : Fin G → α) (w : Fin L → α) : ℕ := by
  classical
  exact (Finset.univ.filter (fun r : Fin G => window hG S r = w)).card

/-- Window support: the observed read-type set. -/
noncomputable def support {α : Type} [DecidableEq α] {G L : ℕ} (hG : 0 < G)
    (S : Fin G → α) : Finset (Fin L → α) := by
  classical
  exact Finset.univ.image (window hG S)

/-- Node set: the distinct `(L-1)`-windows. -/
noncomputable def genomeNodes {α : Type} [DecidableEq α] {G L : ℕ} (hG : 0 < G)
    (S : Fin G → α) : Finset (Fin (L - 1) → α) := by
  classical
  exact Finset.univ.image (nodeWindow hG S)

/-- Edge tail: length-`(L-1)` winPrefix. -/
def winPrefix {α : Type} {L : ℕ} (w : Fin L → α) : Fin (L - 1) → α :=
  fun d => w ⟨d.val, by have := d.isLt; omega⟩

/-- Edge head: length-`(L-1)` winSuffix. -/
def winSuffix {α : Type} {L : ℕ} (w : Fin L → α) : Fin (L - 1) → α :=
  fun d => w ⟨d.val + 1, by have := d.isLt; omega⟩

/-- Start `r + 1` as a start of the circular word. -/
private def nextStart {G : ℕ} (hG : 0 < G) (r : Fin G) : Fin G :=
  ⟨(r.val + 1) % G, Nat.mod_lt _ hG⟩

/-- The winPrefix of a window is the node window at the same start. -/
private lemma winPrefix_window {α : Type} {G L : ℕ} (hG : 0 < G) (S : Fin G → α)
    (r : Fin G) :
    winPrefix (window hG S r : Fin L → α) = nodeWindow hG S r := by
  funext d
  rfl

/-- The winSuffix of a window is the node window at the next start. -/
private lemma winSuffix_window {α : Type} {G L : ℕ} (hG : 0 < G) (S : Fin G → α)
    (r : Fin G) :
    winSuffix (window hG S r : Fin L → α) = nodeWindow hG S (nextStart hG r) := by
  funext d
  have hmod : ((r.val + 1) % G + d.val) % G = (r.val + (d.val + 1)) % G := by
    rw [Nat.mod_add_mod]
    congr 1
    omega
  unfold winSuffix window nodeWindow nextStart cyc
  apply congrArg S
  rw [Fin.mk.injEq]
  exact hmod.symm

/-- Support edges land ∈ the node set (the graph is well-formed). -/
theorem mem_nodes_of_mem_support {α : Type} [DecidableEq α] {G L : ℕ} (hG : 0 < G)
    (S : Fin G → α) (w : Fin L → α)
    (hw : w ∈ support hG S) :
    winPrefix w ∈ genomeNodes hG S ∧
      winSuffix w ∈ genomeNodes hG S := by
  classical
  simp only [support, Finset.mem_image] at hw
  obtain ⟨r, _, rfl⟩ := hw
  constructor
  · rw [winPrefix_window]
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
  · rw [winSuffix_window]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

/-- The truth spectrum is positive on its own support. -/
theorem truth_pos_on_support {α : Type} [DecidableEq α] {G L : ℕ} (hG : 0 < G)
    (S : Fin G → α) :
    ∀ w : Fin L → α, w ∈ support hG S → 1 ≤ specCount hG S w := by
  classical
  intro w hw
  simp only [support, Finset.mem_image] at hw
  obtain ⟨r, _, rfl⟩ := hw
  have hmem : r ∈ Finset.univ.filter
      (fun r' : Fin G => window hG S r' = (window hG S r : Fin L → α)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hpos : 0 < specCount hG S (window hG S r : Fin L → α) :=
    Finset.card_pos.mpr ⟨r, hmem⟩
  omega

/-- The truth spectrum totals to `G` over its support (fiber counting). -/
theorem truth_total {α : Type} [DecidableEq α] {G L : ℕ} (hG : 0 < G)
    (S : Fin G → α) :
    ∑ w ∈ (support hG S : Finset (Fin L → α)), specCount hG S w = G := by
  classical
  have hfib : ∀ w ∈ (support hG S : Finset (Fin L → α)),
      (Finset.univ.filter (fun r : Fin G => window hG S r = w)).card =
        specCount hG S w := fun _ _ => rfl
  rw [← Finset.sum_congr rfl hfib]
  have hmem : ∀ r ∈ (Finset.univ : Finset (Fin G)),
      window hG S r ∈ (support hG S : Finset (Fin L → α)) := by
    intro r _
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
  have hcount := Finset.card_eq_sum_card_fiberwise hmem
  rw [Finset.card_univ, Fintype.card_fin] at hcount
  exact hcount.symm

/-- **Main theorem (rigidity under the triple-repeat hypothesis).**
If every `(L-1)`-mer occurs at most twice (`hcap` — the exact hypothesis
discharged by note §3, Fact D with Lemmas B/C, from the triple-repeat clause
of `I_s` ∈ both primitive and periodic cases), the window support is
connected (`hconn` — note §2, Fact 2), and the truth spectrum is balanced
(`hAbal` — note §2, Fact 1), then every same-length spelled candidate
(same support, positive balanced circulation of total `G`) has exactly the
truth's spectrum. -/
theorem rigidity_same_spectrum
    {α : Type} [DecidableEq α] {G L : ℕ} (hG : 0 < G)
    (S : Fin G → α)
    (B : (Fin L → α) → ℕ)
    (hBsup : ∀ w, w ∈ support hG S ↔ 0 < B w)
    (hBbal : Balanced winPrefix winSuffix
      (genomeNodes hG S) (support hG S) B)
    (hBtot : ∑ w ∈ support hG S, B w = G)
    (hAbal : Balanced winPrefix winSuffix
      (genomeNodes hG S) (support hG S) (specCount hG S : (Fin L → α) → ℕ))
    (hcap : ∀ k : Fin (L - 1) → α, k ∈ genomeNodes hG S →
      ∑ w ∈ (support hG S).filter (fun w => winPrefix w = k),
        specCount hG S w ≤ 2)
    (hconn : SupportConnected winPrefix winSuffix
      (support hG S : Finset (Fin L → α)))
    : ∀ w, B w = specCount hG S w := by
  classical
  have hApos : ∀ w : Fin L → α, w ∈ support hG S → 1 ≤ specCount hG S w :=
    truth_pos_on_support (L := L) hG S
  have hAtot := truth_total (L := L) hG S
  have hBpos : ∀ w ∈ support hG S, 1 ≤ B w := fun w hw => (hBsup w).mp hw
  have hmemT : ∀ w : Fin L → α, w ∈ support hG S →
      winPrefix w ∈ genomeNodes hG S ∧ winSuffix w ∈ genomeNodes hG S :=
    mem_nodes_of_mem_support (L := L) hG S
  have heq := unique_positive_circulation (winPrefix) (winSuffix)
    (genomeNodes hG S) (support hG S) G (specCount hG S) B
    hmemT hApos hBpos hAbal hBbal hAtot hBtot hcap hconn
  intro w
  by_cases hw : w ∈ support hG S
  · exact heq w hw
  · have hB0 : B w = 0 := Nat.eq_zero_of_not_pos (fun h => hw ((hBsup w).mpr h))
    have hA0 : specCount hG S w = 0 := by
      have hemp : Finset.univ.filter (fun r : Fin G => window hG S r = w) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro r hr
        apply hw
        have hwr : window hG S r = w := (Finset.mem_filter.mp hr).2
        rw [← hwr]
        exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
      show (Finset.univ.filter (fun r : Fin G => window hG S r = w)).card = 0
      rw [hemp, Finset.card_empty]
    rw [hB0, hA0]

/-- Cyclic-shift (rotation) equivalence of same-length circular genomes. -/
def RotEquiv {α : Type} {G : ℕ} (hG : 0 < G) (D₁ D₂ : Fin G → α) : Prop :=
  ∃ s : Fin G, ∀ i : Fin G, D₁ i = D₂ ⟨(i.val + s.val) % G, Nat.mod_lt _ hG⟩

/-- **Rotation uniqueness, conditional on the external complete-spectrum
theorem.** With the same hypotheses as `rigidity_same_spectrum`, plus the
Bresler–Bresler–Tse complete-spectrum uniqueness input (`bbt`: equal
length-`L` spectra determine the genome up to rotation — cited, not proved;
formalizing BBT is out of scope per issue #63), every same-length spelled
candidate is a rotation of the truth. Project reduction: Lean-checked;
external BBT input: cited. -/
theorem rigidity_up_to_rotation
    {α : Type} [DecidableEq α] {G L : ℕ} (hG : 0 < G)
    (S D : Fin G → α)
    (hDsup : ∀ w : Fin L → α, w ∈ support hG S ↔ 0 < specCount hG D w)
    (hDbal : Balanced winPrefix winSuffix
      (genomeNodes hG S) (support hG S) (specCount hG D : (Fin L → α) → ℕ))
    (hDtot : ∑ w ∈ (support hG S : Finset (Fin L → α)), specCount hG D w = G)
    (hAbal : Balanced winPrefix winSuffix
      (genomeNodes hG S) (support hG S) (specCount hG S : (Fin L → α) → ℕ))
    (hcap : ∀ k : Fin (L - 1) → α, k ∈ genomeNodes hG S →
      ∑ w ∈ (support hG S).filter (fun w => winPrefix w = k),
        specCount hG S w ≤ 2)
    (hconn : SupportConnected winPrefix winSuffix
      (support hG S : Finset (Fin L → α)))
    (bbt : ∀ D₁ D₂ : Fin G → α,
      (specCount hG D₁ : (Fin L → α) → ℕ) = specCount hG D₂ → RotEquiv hG D₁ D₂)
    : RotEquiv hG D S := by
  classical
  have hspec : ∀ w : Fin L → α, specCount hG D w = specCount hG S w :=
    rigidity_same_spectrum hG S (specCount hG D)
      hDsup hDbal hDtot hAbal hcap hconn
  exact bbt D S (funext hspec)

/-- **Corollary (same-length likelihood tie).** Any objective depending only
on the length-`L` spectrum and the observation ties the truth on the
same-length slice — covering both the exact multinomial (candidate-intrinsic
`N(D) = |D|`, same length so length factors cancel) and the fixed-`N` §6.1
binomial objectives of the note. -/
theorem spectrum_tie
    {α : Type} [DecidableEq α] {G L : ℕ} (hG : 0 < G)
    (obj : ((Fin L → α) → ℕ) → ℝ)
    (S : Fin G → α)
    (B : (Fin L → α) → ℕ)
    (hBsup : ∀ w, w ∈ support hG S ↔ 0 < B w)
    (hBbal : Balanced winPrefix winSuffix
      (genomeNodes hG S) (support hG S) B)
    (hBtot : ∑ w ∈ support hG S, B w = G)
    (hAbal : Balanced winPrefix winSuffix
      (genomeNodes hG S) (support hG S) (specCount hG S : (Fin L → α) → ℕ))
    (hcap : ∀ k : Fin (L - 1) → α, k ∈ genomeNodes hG S →
      ∑ w ∈ (support hG S).filter (fun w => winPrefix w = k),
        specCount hG S w ≤ 2)
    (hconn : SupportConnected winPrefix winSuffix
      (support hG S : Finset (Fin L → α)))
    : obj B = obj (specCount hG S) := by
  classical
  have hspec : ∀ w : Fin L → α, B w = specCount hG S w :=
    rigidity_same_spectrum hG S B hBsup hBbal hBtot hAbal hcap hconn
  rw [funext hspec]

/-- **Corollary (no strict same-length counterexample).** No same-length
spelled candidate strictly improves on the truth under any spectrum-based
objective, for any `G`, `L`, or alphabet. -/
theorem no_strict_samelength_improvement
    {α : Type} [DecidableEq α] {G L : ℕ} (hG : 0 < G)
    (obj : ((Fin L → α) → ℕ) → ℝ)
    (S : Fin G → α)
    (B : (Fin L → α) → ℕ)
    (hBsup : ∀ w, w ∈ support hG S ↔ 0 < B w)
    (hBbal : Balanced winPrefix winSuffix
      (genomeNodes hG S) (support hG S) B)
    (hBtot : ∑ w ∈ support hG S, B w = G)
    (hAbal : Balanced winPrefix winSuffix
      (genomeNodes hG S) (support hG S) (specCount hG S : (Fin L → α) → ℕ))
    (hcap : ∀ k : Fin (L - 1) → α, k ∈ genomeNodes hG S →
      ∑ w ∈ (support hG S).filter (fun w => winPrefix w = k),
        specCount hG S w ≤ 2)
    (hconn : SupportConnected winPrefix winSuffix
      (support hG S : Finset (Fin L → α)))
    : ¬ obj (specCount hG S) < obj B := by
  classical
  rw [spectrum_tie hG obj S B hBsup hBbal hBtot hAbal hcap hconn]
  exact lt_irrefl _

end WordLayer

end AssemblyP1.OrientedRigidity
