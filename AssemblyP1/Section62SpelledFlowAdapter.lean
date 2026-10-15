import AssemblyP1.Section62FlowCountVectorAdapter

/-!
# The spelled-circuit → §6.2 feasible-flow adapter (#261)

This module closes one of the declared OPEN axes of #261: the construction of a
literal MB09 §6.2 zero-terminal feasible flow from a *spelled* circular candidate
(`Spelling`), with count vector `d = Spelling.visits` and no terminal usage.

The proof sketch recorded in `docs/issue261-axis-matrix-20261014.md` §4 lists
four obligations.  This module discharges all four as a single kernel-checked
theorem `spelling_flow_feasible`:

1. **Throughput.**  `throughput (sp.flow) edges v = sp.visits v`; the cyclic
   walk's edge multiplicities de-duplicate against the `Nodup` graph `edges`
   (`weighted_dedup`, `throughput_eq_visits`).
2. **Balance.**  `balCore (sp.flow) edges v = 0` for every vertex; the signed
   incidences cancel termwise by `BidirectedCircuit`, after reindexing the
   arrival sum by the cyclic predecessor (`balCore_eq_zero`).
3. **Vertex lower bound.**  Carried as the explicit hypothesis
   `∀ v ∈ verts, 1 ≤ sp.visits rep v`; the flow is *not* feasible for an observed
   vertex that the walk never visits, so this hypothesis is genuine.
4. **Terminals / edge bounds.**  `noTerminals` and the zero edge lower bound are
   immediate.

## Candidates, truth, likelihood, length universe

* **Candidates** are *spelled circuits*: circular spellings `Spelling A W n`
  together with the walk flow `Spelling.flow`.  The theorem is about the
  *feasible-flow* representation of such a candidate; it does not assert that
  every feasible flow is spelled.
* **Truth is admitted**: the statement is likelihood-independent.  It identifies
  a spelled candidate's throughput vector as an element of the throughput image
  of the zero-terminal feasible set, which any score factoring through the
  throughput vector (the exact iid score, the fixed-`N` product-binomial
  surrogate, and every count-vector criterion of
  `AssemblyP1.Section62BinomialCriterion`) can then evaluate.
* **Length universe**: all `n ≥ 1` (the `Spelling.hn : 0 < n` field), arbitrary
  `readLen` and arbitrary observed vertex list `verts`.

## What is *not* claimed here

* No characterization of the throughput image: the `AAATT` obstruction
  (`AssemblyP1.Section62NonSpelledFlow.no_sequence_has_star_spectrum`) shows the
  image strictly contains the spelled throughputs, so the converse (every
  feasible throughput is spelled) is false.
* No source-fidelity identification of the exact MB09 objective with the §6.1
  product-binomial surrogate; see `docs/issue261-general-bidirected-flow-ml.md`.
* No transfer of the transitive-reduction axis: `edges` is an abstract `Nodup`
  graph, so the interaction of the reduction with ML maximality stays OPEN.
-/

namespace AssemblyP1.Section62SpelledFlowAdapter

open AssemblyP1.Section62Flow
open AssemblyP1.Section62FlowCountVectorAdapter

variable {A W : Type} [DecidableEq W]

/-! ## The cyclic walk's step list and its multiplicities -/

/-- The list of steps of the cyclic walk of a spelling. -/
def walkSteps {n : Nat} (rep : W → W) (readLen : Nat) (sp : Spelling A W n) :
    List (BdEdge A W) :=
  (List.finRange n).map (sp.step rep readLen)

/-- Every step of the walk is an edge of a graph that contains all steps. -/
theorem walkSteps_subset {n readLen : Nat} (rep : W → W) (sp : Spelling A W n)
    (edges : List (BdEdge A W)) (hSteps : ∀ i : Fin n, sp.step rep readLen i ∈ edges) :
    ∀ s ∈ walkSteps rep readLen sp, s ∈ edges := by
  intro s hs
  rw [walkSteps, List.mem_map] at hs
  obtain ⟨i, _, rfl⟩ := hs
  exact hSteps i

/-- The flow carried by the walk is the multiplicity of an edge among the walk's
steps. -/
theorem flow_eq_mult {n : Nat} (rep : W → W) (readLen : Nat) (sp : Spelling A W n)
    (e : BdEdge A W) :
    sp.flow rep readLen e = (walkSteps rep readLen sp).countP (fun s => decide (s = e)) := by
  unfold Spelling.flow walkSteps
  rw [List.countP_eq_length_filter, List.filter_map]
  simp only [List.length_map]
  rfl

/-! ## The weighted de-duplication identity -/

/-- Summing a multiplicity-weighted function over the distinct elements of a list
`l` that contains all elements of `steps` equals summing the function over
`steps`.  This is the weighted de-duplication step of the adapter. -/
theorem weighted_dedup (l steps : List (BdEdge A W))
    (hsub : ∀ s ∈ steps, s ∈ l) (p : BdEdge A W → Prop) [DecidablePred p]
    {M : Type} [AddCommMonoid M] (g : BdEdge A W → M) :
    ∑ e ∈ l.toFinset, (steps.countP (fun s => decide (s = e))) • (if p e then g e else 0)
      = (steps.map (fun s => if p s then g s else 0)).sum := by
  induction steps with
  | nil => simp
  | cons t ts ih =>
    have hsub_ts : ∀ s ∈ ts, s ∈ l := fun s hs => hsub s (List.mem_cons_of_mem t hs)
    have hcount : ∀ e, (t :: ts).countP (fun s => decide (s = e))
        = ts.countP (fun s => decide (s = e)) + (if t = e then 1 else 0) := by
      intro e
      rw [List.countP_cons]
      congr 1
      by_cases h : t = e <;> simp [h]
    have hsimp : ∀ e, (if t = e then (1 : ℕ) else 0) • (if p e then g e else 0)
        = if t = e then (if p e then g e else 0) else 0 := by
      intro e
      by_cases h : t = e <;> simp [h]
    rw [List.map_cons, List.sum_cons]
    calc ∑ e ∈ l.toFinset, (t :: ts).countP (fun s => decide (s = e)) • (if p e then g e else 0)
        = ∑ e ∈ l.toFinset, (ts.countP (fun s => decide (s = e)) • (if p e then g e else 0)
            + (if t = e then (1 : ℕ) else 0) • (if p e then g e else 0)) := by
          apply Finset.sum_congr rfl
          intro e _
          rw [hcount e, add_nsmul]
        _ = (∑ e ∈ l.toFinset, ts.countP (fun s => decide (s = e)) • (if p e then g e else 0))
            + ∑ e ∈ l.toFinset, (if t = e then (1 : ℕ) else 0) • (if p e then g e else 0) := by
          rw [Finset.sum_add_distrib]
        _ = (ts.map (fun s => if p s then g s else 0)).sum + (if p t then g t else 0) := by
          congr 1
          · exact ih hsub_ts
          · have h2 : ∑ e ∈ l.toFinset, (if t = e then (1 : ℕ) else 0) • (if p e then g e else 0)
                = ∑ e ∈ l.toFinset, (if t = e then (if p e then g e else 0) else 0) :=
              Finset.sum_congr rfl (fun e _ => hsimp e)
            rw [h2, Finset.sum_ite_eq]
            simp [hsub t (by simp : t ∈ t :: ts)]
        _ = (if p t then g t else 0) + (ts.map (fun s => if p s then g s else 0)).sum := by
          rw [add_comm]

/-! ## Bridge from the `foldr` definitions to `Finset` sums -/

theorem foldr_eq_sum {α M : Type} [AddCommMonoid M] (l : List α) (h : α → M) :
    l.foldr (fun e acc => h e + acc) 0 = (l.map h).sum := by
  rw [List.sum, List.foldr_map]

theorem foldr_ite_eq_sum {α M : Type} [AddCommMonoid M] (l : List α)
    (c : α → Prop) [DecidablePred c] (h : α → M) :
    l.foldr (fun e acc => (if c e then h e else 0) + acc) 0
      = (l.map (fun e => if c e then h e else 0)).sum := by
  rw [foldr_eq_sum]

/-- The `foldr` definition of `throughput` is the `Finset` sum over the graph. -/
theorem throughput_eq_sum (rep : W → W) (f : BdFlow A W) (edges : List (BdEdge A W))
    (hNodup : edges.Nodup) (v : W) :
    throughput A W rep f edges v
      = ∑ e ∈ edges.toFinset, (if rep e.sx = v then f e else 0) := by
  unfold throughput
  rw [show (fun e acc => (if rep e.sx = v then f e + acc else acc))
        = (fun e acc => (if rep e.sx = v then f e else 0) + acc) from by
      funext e acc; by_cases h : rep e.sx = v <;> simp [h]]
  rw [foldr_ite_eq_sum, ← List.sum_toFinset (fun e => if rep e.sx = v then f e else 0) hNodup]

/-- The `foldr` definition of `balCore` is the difference of two `Finset` sums. -/
theorem balCore_eq_sum (rep : W → W) (f : BdFlow A W) (edges : List (BdEdge A W))
    (hNodup : edges.Nodup) (v : W) :
    balCore A W rep f edges v
      = (∑ e ∈ edges.toFinset, (if rep e.sx = v then (f e : ℤ) * e.sgnX else 0))
        + (∑ e ∈ edges.toFinset, (if rep e.sy = v then (f e : ℤ) * e.sgnY else 0)) := by
  unfold balCore
  congr 1
  · rw [foldr_eq_sum, ← List.sum_toFinset (fun e => (f e : ℤ) * e.sgnX) (hNodup.filter _)]
    rw [List.toFinset_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    by_cases h : rep e.sx = v <;> simp [h]
  · rw [foldr_eq_sum, ← List.sum_toFinset (fun e => (f e : ℤ) * e.sgnY) (hNodup.filter _)]
    rw [List.toFinset_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    by_cases h : rep e.sy = v <;> simp [h]

/-! ## Sum-of-indicator helpers -/

theorem sum_ite_one_eq_countP {β : Type} (l : List β) (q : β → Prop) [DecidablePred q] :
    (l.map (fun x => if q x then (1 : ℕ) else 0)).sum = l.countP (fun x => decide (q x)) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
    by_cases h : q a
    · simp [h]; omega
    · simp [h]

theorem sum_finRange_eq {n : Nat} {M : Type} [AddCommMonoid M] (F : Fin n → M) :
    ((List.finRange n).map F).sum = ∑ i : Fin n, F i := by
  rw [← List.sum_toFinset F (List.nodup_finRange n), List.toFinset_finRange]

/-! ## The two main computations -/

/-- **Throughput.**  The throughput of the walk flow is exactly the number of
times the walk visits the molecule class: `throughput (sp.flow) edges v =
sp.visits v`. -/
theorem throughput_eq_visits {n readLen : Nat} (rep : W → W) (sp : Spelling A W n)
    (edges : List (BdEdge A W)) (hNodup : edges.Nodup)
    (hSteps : ∀ i : Fin n, sp.step rep readLen i ∈ edges) (v : W) :
    throughput A W rep (sp.flow rep readLen) edges v = sp.visits rep v := by
  rw [throughput_eq_sum rep (sp.flow rep readLen) edges hNodup v]
  simp only [flow_eq_mult rep readLen sp]
  have hconv : ∑ e ∈ edges.toFinset,
        (if rep e.sx = v then (walkSteps rep readLen sp).countP (fun s => decide (s = e)) else 0)
      = ∑ e ∈ edges.toFinset, (walkSteps rep readLen sp).countP (fun s => decide (s = e))
          • (if rep e.sx = v then (1 : ℕ) else 0) := by
    apply Finset.sum_congr rfl
    intro e _
    by_cases h : rep e.sx = v <;> simp [h]
  rw [hconv, weighted_dedup edges (walkSteps rep readLen sp)
        (walkSteps_subset rep sp edges hSteps) (fun e => rep e.sx = v) (fun _ => (1 : ℕ))]
  rw [sum_ite_one_eq_countP]
  rw [List.countP_eq_length_filter]
  unfold Spelling.visits walkSteps
  rw [List.filter_map]
  simp only [List.length_map]
  rfl

/-! ## Cyclic successor/predecessor arithmetic -/

omit [DecidableEq W] in
/-- The cyclic predecessor inverts the cyclic successor. -/
theorem pred_next {n : Nat} (sp : Spelling A W n) (i : Fin n) : pred sp (next sp i) = i := by
  apply Fin.ext
  simp only [next, pred]
  have hn : 0 < n := sp.hn
  have hlt : i.val < n := i.isLt
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hlt) with h | h
  · have h' : i.val + 1 = n := by omega
    rw [h', Nat.mod_self]
    have h2 : (0 + n - 1) % n = n - 1 := by
      rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    rw [h2]
    omega
  · have hmod : (i.val + 1) % n = i.val + 1 := Nat.mod_eq_of_lt h
    rw [hmod]
    have heq : i.val + 1 + n - 1 = i.val + n := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]

omit [DecidableEq W] in
/-- The cyclic successor inverts the cyclic predecessor. -/
theorem next_pred {n : Nat} (sp : Spelling A W n) (i : Fin n) : next sp (pred sp i) = i := by
  apply Fin.ext
  simp only [next, pred]
  have hn : 0 < n := sp.hn
  have hlt : i.val < n := i.isLt
  rcases Nat.eq_zero_or_pos i.val with h | h
  · rw [h]
    have h2 : (0 + n - 1) % n = n - 1 := by
      rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    rw [h2]
    have h3 : (n - 1 + 1) % n = 0 := by
      rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
    rw [h3]
  · have h2 : (i.val + n - 1) % n = i.val - 1 := by
      have heq : i.val + n - 1 = (i.val - 1) + n := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [h2]
    have h3 : (i.val - 1 + 1) % n = i.val := by
      rw [Nat.sub_add_cancel h, Nat.mod_eq_of_lt hlt]
    rw [h3]

omit [DecidableEq W] in
/-- The cyclic successor as a permutation of the read positions. -/
def nextEquiv {n : Nat} (sp : Spelling A W n) : Fin n ≃ Fin n where
  toFun := next sp
  invFun := pred sp
  left_inv := pred_next sp
  right_inv := next_pred sp

/-- **Balance.**  The signed-incidence balance of the walk flow vanishes at every
vertex, because the arriving and departing incidences are opposite along a
bidirected circuit. -/
theorem balCore_eq_zero {n readLen : Nat} (rep : W → W) (sp : Spelling A W n)
    (edges : List (BdEdge A W)) (hNodup : edges.Nodup)
    (hSteps : ∀ i : Fin n, sp.step rep readLen i ∈ edges)
    (hCircuit : BidirectedCircuit rep readLen sp) (v : W) :
    balCore A W rep (sp.flow rep readLen) edges v = 0 := by
  rw [balCore_eq_sum rep (sp.flow rep readLen) edges hNodup v]
  simp only [flow_eq_mult rep readLen sp]
  have hX : ∑ e ∈ edges.toFinset,
        (if rep e.sx = v then ((walkSteps rep readLen sp).countP (fun s => decide (s = e)) : ℤ) * e.sgnX else 0)
      = ((walkSteps rep readLen sp).map
          (fun (s : BdEdge A W) => if rep s.sx = v then s.sgnX else 0)).sum := by
    have := weighted_dedup (M := ℤ) edges (walkSteps rep readLen sp)
      (walkSteps_subset rep sp edges hSteps) (fun e => rep e.sx = v) (fun e => e.sgnX)
    simpa [nsmul_eq_mul] using this
  have hY : ∑ e ∈ edges.toFinset,
        (if rep e.sy = v then ((walkSteps rep readLen sp).countP (fun s => decide (s = e)) : ℤ) * e.sgnY else 0)
      = ((walkSteps rep readLen sp).map
          (fun (s : BdEdge A W) => if rep s.sy = v then s.sgnY else 0)).sum := by
    have := weighted_dedup (M := ℤ) edges (walkSteps rep readLen sp)
      (walkSteps_subset rep sp edges hSteps) (fun e => rep e.sy = v) (fun e => e.sgnY)
    simpa [nsmul_eq_mul] using this
  rw [hX, hY]
  have hA : ((walkSteps rep readLen sp).map
        (fun (s : BdEdge A W) => if rep s.sx = v then s.sgnX else 0)).sum
      = ∑ j : Fin n, (if rep (sp.strand j) = v then (sp.step rep readLen j).sgnX else 0) := by
    rw [walkSteps, List.map_map, sum_finRange_eq]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Function.comp_apply, Spelling.step, bdEdge]
    by_cases h : rep (sp.strand j) = v <;> simp [h]
  have hB : ((walkSteps rep readLen sp).map
        (fun (s : BdEdge A W) => if rep s.sy = v then s.sgnY else 0)).sum
      = ∑ j : Fin n, (if rep (sp.strand (next sp j)) = v then (sp.step rep readLen j).sgnY else 0) := by
    rw [walkSteps, List.map_map, sum_finRange_eq]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Function.comp_apply, Spelling.step, bdEdge]
    by_cases h : rep (sp.strand (next sp j)) = v <;> simp [h]
  rw [hA, hB]
  have hreindex : ∑ j : Fin n,
        (if rep (sp.strand (next sp j)) = v then (sp.step rep readLen j).sgnY else 0)
      = ∑ j : Fin n,
        (if rep (sp.strand j) = v then (sp.step rep readLen (pred sp j)).sgnY else 0) := by
    rw [← Equiv.sum_comp (nextEquiv sp)
      (fun j => if rep (sp.strand j) = v then (sp.step rep readLen (pred sp j)).sgnY else 0)]
    apply Finset.sum_congr rfl
    intro j _
    simp only [nextEquiv, Equiv.coe_fn_mk, pred_next]
  rw [hreindex, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j _
  rw [hCircuit j]
  by_cases h : rep (sp.strand j) = v <;> simp [h]

/-! ## The adapter -/

/-- **The spelled-circuit → feasible-flow adapter (#261).**  The cyclic window
walk of a circular spelling, whose steps all lie in the `Nodup` graph `edges` and
form a bidirected circuit, and which visits every observed vertex at least once,
carries a genuine §6.2 zero-terminal feasible flow whose count vector is exactly
`Spelling.visits`. -/
theorem spelling_flow_feasible {n readLen : Nat} (rep : W → W) (sp : Spelling A W n)
    (verts : List W) (edges : List (BdEdge A W)) (hNodup : edges.Nodup)
    (hSteps : ∀ i : Fin n, sp.step rep readLen i ∈ edges)
    (hCircuit : BidirectedCircuit rep readLen sp)
    (hVisit : ∀ v ∈ verts, 1 ≤ sp.visits rep v) :
    Feasible62 A W rep verts edges (sp.flow rep readLen) (noTerminals W) (sp.visits rep) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro e _
    exact Nat.zero_le _
  · intro v hv
    rw [throughput_eq_visits rep sp edges hNodup hSteps v]
    exact hVisit v hv
  · intro v _
    simp only [balance, noTerminals]
    rw [balCore_eq_zero rep sp edges hNodup hSteps hCircuit v]
    ring
  · intro v _
    exact throughput_eq_visits rep sp edges hNodup hSteps v
  · intro v
    exact noTerminals_usage_zero W v

/-- **Spelled throughputs lie in the feasible throughput image.**  The count
vector `Spelling.visits` of a spelled circuit is the throughput vector of a
member of the zero-terminal §6.2 feasible set, hence an element of the throughput
image to which the count-vector likelihood criteria apply. -/
theorem visits_mem_throughput_image {n readLen : Nat} (rep : W → W) (sp : Spelling A W n)
    (verts : List W) (edges : List (BdEdge A W)) (hNodup : edges.Nodup)
    (hSteps : ∀ i : Fin n, sp.step rep readLen i ∈ edges)
    (hCircuit : BidirectedCircuit rep readLen sp)
    (hVisit : ∀ v ∈ verts, 1 ≤ sp.visits rep v) :
    sp.visits rep ∈ Set.image (fun f => throughputVec rep f edges)
        (AssemblyP1.Section62FlowCountVectorAdapter.feasibleFlowSet rep verts edges) := by
  refine ⟨sp.flow rep readLen, ?_, ?_⟩
  · show Feasible62 A W rep verts edges (sp.flow rep readLen) (noTerminals W)
      (throughputVec rep (sp.flow rep readLen) edges)
    rw [show throughputVec rep (sp.flow rep readLen) edges = sp.visits rep from
      funext (fun v => throughput_eq_visits rep sp edges hNodup hSteps v)]
    exact spelling_flow_feasible rep sp verts edges hNodup hSteps hCircuit hVisit
  · exact funext (fun v => throughput_eq_visits rep sp edges hNodup hSteps v)

end AssemblyP1.Section62SpelledFlowAdapter
